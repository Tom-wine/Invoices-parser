import email
import imaplib
import logging
import os
import re
import time
from datetime import datetime
from email.header import decode_header, make_header

import cv2
import fitz  # PyMuPDF
import numpy as np
import pandas as pd
import pytesseract
from concurrent.futures import ThreadPoolExecutor, as_completed
from rapidfuzz import fuzz
from schwifty import IBAN, exceptions

# ← Update this path if your Tesseract installation differs:
pytesseract.pytesseract.tesseract_cmd = r"C:\Program Files\Tesseract-OCR\tesseract.exe"

# ---------------------
# Configuration
# ---------------------
EMAIL_USER = "Your email"
EMAIL_PASS = "Your imap password"
IMAP_SERVER = "Imap server"
SAVE_DIR = "./invoices"
VAT_RATE = 0.20
MAX_INVOICES = 200  # Max number of invoices to parse

# Only download attachments from emails matching these keywords
invoice_regex = re.compile(r"\b(?:facture|fact\.?|invoice|inv\.?|réf)\b", re.IGNORECASE)

logging.basicConfig(
    filename="log.txt",
    level=logging.DEBUG,
    format="%(asctime)s [%(levelname)s] %(message)s",
)

os.makedirs(SAVE_DIR, exist_ok=True)


def sanitize_filename(filename):
    filename = re.sub(r'[<>:"/\\|?*]', '_', filename)
    return filename.replace('\n', '').replace('\r', '')


def parse_amount(s):
    s = s.strip().replace('\u00A0', ' ')  # non-breaking spaces
    s = s.replace(' ', '').replace(',', '.')
    try:
        return float(s)
    except ValueError:
        return None


def find_amount(patterns, text):
    for pat in patterns:
        for m in re.finditer(pat, text):
            amt = parse_amount(m.group(1))
            if amt is not None:
                return amt
    return None


def find_payment_details(text, due_date_str):
    """Extract payment details from text"""
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if due_date_str in line:
            detail = line.strip()
            if i > 0 and re.search(r'(?i)r[ée]glement|paiement|payable', lines[i - 1]):
                detail = lines[i - 1].strip() + " " + detail
            if i < len(lines) - 1 and lines[i + 1].strip():
                detail += " " + lines[i + 1].strip()
            return detail
    return ""


def find_ht(text):
    """Extract HT (pre-tax) amount from text"""
    patterns = [
        r'(?i)(?:total\s+HT|montant\s+HT|net\s+HT|HT|H\.T\.|hors\s+taxe)\s*[:\-]?\s*([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)([\d\s]+(?:[.,]\d{1,3}))\s*(?:€|\$)?\s*(?:HT|H\.T\.|hors\s+taxe)',
        r'(?i)total\s*(?:HT|hors\s*taxe).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)montant\s*(?:HT|hors\s*taxe).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)prix\s*(?:HT|hors\s*taxe).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)sous[- ]?total.*?([\d\s]+(?:[.,]\d{1,3}))'
    ]
    for pat in patterns:
        for m in re.finditer(pat, text):
            try:
                return parse_amount(m.group(1))
            except Exception as e:
                logging.debug(f"Failed to parse HT value: {e}")
    return None


def find_tva_amount(text):
    """Extract TVA (tax) amount from text"""
    patterns = [
        r'(?i)(?:TVA|T\.V\.A\.|taxe)\s*[:\-]?\s*([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)(?:TVA|T\.V\.A\.|taxe)\s*(?:à\s*\d{1,2}[.,]\d{1,2}\s*%)\s*[:\-]?\s*([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)montant\s*(?:de\s*la\s*)?(?:TVA|T\.V\.A\.|taxe).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)total\s*(?:TVA|T\.V\.A\.|taxe).*?([\d\s]+(?:[.,]\d{1,3}))'
    ]
    for pat in patterns:
        for m in re.finditer(pat, text):
            try:
                return parse_amount(m.group(1))
            except:
                continue
    return None


def find_ttc(text):
    """Extract TTC (tax-included) amount from text"""
    patterns = [
        r'(?i)(?:total\s*TTC|montant\s*TTC|TTC|T\.T\.C\.|toutes\s*taxes\s*comprises)\s*[:\-]?\s*([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)([\d\s]+(?:[.,]\d{1,3}))\s*(?:€|\$)?\s*(?:TTC|T\.T\.C\.|toutes\s*taxes\s*comprises)',
        r'(?i)(?:total|montant|prix)\s*(?:à\s*payer).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)(?:net\s*à\s*payer|à\s*payer).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)total\s*(?:général|global).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)montant\s*(?:total).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)total\s*(?:du\s*document).*?([\d\s]+(?:[.,]\d{1,3}))',
        r'(?i)(?:total|montant)\s*(?:\(|en\s*)?(?:€|euros?|EUR)(?:\)|).*?([\d\s]+(?:[.,]\d{1,3}))'
    ]
    for pat in patterns:
        for m in re.finditer(pat, text):
            try:
                return parse_amount(m.group(1))
            except:
                continue
    # Fallback: scan bottom lines
    lines = text.splitlines()
    bottom = "\n".join(lines[-20:])
    vals = re.findall(r'(?:€|\$|EUR)?\s*([\d\s]+(?:[.,]\d{1,3}))', bottom)
    amounts = [parse_amount(v) for v in vals]
    return max([amt for amt in amounts if amt is not None], default=None)


def find_numbers_at_bottom(text):
    """Find numerical values at the bottom of the document"""
    lines = text.splitlines()
    last_lines = lines[-20:]
    vals = re.findall(r'(?:€|\$|EUR)?\s*([\d\s]+(?:[.,]\d{1,3}))', "\n".join(last_lines))
    amounts = [parse_amount(v) for v in vals]
    return max([amt for amt in amounts if amt is not None], default=None)


def compute_missing_amounts(ht, tva, ttc):
    """Compute missing HT, TVA, or TTC using VAT_RATE"""
    if ttc is not None:
        if ht is None and tva is not None:
            ht = ttc - tva
        elif ht is None:
            ht = ttc / (1 + VAT_RATE)
        if tva is None and ht is not None:
            tva = ttc - ht
    else:
        if ht is not None:
            if tva is not None:
                ttc = ht + tva
            else:
                tva = ht * VAT_RATE
                ttc = ht + tva
        else:
            ttc = None
    return ht, tva, ttc


def extract_fields(text, sender_email, pdf_path):
    """Extract all invoice fields from the text"""
    invoice_no = find_invoice_number(text)
    due_date = find_due_date(text)
    ht = find_ht(text)
    tva = find_tva_amount(text)
    ttc = find_ttc(text)
    ht, tva, ttc = compute_missing_amounts(ht, tva, ttc)
    payment_details = find_payment_details(text, due_date)
    iban = find_iban(text)

    return {
        "Facture_numero": invoice_no,
        "HT": round(ht, 2) if ht is not None else None,
        "TVA": round(tva, 2) if tva is not None else None,
        "TTC": round(ttc, 2) if ttc is not None else None,
        "Produits": [],
        "Echeance": due_date,
        "Details_paiement": payment_details,
        "Expediteur": sender_email,
        "IBAN": iban,
        "Email_sender": sender_email,
        "pdf_path": pdf_path
    }


def find_invoice_number(text):
    patterns = [
        r'(?i)\b(?:facture|invoice)\s*(?:no\.?|n°|#)?\s*[:\-]?\s*([A-Z0-9\-/]+)',
        r'(?i)\b(?:réf|ref)\s*[:\-]?\s*([A-Z0-9\-/]+)',
    ]
    for pat in patterns:
        m = re.search(pat, text)
        if m:
            return m.group(1).strip()
    for line in text.splitlines():
        if fuzz.partial_ratio("facture", line) > 75:
            m = re.search(r'([A-Z0-9\-/]+)', line)
            if m:
                return m.group(1)
    return ""


def find_due_date(text):
    for m in re.finditer(r"\b(\d{1,2})/(\d{1,2})/(\d{2,4})\b", text):
        d, mo, yr = m.groups()
        if len(yr) == 2:
            yr = f"20{yr}"
        try:
            return datetime.strptime(f"{d}/{mo}/{yr}", "%d/%m/%Y").strftime("%d/%m/%Y")
        except ValueError:
            continue
    for m in re.finditer(r"\b(\d{4})-(\d{2})-(\d{2})\b", text):
        y, mo, d = m.groups()
        try:
            return datetime.strptime(f"{d}/{mo}/{y}", "%d/%m/%Y").strftime("%d/%m/%Y")
        except ValueError:
            continue
    return ""


def find_iban(text):
    candidates = re.findall(r"\b[A-Z]{2}\d{2}(?:[ \-]?[A-Z0-9]){11,30}\b", text.upper())
    for cand in candidates:
        raw = re.sub(r"[\s\-]", "", cand)
        try:
            iban = IBAN(raw)
            return iban.compact
        except exceptions.SchwiftyException:
            continue
    return ""


def is_invoice(text):
    return all([
        find_invoice_number(text),
        find_due_date(text),
        re.search(r"(?i)\bTVA\b|\btaxe\b", text),
        re.search(r"\b\d+[.,]?\d*\s?€", text)
    ])


def extract_text_from_pdf(path):
    try:
        doc = fitz.open(path)
    except RuntimeError:
        logging.warning(f"Cannot open PDF (encrypted or corrupt), skipping: {path}")
        return ""
    all_text = ""
    for page in doc:
        text = page.get_text("text") or ""
        if not text.strip():
            pix = page.get_pixmap(dpi=300)
            img = cv2.imdecode(np.frombuffer(pix.tobytes(), dtype=np.uint8), cv2.IMREAD_COLOR)
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
            thresh = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 31, 2)
            for psm in (6, 4, 11, 3):
                ocr = pytesseract.image_to_string(thresh, lang="fra+eng+deu", config=f"--psm {psm}")
                if ocr.strip():
                    text = ocr
                    break
        all_text += text + "\n"
    doc.close()
    return all_text


def _fetch_batch(batch_ids):
    out = []
    m = imaplib.IMAP4_SSL(IMAP_SERVER)
    m.login(EMAIL_USER, EMAIL_PASS)
    m.select("inbox")
    for eid in batch_ids:
        try:
            _, data = m.fetch(eid, "(RFC822)")
            for part in data:
                if isinstance(part, tuple):
                    msg = email.message_from_bytes(part[1])
                    subj = str(make_header(decode_header(msg.get("Subject", ""))))
                    if not invoice_regex.search(subj):
                        continue
                    sender = email.utils.parseaddr(msg.get("From"))[1]
                    for p in msg.walk():
                        if p.get_content_maintype() != 'multipart' and p.get("Content-Disposition"):
                            fn = p.get_filename()
                            if fn and fn.lower().endswith(".pdf"):
                                raw = decode_header(fn)[0][0]
                                name = raw.decode() if isinstance(raw, bytes) else raw
                                name = sanitize_filename(name)
                                path = os.path.join(SAVE_DIR, f"{name}_{int(time.time()*1000)}.pdf")
                                if os.path.exists(path):
                                    continue
                                with open(path, "wb") as f:
                                    f.write(p.get_payload(decode=True))
                                print(f"📥 Downloaded: {os.path.basename(path)}")
                                out.append((path, sender))
        except Exception:
            logging.exception("Error fetching email batch")
    m.logout()
    return out


def login_and_fetch_emails():
    print("🔌 Connecting to IMAP server...")
    pdfs = []
    try:
        mail = imaplib.IMAP4_SSL(IMAP_SERVER)
        mail.login(EMAIL_USER, EMAIL_PASS)
        print("✅ IMAP login successful.")
        mail.select("inbox")
        _, msgs = mail.search(None, 'OR SUBJECT "facture" SUBJECT "invoice"')
        ids = msgs[0].split()[::-1]
        print(f"Found {len(ids)} invoice-like messages.")
    except Exception:
        logging.exception("IMAP login/fetch error")
        print("❌ Failed to connect or authenticate.")
        return pdfs

    def batches():
        batch = []
        for eid in ids:
            batch.append(eid)
            if len(batch) >= 100:
                yield batch
                batch = []
        if batch:
            yield batch

    print(f"🗂️  Fetching up to {MAX_INVOICES} invoices in batches...")
    with ThreadPoolExecutor(max_workers=20) as ex:
        for fut in as_completed([ex.submit(_fetch_batch, b) for b in batches()]):
            batch_pdfs = fut.result()
            pdfs.extend(batch_pdfs)
            print(f"Downloaded batch: {len(batch_pdfs)} (total {len(pdfs)})")
            if len(pdfs) >= MAX_INVOICES:
                break

    return pdfs[:MAX_INVOICES]


def process_attachment(path, sender_email):
    print(f"📄 Processing {os.path.basename(path)}...")
    text = extract_text_from_pdf(path)
    if not is_invoice(text):
        print(f"⏭️ Skipped non-invoice: {os.path.basename(path)}")
        logging.info(f"Skipped: {path}")
        return None
    data = extract_fields(text, sender_email, path)
    print(f"✅ Extracted #{data['Facture_numero']} (TTC={data['TTC']})")
    return data


def write_to_csv(rows, filename="invoices_output.csv"):
    df = pd.DataFrame(rows)
    for c in ["HT", "TVA", "TTC"]:
        df[c] = pd.to_numeric(df[c], errors="coerce").round(2)
    df.to_csv(filename, index=False, encoding="utf-8-sig", float_format="%.2f")
    print(f"💾 Wrote {len(rows)} records to {filename}.")


def main():
    start = time.time()
    attachments = login_and_fetch_emails()
    if not attachments:
        print("📭 No invoices to process.")
        return

    parsed = []
    with ThreadPoolExecutor(max_workers=min(50, os.cpu_count() * 5)) as ex:
        futures = [ex.submit(process_attachment, p, s) for p, s in attachments]
        for fut in as_completed(futures):
            res = fut.result()
            if not res:
                continue
            if any(res["Facture_numero"] == prev["Facture_numero"] and res["TTC"] == prev["TTC"] for prev in parsed):
                continue
            parsed.append(res)
            if len(parsed) >= MAX_INVOICES:
                break

    write_to_csv(parsed)
    print(f"✅ Finished: {len(parsed)} invoices parsed in {time.time()-start:.1f}s.")


if __name__ == "__main__":
    main()
