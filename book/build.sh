#!/usr/bin/env bash
# Build the Kindle EPUB3 for the Idea Theory monograph.
# Optimised for the Kindle reflowable renderer (KF8 / EPUB3).
# Send the resulting .epub directly to a Kindle via USB or
# the "Send to Kindle" app (supported since 2022 firmware).

set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build

# ── Cover image ───────────────────────────────────────────────────────────────
# Kindle recommends 1600×2400 px, 72 dpi, sRGB.
if [ ! -f cover.png ]; then
  if command -v convert >/dev/null 2>&1; then
    convert -size 1600x2400 xc:'#1a3553' \
      -fill white  -gravity North  -font 'Times-Bold'   -pointsize 130 \
      -annotate +0+400 'Idea Theory' \
      -fill '#cdd9e6' -font 'Times-Italic' -pointsize 64 \
      -annotate +0+600 'A Mathematical Formalism' \
      -annotate +0+700 'for the Zoo of Ideas About Ideas' \
      -fill '#a8b8ca' -font 'Times' -pointsize 52 \
      -annotate +0+1900 'The IdeaTheory Project' \
      cover.png
  else
    python3 - <<'PY'
import struct, zlib
W, H = 800, 1200
raw = b''.join(b'\x00' + bytes([26, 53, 83]) * W for _ in range(H))
def chunk(t, d):
    return struct.pack('>I', len(d)) + t + d + struct.pack('>I', zlib.crc32(t+d)&0xffffffff)
ihdr = struct.pack('>IIBBBBB', W, H, 8, 2, 0, 0, 0)
png  = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR',ihdr) + chunk(b'IDAT',zlib.compress(raw)) + chunk(b'IEND',b'')
open('cover.png','wb').write(png)
PY
  fi
fi

# ── Build EPUB3 ───────────────────────────────────────────────────────────────
EPUB=build/IdeaTheory.epub

pandoc book.tex \
  --from=latex \
  --to=epub3 \
  --metadata-file=metadata.yaml \
  --bibliography=references.bib \
  --citeproc \
  --mathml \
  --toc --toc-depth=2 \
  --epub-cover-image=cover.png \
  --css=epub.css \
  --top-level-division=chapter \
  --epub-chapter-level=1 \
  --number-sections \
  --split-level=1 \
  -o "$EPUB"

echo
echo "Built: $EPUB  ($(du -h "$EPUB" | cut -f1))"

# ── Optional AZW3 (older Kindles, or "Send to Kindle" desktop app) ────────────
if command -v ebook-convert >/dev/null 2>&1; then
  ebook-convert "$EPUB" build/IdeaTheory.azw3 \
    --output-profile=kindle_pw3 \
    --no-inline-toc \
    --max-toc-links=200 \
    --pretty-print
  echo "Built: build/IdeaTheory.azw3  ($(du -h build/IdeaTheory.azw3 | cut -f1))"
fi
