#!/usr/bin/env bash
# `split --filter` helper of save.sh: uploads stdin as one Azure block blob
# block named after $FILE (blk-00000, blk-00001, ...).
set -uo pipefail
tmp="$RLC_BLOCKS/$FILE.bin"
cat > "$tmp"
id="$(printf 'rlc-%s' "$FILE" | base64 -w0)"
id_q="$(jq -rn --arg s "$id" '$s|@uri')"
if curl -fsS --retry 5 --retry-all-errors -X PUT -H 'Content-Type: application/octet-stream' \
    -T "$tmp" "$RLC_UPLOAD_URL&comp=block&blockid=$id_q" -o /dev/null; then
  printf '%s' "$id" > "$RLC_BLOCKS/$FILE.id"
  stat -c %s "$tmp" > "$RLC_BLOCKS/$FILE.size"
else
  touch "$RLC_BLOCKS/failed"
fi
rm -f "$tmp"
