#!/usr/bin/env bash
# Post step of restore-lake-cache (post-if: always(), so it also runs after a
# failed, timed-out or cancelled build).  Saves to the per-branch Actions cache
# the `.lake/build` files this branch compiled: those restored from the
# previous per-branch entry plus those Lake wrote during this job.  Files that
# only came from the release are not saved again.  Never fails the job.
#
# A step can skip the save by creating "$RUNNER_TEMP/restore-lake-cache/skip-save"
# (the lake-cache-release workflow does, after publishing a release).
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=cache-lib.sh
. "$here/cache-lib.sh"

work="${STATE_RLC_WORK:-}"
key="${STATE_RLC_KEY:-}"
mode="${STATE_RLC_MODE:-false}"
if [ "$mode" != true ] || [ -z "$work" ] || [ -z "$key" ]; then
  echo "Per-branch cache: not saving (branch-cache: $mode)."
  exit 0
fi
if [ -e "${RUNNER_TEMP:-/tmp}/restore-lake-cache/skip-save" ]; then
  echo "Per-branch cache: not saving (skip-save requested by the workflow)."
  exit 0
fi
if ! rlc_cache_available; then
  echo "::warning::Actions cache service not available; not saving."
  exit 0
fi
cd "${STATE_RLC_ROOT:-.}" || exit 0
[ -f "$work/marker" ] || { echo "::warning::Per-branch cache: restore marker missing; not saving."; exit 0; }

start=$SECONDS
rlc_list_build_files -newer "$work/marker" | sort > "$work/new.txt"
new_count="$(wc -l < "$work/new.txt")"
if [ "$new_count" -eq 0 ]; then
  echo "Per-branch cache: Lake wrote no new outputs; the restored entry ${STATE_RLC_MATCHED:-(none)} stays current."
  exit 0
fi
# Keep the previously restored files that still exist (Lake may have replaced
# some of them; those are in new.txt as well).
{
  cat "$work/new.txt"
  while IFS= read -r f; do [ -f "$f" ] && printf '%s\n' "$f"; done < "$work/restored.txt"
} | grep -E '^\.lake/build/(lib/lean|ir)/' | sort -u > "$work/save.txt"
total="$(xargs -d '\n' -a "$work/save.txt" stat -c %s 2>/dev/null | awk '{s += $1} END {print s + 0}')"
echo "Per-branch cache: saving $(wc -l < "$work/save.txt") files ($new_count written by this job, $(rlc_human "$total") uncompressed) as $key"

req="$(jq -cn --arg key "$key" --arg version "$RLC_VERSION" '{key: $key, version: $version}')"
if ! resp="$(rlc_twirp CreateCacheEntry "$req")"; then
  echo "::warning::Per-branch cache: could not reserve $key: $resp"
  exit 0
fi
upload_url="$(jq -r '.signed_upload_url // .signedUploadUrl // empty' <<<"$resp")"
if [ "$(jq -r '.ok // false' <<<"$resp")" != true ] || [ -z "$upload_url" ]; then
  echo "::warning::Per-branch cache: could not reserve $key: $resp"
  exit 0
fi

# Stream tar | zstd into 64 MiB Azure blob blocks (no full archive on disk).
blocks="$work/blocks"
rm -rf "$blocks" && mkdir -p "$blocks"
export RLC_UPLOAD_URL="$upload_url" RLC_BLOCKS="$blocks"
tar -cf - --no-recursion -T "$work/save.txt" \
  | zstd -q -3 -T0 -c \
  | split -b 64M -a 5 -d --filter="bash '$here/put-block.sh'" - blk-
status=("${PIPESTATUS[@]}")
if [ "${status[0]}" -ne 0 ] || [ "${status[1]}" -ne 0 ] || [ "${status[2]}" -ne 0 ] || [ -e "$blocks/failed" ]; then
  echo "::warning::Per-branch cache: upload failed (tar/zstd/split: ${status[*]}); not saved."
  exit 0
fi
size="$(cat "$blocks"/*.size | awk '{s += $1} END {print s + 0}')"
{
  echo '<?xml version="1.0" encoding="utf-8"?><BlockList>'
  for f in $(ls "$blocks"/*.id | sort); do printf '<Latest>%s</Latest>' "$(cat "$f")"; done
  echo '</BlockList>'
} > "$work/blocklist.xml"
if ! curl -fsS --retry 3 --retry-all-errors -X PUT -H 'Content-Type: application/xml' \
    --data-binary @"$work/blocklist.xml" "$upload_url&comp=blocklist" -o /dev/null; then
  echo "::warning::Per-branch cache: committing the upload failed; not saved."
  exit 0
fi
req="$(jq -cn --arg key "$key" --arg version "$RLC_VERSION" --arg size "$size" '{key: $key, version: $version, size_bytes: $size}')"
if resp="$(rlc_twirp FinalizeCacheEntryUpload "$req")" && [ "$(jq -r '.ok // false' <<<"$resp")" = true ]; then
  echo "Per-branch cache: saved $key ($(rlc_human "$size") compressed) in $((SECONDS - start))s"
else
  echo "::warning::Per-branch cache: finalizing $key failed: $resp"
fi
rm -rf "$blocks"
exit 0
