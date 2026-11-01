#!/usr/bin/env bash
# Main step of restore-lake-cache (started by main.js from the Lake project root).
#
# 1. Unpack the newest published lake-cache-* release (or RLC_TAG).
# 2. Unpack, on top of it, the newest per-branch Actions cache entry: the
#    `.lake/build` files that earlier runs of this branch compiled.  Lookup
#    order: same branch and job, same branch any job, base branch (pull
#    requests only).  The Actions cache scopes entries by ref, so a
#    pull_request run sees entries of its own PR and of the base branch, and a
#    push run sees entries of its own branch (and of the default branch).
# 3. Record what was restored and a timestamp, so that the post step (save.sh)
#    can save exactly the files this branch compiled.
#
# Overlaying older outputs is safe: Lake decides by the input hashes in the
# `.trace` files, so any module whose sources or imports changed is rebuilt.
# The per-branch layer is unpacked last because its files were compiled from
# this branch's sources, which the release (built from the base branch) may
# not match.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=cache-lib.sh
. "$here/cache-lib.sh"

step="$(printf '%s' "${GITHUB_ACTION:-restore}" | tr -c 'A-Za-z0-9_.-' '_')"
work="${RUNNER_TEMP:-/tmp}/restore-lake-cache/$step"
rm -rf "$work" && mkdir -p "$work"
mode="${RLC_BRANCH_CACHE:-true}"
case "$mode" in true|restore|false) ;; *) echo "::warning::branch-cache: unknown value '$mode', using true"; mode=true ;; esac

command -v zstd >/dev/null || { sudo apt-get update -qq && sudo apt-get install -y -qq zstd; }

# --- 1. release -------------------------------------------------------------
tag="${RLC_TAG:-}"
repo="${RLC_REPOSITORY:-$GITHUB_REPOSITORY}"
if [ -z "$tag" ]; then
  # Drafts are skipped: a release is only published once all parts are uploaded.
  tag="$(gh release list -R "$repo" --limit 100 --exclude-drafts --json tagName,publishedAt \
    --jq '[.[] | select(.tagName | startswith("lake-cache-"))] | sort_by(.publishedAt) | last | .tagName // ""')"
fi
if [ -z "$tag" ]; then
  echo "::warning::No lake-cache-* release found in $repo; building from scratch."
else
  if [ ! -d .lake/packages/TauCeti ]; then
    echo "::warning::.lake/packages/TauCeti is missing; run this action after 'lake exe cache get'."
  fi
  dl="$work/release"
  mkdir -p "$dl"
  echo "Restoring $tag from $repo"
  start=$SECONDS
  gh release download "$tag" -R "$repo" -D "$dl" \
    -p 'lake-cache.tar.zst.part-*' -p SHA256SUMS -p lake-cache-manifest.json
  (cd "$dl" && sha256sum -c SHA256SUMS)
  echo "Downloaded $(du -sh "$dl" | cut -f1) in $((SECONDS - start))s"
  cat "$dl"/lake-cache.tar.zst.part-* | zstd -d -T0 | tar -xf - --no-same-owner
  rm -f "$dl"/lake-cache.tar.zst.part-*
  jq -r '"Commit \(.commit); " + (.build_roots | to_entries | map("\(.key): \(.value.modules) modules") | join(", "))' \
    "$dl/lake-cache-manifest.json" || true
  echo "Restored $tag in $((SECONDS - start))s"
fi
echo "tag=$tag" >> "$GITHUB_OUTPUT"

# --- 2. per-branch cache ----------------------------------------------------
set +e
matched=""
key=""
if [ "$mode" = false ]; then
  echo "Per-branch cache disabled (branch-cache: false)."
elif ! rlc_cache_available; then
  echo "::warning::Actions cache service not available; per-branch cache disabled."
  mode=false
else
  env_hash="$(cat lean-toolchain lake-manifest.json 2>/dev/null | sha256sum | cut -c1-12)"
  prefix="lake-build-v1-$env_hash-"
  branch="${GITHUB_HEAD_REF:-${GITHUB_REF_NAME:-unknown}}"
  branch="${branch//,/_}"
  lineage="$(printf '%s' "$GITHUB_JOB" | tr -c 'A-Za-z0-9_.-' '_' | cut -c1-40)-$(printf '%s' "${GITHUB_WORKFLOW_REF:-$GITHUB_WORKFLOW}" | sed 's/@.*//' | sha256sum | cut -c1-6)"
  # The random part keeps matrix legs (same job id, same run) from colliding.
  key="$prefix$branch:$lineage:$GITHUB_RUN_ID-${GITHUB_RUN_ATTEMPT:-1}-$(od -An -N3 -tx1 /dev/urandom | tr -d ' \n')"
  restore_keys=("$prefix$branch:$lineage:" "$prefix$branch:")
  base="${GITHUB_BASE_REF:-}"
  if [ -n "$base" ] && [ "$base" != "$branch" ]; then restore_keys+=("$prefix${base//,/_}:"); fi
  req="$(jq -cn --arg key "$key" --arg version "$RLC_VERSION" '{key: $key, version: $version, restore_keys: $ARGS.positional}' \
    --args "${restore_keys[@]}")"
  echo "Per-branch cache: looking up ${restore_keys[*]}"
  if resp="$(rlc_twirp GetCacheEntryDownloadURL "$req")"; then
    url="$(jq -r '.signed_download_url // .signedDownloadUrl // empty' <<<"$resp")"
    matched="$(jq -r '.matched_key // .matchedKey // empty' <<<"$resp")"
  else
    echo "::warning::Per-branch cache lookup failed: $resp"
    url=""
  fi
  if [ -z "${url:-}" ] || [ -z "$matched" ]; then
    echo "Per-branch cache: no entry yet; the post step will save one."
    matched=""
  else
    start=$SECONDS
    if curl -fsSL --retry 3 --retry-all-errors -o "$work/branch.tar.zst" "$url"; then
      size="$(stat -c %s "$work/branch.tar.zst")"
      if zstd -d -T0 -c "$work/branch.tar.zst" | tar -xvf - --no-same-owner > "$work/restored.raw"; then
        grep -v '/$' "$work/restored.raw" > "$work/restored.txt"
        echo "Per-branch cache: restored $matched ($(rlc_human "$size") compressed, $(wc -l < "$work/restored.txt") files) in $((SECONDS - start))s"
      else
        echo "::warning::Per-branch cache: unpacking $matched failed; Lake will rebuild whatever is inconsistent."
        grep -v '/$' "$work/restored.raw" > "$work/restored.txt"
      fi
      rm -f "$work/branch.tar.zst" "$work/restored.raw"
    else
      echo "::warning::Per-branch cache: download of $matched failed."
      matched=""
    fi
  fi
fi
touch "$work/restored.txt"
# Everything Lake writes from now on is newer than this marker.
sleep 1
touch "$work/marker"
echo "branch-cache-key=$matched" >> "$GITHUB_OUTPUT"
{
  echo "RLC_WORK=$work"
  echo "RLC_ROOT=$PWD"
  echo "RLC_MODE=$mode"
  echo "RLC_KEY=$key"
  echo "RLC_MATCHED=$matched"
} >> "$GITHUB_STATE"
exit 0
