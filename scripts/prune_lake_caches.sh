#!/usr/bin/env bash
# Prune superseded Lake caches of this repository.  Run by the
# lake-cache-release workflow after it publishes a release; can also be run by
# hand (needs a `gh` login with `actions: write` and `contents: write`).
#
#   scripts/prune_lake_caches.sh [--dry-run]
#
# Actions cache, per-branch entries of restore-lake-cache (`lake-build-*`):
#   - entries of dtests-handoff itself (the new release supersedes them);
#   - entries of refs whose branch was deleted or whose PR is closed;
#   - in every lineage (ref + branch + job), all but the newest entry.
# Releases: all but the newest $KEEP_RELEASES (default 3) published
# `lake-cache-*` releases, together with their tags.
set -euo pipefail
repo="${GITHUB_REPOSITORY:-Rogerhu12/hecke-seven-eighths}"
base="${BASE_BRANCH:-dtests-handoff}"
keep="${KEEP_RELEASES:-3}"
dry=false
[ "${1:-}" = --dry-run ] && dry=true

del() { # description, api path
  echo "delete $1"
  $dry || gh api -X DELETE "$2" >/dev/null || echo "::warning::could not delete $1"
}

branches="$(gh api --paginate "repos/$repo/branches?per_page=100" --jq '.[].name')"
open_prs="$(gh pr list -R "$repo" --state open --limit 500 --json number --jq '.[].number')"
live_ref() {
  case "$1" in
    "refs/heads/$base") return 1 ;;
    refs/heads/*) grep -qxF "${1#refs/heads/}" <<<"$branches" ;;
    refs/pull/*/merge) n="${1#refs/pull/}"; grep -qxF "${n%/merge}" <<<"$open_prs" ;;
    *) return 0 ;;
  esac
}

# id ref key size created, newest first
gh api --paginate "repos/$repo/actions/caches?per_page=100&key=lake-build-&sort=created_at&direction=desc" \
  --jq '.actions_caches[] | [.id, .ref, .key, .size_in_bytes, .created_at] | @tsv' > "${TMPDIR:-/tmp}/lake-caches.tsv"
declare -A seen=()
kept=0
while IFS=$'\t' read -r id ref key size created; do
  lineage="$ref ${key%:*}"
  if ! live_ref "$ref"; then
    del "cache $key ($ref, superseded or gone)" "repos/$repo/actions/caches/$id"
  elif [ -n "${seen[$lineage]:-}" ]; then
    del "cache $key ($ref, older than ${seen[$lineage]})" "repos/$repo/actions/caches/$id"
  else
    seen[$lineage]="$key"
    kept=$((kept + size))
  fi
done < "${TMPDIR:-/tmp}/lake-caches.tsv"
echo "kept ${#seen[@]} per-branch entries, $((kept / 1048576)) MiB"

gh release list -R "$repo" --limit 100 --exclude-drafts --json tagName,publishedAt \
  --jq '[.[] | select(.tagName | startswith("lake-cache-"))] | sort_by(.publishedAt) | reverse | .[].tagName' \
  | tail -n +"$((keep + 1))" | while read -r tag; do
    echo "delete release $tag"
    $dry || gh release delete "$tag" -R "$repo" --yes --cleanup-tag || echo "::warning::could not delete release $tag"
  done
gh api "repos/$repo/actions/cache/usage" --jq '"Actions cache in use: \(.active_caches_count) entries, \(.active_caches_size_in_bytes / 1048576 | floor) MiB"'
