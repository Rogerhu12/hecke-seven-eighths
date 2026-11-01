# Shared helpers for restore.sh and save.sh (sourced, not executed).
#
# The per-branch cache talks to the Actions cache service (v2, the Twirp API
# that actions/cache uses) directly with curl, so that the save can run from
# this action's own post step with `post-if: always()`.  actions/cache's own
# post step has `post-if: success()`, and its `save-always` input never took
# effect, so neither it nor actions/cache/save placed inside a composite action
# can save the outputs of a failed build.
#
# Entries are only read and written by this action, so `version` is a fixed
# string of ours rather than actions/cache's hash of the paths.

RLC_VERSION="$(printf 'restore-lake-cache|lake-build|tar|zstd|v1' | sha256sum | cut -d' ' -f1)"

# Files of `.lake/build` that Lake needs to treat a module as up to date
# (the same selection as scripts/build_lake_cache.py; `ir/**.setup.json` is
# regenerated before every compilation and skipped).
rlc_list_build_files() { # [find predicates...]
  local roots=()
  [ -d .lake/build/lib/lean ] && roots+=(.lake/build/lib/lean)
  [ -d .lake/build/ir ] && roots+=(.lake/build/ir)
  [ ${#roots[@]} -gt 0 ] || return 0
  find "${roots[@]}" -type f "$@" \( \
      -name '*.trace' -o -name '*.olean' -o -name '*.olean.hash' \
      -o -name '*.ilean' -o -name '*.ilean.hash' \
      -o -name '*.olean.server' -o -name '*.olean.server.hash' \
      -o -name '*.olean.private' -o -name '*.olean.private.hash' \
      -o -name '*.ir' -o -name '*.ir.hash' -o -name '*.ir.sig' -o -name '*.ir.sig.hash' \
      -o -name '*.c' -o -name '*.c.hash' \)
}

rlc_cache_available() {
  [ -n "${ACTIONS_RUNTIME_TOKEN:-}" ] && [ -n "${ACTIONS_RESULTS_URL:-}" ]
}

# rlc_twirp METHOD JSON -> response body on stdout; non-zero on HTTP errors.
rlc_twirp() {
  local out code
  out="$(mktemp)"
  code="$(curl -sS --retry 3 --retry-all-errors --max-time 120 -o "$out" -w '%{http_code}' \
    -X POST "${ACTIONS_RESULTS_URL%/}/twirp/github.actions.results.api.v1.CacheService/$1" \
    -H "Authorization: Bearer $ACTIONS_RUNTIME_TOKEN" \
    -H 'Content-Type: application/json' -H 'Accept: application/json' \
    --data "$2")" || code=000
  cat "$out"
  rm -f "$out"
  [ "${code:0:1}" = 2 ]
}

rlc_human() { numfmt --to=iec --suffix=B "$1" 2>/dev/null || echo "$1 bytes"; }
