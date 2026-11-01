// Main step: restore the release, then the per-branch cache (restore.sh).
// The runner gives JavaScript actions ACTIONS_RUNTIME_TOKEN and
// ACTIONS_RESULTS_URL, which the Actions cache service needs; the child
// shell inherits them.
const { spawnSync } = require("child_process");
const path = require("path");

const input = (name, fallback = "") => {
  const v = process.env[`INPUT_${name.replace(/ /g, "_").toUpperCase()}`];
  return v === undefined || v === "" ? fallback : v.trim();
};

const env = {
  ...process.env,
  RLC_TAG: input("tag"),
  RLC_REPOSITORY: input("repository", process.env.GITHUB_REPOSITORY || ""),
  GH_TOKEN: input("token"),
  RLC_BRANCH_CACHE: input("branch-cache", "true"),
};
const r = spawnSync("bash", [path.join(__dirname, "restore.sh")], { stdio: "inherit", env });
if (r.error) console.log(`::error::restore.sh: ${r.error.message}`);
process.exit(r.status === null ? 1 : r.status);
