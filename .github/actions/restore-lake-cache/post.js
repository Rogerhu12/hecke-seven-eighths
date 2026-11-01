// Post step (post-if: always()): save this run's `.lake/build` outputs to the
// per-branch Actions cache (save.sh). It never fails the job.
const { spawnSync } = require("child_process");
const path = require("path");

const r = spawnSync("bash", [path.join(__dirname, "save.sh")], { stdio: "inherit", env: process.env });
if (r.error) console.log(`::warning::save.sh: ${r.error.message}`);
process.exit(0);
