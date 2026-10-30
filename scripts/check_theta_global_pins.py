"""Check the exact repository and runtime pins used by THETA_GLOBAL CI."""

from pathlib import Path
import argparse
import json
import subprocess
import tomllib


ROOT = Path(__file__).resolve().parents[1]
LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB_COMMIT = "0493595ecd5da8ef14742febab99728f98e948e8"

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--runtime", action="store_true")
args = parser.parse_args()

toolchain = (ROOT / "lean-toolchain").read_text().strip()
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
config = tomllib.loads((ROOT / "lakefile.toml").read_text())
mathlib_manifest = next(p for p in manifest["packages"] if p["name"] == "mathlib")
mathlib_config = next(p for p in config["require"] if p["name"] == "mathlib")

report = {
    "lean_toolchain": toolchain,
    "lean_commit_expected": LEAN_COMMIT,
    "mathlib_manifest_rev": mathlib_manifest["rev"],
    "mathlib_config_rev": mathlib_config["rev"],
}
errors = []
if toolchain != LEAN_TOOLCHAIN:
    errors.append(f"Unexpected lean-toolchain: {toolchain}")
for source, revision in (
    ("lake-manifest.json", mathlib_manifest["rev"]),
    ("lakefile.toml", mathlib_config["rev"]),
):
    if revision != MATHLIB_COMMIT:
        errors.append(f"Unexpected Mathlib revision in {source}: {revision}")

if args.runtime:
    version = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=ROOT, text=True
    ).strip()
    mathlib_dir = ROOT / manifest.get("packagesDir", ".lake/packages") / "mathlib"
    mathlib_head = subprocess.check_output(
        ["git", "-C", str(mathlib_dir), "rev-parse", "HEAD"], text=True
    ).strip()
    report.update({"lean_version": version, "mathlib_runtime_rev": mathlib_head})
    if "4.35.0-rc3" not in version or LEAN_COMMIT not in version:
        errors.append(f"Unexpected Lean runtime: {version}")
    if mathlib_head != MATHLIB_COMMIT:
        errors.append(f"Unexpected Mathlib checkout: {mathlib_head}")

report["errors"] = errors
output = ROOT / "verification/theta_global"
output.mkdir(parents=True, exist_ok=True)
(output / "pins.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
raise SystemExit(bool(errors))
