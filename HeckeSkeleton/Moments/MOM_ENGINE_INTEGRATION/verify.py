#!/usr/bin/env python3
"""Retain the strict unconditional original-target gate after STEP integration.

This is a separate phase from the explicitly conditional induction. It compiles
all core and migrated modules, audits their declarations, and then rejects any
nonstandard axiom in the three unchanged HeckeSkeleton target names.
"""
from __future__ import annotations
import argparse
import json
import re
import runpy
from pathlib import Path

TASK = Path(__file__).resolve().parent
ROOT = TASK.parents[2]
core = runpy.run_path(str(TASK.parent / "MOM_ENGINE_INDUCTION/verify.py"))
require = core["require"]
digest = core["digest"]
verify_checkout = core["verify_checkout"]
axiom_records = core["axiom_records"]
ALLOWED = core["ALLOWED"]
UPSTREAM_PROBES = (
    "HeckeSkeleton.paired_zero_slot_models",
    "HeckeSkeleton.paired_positive_below_one",
    "HeckeSkeleton.paired_positive_endpoint",
    "HeckeSkeleton.targetData",
    "HeckeSkeleton.momentModels",
)
SOURCE_ADAPTERS = ("SkeletonFamily", "SkeletonSource")
SCOPE = "unconditional-engine-integration"


def inventory() -> dict:
    independent = core["source_inventory"]()
    modules = [core["INTEGRATION_PREFIX"] + "." + name for name in sorted(core["MIGRATED_MODULES"])]
    names = set(independent["declarations"])
    adapter_names: set[str] = set()
    for name in core["MIGRATED_MODULES"]:
        path = TASK / (name + ".lean")
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b",
                               core["lean_code"](path.read_text()))
        require(not forbidden, f"Proof shortcut in integrated module {name}: {forbidden}")
        current = core["declarations"](path)
        require(not (names & current), f"Duplicate public declaration in integration module {name}")
        names.update(current)
        if name in SOURCE_ADAPTERS:
            adapter_names.update(current)
    roots = independent["modules"] + modules + ["HeckeSkeleton.Moments"]
    hashes, closure, external = core["source_closure"](roots)
    hashes.update(independent["source_sha256"])
    for path in (TASK / "verify.py", ROOT / ".github/workflows/mom-engine-integration.yml"):
        hashes[str(path.relative_to(ROOT))] = digest(path)
    return dict(scope=SCOPE, modules=roots, declarations=sorted(names),
                strict_declarations=sorted(names - adapter_names),
                source_adapter_declarations=sorted(adapter_names),
                source_sha256=dict(sorted(hashes.items())), repository_import_closure=closure,
                external_imports=external, upstream_probes=list(UPSTREAM_PROBES),
                conditional_induction_modules=independent["modules"],
                migrated_integration_modules=modules)


def audit_text(modules: list[str], names: list[str]) -> str:
    return ("\n".join("import " + name for name in modules) + "\n\n" +
            "\n".join("#print axioms " + name for name in names) + "\n")


def preflight(expected: str, output: Path) -> None:
    verify_checkout(expected)
    data = inventory()
    verify_checkout(expected, list(data["source_sha256"]))
    record = dict(head_sha=expected, **data, **core["environment"](),
                  runner_resources=core["runner_resources"]())
    output.mkdir(parents=True, exist_ok=True)
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    (output / "IntegrationAudit.lean").write_text(audit_text(data["modules"], data["declarations"]))
    (output / "UpstreamAudit.lean").write_text(audit_text(["HeckeSkeleton.Moments"], list(UPSTREAM_PROBES)))
    (output / "build-targets.txt").write_text("\n".join(data["modules"]) + "\n")
    print(f"Unconditional integration preflight: {expected}, {len(data['modules'])} module targets, "
          f"{len(data['declarations'])} declarations; original-name gate still required")


def check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    data = inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before.get("head_sha") == expected, "Integration preflight belongs to another commit")
    for key, value in data.items():
        require(before.get(key) == value, f"Integration source/inventory changed: {key}")
    for key, value in core["environment"]().items():
        require(before.get(key) == value, f"Integration environment changed: {key}")
    require((output / "IntegrationAudit.lean").read_text() == audit_text(data["modules"], data["declarations"]),
            "Generated complete integration audit changed")
    require((output / "UpstreamAudit.lean").read_text() == audit_text(["HeckeSkeleton.Moments"], list(UPSTREAM_PROBES)),
            "Generated original-target audit changed")
    require((output / "build-targets.txt").read_text() == "\n".join(data["modules"]) + "\n",
            "Native build target inventory changed")
    for kind, filename in (("BUILD", "build.log"), ("AUDIT", "axioms.log"),
                           ("UPSTREAM_AUDIT", "upstream-axioms.log")):
        core["successful_log"](output / filename, f"MOM_ENGINE_INTEGRATION_{kind}_OK {expected}")
    records = axiom_records((output / "axioms.log").read_text(), set(data["declarations"]), ALLOWED | {"sorryAx"})
    for name in data["strict_declarations"]:
        require(set(records[name]) <= ALLOWED,
                f"Integrated task declaration {name}: nonstandard axioms {records[name]}")
    upstream = axiom_records((output / "upstream-axioms.log").read_text(), set(UPSTREAM_PROBES), ALLOWED | {"sorryAx"})
    inherited = [name for name in data["source_adapter_declarations"] if "sorryAx" in records[name]]
    record = dict(before, status="integration-compiled", axioms=records,
                  upstream_probe_axioms=upstream, allowed_axioms=sorted(ALLOWED),
                  source_adapters_with_inherited_sorryAx=inherited,
                  build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"),
                  upstream_axiom_log_sha256=digest(output / "upstream-axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS integration compilation: {len(data['strict_declarations'])} strict declarations; "
          f"{len(inherited)} diagnostic source adapters inherit sorryAx")
    print("The original-target gate must still pass independently.")


def original_check(expected: str, output: Path) -> None:
    """Enforce the task's original-name acceptance gate after source compilation."""
    verify_checkout(expected)
    integration = json.loads((output / "verification.json").read_text())
    require(integration.get("head_sha") == expected
            and integration.get("status") == "integration-compiled",
            "Original targets require successful exact-head source integration")
    log = output / "upstream-axioms.log"
    require(digest(log) == integration["upstream_axiom_log_sha256"],
            "Original target axiom log changed after integration verification")
    records = axiom_records(log.read_text(), set(UPSTREAM_PROBES), ALLOWED | {"sorryAx"})
    targets = UPSTREAM_PROBES[:3]
    unexpected = {name: sorted(set(records[name]) - ALLOWED) for name in targets
                  if set(records[name]) - ALLOWED}
    result = dict(head_sha=expected, scope=SCOPE, status="passed" if not unexpected else "blocked",
                  targets=list(targets), axioms={name: records[name] for name in targets},
                  allowed_axioms=sorted(ALLOWED), unexpected_axioms=unexpected,
                  upstream_axiom_log_sha256=digest(log))
    (output / "original-targets.json").write_text(json.dumps(result, indent=2) + "\n")
    for name in targets:
        print(name + ": " + json.dumps(records[name]))
    require(not unexpected,
            "Original target axiom gate failed: " + json.dumps(unexpected)
            + ". Conditional clean theorems do not satisfy this acceptance gate.")
    print(f"PASS original targets: {len(targets)} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("inventory", "preflight", "check", "original-check"))
    parser.add_argument("--expected-sha")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.phase == "inventory":
        data = inventory()
        print(json.dumps({key: len(value) for key, value in data.items() if isinstance(value, (dict, list))}, indent=2))
        return
    require(args.expected_sha is not None and args.output is not None,
            "Verification requires --expected-sha and --output")
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    {"preflight": preflight, "check": check, "original-check": original_check}[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
