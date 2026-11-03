# Hecke L-functions are zero-free for Re(s) > 7/8

A Lean 4 formalization of the main theorem of
[paper/weil_seven_eighths_revised.tex](paper/weil_seven_eighths_revised.tex):
for every number field $F$ and every Hecke character $\chi$ of $F$, the
continued Hecke L-function $L(s, \chi)$ has no zeros with $\mathrm{Re}(s) > 7/8$.

## Main result

The statement is `GeneralHeckeSevenEighths` in
[src/HeckeGeneral/Analysis/HeckeEndpointTarget.lean](src/HeckeGeneral/Analysis/HeckeEndpointTarget.lean):

```lean
def HeckeSevenEighths : Prop :=
  ∀ χ : HeckeCharacter K,
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (7 / 8))

def GeneralHeckeSevenEighths : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], HeckeSevenEighths F
```

The proof is `HeckeSkeleton.generalHeckeSevenEighths_skeleton` in
[src/HeckeSkeleton/Main.lean](src/HeckeSkeleton/Main.lean). It depends only on the
three standard axioms `propext`, `Classical.choice` and `Quot.sound`;
[src/HeckeSkeleton/Audit.lean](src/HeckeSkeleton/Audit.lean) checks this and rejects
`sorryAx`.

## Verifying

```sh
lake exe cache get
lake build HeckeSkeleton.Audit
```

The whole-project build (every library in `lakefile.toml`, followed by an axiom
printout of the endpoint and its main inputs) runs in CI on every pull request,
see [.github/workflows/integration-build.yml](.github/workflows/integration-build.yml).
Pushes to `dtests-handoff` publish a precompiled Lake cache as a release, which
CI restores through [.github/actions/restore-lake-cache](.github/actions/restore-lake-cache).

## Layout

| Path | Contents |
|---|---|
| `src/` | This project's Lean libraries (module names do not include `src`) |
| `src/HeckeGeneral/` | Hecke characters, continuations and the target statement over a general number field |
| `src/HeckeSkeleton/` | The proof: principal part, expansion, high bin, descent, and the moment machinery under `Moments/` |
| `src/HeckeSkeleton/Moments/MOM_ENGINE_STEP_V2/` | The paired engine step, written as a blueprint of 24 task statements and their proofs; see its `PLAN.md` and `TASKS.md` |
| `src/ThetaGlobal/`, `src/Expansion*/`, `src/HeckePort/`, `src/CubicSieve/`, `src/PrimeCancellation/` | Analytic inputs used by the proof |
| `src/SkeletonInputs/`, `src/GramCoreInputs/`, `src/GramAssemblyInputs/` | Arithmetic and Gram-matrix input modules |
| `src/HeckeAxiom/` | Bridge from the base project's ray class character theorems |
| `base/` | The base project this repository started from (see below) |
| `vendor/` | Vendored dependencies: class field theory, FLT, Tau Ceti and openai/math excerpts |
| `paper/` | The paper being formalized |
| `docs/WORK_LEDGER.md` | Progress ledger of the formalization |
| `docs/archive/` | Historical task descriptions, reports, coordination notes and one-off scripts |
| `scripts/` | Scripts used by CI (Lake cache build and pruning) |

## Base project

This repository started from AxiomMath's formalization of the Dedekind zeta
zero-free region $\mathrm{Re}(s) > 31/32$
([A quasi-Riemann hypothesis for Dedekind zeta functions](https://hexagonmath.org/2610.00200v1),
Dean Cureton and Jesse Thorner). That development lives in
`base/`: the library in `base/DedekindZetaZeroFree/`, its challenge statement
in `base/Challenge/` and its solution in `base/Solution/`. `base/comparator.json`
and `base/formalization.yaml` describe that base project. To check it:

```sh
lake build DedekindZetaZeroFree DedekindZetaChallenge DedekindZetaSolution
lake comparator --config base/comparator.json
```

## Dependencies

* [Mathlib](https://github.com/leanprover-community/mathlib4)
* [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
* [FiniteAbelianGlobalReciprocityv2](https://github.com/PalomarArchive/n-yamaguchi-0729--FiniteAbelianGlobalReciprocityv2--ccc6f4bb14f4),
  vendored under `vendor/class-field-theory` with compatibility changes

The code also adapts material from Tau Ceti,
[LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) and
[openai/math](https://github.com/openai/math).
