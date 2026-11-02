# T3a / T3b shared proof sources

The following N1 implementation uses PR #32, commit
`7e638f772946e3f9e738761816cf2530616f6b77` as its fixed source snapshot. All 22
source blobs were checked before the proof-only corrections recorded below.
T3b uses its universal original-row atom formula. The modules
retain their original paths and names so B-line integration shares one implementation.
The initial snapshot was `6caa522ba57bb248e62e4dd3499f7776ff20167d`; its subsequent
CI-driven corrections remain documented below.

Root: `OrdinaryRawAtomFormula.lean`, specifically `RawLeafPacket.beforeAtomTable_left` and `beforeAtomTable_right`.

- `OrdinaryAtomExtraction.lean`
- `OrdinaryAtomModel.lean`
- `OrdinaryCharacterFacts.lean`
- `OrdinaryDivisorGate.lean`
- `OrdinaryFirstAtomFormula.lean`
- `OrdinaryLeafBinding.lean`
- `OrdinaryLeafLocations.lean`
- `OrdinaryMultiplierTransport.lean`
- `OrdinaryNormPower.lean`
- `OrdinaryNormProfile.lean`
- `OrdinaryOccurrenceFacts.lean`
- `OrdinaryOriginalCoordinates.lean`
- `OrdinaryOriginalTerms.lean`
- `OrdinaryPhaseCoefficients.lean`
- `OrdinaryPhaseFacts.lean`
- `OrdinaryPointTransport.lean`
- `OrdinaryRawAtomData.lean`
- `OrdinaryRawAtomFormula.lean`
- `OrdinaryRectangleFactors.lean`
- `OrdinaryScaleFacts.lean`
- `OrdinarySourceFacts.lean`
- `OrdinarySourceTransport.lean`

Original snapshot: 4431 physical lines. CI-driven compatibility changes are recorded below and reported in the PR #31 coordination thread.

### CI compatibility correction

Commit `3cfd114086b29724da88721d9f5f7dfeaa379bde` changes only the two proof steps in
`OrdinaryCharacterFacts.twist_plain` and `twist_prime`: the exact singleton identity
is transported with `congrArg` instead of `rw`, which was unable to match the
semireducible exterior-ideal projection in CI. Statements, characters, masks and
source coefficients are unchanged. The diagnostics are from run `41448321827`,
job `125286921697`; the shared-owner coordination is PR #31 comment `6578016005`.

The first formal T3 round on real baseline bff9840c, head ad8cd07d, reached the
shared implementation and exposed compatibility failures. PR #32 R16 logs at
the fixed snapshot above expose the next layer. In accordance with PR #31
comment `6577195608`, corrections retain every original public statement,
path, namespace and theorem name and are reported for unified N1/T3 integration:

- `OrdinaryOriginalCoordinates`: private Eq.mp/Eq.mpr transport lemmas match
  the actual atlas construction; exact count casts are supplied explicitly;
  residual columns unfold their original definition; two Bool case branches
  receive valid continuation indentation.
- `OrdinaryRawAtomData`: function-valued comparison conditionals are applied
  before normalization; the true plain-divisor conditional is simplified.
  A private scalar/extraction lemma proves the same scaled term identity on
  a generic atom table, avoiding broad rewriting through the full packet.
- `OrdinaryDivisorGate`: the existing residual-divisor projection equality is
  elaborated independently before conversion to the original transport goal.

These are proof compatibility corrections, not new ordinary assumptions for
exceptional packets. CI must validate the resulting shared implementation.

## N4 frozen ideals and scale identities

Reused verbatim from PR #39 candidate `d98ab940632fbc73127ac655493f89b5af6f67ef`:

- `N4ScaleProduct.lean`
- `N4FrozenIdeals.lean`

This 473-line minimal closure proves the actual first frozen ideal includes the complete pool valuation, and the second frozen ideal is the actual common ideal. T3b uses the universal packet identities, without importing an ordinary-only certificate or any placeholder task.

The ad8cd07d real-baseline CI exposed three proof failures in N4ScaleProduct.
The shared correction qualifies the existing primeSupport constant and proves
the two original scale-product equalities by explicitly instantiated
prod_fin_cast and congrArg. All public statements, original count transports,
plain scales and ideals remain unchanged. PR #39 snapshot 6b1cf628 retains the
same failing proof bodies; its unrelated helper split is not required here.

## B-line CI repair

`OriginalPhaseData.lean` is synchronized verbatim with B-line
`ad4f0a10927063901caae60440f8c3847f232231` (local principal-ideal instance).
The shared process watchdog introduced at that commit remains in the newer
public driver recorded below.

The verified real baseline is B-line
`bff9840cf0af65b7782c73799f41b59bfdbca875`, retained as a merge parent.
Its seven changes since `ad7c9c79` are consumed verbatim: RawLeafData,
OrdinaryData, ExceptionalRecoveryContracts, PassiveData, RefinementData,
SourceAssembly and GlobalAssembly. RawContracts itself is unchanged.
The b3 reindex input wrappers and D9 ordinary source wrappers retain the
original Sigma key, AllocationKey, subtype projection, ordinary equality,
rectangles and binding. All eight OrdinaryData fields retain their order
and original data. This baseline contains no stubs.

`SourceIndexContracts.lean` remains the exact B1f5849 snapshot, unchanged in
Bad7c9c79: the two existing Möbius factors are fully namespace-qualified.
Mathematical fields, carrier types, coefficients and task statements are preserved.

## N8 original frozen-profile and common-scalar bounds

Originally split in PR #42 candidate `773795d60dabbb136311e8187e21d130714e3aeb`,
following PR #31 comments `6578016005`, `6578119255` and `6578269366`.
The upstream snapshot is `8cda5bb1ad0785d9ee862e0ef868f802f252d8e8`, with the
additional CI compatibility correction recorded below:

- `N8FrozenProfileBounds.lean` (100 lines)
- `N8CommonScalarBounds.lean` (251 lines)

The update changes only the nonnegative finite-product API to `prod_le_prod₀`
and supplies the existing arithmetic data/embedding parameters explicitly in
the envelope bound. Statements and original scalar formulas are unchanged.

Run `41454774485`, job `125308565392`, also exposed the omission of the section
variable `input` from `commonAnnulus_nonneg` and `original_slot_window`.
Both intended input-dot helper methods now use `include input in`, preserving
the original inequalities and proof bodies while retaining the `ProfileInput`
argument needed by their existing callers and the latter proof's raw fields.
This exact two-line compatibility patch is coordinated with N8 in PR #31.

Run `41458052013`, job `125319706480`, then exposed an unmatched simplifier
rewrite in `original_slot_window`. The nonzero representative proof now applies
`input.raw.prime_eq i 0 _` in its original direction and composes it with the
assumed zero equality before invoking the original-profile nonzero hypothesis.
The profile, evaluation point and window statement are unchanged; the exact
patch is recorded in PR #31 comment `6579471045`.

These two modules preserve the upstream public names and original prime
profiles, complete common frozen ideals and pointwise scalar estimates.
The second exceptional common bound is constructed in `T3bCommonBounds`
on the actual universal `firstAtomTable`; it uses no ordinary-data
hypothesis. The two private upstream scale-positivity helpers no longer
conflict with the existing public N1 declarations. No N8 task proof or
ordinary normalized-mass certificate is imported.


## CI synchronization and shared dependency diagnostics

The public V2 driver `.github/v2/build.py` follows B commit
`1f5849c7025a1bd57589ab3d3e580503a159a3c3` verbatim, including its strict
300-second per-module watchdog and the typed `moduleNames` cache accepted in
PR #31 comment `6578888764`. The selected declaration set and axiom whitelist
are unchanged. Public manifest task scopes follow the same B commit, with
`t3_shared_n8` included in this branch's complete explicit T3 scope. The
current manifest retains every original target and also registers the
independent finite-support, first-kernel and scale-arithmetic helpers. The
separate T3 proof job derives its full scope from those same T3 groups and
also requires both task endpoints.

The diagnostic script follows N7 commit
`054b434f2acab53a1ff5e7cfc79e56ea06803cbf`, including explicit `IO Unit` markers,
filtered console output and exclusion of toolchain imports from Lake targets.
The probe imports remain complete. Its safety assertion is synchronized to B's
new 300-second timeout and the value is recorded in diagnostic results.
After B008113e7, declaration anchors accept an optional explicit `noncomputable`
prefix while preserving exact uniqueness and complete wrapper boundaries. This
only adapts temporary checkpoint placement to the new canonical source spelling.
The previously completed branch probe targeted RawContracts. Since commit
`3e0a6cfeeaac51b5563401d77d143860a78c0c69`, this non-acceptance job is
manual-only; its probe script, commands and watchdog are retained. Shared
baseline diagnosis follows the coordinator's central and parallel repair
branches. Temporary instrumented source output is diagnostic only and cannot
replace the canonical build or axiom audit.

## Task CI routing from dtests-handoff

Coordinator comment `6580209603` and dtests-handoff commit
`996cb49685a51cf789ea962af9f725b02dc363c7` exclude `cloud/mom-v2-*` task
branches from the whole-project workflow, reserving it for final V2 integration.
This branch consumes B bff9840c's inherited workflow verbatim, retaining that
exact task-prefix rule and B's existing draft/manual integration routing.
Both V2 gates retain every original target, the required endpoints and the
complete recursive axiom audits. Added independent proof helpers remain
explicitly listed in the manifest and Interface and are included in both
task builds and the fresh full-closure audits.
