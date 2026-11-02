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

Formal head `938c15eb6a8d89aece94d8deef04716914a75a93` built the N1 source,
phase, leaf-binding, occurrence, location, divisor and scale dependencies and
validated the generic scaled extraction term. Its complete public/strict
logs and strict artifact agree on the remaining failures. The next proof
corrections stay in the same shared files:

- `OrdinaryRawAtomData`: the Boolean zero-versus-product identity is proved
  on scalars before application, avoiding a simplifier call on the expanded
  packet's dependent exterior-ideal types.
- `OrdinaryMultiplierTransport`: normalize the actual powerIdeal projection
  before the existing ring calculation; independently type the three original
  main-tag record projections; convert the original two tag matchers by
  explicit Option cases; transport the second-mask subset as a proposition
  rather than rewriting its dependent carrier.
- `OrdinaryOriginalCoordinates`: retain the public proofs and add synchronous,
  flushed declaration/step checkpoints to locate its 300-second timeout. The
  same canonical module remains required by both formal gates and all audits.

Formal head `287033f7b52ceb9f59acee374c00f8b0d8d9da35` then built
`OrdinaryRawAtomData` in 32s/53s and `OrdinaryMultiplierTransport` in 68s/114s
in the public/strict gates. Their exact blobs are respectively
`21772903feb205fec023147b122f73e14287c719` and
`b0ec3e0822bc6a9ee8b120d0f350ec02fcec8514`. These same-path sources are
reported to N1 in PR #31 comment `6587076397`. N1 R17 snapshot
`2abc270913f32620d3bda15412abc1ad699c6db5` still failed its RawAtomData module
on `Bool.true_eq_true`; it does not replace the two validated T3 source blobs.
The complete T3 tasks and fresh audits remain unaccepted at this stage.

N1 R18 snapshot `70c2e8601417a81236aea95cf5b138c0f6033b8e` subsequently built
its corrected `OrdinaryRawAtomData` in 63s/65s in its public/strict gates.
This file is now consumed verbatim from that owner snapshot: 252 lines,
blob `a846d978462563413f773b8b4e506830cca7ff35`. All 23 public declaration
headers and all seven complete computational definitions equal the previously
validated T3 version; only two theorem proofs and private helper organization
differ. The failing R18 MultiplierTransport and Coordinates variants are not
consumed. T3's complete combination must still pass its own formal gates.

N1 R19 snapshot `f8458da297108c7bc26d7b32021da464d0537287` then built
`OrdinaryMultiplierTransport` in 101s/134s in its two formal gates. The
current file is unified to that exact owner source: 444 lines, blob
`20de319d3676cdacbda09c61f8aa5073189f315f`. Relative to the already built
T3 447-line version, the only differences are three line wraps and the
explicit original mask carrier `Finset (HeightOneSpectrum (Arithmetic.data c).R)`.
All 19 public declaration headers, definitions and section parameters are
unchanged. Both complete official logs were read before adoption. The
owner's Coordinates variant still timed out and is not consumed.

The 67 flushed Coordinates labels in both official logs and the full strict
artifact locate its remaining timeout after the `realizes_firstIndex` true
branch and before `secondColumn`. The next proof correction factors the
realization elimination into a private helper with an independent count
equality; the public theorem supplies its same original count proof afterward.
The original ancestor, column, cast, public statement and watchdog remain
unchanged. At T3 head `fe1eea49`, both cover equalities were constructed, but
the last label remained `realizes_firstIndex_of_count.true.index` and the
module still exceeded 300 seconds. Independent count abstraction alone was
therefore insufficient; it is not reported as a successful timeout repair.

The next correction performs count-proof alignment in a small private
`OriginalCover.Realizes.ancestor_index_of_count` lemma before instantiation
at the raw packet. Both actual branches then pass the same independent
count proof used in their target. Ordinary returned markers and monotonic
millisecond timestamps distinguish final tactic alignment from subsequent
declaration checking and quantify time spent in earlier statements. Every
public declaration and the 300-second module gate remain unchanged.

At T3 head `6e2052a2a88cea217729459321ce1f29be532948`, both formal gates
naturally failed. Their complete official logs and the six-file strict
artifact `13176273454` agree on all four source diagnostics and all 73
normalized Coordinates labels. The exact 183 source and 10 configuration
hashes match the sealed head. RawAtomData built in 90s/78s, and the empty
supremum correction in T3bOrbitFibrePackets built in 6.4s/6.7s.

The monotonic timestamps isolate the remaining Coordinates bottleneck:
the abstract count helper returns quickly, while the concrete false-branch
`exact h` alone takes 98.653s/106.947s. Both jobs then stop after the true
branch's `.index` label without its `.returned` label. The next correction
therefore supplies the already constructed local `h` directly as the goal's
proof term, using the `withMainContext`/local-FVar/`goal.assign` pattern from
the true baseline's OrdinaryData. Normal synchronous kernel checking and
the full recursive axiom audits remain enabled. The doc comment now directly
precedes its private theorem, with `include hcover in` before the comment.
All 33 public headers and every timing boundary remain unchanged; the
next formal gates must establish whether this resolves the measured cost.

The same consumer repair batch incorporates the three proof-only files from
the parallel PR #41 candidate `c5f13434f42a7a43a6ddd540738335689a61af42`, whose
unique parent is `6e2052a2`. T3aValuationAtomCharacters uses fixed-character
membership transport through the original theta equality; T3bFirstColumnBounds
and T3bScaleCompensation transport original-profile nonzeroness along the
existing representative equalities. Their 40 public declaration headers,
original definitions and parameters are unchanged. These are source-reviewed
candidate proofs, not claimed CI results. T3bOriginalGeometry is separately
repaired against the three actual diagnostics in this same R5 evidence.

T3 head `a80a8ec4ffeae331b7eb3801e5b495294ef27f7d` then built the exact
Coordinates blob `cb0cfffbaa5ecd232ae3f8bfab9e90f319716ece` in 123s/125s
in its public/strict gates. All 98 normalized checkpoints reached completion;
the concrete false-branch alignment took 79ms/71ms and the true branch
67ms/61ms. Both jobs had zero watchdog kills or monitor errors. The current
942-line successful source is preserved verbatim and shared with N1.
The owner-aligned MultiplierTransport also built here in 143s/129s, and
OrdinaryFirstAtomFormula built in 7.5s/7.3s.

Both R6 jobs still failed on three source errors. The complete official logs
and all six files in strict artifact `13177328592` were read; all 193 source
and configuration hashes matched the sealed head, and the error contexts
matched exactly. The next correction in OrdinaryRawAtomFormula explicitly
unfolds `firstResidualColumn` immediately before the existing final `ring`,
so the original cast and its named wrapper become the same polynomial atom.
Its five public declarations and its complete definition are unchanged.
The two remaining T3bOriginalGeometry proofs first derive a mask-union
equality independently of the original divisor subtype, then compose the
existing subset proof with that equality. They no longer rewrite the
divisor's dependent carrier. The resulting divisibility is transported
through the original common-left/right equality with that same divisor
fixed. All 12 public statements remain unchanged.

The two T3 tasks and four fresh audits remain unaccepted at this stage.
ValuationAtomCharacters, FirstColumnBounds and ScaleCompensation were not
reached by R6 and are still candidate proofs awaiting the task's own CI.

At T3 head `317d293da0da1b7b1d0bb05af80e133849606f54`, the original
Geometry blob `6d79603725051e8786cf0844a6949fe9c0049736` built in 31s/25s
and RawAtomFormula blob `534c121331721881e4d38c7feaf9ac16764458f1` built
in 71s/83s in the public/strict gates. Their four printed theorem dependencies
were all standard. Both complete official logs and strict artifact
`13178527782` were read, with all 183 source and 10 configuration hashes
matching the exact head. The archive SHA256 is
`e511d3a07ab7766e7cd3e01350105987cda57a55d662909c96f2c38b3469efa3`.
The build exited 1 on newly reached proof files, with no watchdog kill or
monitor error and no fresh audit yet.

The next proof repair uses the independently reviewed SourceSupport candidate
`256b7dbb0c1ce4f4fdf0d65d4d25d5c8e7d43a10` and AtomFrames candidate
`a6010c0ccab45d69e83d49b1882316fb4064ccaa`, both based on that exact head.
SourceSupport directly extracts nonzero factors and composes the two original
atom equations at their identical cast. AtomFrames factors allocation
membership and whole subtraction into private shallow proofs, imports the
existing base ExceptionalOriginalLabel definition, and repairs two field
notation line breaks. The allocation helper's parameter shape matches N1
R21 `c50de627c4ad94e4bc01a4c62ea5ffcc067cfde5`, whose OrdinaryFromAtoms
built in 183s in its successful supplemental gate; the private helper and
both public membership theorems passed its fresh recursive audit.
OrbitFibreUniform proves the existing real addition inequality directly,
without relying on the ambiguous add_le_add_right argument order.
Public statements, original computational definitions, the 97-module scope,
four fresh audits, and all verification budgets remain unchanged. These T3
repairs still require their own exact-head CI and full recursive audit.

## N4 frozen ideals and scale identities

Initially reused verbatim from PR #39 candidate `d98ab940632fbc73127ac655493f89b5af6f67ef`:

- `N4ScaleProduct.lean`
- `N4FrozenIdeals.lean`

This 473-line minimal closure proves the actual first frozen ideal includes the complete pool valuation, and the second frozen ideal is the actual common ideal. T3b uses the universal packet identities, without importing an ordinary-only certificate or any placeholder task.

The ad8cd07d real-baseline CI exposed three proof failures in N4ScaleProduct.
The shared correction qualifies the existing primeSupport constant and proves
the two original scale-product equalities by explicitly instantiated
prod_fin_cast and congrArg. All public statements, original count transports,
plain scales and ideals remain unchanged. PR #39 snapshot 6b1cf628 retains the
same failing proof bodies; its unrelated helper split is not required here.

`N4FrozenIdeals.lean` first followed PR #42 snapshot
`8b17b6da79234dcdb9164e19c132df00e86cf711` verbatim (blob
`484452c827e2c5db4e5f9bac016f0b24636bfa1a`), coordinated with N4 in PR #39
comment `6586444523` and announced in PR #31 comment `6586480240`.
Those corrections explicitly reduce the original direct-source projection
and identify the unit ideal with top. T3 head `287033f7` confirmed that its
remaining filter-to-image step used different DecidableEq algorithms.

The current file follows PR #42 snapshot
`01f544a14c07f339126e36ed0933eba2dc1ccd99` verbatim (blob
`ef8048edd1f3d05b0a9e2bdf2db01e6f6b1eaa3c`), coordinated in PR #39 comment
`6586842459` and PR #31 comment `6586880188`. The original fibre equality is
first transported to a membership proposition, then filter/image membership
is reduced and rebuilt using the target's own image constructor. No ideal,
index or premise changes. Imports and every declaration header are unchanged.
The owner built this exact file in 29s/32s; T3 head `fe1eea49` independently
built it in 35s/31s in its own public/strict gates, with the same standard
axiom print. These are module results, not completion of either T3 task or
the full fresh recursive audits.

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
