# Shared character normalization and model exclusions

This correction answers the two actual-source defects reported by
MOM_ENGINE_INDUCTION in PR #5, comment 6542251672. EXPANSION acknowledged
ownership in PR #12 before changing the shared source. The final theorem
`GeneralHeckeSevenEighths` and its assumptions are unchanged.

## The global norm parameter

The previous `normTwistParameter` chose the number `t` in some presentation
`target = theta * omega^e * heckeNormTwist t`. The previous `untwisted_eq`
then returned `theta * omega^e`. This does not remove a norm component of
the arbitrary family generator `omega` itself. In particular, an untwisted
target could still be a nontrivial pure norm character, so nonprincipality
alone did not imply the condition needed for the entire Hecke functional
equation.

Fix one infinite place `w = normNormalizationPlace K`, before choosing the
target. Write `r_w(chi) = heckeRadialParameter K w chi`. The repository's
sign convention is `r_w(heckeNormTwist t) = -t`. The corrected normalization
is therefore the multiplicative map

`N_w(chi) = chi * heckeNormTwist K (r_w(chi))`.

| Object | Previous definition or conclusion | Corrected definition or conclusion |
| --- | --- | --- |
| `normTwistParameter c` | Chosen explicit `t` in a packet presentation | `-r_w(c.target.val)` |
| `(untwisted K c).val` | Target multiplied by the inverse of that explicit norm twist | `N_w(c.target.val)` |
| `untwisted_eq` | `theta * omega^e` | `theta * N_w(omega)^e` |
| Radial component at `w` | No zero component established | Exactly zero |
| Packet membership and zero real parts | Original packet and original zero real parts | Same original packet and same original zero real parts |

`HeckeGeneral.Characters.RadialNormalization` proves multiplicativity,
fixing of finite-order characters, removal of every pure norm character,
the corrected packet formula, and preservation of zero real parts from the
original norm-twist theorem. It does not import `HeckeSkeleton.Base` or its
unfinished recipe. `Base.untwisted_radial_zero` and
`Base.targetCharacter_radial_zero` retain this property after the permitted
inverse for angular orientation. The statement `untwisted_eq` had no
external caller in the branch at the time of this correction.

Only one radial component is zeroed. The other relative radial parameters
are not asserted to vanish. If a character with this zero component equals
`heckeNormTwist t`, then `t=0` and the character is one. Multiplication by a
finite-order row and inversion preserve this zero component. Consequently
the original zero-slot condition `plainBackground * rowCharacter != 1`
supplies the needed exclusion of all pure norm characters for a normalized
background.

## Finite background absorption in the full model

The canonical presentations have plain backgrounds `1` and `psi^-1`.
Their old filter was `theta={1}` in both cases. When `psi` is finite order,
the full positive-slot model could retain the row character `psi`; its
actual plain character would then be principal. A physical shell lower
bound cannot repair a statement about that full model ball.

The corrected fixed finite filter is

`canonicalDetectorTheta K psi = if FiniteOrder psi then {1, psi, psi^-1} else {1}`.

Every member is proved finite order. For both presentations, whenever the
plain background is finite order its inverse belongs to this same filter.
`canonicalDetector_plain_ne_one` uses precisely the existing positive-slot
condition `rowCharacter notin theta` to exclude cancellation. Combined with
the actual radial normalization,
`canonicalDetector_plain_ne_normTwist` excludes every pure norm character.
No extra moment bound or functional-equation conclusion is a premise.

The literal inverse and plain polynomial values, prime-slot coefficients,
tests, common masks, and four physical zero-detection characters stay as
defined. The positive-slot model filter is strengthened by the necessary
fixed finite family; the physical detector companion set remains `{1}`.
These two finite sets have different roles.

Separately, `exists_finite_rowCharacter_cutoff` follows from the existing
arithmetic finite-family fiber theorem. Its constant is chosen before all
physical rows and scales. `exists_canonicalDetectorTheta_cutoff` applies it
to the corrected filter, so sufficiently large original physical rows are
eligible. This is a proof about the genuine arithmetic rows, with no
assumed character injectivity and no modification of the source mask.

## Paper basis and affected consumers

- `weil_seven_eighths_revised.tex`, lines 1537–1548: fixed finite-order
  backgrounds are absorbed into the finite family, and every global norm
  twist is separated before the remaining fixed character is used.
- Lines 3275–3276 and 4359–4360: the physical target has its global norm
  twist removed and the permitted conjugate is selected.
- Lines 3818–3825: the zero-slot actual inducing character must be
  nonprincipal after separating the norm twist; positive-slot rows must
  avoid the fixed finite family.

The primitive MOM_ENGINE_INDUCTION functional-equation consumers can use
the new radial and finite-filter lemmas. Existing moment identities do not
depend on theta; the explicit eligibility consumers must use the corrected
same filter. Angular orientation and zero-real-part transport continue to
use the original theorems. No field is added to `FamilyContext`,
`TargetContext`, `PolynomialPresentation`, or `MomentData`, and the common
packet boundary and final seven-eighths statement are not strengthened.

## Validation status

The correction is independently committed for review. Source proofs have
been written without proof admissions; the native build and recursive
three-standard-axiom gate are still pending. This document does not count
uncompiled source as a successful proof. The primitive normalization
module is included explicitly in the EXPANSION source/audit manifest.
