import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingSupportWindows
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Exact exterior radical of the original remaining deletion mask

The complete original row mask already excludes the primes of `A.Sf`.
Consequently those primes in the remaining ideal are redundant, and the
other primes matter only through their presence, not their multiplicity.
The normalization below uses the existing `redundantIdeal` product and
proves the complete Boolean mask identity on every ideal.

`CompleteMovingRowRecipe.exteriorRemaining` is a recipe for the SAME
`MomentData` family. It changes no row, profile, character, polynomial,
energy, or chosen child. Its complete support divides the original full
support, so the original `FullJointBudget` transfers in the correct
direction. No bound for the displayed support alone is used to pay for
the remaining ideal.

The old `SupportAtoms` structure is unchanged. For the normalized recipe,
the squarefree remaining ideal genuinely divides its actual full support.
The optional `effectiveSupportAtoms` constructor also derives every
displayed factor's power divisibility from its literal prime support.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

/-- Every prime of the remaining ideal outside the original fixed `S`,
retained exactly once. No cancellation of moving character exponents is
involved. -/
def remainingMaskRadical (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) : A.Exterior :=
  ⟨redundantIdeal remaining.val A.cS,
    redundantIdeal_ne_zero remaining.val A.cS,
    (redundantIdeal_coprime remaining.val A.cS A.cS_ne_zero).sup_eq⟩

/-- The same normalized ideal in the original complete-row type. -/
def remainingMaskIdeal (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  (HeckeAxiom.exteriorEquiv A (remainingMaskRadical A remaining)).val

@[simp] theorem remainingMaskIdeal_val (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (remainingMaskIdeal A remaining).val = (remainingMaskRadical A remaining).val := rfl

theorem remainingMaskRadical_squarefree (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    Squarefree (remainingMaskRadical A remaining).val :=
  redundantIdeal_squarefree remaining.val A.cS

/-- In particular, every outside-`S` prime of every original remaining
prime power survives. -/
theorem remainingMaskRadical_primes (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport (remainingMaskRadical A remaining).val =
      primeSupport remaining.val \ primeSupport A.cS :=
  redundantIdeal_support remaining.val A.cS

theorem remainingMaskRadical_dvd (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (remainingMaskRadical A remaining).val ∣ remaining.val :=
  support_product_dvd (nonZeroDivisors.ne_zero remaining.property)
    (redundantSet_subset remaining.val A.cS)

theorem remainingMaskRadical_coprime_iff (A : SArithmeticData K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K))
    (hIS : IsCoprime I A.cS) :
    IsCoprime I remaining.val ↔ IsCoprime I (remainingMaskRadical A remaining).val := by
  constructor
  · intro h
    exact h.of_isCoprime_of_dvd_right (remainingMaskRadical_dvd A remaining)
  · intro h
    apply (coprime_support_iff I remaining.val
      (nonZeroDivisors.ne_zero remaining.property)).mpr
    intro p hp
    by_cases hpS : p ∈ primeSupport A.cS
    · exact (coprime_support_iff I A.cS A.cS_ne_zero).mp hIS p hpS
    · apply (coprime_support_iff I (remainingMaskRadical A remaining).val
        (remainingMaskRadical A remaining).property.1).mp h p
      rw [remainingMaskRadical_primes]
      exact Finset.mem_sdiff.mpr ⟨hp, hpS⟩

/-- The original Boolean row gate supplies the `S`-coprimality used
above even when the candidate ideal is zero. No nonzero candidate or
extra exteriority hypothesis is required. -/
theorem completeIdealCommonMask_coprime_cS (A : SArithmeticData K)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K))
    (hmask : completeIdealCommonMask K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I = true) :
    IsCoprime I A.cS := by
  have hgood : (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
      p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧
      IsCoprime I u.val := by
    simpa only [completeIdealCommonMask, decide_eq_true_eq] using hmask
  apply Ideal.isCoprime_iff_sup_eq.mpr
  change I ⊔ (∏ v ∈ A.Sf, v.asIdeal) = ⊤
  apply Ideal.sup_prod_eq_top
  intro v hv
  have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  by_contra hne
  have hle : I ≤ v.asIdeal := by
    have he := hmax.eq_of_le hne le_sup_right
    exact (le_sup_left : I ≤ I ⊔ v.asIdeal).trans_eq he.symm
  exact (hgood.1 v (Ideal.dvd_iff_le.mpr hle)).1 (Finset.mem_coe.mpr hv)

/-- Exact equality of the full original Boolean mask, with any other
deletion gate retained. Primes in `S` are removed only behind the
original complete row gate which already excludes them. -/
theorem completeMovingMask_remainingRadical (A : SArithmeticData K)
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K))
    (extra : Bool) :
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I && extra) &&
      decide (IsCoprime I remaining.val)) =
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I && extra) &&
      decide (IsCoprime I (remainingMaskIdeal A remaining).val)) := by
  by_cases hmask : completeIdealCommonMask K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I = true
  · rw [remainingMaskIdeal_val,
      remainingMaskRadical_coprime_iff A remaining I
        (completeIdealCommonMask_coprime_cS A u I hmask)]
  · have hfalse := Bool.eq_false_of_not_eq_true hmask
    simp only [hfalse, Bool.false_and]

namespace OriginalMovingFactors

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (D : OriginalMovingFactors A P R)

/-- The entire actual additional support after exact remaining-mask
normalization. Displayed factors, including exponent-zero occurrences,
are all retained. -/
def effectiveFullSupport (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.Exterior := by
  refine ⟨(D.fullMaskSupport (remainingMaskIdeal A remaining)).val,
    nonZeroDivisors.ne_zero (D.fullMaskSupport (remainingMaskIdeal A remaining)).property, ?_⟩
  have hprod : D.support.val * (remainingMaskRadical A remaining).val ≠ 0 :=
    mul_ne_zero D.support.property.1 (remainingMaskRadical A remaining).property.1
  have hd := (commonRadical_dvd _ _ hprod hprod).1
  have hcop : IsCoprime (D.support.val * (remainingMaskRadical A remaining).val) A.cS :=
    (Ideal.isCoprime_iff_sup_eq.mpr D.support.property.2).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr (remainingMaskRadical A remaining).property.2)
  exact (hcop.of_isCoprime_of_dvd_left hd).sup_eq

@[simp] theorem effectiveFullSupport_val
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (D.effectiveFullSupport remaining).val =
      (D.fullMaskSupport (remainingMaskIdeal A remaining)).val := rfl

theorem effectiveFullSupport_squarefree
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    Squarefree (D.effectiveFullSupport remaining).val :=
  D.fullMaskSupport_squarefree (remainingMaskIdeal A remaining)

theorem effectiveFullSupport_primes (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport (D.effectiveFullSupport remaining).val =
      primeSupport D.support.val ∪ (primeSupport remaining.val \ primeSupport A.cS) := by
  rw [effectiveFullSupport_val, D.fullMaskSupport_primes,
    remainingMaskIdeal_val, remainingMaskRadical_primes]

theorem support_dvd_effectiveFullSupport
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    D.support.val ∣ (D.effectiveFullSupport remaining).val :=
  D.support_dvd_fullMaskSupport (remainingMaskIdeal A remaining)

/-- Unlike the unnormalized remaining ideal, this is genuinely a
divisor of the complete squarefree support, without any new premise. -/
theorem remainingMaskIdeal_dvd_effectiveFullSupport
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (remainingMaskIdeal A remaining).val ∣ (D.effectiveFullSupport remaining).val := by
  have hprod : D.support.val * (remainingMaskRadical A remaining).val ≠ 0 :=
    mul_ne_zero D.support.property.1 (remainingMaskRadical A remaining).property.1
  exact old_mask_dvd_commonRadical (remainingMaskRadical A remaining).val _ _
    (remainingMaskRadical_squarefree A remaining) hprod hprod
    (dvd_mul_of_dvd_right (dvd_refl _) _) (dvd_mul_of_dvd_right (dvd_refl _) _)

/-- No uncharged support is introduced by the exact mask replacement. -/
theorem effectiveFullSupport_dvd_fullMaskSupport
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (D.effectiveFullSupport remaining).val ∣ (D.fullMaskSupport remaining).val := by
  rw [← squarefree_support_product_self (D.effectiveFullSupport_squarefree remaining)]
  apply support_product_dvd (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
  intro p hp
  rw [D.effectiveFullSupport_primes remaining] at hp
  rw [D.fullMaskSupport_primes remaining]
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union_left _ hp
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hp).1

theorem effectiveFullSupport_norm_le
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm (D.effectiveFullSupport remaining) ≤
      idealNorm K (D.fullMaskSupport remaining) :=
  HeckePort.Moments.norm_le_of_dvd
    (nonZeroDivisors.ne_zero (D.fullMaskSupport remaining).property)
    (D.effectiveFullSupport_dvd_fullMaskSupport remaining)

/-- Full original mask equality, including the complete row and both
the displayed and remaining deletions. -/
theorem effectiveFullSupport_mask
    (remaining u : HeckeGeneral.Analysis.NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    ((completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I D.support.val)) && decide (IsCoprime I remaining.val)) =
    (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
      decide (IsCoprime I (D.effectiveFullSupport remaining).val)) :=
  (completeMovingMask_remainingRadical A remaining u I
    (decide (IsCoprime I D.support.val))).trans
      (D.fullMaskSupport_mask (remainingMaskIdeal A remaining)
        (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I) I)

/-- Each actual displayed factor divides a power of the computed full
support. The exponent is its literal finite prime multiplicity count. -/
theorem factorIdeal_dvd_effectiveFullSupport_pow
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (i : Fin D.count) :
    (D.factorIdeal i).val ∣ (D.effectiveFullSupport remaining).val ^
      (normalizedFactors (D.factorIdeal i).val).card := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (D.factorIdeal i).property.1
    (pow_ne_zero _ (D.effectiveFullSupport remaining).property.1)).mpr
  rw [normalizedFactors_pow, Multiset.le_card_smul_iff_subset]
  intro p hp
  apply Multiset.mem_toFinset.mp
  change p ∈ primeSupport (D.effectiveFullSupport remaining).val
  rw [D.effectiveFullSupport_primes remaining]
  exact Finset.mem_union_left _ ((D.mem_support_iff p).mpr
    ⟨i, Multiset.mem_toFinset.mpr hp⟩)

/-- A concrete old-support choice for the unchanged `SupportAtoms`
interface. All divisibilities are proved from the actual factor list;
the old ideal is precisely the computed complete exterior support. -/
def effectiveSupportAtoms (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (unit nonunit : A.Exterior) :
    D.SupportAtoms (D.effectiveFullSupport remaining) unit nonunit
      (remainingMaskIdeal A remaining) where
  ideal := D.factorIdeal
  generates := D.factorIdeal_generates
  oldPower i := (normalizedFactors (D.factorIdeal i).val).card
  unitPower _ := 0
  nonunitPower _ := 0
  factor_divides i := by
    simpa only [pow_zero, mul_one] using D.factorIdeal_dvd_effectiveFullSupport_pow remaining i
  remaining_divides :=
    dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (D.remainingMaskIdeal_dvd_effectiveFullSupport remaining) _) _

@[simp] theorem effectiveSupportAtoms_fullSupport
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (unit nonunit : A.Exterior) :
    (D.effectiveSupportAtoms remaining unit nonunit).fullSupport =
      D.effectiveFullSupport remaining := Subtype.ext rfl

end OriginalMovingFactors

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- Only the arithmetic certificate changes. The type still refers to
exactly `data`, so the original allowed rows, all profiles, both
polynomials, and every chosen child's energy remain literally the same. -/
def exteriorRemaining : CompleteMovingRowRecipe A P R data where
  moving := Q.moving
  correction := Q.correction
  correction_mem := Q.correction_mem
  sector := Q.sector
  exterior := Q.exterior
  character := Q.character
  remaining := remainingMaskIdeal A Q.remaining
  mask ξ u I := (Q.mask ξ u I).trans
    (completeMovingMask_remainingRadical A Q.remaining u I
      (decide (IsCoprime I Q.moving.support.val)))

@[simp] theorem exteriorRemaining_moving : Q.exteriorRemaining.moving = Q.moving := rfl

@[simp] theorem exteriorRemaining_correction :
    Q.exteriorRemaining.correction = Q.correction := rfl

@[simp] theorem exteriorRemaining_sector : Q.exteriorRemaining.sector = Q.sector := rfl

@[simp] theorem exteriorRemaining_remaining :
    Q.exteriorRemaining.remaining = remainingMaskIdeal A Q.remaining := rfl

theorem exteriorRemaining_remaining_squarefree :
    Squarefree Q.exteriorRemaining.remaining.val :=
  remainingMaskRadical_squarefree A Q.remaining

theorem exteriorRemaining_remaining_dvd :
    Q.exteriorRemaining.remaining.val ∣
      (Q.moving.effectiveFullSupport Q.remaining).val :=
  Q.moving.remainingMaskIdeal_dvd_effectiveFullSupport Q.remaining

/-- The displayed moving list and its support budget are unchanged. -/
theorem exteriorRemaining_supportBudget_iff (Z q : ℝ) :
    Q.exteriorRemaining.SupportBudget Z q ↔ Q.SupportBudget Z q := Iff.rfl

/-- The ORIGINAL full budget implies the normalized full budget on the
SAME allowed rows. The converse, or a bound using only displayed
support, is neither assumed nor asserted. -/
theorem exteriorRemaining_fullJointBudget (Z width : ℝ)
    (hbudget : Q.FullJointBudget Z width) :
    Q.exteriorRemaining.FullJointBudget Z width := by
  intro ξ u hu
  change idealNorm K u * A.exteriorNorm (Q.moving.effectiveFullSupport Q.remaining) ≤ _
  exact (mul_le_mul_of_nonneg_left (Q.moving.effectiveFullSupport_norm_le Q.remaining)
    (idealNorm_pos K u).le).trans (hbudget ξ u hu)

/-- The actual mask recipe needs no remaining-divisibility certificate:
it is built from the original complete Boolean mask itself. -/
def effectiveMovingMaskRecipe : ActualMovingMaskRecipe A data where
  support _ := Q.moving.effectiveFullSupport Q.remaining
  squarefree _ := Q.moving.effectiveFullSupport_squarefree Q.remaining
  mask ξ u I := (Q.mask ξ u I).trans (Q.moving.effectiveFullSupport_mask Q.remaining u I)

@[simp] theorem effectiveMovingMaskRecipe_support (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    Q.effectiveMovingMaskRecipe.support u = Q.moving.effectiveFullSupport Q.remaining := rfl

theorem effectiveMovingMaskRecipe_jointBudget (Z width : ℝ)
    (hbudget : Q.FullJointBudget Z width) (ξ : X)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u) :
    idealNorm K u * A.exteriorNorm (Q.effectiveMovingMaskRecipe.support u) ≤ Z ^ width :=
  Q.exteriorRemaining_fullJointBudget Z width hbudget ξ u hu

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.completeMovingMask_remainingRadical
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.effectiveSupportAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.exteriorRemaining
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.exteriorRemaining_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.effectiveMovingMaskRecipe
