import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm

/-!
# The actual frozen scalar of a passive-deletion allocation

The signed scalar is estimated on the actual occurrence allocation.
Nonsquarefree divisors vanish by their Mobius coefficient.  For the
remaining labels the original central denominators pay the divisor's
inverse norm, using only the original individual arithmetic, profile
and annulus bounds.

The left and right deletion labels are independent.  Their scalar
product therefore retains two square-root denominators.  It is not
identified with the inverse norm of a shared second divisor.  The
additional frozen-slot envelope is kept explicitly; a uniform
single-slot budget pays at most one further `cap` power for the pair.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {k : ℕ}

/-- Membership in the actual live carrier supplies the occurrence
selection property used by the frozen-ideal divisibility theorem. -/
theorem allocation_selection_mem (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal}) :
    (allocation M S₁ S₂ S hS₁ hS₂ a).selection ∈
      AllocationMass.idealAllocations (allocation M S₁ S₂ S hS₁ hS₂ a).divisor
        (k + 2) :=
  (Finset.mem_sigma.mp (Finset.mem_filter.mp a.property).1).2

/-- No squarefreeness hypothesis is needed: a nonsquarefree allocation
has zero signed scalar before any bound is applied. -/
theorem signed_scalar_norm_sq_le_divisor
    (B : ActualColumnAllocation K k)
    (C : A.GeneralArithmeticContext σ η hS)
    (T : FixedChildCharacters K k) (g h : A.R) (Z : ℝ) (hZ : 0 < Z)
    (length : Fin k → ℝ) (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask
      (B.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (B.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ length i)
    (hprofile : ∀ i ∈ Finset.univ \ B.keep, ‖w i (B.witness.2 i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (ha : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2)) :
    ‖sign ⟨B.divisor, B.selection⟩ * B.scalar (σ := σ) T g h Z length w‖ ^ 2 ≤
      (∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) /
        (Ideal.absNorm B.divisor : ℝ) := by
  by_cases hsq : Squarefree B.divisor
  · have hsign : ‖sign ⟨B.divisor, B.selection⟩‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (norm_sign_le_one ⟨B.divisor, B.selection⟩) 2
    rw [norm_mul, mul_pow]
    calc
      _ ≤ ‖B.scalar (σ := σ) T g h Z length w‖ ^ 2 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hsign (sq_nonneg ‖B.scalar (σ := σ) T g h Z length w‖)
      _ ≤ _ := B.scalar_norm_sq_le_divisor C T g h Z hZ length w annulus profile
        hplain₁ hplain₂ hprime hannulus hprofile hA hP hsq ha
  · simp only [sign, moebius_of_not_squarefree hsq, Int.cast_zero,
      zero_mul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact div_nonneg
      (Finset.prod_nonneg fun i _ => mul_nonneg (hA i) (hP i)) (Nat.cast_nonneg _)

/-- The preceding estimate instantiated on the branch actually computed
from the original passive mask and finite source carriers. -/
theorem allocation_signed_scalar_norm_sq_le
    (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal})
    (C : A.GeneralArithmeticContext σ η hS)
    (T : FixedChildCharacters K k) (g h : A.R) (Z : ℝ) (hZ : 0 < Z)
    (length : Fin k → ℝ) (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (annulus profile : Fin k → ℝ) :
    let B := allocation M S₁ S₂ S hS₁ hS₂ a
    (∀ i, 0 ≤ annulus i) → (∀ i, 0 ≤ profile i) →
    ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor 0)‖ ≤ 1 →
    ‖sourcePlainCoefficient T.plain T.plainTwist T.mask
      (B.plainDivisor (Fin.succ 0))‖ ≤ 1 →
    (∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (B.witness.2 i)‖ ≤ 1) →
    (∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ length i) →
    (∀ i ∈ Finset.univ \ B.keep, ‖w i (B.witness.2 i)‖ ^ 2 ≤ profile i) →
    ‖sign a.val * B.scalar (σ := σ) T g h Z length w‖ ^ 2 ≤
      (∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) /
        (Ideal.absNorm a.val.1 : ℝ) := by
  dsimp only
  intro hA hP hplain₁ hplain₂ hprime hannulus hprofile
  exact signed_scalar_norm_sq_le_divisor (allocation M S₁ S₂ S hS₁ hS₂ a)
    C T g h Z hZ length w annulus profile hplain₁ hplain₂ hprime hannulus hprofile hA hP
    (allocation_selection_mem M S₁ S₂ S hS₁ hS₂ a)

/-- A raw uniform bound on each original slot pays the actual frozen
subset. No cardinality estimate for a final label family is assumed. -/
theorem frozen_envelope_le_slotBudget
    (B : ActualColumnAllocation K k) (annulus profile : Fin k → ℝ)
    (slotBudget : ℝ) (hslotBudget : 1 ≤ slotBudget) (cap : ℕ) (hcap : k ≤ cap)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hslot : ∀ i, annulus i * profile i ≤ slotBudget) :
    (∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) ≤ slotBudget ^ cap := by
  have hcard : (Finset.univ \ B.keep).card ≤ cap :=
    (Finset.card_le_card Finset.sdiff_subset).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hcap)
  calc
    _ ≤ ∏ _i ∈ Finset.univ \ B.keep, slotBudget :=
      Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hA i) (hP i)) (fun i _ => hslot i)
    _ = slotBudget ^ (Finset.univ \ B.keep).card := by rw [Finset.prod_const]
    _ ≤ _ := pow_le_pow_right₀ hslotBudget hcard

/-- Two independently selected passive divisors retain their separate
square-root denominators. The shared-second-divisor estimate is not used. -/
theorem independent_scalar_inverse_norm (left right : ℂ) (NL NR EL ER : ℝ)
    (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hleft : ‖left‖ ^ 2 ≤ EL / NL) (hright : ‖right‖ ^ 2 ≤ ER / NR) :
    ‖left‖ * ‖right‖ ≤
      Real.sqrt EL * Real.sqrt ER / (Real.sqrt NL * Real.sqrt NR) := by
  have hl : ‖left‖ ≤ Real.sqrt EL / Real.sqrt NL := by
    simpa only [Real.sqrt_sq (norm_nonneg left), Real.sqrt_div hEL NL] using
      Real.sqrt_le_sqrt hleft
  have hr : ‖right‖ ≤ Real.sqrt ER / Real.sqrt NR := by
    simpa only [Real.sqrt_sq (norm_nonneg right), Real.sqrt_div hER NR] using
      Real.sqrt_le_sqrt hright
  calc
    _ ≤ (Real.sqrt EL / Real.sqrt NL) * (Real.sqrt ER / Real.sqrt NR) :=
      mul_le_mul hl hr (norm_nonneg right)
        (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by rw [div_mul_div_comm]

/-- With the same raw slot budget on both sides, the entire additional
pair of frozen subsets costs at most one further `cap` power. -/
theorem independent_pair_slotBudget (left right : ℂ) (NL NR slotBudget : ℝ)
    (hslotBudget : 0 ≤ slotBudget) (cap : ℕ)
    (hleft : ‖left‖ ^ 2 ≤ slotBudget ^ cap / NL)
    (hright : ‖right‖ ^ 2 ≤ slotBudget ^ cap / NR) :
    ‖left‖ * ‖right‖ ≤ slotBudget ^ cap / (Real.sqrt NL * Real.sqrt NR) := by
  simpa only [← sq, Real.sq_sqrt (pow_nonneg hslotBudget cap)] using
    independent_scalar_inverse_norm left right NL NR (slotBudget ^ cap) (slotBudget ^ cap)
      (pow_nonneg hslotBudget cap) (pow_nonneg hslotBudget cap) hleft hright

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.allocation_selection_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.signed_scalar_norm_sq_le_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.allocation_signed_scalar_norm_sq_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.frozen_envelope_le_slotBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.independent_scalar_inverse_norm
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveDeletion.independent_pair_slotBudget
