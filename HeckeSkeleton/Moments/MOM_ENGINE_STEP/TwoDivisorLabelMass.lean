import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDivisorMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FinitePhase

/-!
# The complete two-divisor carrier and its finite phase weights

The label retains both common-support labels, the first shared divisor,
the independent second divisor, both original finite characters and
both full occurrence allocations of the second divisor.  Its harmonic
weight is exactly the weight in `TwoDivisorCommonBranch.mass`; finite
characters cost only the fixed ray-quotient constant.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid HeckeGeneral.Characters
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]
variable (Ray : Type*) [CommGroup Ray] [Fintype Ray]

local instance twoDivisorLabelMassCircleCharacterFintype : Fintype ((Ray × Ray) →* Circle) := Fintype.ofFinite _

namespace TwoDivisorCommonBranch

variable (b : TwoDivisorCommonBranch (K := K))

/-- No compatible nonempty original label is selected after the
continuous Fourier parameter: this is the full finite carrier. -/
abbrev AtomicLabel :=
  Σ v : b.first, Σ S : b.firstDivisors v.val, Σ _χ₁ : (Ray × Ray) →* Circle,
    Σ w : b.second v.val S.val, Σ L : b.secondDivisors v.val S.val w.val,
      Σ _χ₂ : (Ray × Ray) →* Circle,
        Σ _a : AllocationMass.idealAllocations L.val (b.leftOccurrences v.val S.val w.val L.val),
          AllocationMass.idealAllocations L.val (b.rightOccurrences v.val S.val w.val L.val)

namespace AtomicLabel

variable {Ray b} (z : b.AtomicLabel Ray)

def firstLabel : Label K := z.1.val
def firstDivisor : Ideal (𝓞 K) := z.2.1.val
def firstPhase : (Ray × Ray) →* Circle := z.2.2.1
def secondLabel : Label K := z.2.2.2.1.val
def secondDivisor : Ideal (𝓞 K) := z.2.2.2.2.1.val
def secondPhase : (Ray × Ray) →* Circle := z.2.2.2.2.2.1

def harmonicWeight : ℝ :=
  (1 / (Ideal.absNorm (commonRadical z.firstLabel.1.1 z.firstLabel.1.2) : ℝ)) *
    ‖(moebius z.firstDivisor : ℂ)‖ *
    (1 / (Ideal.absNorm (commonRadical z.secondLabel.1.1 z.secondLabel.1.2) : ℝ)) *
    ‖(moebius z.secondDivisor : ℂ)‖ / (Ideal.absNorm z.secondDivisor : ℝ)

theorem harmonicWeight_nonneg : 0 ≤ z.harmonicWeight := by
  unfold harmonicWeight
  positivity

/-- These are the actual normalized finite Fourier coefficients, not
arbitrary label weights.  Their phase tables may depend on every fixed
finite label. -/
def weight (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle) : ℝ :=
  z.harmonicWeight * ‖fixedPhaseCoefficient Ray (phase₁ z) z.firstPhase‖ *
    ‖fixedPhaseCoefficient Ray (phase₂ z) z.secondPhase‖

theorem weight_nonneg (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle) :
    0 ≤ z.weight phase₁ phase₂ :=
  mul_nonneg (mul_nonneg z.harmonicWeight_nonneg (norm_nonneg _)) (norm_nonneg _)

theorem weight_le_harmonic (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle) :
    z.weight phase₁ phase₂ ≤ z.harmonicWeight := by
  have h₁ := fixed_phase_coefficient_norm Ray (phase₁ z) z.firstPhase
  have h₂ := fixed_phase_coefficient_norm Ray (phase₂ z) z.secondPhase
  calc
    _ ≤ z.harmonicWeight * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left h₁ z.harmonicWeight_nonneg) h₂
        (norm_nonneg _) (by simpa only [mul_one] using z.harmonicWeight_nonneg)
    _ = _ := by ring

end AtomicLabel

/-- Expanding the actual sigma carrier gives exactly the old harmonic
mass and the two fixed finite-character cardinalities. -/
theorem atomic_harmonic_mass :
    (∑ z : b.AtomicLabel Ray, z.harmonicWeight) = (Nat.card Ray : ℝ) ^ 4 * b.mass := by
  have hchar : (Fintype.card ((Ray × Ray) →* Circle) : ℝ) = (Nat.card Ray : ℝ) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, natCard_circleDual, Nat.card_prod, Nat.cast_mul, pow_two]
  simp only [AtomicLabel, Fintype.sum_sigma, AtomicLabel.harmonicWeight,
    AtomicLabel.firstLabel, AtomicLabel.firstDivisor, AtomicLabel.secondLabel, AtomicLabel.secondDivisor]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, hchar,
    mass, secondDivisorAllocationMass]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  rw [← Finset.sum_coe_sort b.first]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_coe_sort (b.firstDivisors v.val)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← Finset.sum_coe_sort (b.second v.val S.val)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.sum_coe_sort (b.secondDivisors v.val S.val w.val)]
  apply Finset.sum_congr rfl
  intro L hL
  ring

theorem atomic_weight_mass
    (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle) :
    (∑ z : b.AtomicLabel Ray, z.weight phase₁ phase₂) ≤ (Nat.card Ray : ℝ) ^ 4 * b.mass :=
  (Finset.sum_le_sum (fun z _ => z.weight_le_harmonic phase₁ phase₂)).trans_eq
    (b.atomic_harmonic_mass Ray)

/-- Any original compatibility filter can only reduce the positive
label mass; every surviving label retains its original coefficient. -/
theorem atomic_filtered_weight_mass (labels : Finset (b.AtomicLabel Ray))
    (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle) :
    (∑ z ∈ labels, z.weight phase₁ phase₂) ≤ (Nat.card Ray : ℝ) ^ 4 * b.mass := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ labels)
    (fun z _ _ => z.weight_nonneg phase₁ phase₂)).trans
  exact b.atomic_weight_mass Ray phase₁ phase₂

end TwoDivisorCommonBranch

/-- Original norm windows and occurrence bounds suffice for the full
two-character, two-allocation label family.  The same constant precedes
the scale, old mask, both phase tables and every retained finite subset. -/
theorem actual_two_divisor_label_uniform_mass (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
    ∀ b : TwoDivisorCommonBranch (K := K), b.Admissible N B Z s →
    ∀ (labels : Finset (b.AtomicLabel Ray))
      (phase₁ phase₂ : b.AtomicLabel Ray → Ray × Ray → Circle),
      (∑ z ∈ labels, z.weight phase₁ phase₂) ≤ C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  obtain ⟨C₀, hC₀, hmass⟩ := TwoDivisorCommonBranch.uniform_mass (K := K) N B ε hB hε
  have hRay : 0 < (Nat.card Ray : ℝ) ^ 4 :=
    pow_pos (Nat.cast_pos.mpr (Nat.card_pos (α := Ray))) 4
  refine ⟨(Nat.card Ray : ℝ) ^ 4 * C₀, mul_pos hRay hC₀, ?_⟩
  intro Z hZ s hs hs0 b hb labels phase₁ phase₂
  apply (b.atomic_filtered_weight_mass Ray labels phase₁ phase₂).trans
  exact (mul_le_mul_of_nonneg_left (hmass Z hZ s hs hs0 b hb) hRay.le).trans_eq (by ring)

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.atomic_harmonic_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.actual_two_divisor_label_uniform_mass
