import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedCommonMass

/-!
# The independent second divisor and both common-support sums

The divisor S from the first coprimality expansion is the old mask of
the second common-support labels. The second residual divisor L is a
different summation variable. Its two complete occurrence-allocation
families are paid by the literal 1 / N(L) density supplied by the two
frozen column scalars. No allocation count of S replaces this L sum.

Only finite carriers, original norm windows and bounded occurrence
counts occur in the hypotheses below. All constants precede the scale,
the old mask, both divisor carriers and every moving common label.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

/-- Absolute allocation mass with the actual second divisor's density. -/
def secondDivisorAllocationMass (S : Finset (Ideal (𝓞 K)))
    (k₁ k₂ : Ideal (𝓞 K) → ℕ) : ℝ :=
  ∑ L ∈ S, ‖(moebius L : ℂ)‖ *
    ((AllocationMass.idealAllocations L (k₁ L)).card : ℝ) *
    ((AllocationMass.idealAllocations L (k₂ L)).card : ℝ) /
      (Ideal.absNorm L : ℝ)

theorem secondDivisorAllocationMass_nonneg (S : Finset (Ideal (𝓞 K)))
    (k₁ k₂ : Ideal (𝓞 K) → ℕ) : 0 ≤ secondDivisorAllocationMass S k₁ k₂ := by
  apply Finset.sum_nonneg
  intro L hL
  exact div_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

private theorem moebius_norm_le_one (L : Ideal (𝓞 K)) :
    ‖(moebius L : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

/-- Two full allocation families of L together with their own harmonic
density have a small-power cost, uniformly in all moving carriers. -/
theorem second_divisor_allocation_mass (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ S : Finset (Ideal (𝓞 K)), (∀ L ∈ S, L ≠ 0) →
      (∀ L ∈ S, (Ideal.absNorm L : ℝ) ≤ Z ^ B) →
      ∀ k₁ k₂ : Ideal (𝓞 K) → ℕ,
      (∀ L ∈ S, k₁ L ≤ N ∧ k₂ L ≤ N) →
      secondDivisorAllocationMass S k₁ k₂ ≤ C * Z ^ ε := by
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C₁, hC₁, halloc⟩ := allocation_card_power_scale (K := K) N B δ hB hδ
  obtain ⟨C₂, hC₂, hsum⟩ := ideal_inverse_norm_subpower (K := K) B δ hB hδ
  refine ⟨C₁ ^ 2 * C₂, by positivity, ?_⟩
  intro Z hZ S hS hnorm k₁ k₂ hk
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let F : ℝ := (C₁ * Z ^ δ) ^ 2
  have hF : 0 ≤ F := sq_nonneg _
  have hterm (L : Ideal (𝓞 K)) (hL : L ∈ S) :
      ‖(moebius L : ℂ)‖ *
          ((AllocationMass.idealAllocations L (k₁ L)).card : ℝ) *
          ((AllocationMass.idealAllocations L (k₂ L)).card : ℝ) /
            (Ideal.absNorm L : ℝ) ≤ F * (1 / (Ideal.absNorm L : ℝ)) := by
    have h₁ := halloc Z hZ L (hS L hL) (hnorm L hL) (k₁ L) (hk L hL).1
    have h₂ := halloc Z hZ L (hS L hL) (hnorm L hL) (k₂ L) (hk L hL).2
    have hcards : ‖(moebius L : ℂ)‖ *
        ((AllocationMass.idealAllocations L (k₁ L)).card : ℝ) *
        ((AllocationMass.idealAllocations L (k₂ L)).card : ℝ) ≤
          1 * (C₁ * Z ^ δ) * (C₁ * Z ^ δ) :=
      mul_le_mul
        (mul_le_mul (moebius_norm_le_one L) h₁ (Nat.cast_nonneg _) zero_le_one)
        h₂ (Nat.cast_nonneg _) (by positivity)
    calc
      _ ≤ (1 * (C₁ * Z ^ δ) * (C₁ * Z ^ δ)) / (Ideal.absNorm L : ℝ) :=
        div_le_div_of_nonneg_right hcards (Nat.cast_nonneg _)
      _ = _ := by dsimp only [F]; ring
  calc
    _ ≤ ∑ L ∈ S, F * (1 / (Ideal.absNorm L : ℝ)) := Finset.sum_le_sum hterm
    _ = F * (∑ L ∈ S, 1 / (Ideal.absNorm L : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ F * (C₂ * Z ^ δ) := mul_le_mul_of_nonneg_left (hsum Z hZ S hS hnorm) hF
    _ = _ := by
      dsimp only [F]
      have he : ε = δ + δ + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      ring

/-- The first shared divisor and the second residual divisor are
independent fields of the actual finite carrier. -/
structure TwoDivisorCommonBranch where
  first : Finset (Label K)
  firstDivisors : Label K → Finset (Ideal (𝓞 K))
  second : Label K → Ideal (𝓞 K) → Finset (Label K)
  secondDivisors : Label K → Ideal (𝓞 K) → Label K → Finset (Ideal (𝓞 K))
  leftOccurrences : Label K → Ideal (𝓞 K) → Label K → Ideal (𝓞 K) → ℕ
  rightOccurrences : Label K → Ideal (𝓞 K) → Label K → Ideal (𝓞 K) → ℕ

namespace TwoDivisorCommonBranch

def mass (b : TwoDivisorCommonBranch (K := K)) : ℝ :=
  ∑ v ∈ b.first, (1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) *
    ∑ S ∈ b.firstDivisors v, ‖(moebius S : ℂ)‖ *
      ∑ w ∈ b.second v S, (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) *
        secondDivisorAllocationMass (b.secondDivisors v S w)
          (b.leftOccurrences v S w) (b.rightOccurrences v S w)

theorem mass_nonneg (b : TwoDivisorCommonBranch (K := K)) : 0 ≤ b.mass := by
  apply Finset.sum_nonneg
  intro v hv
  apply mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro S hS
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro w hw
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    (secondDivisorAllocationMass_nonneg _ _ _)

/-- Raw finite-support conditions, with no input bound on the mass. -/
structure Admissible (b : TwoDivisorCommonBranch (K := K))
    (N : ℕ) (B Z : ℝ) (s : Ideal (𝓞 K)) : Prop where
  first_valid : ∀ v ∈ b.first, Valid s v
  first_norm : ∀ v ∈ b.first,
    (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B
  first_divisor_valid : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v, Squarefree S ∧ S ≠ 0
  first_divisor_norm : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v,
    (Ideal.absNorm S : ℝ) ≤ Z ^ B
  second_valid : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v, ∀ w ∈ b.second v S, Valid S w
  second_norm : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v, ∀ w ∈ b.second v S,
    (Ideal.absNorm w.1.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm w.1.2 : ℝ) ≤ Z ^ B
  second_divisor_ne_zero : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v,
    ∀ w ∈ b.second v S, ∀ L ∈ b.secondDivisors v S w, L ≠ 0
  second_divisor_norm : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v,
    ∀ w ∈ b.second v S, ∀ L ∈ b.secondDivisors v S w, (Ideal.absNorm L : ℝ) ≤ Z ^ B
  occurrences : ∀ v ∈ b.first, ∀ S ∈ b.firstDivisors v,
    ∀ w ∈ b.second v S, ∀ L ∈ b.secondDivisors v S w,
    b.leftOccurrences v S w L ≤ N ∧ b.rightOccurrences v S w L ≤ N

/-- Both common-support sums, the first shared divisor and the genuinely
independent second allocation divisor have a uniform harmonic mass.
The old-mask factor is retained exactly once. -/
theorem uniform_mass (N : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
      ∀ b : TwoDivisorCommonBranch (K := K), b.Admissible N B Z s →
        b.mass ≤ C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C₁, hC₁, hcommon⟩ := common_radical_harmonic_mass (K := K) B δ hB hδ
  obtain ⟨C₂, hC₂, hfirstDivisor⟩ := ideal_inverse_norm_subpower (K := K) B δ hB hδ
  obtain ⟨C₃, hC₃, hsecondDivisor⟩ := second_divisor_allocation_mass (K := K) N B δ hB hδ
  refine ⟨C₃ * C₁ * C₂ * C₁, by positivity, ?_⟩
  intro Z hZ s hs hs0 b hb
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let F : ℝ := C₃ * C₁ * Z ^ (2 * δ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hsecond (v : Label K) (hv : v ∈ b.first) (S : Ideal (𝓞 K))
      (hS : S ∈ b.firstDivisors v) :
      ‖(moebius S : ℂ)‖ *
        (∑ w ∈ b.second v S,
          (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) *
            secondDivisorAllocationMass (b.secondDivisors v S w)
              (b.leftOccurrences v S w) (b.rightOccurrences v S w)) ≤
        F * (1 / (Ideal.absNorm S : ℝ)) := by
    have hraw :
        (∑ w ∈ b.second v S,
          (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) *
            secondDivisorAllocationMass (b.secondDivisors v S w)
              (b.leftOccurrences v S w) (b.rightOccurrences v S w)) ≤
        (C₃ * Z ^ δ) * radicalMass (b.second v S) := by
      calc
        _ ≤ ∑ w ∈ b.second v S,
            (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) * (C₃ * Z ^ δ) := by
          apply Finset.sum_le_sum
          intro w hw
          apply mul_le_mul_of_nonneg_left
          · exact hsecondDivisor Z hZ (b.secondDivisors v S w)
              (hb.second_divisor_ne_zero v hv S hS w hw)
              (hb.second_divisor_norm v hv S hS w hw)
              (b.leftOccurrences v S w) (b.rightOccurrences v S w)
              (hb.occurrences v hv S hS w hw)
          · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
        _ = _ := by
          rw [radicalMass, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w hw
          ring
    have hsum := hraw.trans (mul_le_mul_of_nonneg_left
      (hcommon Z hZ S (hb.first_divisor_valid v hv S hS).1
        (hb.first_divisor_valid v hv S hS).2 (b.second v S)
        (hb.second_valid v hv S hS) (hb.second_norm v hv S hS)) (by positivity))
    have hraw0 : 0 ≤ ∑ w ∈ b.second v S,
        (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) *
          secondDivisorAllocationMass (b.secondDivisors v S w)
            (b.leftOccurrences v S w) (b.rightOccurrences v S w) :=
      Finset.sum_nonneg (fun w _ =>
        mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
          (secondDivisorAllocationMass_nonneg _ _ _))
    calc
      _ ≤ 1 * ((C₃ * Z ^ δ) * (C₁ * Z ^ δ / (Ideal.absNorm S : ℝ))) :=
        mul_le_mul (moebius_norm_le_one S) hsum hraw0 zero_le_one
      _ = _ := by
        dsimp only [F]
        rw [show 2 * δ = δ + δ by ring, Real.rpow_add hz]
        ring
  have hinner (v : Label K) (hv : v ∈ b.first) :
      (∑ S ∈ b.firstDivisors v, ‖(moebius S : ℂ)‖ *
        ∑ w ∈ b.second v S, (1 / (Ideal.absNorm (commonRadical w.1.1 w.1.2) : ℝ)) *
          secondDivisorAllocationMass (b.secondDivisors v S w)
            (b.leftOccurrences v S w) (b.rightOccurrences v S w)) ≤
        F * (C₂ * Z ^ δ) := by
    calc
      _ ≤ ∑ S ∈ b.firstDivisors v, F * (1 / (Ideal.absNorm S : ℝ)) :=
        Finset.sum_le_sum (hsecond v hv)
      _ = F * (∑ S ∈ b.firstDivisors v, 1 / (Ideal.absNorm S : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hfirstDivisor Z hZ (b.firstDivisors v)
          (fun S hS => (hb.first_divisor_valid v hv S hS).2)
          (hb.first_divisor_norm v hv)) hF
  calc
    _ ≤ ∑ v ∈ b.first, (1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) *
        (F * (C₂ * Z ^ δ)) :=
      Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hinner v hv)
        (one_div_nonneg.mpr (Nat.cast_nonneg _)))
    _ = (F * (C₂ * Z ^ δ)) * radicalMass b.first := by
      rw [radicalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (F * (C₂ * Z ^ δ)) * (C₁ * Z ^ δ / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (hcommon Z hZ s hs hs0 b.first hb.first_valid hb.first_norm) (by positivity)
    _ = _ := by
      dsimp only [F]
      have he : ε = 2 * δ + δ + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      ring

end TwoDivisorCommonBranch
end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.second_divisor_allocation_mass
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.TwoDivisorCommonBranch.uniform_mass
