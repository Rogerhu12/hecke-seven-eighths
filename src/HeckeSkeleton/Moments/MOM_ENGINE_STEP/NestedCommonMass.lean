import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonHarmonicMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationMass

/-!
# The two actual common-support sums and their shared divisor

The second common-support label retains the divisor from the first
coprimality expansion as its old mask. Its proved harmonic mass therefore
contains the factor `1 / N(D)`. Summing the actual divisors costs only a
logarithm. Both full occurrence-allocation families are retained, and
their cardinalities are bounded from their literal prime supports.

The constants precede the scale, the old mask, every finite label family,
and the two numbers of factor occurrences. No aggregate label estimate
is supplied as an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CommonSupportMass

open NumberField UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

theorem ideal_inverse_norm_subpower (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ S : Finset (Ideal (𝓞 K)),
      (∀ I ∈ S, I ≠ 0) → (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ B) →
      (∑ I ∈ S, 1 / (Ideal.absNorm I : ℝ)) ≤ C * Z ^ ε := by
  obtain ⟨D, hD, hlog⟩ := log_linear_subpower ε hε
  let L : ℝ := 2 + B / Real.log 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hcount : 0 < idealCountConstant K :=
    zero_lt_one.trans_le (one_le_idealCountConstant K)
  refine ⟨2 * idealCountConstant K * L * D, by positivity, ?_⟩
  intro Z hZ S hS hN
  have hraw := divisible_inverse_norm_sum S (1 : Ideal (𝓞 K)) one_ne_zero
    hS (fun I _ => one_dvd I) (Z ^ B) hN
  simp only [map_one, Nat.cast_one, div_one] at hraw
  calc
    _ ≤ 2 * idealCountConstant K * (columnDyadicLength (Z ^ B) + 1 : ℝ) := hraw
    _ ≤ 2 * idealCountConstant K * (L * (1 + Real.log Z)) :=
      mul_le_mul_of_nonneg_left (column_dyadic_length_log_bound B Z hB hZ) (by positivity)
    _ ≤ 2 * idealCountConstant K * (L * (D * Z ^ ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hlog Z hZ) hL.le) (by positivity)
    _ = _ := by ring

/-- The full allocation family at a bounded actual divisor has a uniform
small power cost, for every occurrence count below the earlier bound. -/
theorem allocation_card_power_scale (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ D : Ideal (𝓞 K), D ≠ 0 →
      (Ideal.absNorm D : ℝ) ≤ Z ^ B → ∀ k : ℕ, k ≤ N →
      ((AllocationMass.idealAllocations D k).card : ℝ) ≤ C * Z ^ ε := by
  let e : ℝ := ε / (B + 1)
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨C, hC, halloc⟩ := AllocationMass.ideal_allocation_card_bound K N e he
  refine ⟨C, hC, ?_⟩
  intro Z hZ D hD hnorm k hk
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hbudget : B * e ≤ ε := by
    have hid : e * (B + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm D : ℝ) ^ e := halloc D hD k hk
    _ ≤ C * (Z ^ B) ^ e :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm he.le) hC.le
    _ = C * Z ^ (B * e) := by rw [← Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hbudget) hC.le

def radicalMass (S : Finset (Label K)) : ℝ :=
  ∑ v ∈ S, 1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)

theorem radicalMass_nonneg (S : Finset (Label K)) : 0 ≤ radicalMass S :=
  Finset.sum_nonneg (fun _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _))

/-- The shared divisor has two full inclusion-exclusion allocations.
Their signs have norm one, so these literal cardinalities are the exact
absolute masses before any compatibility restriction. -/
def allocatedRadicalMass (D : Ideal (𝓞 K)) (k₁ k₂ : ℕ)
    (S : Finset (Label K)) : ℝ :=
  ‖(moebius D : ℂ)‖ * ((AllocationMass.idealAllocations D k₁).card : ℝ) *
    ((AllocationMass.idealAllocations D k₂).card : ℝ) * radicalMass S

theorem allocatedRadicalMass_nonneg (D : Ideal (𝓞 K)) (k₁ k₂ : ℕ)
    (S : Finset (Label K)) : 0 ≤ allocatedRadicalMass D k₁ k₂ S :=
  mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) (radicalMass_nonneg S)

/-- The actual nested first/second labels, shared divisors, and both
whole-factor allocation families have uniform mass. The second label
contains the original divisor in both full common ideals. This is the
source of the divisor's harmonic density; it is not imposed afterwards. -/
theorem nested_common_support_mass (N : ℕ) (B ε : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 →
    ∀ first : Finset (Label K), (∀ v ∈ first, Valid s v) →
      (∀ v ∈ first, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ B) →
    ∀ divisors : Label K → Finset (Ideal (𝓞 K)),
      (∀ v ∈ first, ∀ D ∈ divisors v, Squarefree D ∧ D ≠ 0) →
      (∀ v ∈ first, ∀ D ∈ divisors v, (Ideal.absNorm D : ℝ) ≤ Z ^ B) →
    ∀ second : Label K → Ideal (𝓞 K) → Finset (Label K),
      (∀ v ∈ first, ∀ D ∈ divisors v, ∀ w ∈ second v D, Valid D w) →
      (∀ v ∈ first, ∀ D ∈ divisors v, ∀ w ∈ second v D,
        (Ideal.absNorm w.1.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm w.1.2 : ℝ) ≤ Z ^ B) →
    ∀ k₁ k₂ : Label K → Ideal (𝓞 K) → ℕ,
      (∀ v ∈ first, ∀ D ∈ divisors v, k₁ v D ≤ N ∧ k₂ v D ≤ N) →
      (∑ v ∈ first, (1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) *
        ∑ D ∈ divisors v, allocatedRadicalMass D (k₁ v D) (k₂ v D) (second v D)) ≤
        C * Z ^ ε / (Ideal.absNorm s : ℝ) := by
  let δ : ℝ := ε / 5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C₁, hC₁, hcommon⟩ := common_radical_harmonic_mass (K := K) B δ hB hδ
  obtain ⟨C₂, hC₂, hdivisor⟩ := ideal_inverse_norm_subpower (K := K) B δ hB hδ
  obtain ⟨C₃, hC₃, halloc⟩ := allocation_card_power_scale (K := K) N B δ hB hδ
  refine ⟨C₃ ^ 2 * C₁ * C₂ * C₁, by positivity, ?_⟩
  intro Z hZ s hs hs0 first hfirst hfirstN divisors hdiv hdivN second hsecond hsecondN k₁ k₂ hk
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let F : ℝ := C₃ ^ 2 * C₁ * Z ^ (3 * δ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hsecondSum (v : Label K) (hv : v ∈ first) (D : Ideal (𝓞 K))
      (hD : D ∈ divisors v) :
      allocatedRadicalMass D (k₁ v D) (k₂ v D) (second v D) ≤
        F * (1 / (Ideal.absNorm D : ℝ)) := by
    have hcard₁ := halloc Z hZ D (hdiv v hv D hD).2 (hdivN v hv D hD) (k₁ v D)
      (hk v hv D hD).1
    have hcard₂ := halloc Z hZ D (hdiv v hv D hD).2 (hdivN v hv D hD) (k₂ v D)
      (hk v hv D hD).2
    have hsecondMass : radicalMass (second v D) ≤ C₁ * Z ^ δ / (Ideal.absNorm D : ℝ) :=
      hcommon Z hZ D (hdiv v hv D hD).1 (hdiv v hv D hD).2 (second v D)
        (hsecond v hv D hD) (hsecondN v hv D hD)
    have hmu : ‖(moebius D : ℂ)‖ ≤ 1 := by
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    have hcards : ‖(moebius D : ℂ)‖ *
        ((AllocationMass.idealAllocations D (k₁ v D)).card : ℝ) *
        ((AllocationMass.idealAllocations D (k₂ v D)).card : ℝ) ≤
        1 * (C₃ * Z ^ δ) * (C₃ * Z ^ δ) :=
      mul_le_mul (mul_le_mul hmu hcard₁ (Nat.cast_nonneg _) zero_le_one)
        hcard₂ (Nat.cast_nonneg _) (by positivity)
    calc
      _ ≤ (1 * (C₃ * Z ^ δ) * (C₃ * Z ^ δ)) *
          (C₁ * Z ^ δ / (Ideal.absNorm D : ℝ)) :=
        mul_le_mul hcards hsecondMass (radicalMass_nonneg _) (by positivity)
      _ = _ := by
        dsimp only [F]
        rw [show 3 * δ = δ + δ + δ by ring, Real.rpow_add hz, Real.rpow_add hz]
        ring
  have hinner (v : Label K) (hv : v ∈ first) :
      (∑ D ∈ divisors v, allocatedRadicalMass D (k₁ v D) (k₂ v D) (second v D)) ≤
        F * (C₂ * Z ^ δ) := by
    calc
      _ ≤ ∑ D ∈ divisors v, F * (1 / (Ideal.absNorm D : ℝ)) :=
        Finset.sum_le_sum (hsecondSum v hv)
      _ = F * (∑ D ∈ divisors v, 1 / (Ideal.absNorm D : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hdivisor Z hZ (divisors v) (fun D hD => (hdiv v hv D hD).2) (hdivN v hv)) hF
  calc
    _ ≤ ∑ v ∈ first, (1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)) *
        (F * (C₂ * Z ^ δ)) :=
      Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hinner v hv)
        (one_div_nonneg.mpr (Nat.cast_nonneg _)))
    _ = (F * (C₂ * Z ^ δ)) * radicalMass first := by
      rw [radicalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (F * (C₂ * Z ^ δ)) * (C₁ * Z ^ δ / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcommon Z hZ s hs hs0 first hfirst hfirstN) (by positivity)
    _ = _ := by
      dsimp only [F]
      have he : ε = 3 * δ + δ + δ := by dsimp [δ]; ring
      rw [he, Real.rpow_add hz, Real.rpow_add hz]
      ring

end HeckeSkeleton.Moments.EngineStep.CommonSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.ideal_inverse_norm_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.CommonSupportMass.nested_common_support_mass
