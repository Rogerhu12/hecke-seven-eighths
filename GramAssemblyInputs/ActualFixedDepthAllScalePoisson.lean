import ActualFixedDepthPoissonBound
import NonzeroLatticeAllScaleCount

/-!
UNCOMPILED / native 0. The same actual product-lattice periodic sum has a
genuine all-scale trivial bound at zero translation when its Schwartz input
vanishes at the origin and has fixed bounded support. The nonzero lattice
gap supplies the small-scale case. Combining this with the actual arithmetic
mean-zero Poisson estimate gives the min factor, at the fixed depth 2H.

This file does not identify the entire S-integer divisor sum with this sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualFixedDepthAllScaleDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramCoefficientBoundDraft ActualGramPeriodNormDraft
open ActualTraceProductResidueQuotientDraft ActualTraceProductFourierDilationDraft
open ActualMeanZeroProductPoissonDraft ActualFixedDepthPoissonDraft
open NonzeroLatticeAllScaleCountDraft
open scoped Classical BigOperators FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "W" => traceProductSpace K
local notation "L" => ordinaryProductLattice K

/-- A fixed support radius gives a uniform trivial bound for the actual
periodic sum. Both the modulus and its weight are allowed to move. -/
theorem exists_productPeriodicSum_allScale_trivial_bound (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : (Ideal (𝓞 K))⁰)
      (w : LatticeQuotient L (integralProductLattice K I) → ℂ)
      (F : SchwartzMap W ℂ) (N Q : ℝ), 0 < N → 0 ≤ Q →
      (∀ q, ‖w q‖ ≤ Q) → F 0 = 0 →
      (∀ x, F x ≠ 0 → ‖x‖ ≤ R) →
      ‖productPeriodicSum K I w F N 0‖ ≤
        C * Q * SchwartzMap.seminorm ℂ 0 0 F * N ^ 2 := by
  obtain ⟨C, hC, hcount⟩ := exists_nonzero_lattice_norm_power_count_le L
  let dim := Module.finrank ℝ W
  refine ⟨C * R ^ dim, mul_pos hC (pow_pos hR _), ?_⟩
  intro I w F N Q hN hQ hw hF0 hFR
  let r := traceNormScale K N
  have hr : 0 < r := traceNormScale_pos K N hN
  let f : L → ℂ := fun l =>
    w (latticeQuotientMap L (integralProductLattice K I) l) * F (r⁻¹ • (l : W))
  let T : Set W := {x | x ≠ 0 ∧ ‖x‖ ^ dim ≤ (r * R) ^ dim} ∩ (L : Set W)
  have hT : T.Finite := finite_nonzero_lattice_norm_power_sublevel L _
  have hmem (l : L) (hl : f l ≠ 0) : (l : W) ∈ T := by
    have hFl : F (r⁻¹ • (l : W)) ≠ 0 := (mul_ne_zero_iff.mp hl).2
    have hl0 : (l : W) ≠ 0 := by
      intro hz
      exact hFl (by rw [hz, smul_zero, hF0])
    have hnorm : ‖(l : W)‖ ≤ r * R := by
      calc
        _ = ‖r • (r⁻¹ • (l : W))‖ := by
          rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        _ = r * ‖r⁻¹ • (l : W)‖ := by
          rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ ≤ r * R := mul_le_mul_of_nonneg_left (hFR _ hFl) hr.le
    exact ⟨⟨hl0, pow_le_pow_left₀ (norm_nonneg _) hnorm dim⟩, l.property⟩
  have hsupp : (Function.support f).Finite :=
    (hT.preimage Subtype.val_injective.injOn).subset (fun l hl => hmem l hl)
  let j : Function.support f → T := fun l => ⟨l.val.val, hmem l.val l.property⟩
  have hj : Function.Injective j := by
    intro l m hlm
    exact Subtype.ext (Subtype.ext (congrArg (fun z : T => z.val) hlm))
  letI : Finite T := hT.to_subtype
  have hcard : Nat.card (Function.support f) ≤ Nat.card T :=
    Nat.card_le_card_of_injective j hj
  have hcardR : (hsupp.toFinset.card : ℝ) ≤ C * (r * R) ^ dim := by
    rw [← Nat.card_eq_card_finite_toFinset hsupp]
    have hcard' : (Nat.card (Function.support f) : ℝ) ≤ (Nat.card T : ℝ) := by
      exact_mod_cast hcard
    exact hcard'.trans (hcount _ (pow_pos (mul_pos hr hR) _))
  have hzero : ∀ l ∉ hsupp.toFinset, f l = 0 := by
    intro l hl
    by_contra hne
    exact hl (hsupp.mem_toFinset.mpr hne)
  have hfbound (l : L) : ‖f l‖ ≤ Q * SchwartzMap.seminorm ℂ 0 0 F := by
    rw [norm_mul]
    exact mul_le_mul (hw _) (SchwartzMap.norm_le_seminorm ℂ F _) (norm_nonneg _) hQ
  have hseminorm : 0 ≤ SchwartzMap.seminorm ℂ 0 0 F := apply_nonneg _ _
  have hscale : r ^ dim = N ^ 2 := traceNormScale_jacobian K N hN
  change ‖∑' l : L, w (latticeQuotientMap L (integralProductLattice K I) l) *
    F (r⁻¹ • (0 + (l : W)))‖ ≤ _
  simp only [zero_add]
  change ‖∑' l, f l‖ ≤ _
  rw [tsum_eq_sum hzero]
  calc
    _ ≤ ∑ _l ∈ hsupp.toFinset, Q * SchwartzMap.seminorm ℂ 0 0 F :=
      norm_sum_le_of_le _ (fun l _ => hfbound l)
    _ = (hsupp.toFinset.card : ℝ) * (Q * SchwartzMap.seminorm ℂ 0 0 F) := by simp
    _ ≤ (C * (r * R) ^ dim) * (Q * SchwartzMap.seminorm ℂ 0 0 F) :=
      mul_le_mul_of_nonneg_right hcardR (mul_nonneg hQ hseminorm)
    _ = (C * R ^ dim) * Q * SchwartzMap.seminorm ℂ 0 0 F * N ^ 2 := by
      rw [mul_pow, hscale]
      ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "N₀" => H + H

/-- Same literal periodic sum in both branches. The two displayed seminorms
are retained for subsequent actual small/large-radius profile estimates. -/
theorem exists_uniform_fixedDepth_weight_allScale_min_bound
    (R : ℝ) (hR : 0 < R) (A : ℕ) (hA : 2 < A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (c k : NZ)
      (a₁ a₂ : 𝓞 K ⧸ clearedSModulus K S ζ hζ N₀) (d b₁ b₂ : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (F : SchwartzMap W ℂ) (N : ℝ), 0 < N → F 0 = 0 →
      (∀ x, F x ≠ 0 → ‖x‖ ≤ R) →
      ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
        (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂) F N 0‖ ≤
      C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (SchwartzMap.seminorm ℂ 0 0 F +
          SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)) * N ^ 2 *
        min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) / N) ^ A) := by
  obtain ⟨Ct, hCt, ht⟩ := exists_productPeriodicSum_allScale_trivial_bound K R hR
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_uniform_fixedDepth_weight_poisson_bound K S Γ ζ hζ σ hS6 A hA
  refine ⟨Ct + Cp, add_pos hCt hCp, ?_⟩
  intro c k a₁ a₂ d b₁ b₂ p hpC hpJ F N hN hF0 hFR
  let qC : ℝ := Ideal.absNorm (actualFrequencyIdeal K S c)
  let qJ : ℝ := Ideal.absNorm (actualFrequencyIdeal K S k)
  let s0 : ℝ := SchwartzMap.seminorm ℂ 0 0 F
  let sA : ℝ := SchwartzMap.seminorm ℂ (Module.finrank ℚ K * A) 0 (𝓕 F)
  have hqC : 0 ≤ qC := Nat.cast_nonneg _
  have hqJ : 0 ≤ qJ := Nat.cast_nonneg _
  have hs0 : 0 ≤ s0 := apply_nonneg _ _
  have hsA : 0 ≤ sA := apply_nonneg _ _
  have hratio : 0 ≤ (qC * qJ / N) ^ A :=
    pow_nonneg (div_nonneg (mul_nonneg hqC hqJ) hN.le) _
  have hcoefP : Cp * qC * sA ≤ (Ct + Cp) * qC * (s0 + sA) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCt.le) hqC)
      (le_add_of_nonneg_left hs0) hsA (mul_nonneg (add_pos hCt hCp).le hqC)
  have hcoefT : Ct * qC * s0 ≤ (Ct + Cp) * qC * (s0 + sA) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCp.le) hqC)
      (le_add_of_nonneg_right hsA) hs0 (mul_nonneg (add_pos hCt hCp).le hqC)
  have htrivial := ht (fixedChartPeriodIdeal K S ζ hζ c k N₀)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂)
    F N qC hN hqC
    (norm_fixedChartLatticeWeight_le_absNorm K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂)
    hF0 hFR
  have hpoisson := hp c k a₁ a₂ d b₁ b₂ p hpC hpJ F N hN 0
  change ‖productPeriodicSum K (fixedChartPeriodIdeal K S ζ hζ c k N₀)
    (fixedChartLatticeWeight K S ζ hζ σ hS6 c k N₀ H a₁ a₂ d b₁ b₂) F N 0‖ ≤
    (Ct + Cp) * qC * (s0 + sA) * N ^ 2 * min 1 ((qC * qJ / N) ^ A)
  by_cases hsmall : (qC * qJ / N) ^ A ≤ 1
  · rw [min_eq_right hsmall]
    exact hpoisson.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoefP (sq_nonneg N)) hratio)
  · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
    exact htrivial.trans (mul_le_mul_of_nonneg_right hcoefT (sq_nonneg N))

end HeckeGeneral.Analysis.ActualFixedDepthAllScaleDraft
