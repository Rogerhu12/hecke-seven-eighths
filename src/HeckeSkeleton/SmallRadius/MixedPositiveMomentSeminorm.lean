import HeckeSkeleton.SmallRadius.SmallPositiveMomentSeminorm
import HeckeGeneral.Arithmetic.IdealTraceLattice
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.MeasureTheory.Integral.Pi

/-!
Arbitrary mixed Schwartz inputs, not tensor inputs.
The input is pulled back through the actual traceToMixed equivalence. A
product-coordinate decay envelope is dominated by a finite family of the
original trace-space seminorms, chosen before the input. Its positive-small
Mellin additive-density moment is genuinely integrable at every coordinate
hyperplane, including the complex density exponent 2*sigma-2.

The integral is over the literal product of the real and complex additive
Lebesgue measures. This source does not identify that measure with trace
Euclidean volume or multiplicative Haar without their fixed Jacobian and
Haar scalars. Values of real rpow at zero are totalized; a later Haar-density
transport must use the null coordinate-hyperplane bridge.
-/

noncomputable section

namespace HeckeGeneral.Analysis.MixedPositiveMomentDraft

open NumberField NumberField.InfinitePlace HeckeGeneral.Arithmetic MeasureTheory
open SmallPositiveArchimedeanMomentDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

abbrev RealCoord := {v : InfinitePlace K // v.IsReal}
abbrev ComplexCoord := {v : InfinitePlace K // v.IsComplex}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

/-- The actual coordinate Lebesgue product, before any trace Jacobian. -/
def mixedProductLebesgue : Measure W :=
  (Measure.pi (fun _ : RealCoord K => (volume : Measure ℝ))).prod
    (Measure.pi (fun _ : ComplexCoord K => (volume : Measure ℂ)))

theorem mixedProductLebesgue_eq_volume : mixedProductLebesgue K = volume := rfl

def mixedDecayOrder : ℕ := 3 * (Fintype.card (RealCoord K) + Fintype.card (ComplexCoord K))

def mixedArchDecay (y : W) : ℝ :=
  (∏ v : RealCoord K, (1 + ‖y.1 v‖) ^ (-3 : ℝ)) *
    ∏ v : ComplexCoord K, (1 + ‖y.2 v‖) ^ (-3 : ℝ)

/-- Additive density corresponding away from the coordinate hyperplanes
to product multiplicative modulus raised to sigma. -/
def mixedPositiveDensity (σ : ℝ) (y : W) : ℝ :=
  (∏ v : RealCoord K, ‖y.1 v‖ ^ (σ - 1)) *
    ∏ v : ComplexCoord K, ‖y.2 v‖ ^ (2 * σ - 2)

def mixedPositiveEnvelope (σ : ℝ) (y : W) : ℝ :=
  mixedArchDecay K y * mixedPositiveDensity K σ y

theorem mixedArchDecay_nonneg (y : W) : 0 ≤ mixedArchDecay K y := by
  unfold mixedArchDecay
  positivity

theorem mixedPositiveDensity_nonneg (σ : ℝ) (y : W) :
    0 ≤ mixedPositiveDensity K σ y := by
  unfold mixedPositiveDensity
  positivity

theorem mixedPositiveEnvelope_nonneg (σ : ℝ) (y : W) :
    0 ≤ mixedPositiveEnvelope K σ y :=
  mul_nonneg (mixedArchDecay_nonneg K y) (mixedPositiveDensity_nonneg K σ y)

/-- The product envelope is integrable independently of the Schwartz input. -/
theorem integrable_mixedPositiveEnvelope (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Integrable (mixedPositiveEnvelope K σ) (mixedProductLebesgue K) := by
  let f : ℝ → ℝ := fun x => (1 + ‖x‖) ^ (-3 : ℝ) * ‖x‖ ^ (σ - 1)
  let g : ℂ → ℝ := fun z => (1 + ‖z‖) ^ (-3 : ℝ) * ‖z‖ ^ (2 * σ - 2)
  have hf : Integrable f volume := by
    simpa only [f, Module.finrank_self, Nat.cast_one, one_mul, Nat.cast_ofNat] using
      integrable_small_positive_moment_envelope (E := ℝ) (by simp) 3 (by norm_num)
        σ hσ hσ1
  have hg : Integrable g volume := by
    simpa only [g, Complex.finrank_real_complex, Nat.cast_ofNat, mul_sub, mul_one] using
      integrable_small_positive_moment_envelope (E := ℂ)
        (by norm_num [Complex.finrank_real_complex]) 3
        (by norm_num [Complex.finrank_real_complex]) σ hσ hσ1
  have hreal : Integrable (fun x : RealCoord K → ℝ => ∏ v, f (x v))
      (Measure.pi (fun _ : RealCoord K => (volume : Measure ℝ))) :=
    Integrable.fintype_prod_dep (fun _ => hf)
  have hcomplex : Integrable (fun z : ComplexCoord K → ℂ => ∏ v, g (z v))
      (Measure.pi (fun _ : ComplexCoord K => (volume : Measure ℂ))) :=
    Integrable.fintype_prod_dep (fun _ => hg)
  apply (hreal.mul_prod hcomplex).congr
  exact Filter.Eventually.of_forall fun y => by
    simp only [f, g, mixedPositiveEnvelope, mixedArchDecay, mixedPositiveDensity,
      Finset.prod_mul_distrib]
    ring

/-- The decay product is controlled for an arbitrary mixed Schwartz input
by order 3 times the number of infinite places. -/
theorem norm_le_mixedArchDecay (φ : SchwartzMap W ℂ) (y : W) :
    ‖φ y‖ ≤
      (2 ^ mixedDecayOrder K * (Finset.Iic (mixedDecayOrder K, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ) * mixedArchDecay K y := by
  let D : ℝ := (∏ v : RealCoord K, (1 + ‖y.1 v‖) ^ 3) *
    ∏ v : ComplexCoord K, (1 + ‖y.2 v‖) ^ 3
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hreal : (∏ v : RealCoord K, (1 + ‖y.1 v‖) ^ 3) ≤
      (1 + ‖y‖) ^ (3 * Fintype.card (RealCoord K)) := by
    calc
      _ ≤ ∏ _v : RealCoord K, (1 + ‖y‖) ^ 3 := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro v _
        exact pow_le_pow_left₀ (by positivity)
          (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
            ((norm_le_pi_norm y.1 v).trans (norm_fst_le y))) 3
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hcomplex : (∏ v : ComplexCoord K, (1 + ‖y.2 v‖) ^ 3) ≤
      (1 + ‖y‖) ^ (3 * Fintype.card (ComplexCoord K)) := by
    calc
      _ ≤ ∏ _v : ComplexCoord K, (1 + ‖y‖) ^ 3 := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro v _
        exact pow_le_pow_left₀ (by positivity)
          (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
            ((norm_le_pi_norm y.2 v).trans (norm_snd_le y))) 3
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hD : D ≤ (1 + ‖y‖) ^ mixedDecayOrder K := by
    calc
      _ ≤ (1 + ‖y‖) ^ (3 * Fintype.card (RealCoord K)) *
          (1 + ‖y‖) ^ (3 * Fintype.card (ComplexCoord K)) :=
        mul_le_mul hreal hcomplex (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; simp only [mixedDecayOrder, Nat.mul_add]
  have hφ : ‖φ y‖ * D ≤
      2 ^ mixedDecayOrder K * (Finset.Iic (mixedDecayOrder K, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ := by
    calc
      _ ≤ ‖φ y‖ * (1 + ‖y‖) ^ mixedDecayOrder K :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ ≤ _ := by
        simpa only [norm_iteratedFDeriv_zero, mul_comm] using
          (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
            (m := (mixedDecayOrder K, 0)) (k := mixedDecayOrder K) (n := 0)
            le_rfl le_rfl φ y)
  have hdecay : mixedArchDecay K y = D⁻¹ := by
    have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ (-3 : ℝ) = (x ^ (3 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hx, Real.rpow_ofNat]
    simp only [mixedArchDecay, D, mul_inv]
    congr 1
    · rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro v _
      exact hpow _ (by positivity)
    · rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro v _
      exact hpow _ (by positivity)
  rw [hdecay, ← div_eq_mul_inv]
  exact (le_div_iff₀ hDpos).mpr hφ

/-- Uniform majorant for arbitrary trace-space phi. The actual linear
coordinate transport is retained, and the original seminorms precede phi.
(The transport `T` and the seminorm `pW` are introduced as opaque variables
with their defining properties; keeping them let-bound makes elaboration
exceed the default heartbeat budget.) -/
theorem exists_trace_mixed_product_majorant :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ, ∀ y : W,
      ‖φ ((traceToMixed K).symm y)‖ ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * mixedArchDecay K y := by
  have hpV : WithSeminorms (schwartzSeminormFamily ℝ V ℂ) :=
    schwartz_withSeminorms ℝ V ℂ
  have hpW : WithSeminorms (schwartzSeminormFamily ℝ W ℂ) :=
    schwartz_withSeminorms ℝ W ℂ
  obtain ⟨T, hT⟩ : ∃ T : SchwartzMap V ℂ →L[ℝ] SchwartzMap W ℂ,
      ∀ (φ : SchwartzMap V ℂ) (y : W), T φ y = φ ((traceToMixed K).symm y) :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (traceToMixed K).symm,
      fun _ _ => rfl⟩
  obtain ⟨pW, hpWdef⟩ : ∃ pW : Seminorm ℝ (SchwartzMap W ℂ),
      pW = (Finset.Iic (mixedDecayOrder K, 0)).sup (schwartzSeminormFamily ℝ W ℂ) :=
    ⟨_, rfl⟩
  have hpWcont : Continuous pW := by
    rw [hpWdef]
    exact Seminorm.continuous_finsetSup (fun m _ => hpW.continuous_seminorm m)
  have hq : Continuous (pW.comp T.toLinearMap) := hpWcont.comp T.continuous
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous hpV (pW.comp T.toLinearMap) hq
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hC
  refine ⟨s, 2 ^ mixedDecayOrder K * (C : ℝ), by positivity, fun φ y => ?_⟩
  have hbound : pW (T φ) ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    have h := Seminorm.le_def.mp hb φ
    simp only [Seminorm.comp_apply, _root_.smul_apply, NNReal.smul_def, smul_eq_mul,
      ContinuousLinearMap.coe_coe] at h
    exact h
  have hmajor := norm_le_mixedArchDecay K (T φ) y
  have hsup : (Finset.Iic (mixedDecayOrder K, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (T φ) = pW (T φ) := by
    rw [hpWdef]
    rfl
  rw [hsup, hT φ y] at hmajor
  calc
    _ ≤ _ := hmajor
    _ ≤ (2 ^ mixedDecayOrder K * ((C : ℝ) *
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ)) * mixedArchDecay K y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by positivity))
        (mixedArchDecay_nonneg K y)
    _ = _ := by ring

/-- The true arbitrary-input weighted L1 statement, with one fixed finite
original seminorm family and positive constant chosen before phi. -/
theorem exists_mixed_positive_moment_seminorm_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap V ℂ,
      Integrable (fun y : W => ‖φ ((traceToMixed K).symm y)‖ * mixedPositiveDensity K σ y)
        (mixedProductLebesgue K) ∧
      (∫ y : W, ‖φ ((traceToMixed K).symm y)‖ * mixedPositiveDensity K σ y
        ∂mixedProductLebesgue K) ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  obtain ⟨s, A, hA, hmajor⟩ := exists_trace_mixed_product_majorant K
  have henv := integrable_mixedPositiveEnvelope K σ hσ hσ1
  have hI : 0 ≤ ∫ y, mixedPositiveEnvelope K σ y ∂mixedProductLebesgue K :=
    integral_nonneg (mixedPositiveEnvelope_nonneg K σ)
  refine ⟨s, A * ((∫ y, mixedPositiveEnvelope K σ y ∂mixedProductLebesgue K) + 1),
    by positivity, ?_⟩
  intro φ
  let B : ℝ := A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpoint (y : W) :
      ‖φ ((traceToMixed K).symm y)‖ * mixedPositiveDensity K σ y ≤
        B * mixedPositiveEnvelope K σ y := by
    calc
      _ ≤ (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * mixedArchDecay K y) *
          mixedPositiveDensity K σ y :=
        mul_le_mul_of_nonneg_right (hmajor φ y) (mixedPositiveDensity_nonneg K σ y)
      _ = _ := by dsimp only [B, mixedPositiveEnvelope]; ring
  have hmeas : AEStronglyMeasurable
      (fun y : W => ‖φ ((traceToMixed K).symm y)‖ * mixedPositiveDensity K σ y)
      (mixedProductLebesgue K) := by
    apply Measurable.aestronglyMeasurable
    unfold mixedPositiveDensity
    fun_prop
  have hint : Integrable
      (fun y : W => ‖φ ((traceToMixed K).symm y)‖ * mixedPositiveDensity K σ y)
      (mixedProductLebesgue K) := by
    apply (henv.const_mul B).mono' hmeas
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (mixedPositiveDensity_nonneg K σ y))]
      exact hpoint y
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ y : W, B * mixedPositiveEnvelope K σ y ∂mixedProductLebesgue K :=
      integral_mono hint (henv.const_mul B) hpoint
    _ = B * ∫ y : W, mixedPositiveEnvelope K σ y ∂mixedProductLebesgue K :=
      integral_const_mul _ _
    _ ≤ B * ((∫ y : W, mixedPositiveEnvelope K σ y ∂mixedProductLebesgue K) + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB
    _ = _ := by dsimp only [B]; ring

end HeckeGeneral.Analysis.MixedPositiveMomentDraft
