import HeckeGeneral.Arithmetic.SIntegerCompactDenominators
import HeckeGeneral.Analysis.SUnitSchwartzIntegrable
import Mathlib.LinearAlgebra.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute summation over every nonzero S-integer on a compact orbital domain

All nonzero elements of the actual S-integer ring are retained as indices.
Compact finite-place support gives a common integral denominator, and the
active indices inject into one fixed nonzero trace integer lattice. Compact
archimedean multipliers and Schwartz decay then bound every finite sum on the
closure of the genuine fundamental domain. Absolute pointwise convergence,
summability of norm integrals and the complex sum-integral identity follow.

No prior summability, integrability, PID or choice of one ideal sector is an
input. The finite-place support is additive and may contain zero. The radial
parameter is fixed and strictly positive throughout these estimates.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical BigOperators ENNReal nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)

omit [Fintype S] in
/-- Countability is supplied by finite dimension over the countable field ℚ. -/
instance countable_nonzeroSInteger : Countable (NonzeroRingElements (S.integer K)) := by
  letI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  infer_instance

/-- The genuine family indexed by every nonzero S-integer. -/
def sIntegerSchwartzTerm (φ : SchwartzMap V ℂ)
    (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (a : N) (x : T) : ℂ :=
  sLocalTensorTestFunction K S φ ψ
    (sLocalNormSection K S r * (x : G) * sLocalNonzeroIntegerDiagonal K S a)

theorem continuous_sIntegerSchwartzTerm (φ : SchwartzMap V ℂ)
    (ψ : (Π v : S, v.val.adicCompletion K) → ℂ) (hψ : Continuous ψ)
    (r : {r : ℝ // 0 < r}) (a : N) :
    Continuous (sIntegerSchwartzTerm K S φ ψ r a) :=
  (continuous_sLocalTensorTestFunction K S φ ψ hψ).comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The whole nonzero S-integer family has uniformly bounded finite norm sums
on every compact subset of the norm-one group. No subgroup is required. -/
theorem exists_sIntegerSchwartzTerm_finite_sums_bound_on_compact
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (C₀ : Set T) (hC₀ : IsCompact C₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ C₀,
      ∀ t : Finset N, (∑ a ∈ t, ‖sIntegerSchwartzTerm K S φ ψ r a x‖) ≤ D := by
  let Q : Set (SFiniteLocalGroup K S) :=
    (fun x : T => (x : G).2) '' C₀
  have hQ : IsCompact Q :=
    hC₀.image (continuous_snd.comp continuous_subtype_val)
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_sInteger_mem_range_of_finite_support K S
      (Set.toFinite S) Q hQ ψ hψsupport
  obtain ⟨C, hC, hψbound⟩ :=
    exists_pos_norm_finiteTestFunction_le K S ψ hψ hψsupport
  let multiplier : T → Wˣ := fun x => clearedSLocalTraceMultiplier K S a ha
    (sLocalNormSection K S r * (x : G))
  have hmultiplier : Continuous multiplier :=
    (continuous_fst.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const
  let P : Set Wˣ := multiplier '' C₀
  have hP : IsCompact P :=
    hC₀.image hmultiplier
  obtain ⟨B, hB, hBbound⟩ := exists_uniform_traceUnit_inverse_bound K P hP
  let L : Submodule ℤ V := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let M : ℕ := Module.finrank ℤ L + 1
  have hM : Module.finrank ℤ L < M := Nat.lt_succ_self _
  let D : ℝ := C * (SchwartzMap.seminorm ℂ M 0 φ * B ^ M) * latticeInversePowerMass L M
  have hmass : 0 ≤ latticeInversePowerMass L M := tsum_nonneg (fun _ => by positivity)
  have hseminorm : 0 ≤ SchwartzMap.seminorm ℂ M 0 φ :=
    apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun x hx t => ?_⟩
  let p : G := sLocalNormSection K S r * (x : G)
  let b : N → ℂ := fun z => ψ (fun v : S =>
    ((p * sLocalNonzeroIntegerDiagonal K S z).2 v).val)
  let v : N → V := fun z => (traceToMixed K).symm
    ((p * sLocalNonzeroIntegerDiagonal K S z).1 : W)
  have hcleared (z : N) (hz : b z ≠ 0) :
      algebraMap (𝓞 K) K a * (nonzeroSIntegerFieldUnit K S z : K) ∈
        (algebraMap (𝓞 K) K).range := by
    apply hclear (x : G).2 (Set.mem_image_of_mem _ hx) z.val
    change ψ (fun v : S => ((p * sLocalNonzeroIntegerDiagonal K S z).2 v).val) ≠ 0 at hz
    have hfinite : (p * sLocalNonzeroIntegerDiagonal K S z).2 =
        (x : G).2 * (sLocalNonzeroIntegerDiagonal K S z).2 := by
      change (1 * (x : G).2) * (sLocalNonzeroIntegerDiagonal K S z).2 = _
      rw [one_mul]
    rw [hfinite] at hz
    change ψ (fun v : S => ((x : G).2 v).val *
      algebraMap K (v.val.adicCompletion K) (z.val : K)) ≠ 0 at hz
    exact hz
  let j : {z : N // b z ≠ 0} → NonzeroLattice L := fun z =>
    clearedUnitTraceLatticeEmbedding K a ha
      ⟨nonzeroSIntegerFieldUnit K S z.val, hcleared z.val z.property⟩
  have hj : Function.Injective j := by
    intro z w hzw
    apply Subtype.ext
    apply nonzeroSIntegerFieldUnit_injective K S
    exact congrArg (fun u : IntegralMultipleUnits K a => u.val)
      ((clearedUnitTraceLatticeEmbedding K a ha).injective hzw)
  let aW : Wˣ := Units.map (mixedEmbedding K).toMonoidHom
    (Units.mk0 (algebraMap (𝓞 K) K a) (RingOfIntegers.coe_ne_zero_iff.mpr ha))
  have hmatch : ∀ z : {z : N // b z ≠ 0},
      traceUnitMulEquiv K (multiplier x) (((j z : NonzeroLattice L) : L) : V) = v z.val := by
    intro z
    rw [show (((j z : NonzeroLattice L) : L) : V) =
      traceEmbedding K (algebraMap (𝓞 K) K a * (nonzeroSIntegerFieldUnit K S z.val : K)) from rfl]
    apply (traceToMixed K).injective
    rw [traceToMixed_traceUnitMulEquiv]
    simp only [v, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
    rw [map_mul]
    change ((p.1 * aW⁻¹ : Wˣ) : W) *
        ((aW * (sLocalNonzeroIntegerDiagonal K S z.val).1 : Wˣ) : W) =
      ((p.1 * (sLocalNonzeroIntegerDiagonal K S z.val).1 : Wˣ) : W)
    rw [← Units.val_mul]
    exact congrArg Units.val (by simp only [mul_assoc, inv_mul_cancel_left])
  have hreal := sum_norm_weighted_schwartz_le_of_support L φ
    (traceUnitMulEquiv K (multiplier x)) M hM
    (hBbound _ (Set.mem_image_of_mem _ hx)) hC.le v b
    (fun z => hψbound _) j hj hmatch t
  have hterm (z : N) : ‖sIntegerSchwartzTerm K S φ ψ r z x‖ = ‖b z * φ (v z)‖ := by
    change ‖φ (v z) * b z‖ = ‖b z * φ (v z)‖
    rw [mul_comm]
  simpa only [hterm] using hreal

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- The actual fundamental-domain closure specializes the compact-set bound. -/
theorem exists_sIntegerSchwartzTerm_finite_sums_bound
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ closure (sUnitFundamentalDomain K S Γ),
      ∀ t : Finset N, (∑ a ∈ t, ‖sIntegerSchwartzTerm K S φ ψ r a x‖) ≤ D :=
  exists_sIntegerSchwartzTerm_finite_sums_bound_on_compact K S φ ψ hψ hψsupport r
    (closure (sUnitFundamentalDomain K S Γ))
    (isCompact_closure_sUnitFundamentalDomain K S Γ)

/-- Absolute convergence is obtained from the actual finite-sum majorant. -/
theorem summable_norm_sIntegerSchwartzTerm
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (x : T)
    (hx : x ∈ closure (sUnitFundamentalDomain K S Γ)) :
    Summable (fun a : N => ‖sIntegerSchwartzTerm K S φ ψ r a x‖) := by
  obtain ⟨D, _hD, hbound⟩ :=
    exists_sIntegerSchwartzTerm_finite_sums_bound K S Γ φ ψ hψ hψsupport r
  exact summable_of_sum_le (fun a => norm_nonneg _) (hbound x hx)

theorem summable_sIntegerSchwartzTerm
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (x : T)
    (hx : x ∈ closure (sUnitFundamentalDomain K S Γ)) :
    Summable (fun a : N => sIntegerSchwartzTerm K S φ ψ r a x) :=
  (summable_norm_sIntegerSchwartzTerm K S Γ φ ψ hψ hψsupport r x hx).of_norm

/-- Tonelli gives a finite total of the actual extended-norm integrals.
This is the absolute sum-integral input, proved rather than assumed. -/
theorem tsum_lintegral_enorm_sIntegerSchwartzTerm_lt_top
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    (∑' a : N, ∫⁻ x in sUnitFundamentalDomain K S Γ,
      ‖sIntegerSchwartzTerm K S φ ψ r a x‖ₑ ∂sUnitHaarMeasure K S) < ∞ := by
  obtain ⟨D, _hD, hbound⟩ :=
    exists_sIntegerSchwartzTerm_finite_sums_bound K S Γ φ ψ hψ hψsupport r
  rw [← lintegral_tsum (fun a =>
    (continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).aestronglyMeasurable.enorm)]
  calc
    (∫⁻ x in sUnitFundamentalDomain K S Γ,
      ∑' a : N, ‖sIntegerSchwartzTerm K S φ ψ r a x‖ₑ ∂sUnitHaarMeasure K S) ≤
        ∫⁻ _ in sUnitFundamentalDomain K S Γ, ENNReal.ofReal D ∂sUnitHaarMeasure K S := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sUnitFundamentalDomain K S Γ)] with x hx
      apply ENNReal.summable.tsum_le_of_sum_le
      intro t
      have h := ENNReal.ofReal_le_ofReal (hbound x (subset_closure hx) t)
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ha => norm_nonneg _)] at h
      simpa only [ofReal_norm] using h
    _ = ENNReal.ofReal D * sUnitHaarCovolume K S Γ := by
      rw [setLIntegral_const]
      rfl
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sUnitHaarCovolume_lt_top K S Γ)

/-- Every term is integrable on the actual fundamental domain. -/
theorem integrable_sIntegerSchwartzTerm_on_domain
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (a : N) :
    Integrable (sIntegerSchwartzTerm K S φ ψ r a)
      ((sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)) := by
  refine ⟨(continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).aestronglyMeasurable,
    hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact (ENNReal.le_tsum (f := fun b : N =>
    ∫⁻ x in sUnitFundamentalDomain K S Γ,
      ‖sIntegerSchwartzTerm K S φ ψ r b x‖ₑ ∂sUnitHaarMeasure K S) a).trans_lt
    (tsum_lintegral_enorm_sIntegerSchwartzTerm_lt_top K S Γ φ ψ hψ hψsupport r)

/-- The real norm integrals over every ideal sector form a summable family. -/
theorem summable_integral_norm_sIntegerSchwartzTerm_on_domain
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun a : N => ∫ x in sUnitFundamentalDomain K S Γ,
      ‖sIntegerSchwartzTerm K S φ ψ r a x‖ ∂sUnitHaarMeasure K S) := by
  have h := ENNReal.summable_toReal
    (tsum_lintegral_enorm_sIntegerSchwartzTerm_lt_top K S Γ φ ψ hψ hψsupport r).ne
  exact h.congr fun a =>
    (integral_norm_eq_lintegral_enorm
      (continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).aestronglyMeasurable).symm

/-- The complex sum over all nonzero S-integers commutes with domain integration. -/
theorem integral_tsum_sIntegerSchwartzTerm_on_domain
    (φ : SchwartzMap V ℂ) (ψ : (Π v : S, v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) :
    (∫ x in sUnitFundamentalDomain K S Γ,
      (∑' a : N, sIntegerSchwartzTerm K S φ ψ r a x) ∂sUnitHaarMeasure K S) =
      ∑' a : N, ∫ x in sUnitFundamentalDomain K S Γ,
        sIntegerSchwartzTerm K S φ ψ r a x ∂sUnitHaarMeasure K S := by
  apply integral_tsum
  · intro a
    exact (continuous_sIntegerSchwartzTerm K S φ ψ hψ r a).aestronglyMeasurable
  · exact (tsum_lintegral_enorm_sIntegerSchwartzTerm_lt_top K S Γ φ ψ hψ hψsupport r).ne

end HeckeGeneral.Analysis
