import HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallPowerCount
import HeckeSkeleton.Moments.MOM_INV_STEP.SparseFiniteSum
import HeckeGeneral.Analysis.SUnitSchwartzDecay

/-!
# Arbitrarily small radial loss for the actual S-unit orbital profile

Compact finite-place support, the true product formula, the ordinary-unit
log lattice, and a finite shell sum supply this bound. The seminorm and
constant are selected before both the original Schwartz test and radius.
Every element of the given finite-index S-unit subgroup is retained.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallRadius

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis MeasureTheory
open SUnitHeightCounting SUnitSmallPowerCount SparseFiniteSum
open scoped Classical BigOperators ENNReal nonZeroDivisors

theorem coordinateScale_cost_le (d : ℕ) (hd : 0 < d) (ε δ : ℝ)
    (hδε : δ ≤ ε * d) (r : {r : ℝ // 0 < r}) (hr : r.val ≤ 1) :
    (r.val ^ ((d : ℝ)⁻¹)) ^ (-δ) ≤ r.val ^ (-ε) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale : (d : ℝ)⁻¹ * δ ≤ ε := by
    calc
      _ ≤ (d : ℝ)⁻¹ * (ε * d) := mul_le_mul_of_nonneg_left hδε (inv_nonneg.mpr hdR.le)
      _ = ε := by field_simp [hdR.ne']
  rw [← Real.rpow_mul r.property.le]
  apply Real.rpow_le_rpow_of_exponent_ge r.property hr
  nlinarith

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S

/-- The actual finite subgroup orbit has an arbitrarily small radial loss.
This is proved before taking any infinite orbital sum or Haar integral. -/
theorem exists_sLocalSchwartzSlice_smallRadius_finite_gamma_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
      ∀ x ∈ closure (sUnitFundamentalDomain K S Γ), ∀ t : Finset Γ,
        (∑ u ∈ t, ‖sLocalSchwartzSlice K S φ ψ r
          (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖) ≤
          D * (Finset.Iic (3, 0)).sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-ε) := by
  let δ : ℝ := min (ε * Module.finrank ℚ K) 1
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hδ : 0 < δ := lt_min (mul_pos hε hd) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε * Module.finrank ℚ K := min_le_left _ _
  obtain ⟨F, hF, hfinite⟩ := exists_finiteNorm_bound_on_radial_domain K S Γ ψ hψsupport
  obtain ⟨C, hC, hcount⟩ := exists_trace_height_small_power_count K S F hF δ hδ
  obtain ⟨Cψ, hCψ, hψbound⟩ := exists_pos_norm_finiteTestFunction_le K S ψ hψ hψsupport
  let P : Set Wˣ := (fun x : T => (x : G).1) '' closure (sUnitFundamentalDomain K S Γ)
  have hP : IsCompact P := (isCompact_closure_sUnitFundamentalDomain K S Γ).image
    (continuous_fst.comp continuous_subtype_val)
  obtain ⟨B₀, hB₀, hBbound⟩ := exists_uniform_traceUnit_inverse_bound K P hP
  let B : ℝ := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  let D : ℝ := 2 * C * Cψ * B ^ 3 * 8 * inverseSquareMass
  have hmass := inverseSquareMass_nonneg
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun φ r hr x hx t => ?_⟩
  let α : ℝ := r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)
  have hα : 0 < α := Real.rpow_pos_of_pos r.property _
  have hα1 : α ≤ 1 := Real.rpow_le_one r.property.le hr (inv_nonneg.mpr hd.le)
  let p : G := sLocalNormSection K S r * (x : G)
  let e : V ≃L[ℝ] V := traceUnitMulEquiv K (x : G).1
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ B :=
    (hBbound _ (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)
  let height : Γ → ℝ := fun u => ‖traceEmbedding K (((u : S.unit K) : Kˣ) : K)‖
  let b : Γ → ℂ := fun u => ψ (fun v : S => ((p * sLocalDiagonal K S (u : S.unit K)).2 v).val)
  let z : Γ → V := fun u => (traceToMixed K).symm
    ((p * sLocalDiagonal K S (u : S.unit K)).1 : W)
  let f : Γ → ℝ := fun u => ‖sLocalTensorTestFunction K S φ ψ
    (p * sLocalDiagonal K S (u : S.unit K))‖
  have hz (u : Γ) : z u = α • e (traceEmbedding K (((u : S.unit K) : Kˣ) : K)) := by
    have hm : traceUnitMulEquiv K p.1 (traceEmbedding K (((u : S.unit K) : Kˣ) : K)) = z u := by
      apply (traceToMixed K).injective
      rw [traceToMixed_traceUnitMulEquiv]
      simp only [traceEmbedding, z, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    change traceUnitMulEquiv K ((sLocalNormSection K S r).1 * (x : G).1)
      (traceEmbedding K (((u : S.unit K) : Kˣ) : K)) = z u at hm
    rw [traceUnitMulEquiv_normSection_apply] at hm
    exact hm.symm
  have hf (u : Γ) : f u = ‖φ (z u)‖ * ‖b u‖ := by
    exact norm_mul _ _
  let a := t.filter (fun u => b u ≠ 0)
  let Q : ℝ := Cψ * (B ^ 3 * (8 * (Finset.Iic (3, 0)).sup
    (schwartzSeminormFamily ℝ V ℂ) φ))
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hpoint (u : Γ) (_hu : u ∈ a) : (1 + α * height u) ^ 3 * f u ≤ Q := by
    have hp := schwartz_dilated_equiv_weighted_bound φ e B α hB hinv hα
      (traceEmbedding K (((u : S.unit K) : Kˣ) : K))
    rw [← hz u] at hp
    rw [hf]
    calc
      _ = ((1 + α * height u) ^ 3 * ‖φ (z u)‖) * ‖b u‖ := by ring
      _ ≤ (B ^ 3 * (8 * (Finset.Iic (3, 0)).sup
          (schwartzSeminormFamily ℝ V ℂ) φ)) * Cψ :=
        mul_le_mul hp (hψbound _) (norm_nonneg _) (by positivity)
      _ = Q := by dsimp only [Q]; ring
  have hcount' (H : ℝ) (hH : 1 ≤ H) (q : Finset Γ) (hqa : q ⊆ a)
      (hq : ∀ u ∈ q, height u ≤ H) : (q.card : ℝ) ≤ C * H ^ δ := by
    have hb := hcount H hH (q.image (fun u : Γ => (u : S.unit K))) (by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact hq v hv) (by
      intro u hu v
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      exact hfinite r x hx (w : S.unit K) (Finset.mem_filter.mp (hqa hw)).2 v)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective] at hb
  have hsum := finite_sum_le a height f C Q δ α hC hQ hδ hδ1 hα hα1
    (fun u _ => norm_nonneg _) (fun u _ => norm_nonneg _) hpoint hcount'
  have hterm (u : Γ) : ‖sLocalSchwartzSlice K S φ ψ r
      (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖ = f u := by
    congr 1
    unfold sLocalSchwartzSlice
    congr 1
    change sLocalNormSection K S r * (sLocalDiagonal K S (u : S.unit K) * (x : G)) =
      (sLocalNormSection K S r * (x : G)) * sLocalDiagonal K S (u : S.unit K)
    ac_rfl
  have hfilter : ∑ u ∈ t, f u = ∑ u ∈ a, f u := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnot
    have hb : b u = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hu, hne⟩)
    rw [hf, hb, norm_zero, mul_zero]
  have hcost : α ^ (-δ) ≤ r.val ^ (-ε) :=
    coordinateScale_cost_le (Module.finrank ℚ K) Module.finrank_pos ε δ hδε r hr
  calc
    _ = ∑ u ∈ a, f u := by simp only [hterm]; exact hfilter
    _ ≤ 2 * C * Q * α ^ (-δ) * inverseSquareMass := hsum
    _ ≤ 2 * C * Q * r.val ^ (-ε) * inverseSquareMass :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcost (by positivity)) hmass
    _ = _ := by dsimp only [D, Q]; ring

include Γ in
/-- Haar unfolding preserves the actual covolume and the arbitrary small
power. Integrability is already proved for each positive radius. -/
theorem exists_sLocalSchwartzSlice_smallRadius_integral_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
        (∫ x : T, ‖sLocalSchwartzSlice K S φ ψ r x‖ ∂sUnitHaarMeasure K S) ≤
          D * (Finset.Iic (3, 0)).sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-ε) := by
  obtain ⟨D, hD, hbound⟩ := exists_sLocalSchwartzSlice_smallRadius_finite_gamma_bound
    K S Γ ψ hψ hψsupport ε hε
  refine ⟨D * (sUnitHaarCovolume K S Γ).toReal, mul_nonneg hD ENNReal.toReal_nonneg,
    fun φ r hr => ?_⟩
  let C : ℝ := D * (Finset.Iic (3, 0)).sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-ε)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hD (apply_nonneg _ _))
      (Real.rpow_nonneg r.property.le _)
  have horbit : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (sLocalNormOneGamma K S Γ).op,
        ‖sLocalSchwartzSlice K S φ ψ r (g • x)‖ₑ) ≤ ENNReal.ofReal C := by
    intro x hx
    apply sUnitOrbit_enorm_tsum_le_of_finite_sums K S Γ x
    exact sLocalOrbit_enorm_sum_le_of_gamma_bound K S Γ
      (sLocalSchwartzSlice K S φ ψ r) x (hbound φ r hr x (subset_closure hx))
  have h := integral_norm_sUnitHaar_le_of_orbit_bound K S Γ
    (continuous_sLocalSchwartzSlice K S φ ψ hψ r).aestronglyMeasurable
    ENNReal.ofReal_lt_top horbit
  rw [ENNReal.toReal_ofReal hC] at h
  exact h.trans_eq (by dsimp only [C]; ring)

include Γ in
/-- The genuine orbital profile has arbitrarily small loss at zero.
There is no new analytic input or individually chosen radius constant. -/
theorem exists_sLocalSchwartzProfile_smallRadius_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
        ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r‖ ≤
          D * (Finset.Iic (3, 0)).sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-ε) := by
  obtain ⟨D, hD, hb⟩ := exists_sLocalSchwartzSlice_smallRadius_integral_bound
    K S Γ ψ hψ hψsupport ε hε
  exact ⟨D, hD, fun φ r hr => (norm_integral_le_integral_norm _).trans (hb φ r hr)⟩

include Γ in
/-- Combining the new small-radius count with the existing genuine
large-radius Schwartz tail gives one bound for all positive radii.
The finite family of original-test seminorms is fixed in advance. -/
theorem exists_sLocalSchwartzProfile_smallPower_global_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r},
        ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r‖ ≤
          D * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * r.val ^ (-ε) := by
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let M : ℕ := Module.finrank ℤ L + ⌈(Module.finrank ℚ K : ℝ) * ε⌉₊ + 1
  have hM : Module.finrank ℤ L < M := by dsimp only [M]; omega
  have hOrder : (Module.finrank ℚ K : ℝ) * ε ≤ M := by
    have hc := Nat.le_ceil ((Module.finrank ℚ K : ℝ) * ε)
    have hm : ⌈(Module.finrank ℚ K : ℝ) * ε⌉₊ ≤ M := by dsimp only [M]; omega
    exact hc.trans (by exact_mod_cast hm)
  obtain ⟨D₀, hD₀, hsmall⟩ := exists_sLocalSchwartzProfile_smallRadius_bound
    K S Γ ψ hψ hψsupport ε hε
  obtain ⟨D₁, hD₁, hlarge⟩ := exists_sLocalSchwartzProfile_power_decay
    K S Γ ψ hψ hψsupport ε M hM hOrder
  let s : Finset (ℕ × ℕ) := Finset.Iic (3, 0) ∪ {(M, 0)}
  have hsmallSup (φ : SchwartzMap V ℂ) :
      (Finset.Iic (3, 0)).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
  have hlargeSup (φ : SchwartzMap V ℂ) :
      SchwartzMap.seminorm ℂ M 0 φ ≤ s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    simpa only [SchwartzMap.schwartzSeminormFamily_apply, SchwartzMap.seminorm_apply] using
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ V ℂ) (x := φ)
        (show (M, 0) ∈ s by simp only [s, Finset.mem_union,
          Finset.mem_singleton, or_true]))
  refine ⟨s, D₀ + D₁, add_nonneg hD₀ hD₁, fun φ r => ?_⟩
  by_cases hr : r.val ≤ 1
  · exact (hsmall φ r hr).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (by linarith : D₀ ≤ D₀ + D₁) (hsmallSup φ)
          (apply_nonneg _ _) (add_nonneg hD₀ hD₁))
        (Real.rpow_nonneg r.property.le _))
  · exact (hlarge φ r (le_of_not_ge hr)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (by linarith : D₁ ≤ D₀ + D₁) (hlargeSup φ)
          (apply_nonneg _ _) (add_nonneg hD₀ hD₁))
        (Real.rpow_nonneg r.property.le _))

end HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallRadius

end
