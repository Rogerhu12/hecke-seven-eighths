import HeckeGeneral.Analysis.SUnitSchwartzIntegrable
import HeckeGeneral.Analysis.TraceRadialScaling
import HeckeGeneral.Analysis.SUnitOrbitalIntegral

/-!
# Radially uniform decay of actual tensor Schwartz orbital profiles

The denominator selected by the finite support is independent of the radial
parameter. Removing the scalar radial section leaves one compact set of
archimedean multipliers. Its inverse operator bound, together with the
actual trace lattice, gives a finite-sum majorant uniform on the fundamental
domain. Haar unfolding retains its finite covolume in the orbital bound.
The constants are independent of the archimedean test function and the
positive radius; the test function enters through an explicit seminorm.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical BigOperators ENNReal nonZeroDivisors

/-- Converting coordinate scale to norm scale retains the degree in the
required Schwartz order. -/
theorem normSection_inverse_pow_le_rpow (d M : ℕ) (hd : 0 < d)
    (A ρ : ℝ) (hρ : 1 ≤ ρ) (hOrder : (d : ℝ) * A ≤ M) :
    ((ρ ^ (d : ℝ)⁻¹)⁻¹) ^ M ≤ ρ ^ (-A) := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hexp : -(d : ℝ)⁻¹ * M ≤ -A := by
    have h := mul_le_mul_of_nonneg_left hOrder (inv_nonneg.mpr hdpos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hdpos.ne', one_mul] at h
    linarith
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hρpos.le,
    ← Real.rpow_neg hρpos.le]
  apply Real.rpow_le_rpow_of_exponent_le hρ
  simpa only [neg_mul] using hexp

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- The same constant bounds all finite orbital sums at every positive radius.
The rate is the degree-th-root scale, before conversion to a prescribed power. -/
theorem exists_sLocalSchwartzSlice_radial_finite_gamma_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, ∀ x ∈ closure (sUnitFundamentalDomain K S Γ),
      ∀ t : Finset Γ,
        (∑ u ∈ t, ‖sLocalSchwartzSlice K S φ ψ r
          (sLocalNormOneDiagonal K S (u : S.unit K) * x)‖) ≤
          D * SchwartzMap.seminorm ℂ M 0 φ *
            ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹) ^ M := by
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_sUnit_mem_range_on_radial_domain K S Γ ψ hψsupport
  obtain ⟨C, hC, hψbound⟩ :=
    exists_pos_norm_finiteTestFunction_le K S ψ hψ hψsupport
  let multiplier : T → Wˣ := fun x => clearedSLocalTraceMultiplier K S a ha (x : G)
  have hmultiplier : Continuous multiplier :=
    (continuous_fst.comp continuous_subtype_val).mul continuous_const
  let P : Set Wˣ := multiplier '' closure (sUnitFundamentalDomain K S Γ)
  have hP : IsCompact P :=
    (isCompact_closure_sUnitFundamentalDomain K S Γ).image hmultiplier
  obtain ⟨B, hB, hBbound⟩ := exists_uniform_traceUnit_inverse_bound K P hP
  let D : ℝ := C * B ^ M * latticeInversePowerMass L M
  have hmass : 0 ≤ latticeInversePowerMass L M := tsum_nonneg (fun _ => by positivity)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, fun φ r x hx t => ?_⟩
  let α : ℝ := r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)
  have hα : 0 < α := Real.rpow_pos_of_pos r.property _
  let p : G := sLocalNormSection K S r * (x : G)
  have hmult : clearedSLocalTraceMultiplier K S a ha p =
      realScaleMixedUnit K α hα.ne' * multiplier x := by
    change ((realScaleMixedUnit K α hα.ne' * (x : G).1) * _) =
      realScaleMixedUnit K α hα.ne' * ((x : G).1 * _)
    exact mul_assoc _ _ _
  have hBscaled :
      ‖(traceUnitMulEquiv K (clearedSLocalTraceMultiplier K S a ha p)).symm.toContinuousLinearMap‖ ≤
        α⁻¹ * B := by
    rw [hmult, norm_traceUnitMulEquiv_realScale_inverseCLM K α hα]
    exact mul_le_mul_of_nonneg_left (hBbound _ (Set.mem_image_of_mem _ hx))
      (inv_nonneg.mpr hα.le)
  have hfinite := sum_norm_sLocalTensorTestFunction_sUnit_le K S Γ φ ψ a ha p M hM
    hBscaled hC.le hψbound (fun u => hclear r x hx (u : S.unit K)) t
  have hterm (u : Γ) : sLocalSchwartzSlice K S φ ψ r
      (sLocalNormOneDiagonal K S (u : S.unit K) * x) =
      sLocalTensorTestFunction K S φ ψ (p * sLocalDiagonal K S (u : S.unit K)) := by
    unfold sLocalSchwartzSlice
    congr 1
    change sLocalNormSection K S r *
      (sLocalDiagonal K S (u : S.unit K) * (x : G)) = _
    dsimp only [p]
    ac_rfl
  calc
    _ = ∑ u ∈ t, ‖sLocalTensorTestFunction K S φ ψ
        (p * sLocalDiagonal K S (u : S.unit K))‖ := by simp only [hterm]
    _ ≤ C * (SchwartzMap.seminorm ℂ M 0 φ * (α⁻¹ * B) ^ M) *
        latticeInversePowerMass L M := hfinite
    _ = _ := by dsimp only [D, α]; rw [mul_pow]; ring

include Γ in
/-- Integrating the actual majorant preserves every degree and covolume factor.
No assumed integrability or orbit-summability field is used. -/
theorem exists_sLocalSchwartzSlice_radial_integral_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ, ∀ r : {r : ℝ // 0 < r},
      (∫ x : T, ‖sLocalSchwartzSlice K S φ ψ r x‖ ∂sUnitHaarMeasure K S) ≤
        D * SchwartzMap.seminorm ℂ M 0 φ *
          ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹) ^ M := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_sLocalSchwartzSlice_radial_finite_gamma_bound K S Γ ψ hψ hψsupport M hM
  refine ⟨D * (sUnitHaarCovolume K S Γ).toReal,
    mul_nonneg hD ENNReal.toReal_nonneg, fun φ r => ?_⟩
  let C : ℝ := D * SchwartzMap.seminorm ℂ M 0 φ *
    ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹) ^ M
  have hseminorm : 0 ≤ SchwartzMap.seminorm ℂ M 0 φ :=
    apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ
  have hC : 0 ≤ C := by
    exact mul_nonneg (mul_nonneg hD hseminorm)
      (pow_nonneg (inv_nonneg.mpr (Real.rpow_nonneg r.property.le _)) M)
  have horbit : ∀ x ∈ sUnitFundamentalDomain K S Γ,
      (∑' g : (sLocalNormOneGamma K S Γ).op,
        ‖sLocalSchwartzSlice K S φ ψ r (g • x)‖ₑ) ≤ ENNReal.ofReal C := by
    intro x hx
    apply sUnitOrbit_enorm_tsum_le_of_finite_sums K S Γ x
    exact sLocalOrbit_enorm_sum_le_of_gamma_bound K S Γ
      (sLocalSchwartzSlice K S φ ψ r) x (hbound φ r x (subset_closure hx))
  have h := integral_norm_sUnitHaar_le_of_orbit_bound K S Γ
    (continuous_sLocalSchwartzSlice K S φ ψ hψ r).aestronglyMeasurable
    ENNReal.ofReal_lt_top horbit
  rw [ENNReal.toReal_ofReal hC] at h
  calc
    _ ≤ C * (sUnitHaarCovolume K S Γ).toReal := h
    _ = _ := by dsimp only [C]; ring

include Γ in
/-- The genuine orbital integral inherits the same uniform majorant. -/
theorem exists_sLocalSchwartzProfile_radial_bound
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (M : ℕ) (hM : Module.finrank ℤ L < M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ, ∀ r : {r : ℝ // 0 < r},
      ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r‖ ≤
        D * SchwartzMap.seminorm ℂ M 0 φ *
          ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹) ^ M := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_sLocalSchwartzSlice_radial_integral_bound K S Γ ψ hψ hψsupport M hM
  refine ⟨D, hD, fun φ r => ?_⟩
  exact (norm_integral_le_integral_norm _).trans (hbound φ r)

include Γ in
/-- Arbitrarily prescribed polynomial decay is obtained by taking the actual
Schwartz order at least degree times the requested norm-scale exponent. -/
theorem exists_sLocalSchwartzProfile_power_decay
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (A : ℝ) (M : ℕ) (hM : Module.finrank ℤ L < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * A ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SchwartzMap V ℂ,
      ∀ r : {r : ℝ // 0 < r}, 1 ≤ r.val →
      ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r‖ ≤
        D * SchwartzMap.seminorm ℂ M 0 φ * r.val ^ (-A) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_sLocalSchwartzProfile_radial_bound K S Γ ψ hψ hψsupport M hM
  refine ⟨D, hD, fun φ r hr => (hbound φ r).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (normSection_inverse_pow_le_rpow (Module.finrank ℚ K) M
      Module.finrank_pos A r.val hr hOrder)
    (mul_nonneg hD (apply_nonneg (SchwartzMap.seminorm ℂ M 0) φ))

end HeckeGeneral.Analysis
