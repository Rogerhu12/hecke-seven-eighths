import HeckeGeneral.Analysis.SUnitSchwartzDecay
import HeckeGeneral.Arithmetic.SLocalNormSectionAlgebra

/-!
# The actual orbital profile as a continuous complex-linear functional

Addition is justified by the actual integrability of tensor Schwartz slices.
Continuity follows from the proved radial orbital bound at radius one, using
one of the defining Schwartz seminorms. No norm on Schwartz space is chosen.
Other positive radii are obtained by the actual degree-th-root archimedean
dilation; the finite local function and the upstairs Haar measure stay fixed.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "L" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)

include Γ in
/-- Actual slice integrability justifies complex additivity of the profile. -/
theorem sUnitOrbitalProfile_tensor_add (hψ : Continuous ψ)
    (hψsupport : HasCompactSupport ψ) (φ η : SchwartzMap V ℂ)
    (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S (φ + η) ψ) r =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r +
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S η ψ) r := by
  change (∫ x : T, sLocalSchwartzSlice K S (φ + η) ψ r x ∂sUnitHaarMeasure K S) =
    (∫ x : T, sLocalSchwartzSlice K S φ ψ r x ∂sUnitHaarMeasure K S) +
      ∫ x : T, sLocalSchwartzSlice K S η ψ r x ∂sUnitHaarMeasure K S
  have heq : sLocalSchwartzSlice K S (φ + η) ψ r =
      fun x => sLocalSchwartzSlice K S φ ψ r x + sLocalSchwartzSlice K S η ψ r x := by
    funext x
    unfold sLocalSchwartzSlice sLocalTensorTestFunction
    simp only [add_apply, add_mul]
  rw [heq]
  exact integral_add
    (integrable_sLocalSchwartzSlice K S Γ φ ψ hψ hψsupport r)
    (integrable_sLocalSchwartzSlice K S Γ η ψ hψ hψsupport r)

/-- Scalar multiplication is the scalar multiplication of the actual Haar integral. -/
theorem sUnitOrbitalProfile_tensor_smul (a : ℂ) (φ : SchwartzMap V ℂ)
    (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S (a • φ) ψ) r =
      a • sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r := by
  change (∫ x : T, sLocalSchwartzSlice K S (a • φ) ψ r x ∂sUnitHaarMeasure K S) =
    a • (∫ x : T, sLocalSchwartzSlice K S φ ψ r x ∂sUnitHaarMeasure K S)
  have heq : sLocalSchwartzSlice K S (a • φ) ψ r =
      fun x => a • sLocalSchwartzSlice K S φ ψ r x := by
    funext x
    unfold sLocalSchwartzSlice sLocalTensorTestFunction
    simp only [smul_apply, smul_eq_mul, mul_assoc]
  rw [heq, integral_smul]

include Γ in
/-- The constant and seminorm are selected before the archimedean function. -/
theorem exists_sUnitProfile_one_seminorm_bound (hψ : Continuous ψ)
    (hψsupport : HasCompactSupport ψ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap V ℂ,
      ‖sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) ⟨1, zero_lt_one⟩‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ V ℂ) φ := by
  let M := Module.finrank ℤ L + 1
  have hM : Module.finrank ℤ L < M := Nat.lt_succ_self _
  obtain ⟨C, hC, hbound⟩ :=
    exists_sLocalSchwartzProfile_radial_bound K S Γ ψ hψ hψsupport M hM
  refine ⟨{(M, 0)}, C, hC, fun φ => ?_⟩
  simpa only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply,
    Real.one_rpow, inv_one, one_pow, mul_one] using hbound φ ⟨1, zero_lt_one⟩

/-- Integration over the actual norm-one Haar group, as a continuous complex
linear functional on Schwartz space. Its continuity is proved, not assumed. -/
def sUnitProfileOneCLM (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) :
    SchwartzMap V ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun φ => sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) ⟨1, zero_lt_one⟩)
    (fun φ η => sUnitOrbitalProfile_tensor_add K S Γ ψ hψ hψsupport φ η ⟨1, zero_lt_one⟩)
    (fun a φ => sUnitOrbitalProfile_tensor_smul K S ψ a φ ⟨1, zero_lt_one⟩)
    (exists_sUnitProfile_one_seminorm_bound K S Γ ψ hψ hψsupport)

@[simp] theorem sUnitProfileOneCLM_apply (hψ : Continuous ψ)
    (hψsupport : HasCompactSupport ψ) (φ : SchwartzMap V ℂ) :
    sUnitProfileOneCLM K S Γ ψ hψ hψsupport φ =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) ⟨1, zero_lt_one⟩ := rfl

/-- Composition by the actual archimedean part of the positive norm section. -/
def sUnitRadialSchwartzCLM (r : {r : ℝ // 0 < r}) :
    SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (traceUnitMulEquiv K (sLocalNormSection K S r).1)

/-- The radial length is the degree-th root, in the trace Euclidean metric. -/
theorem sUnitRadialSchwartzCLM_apply (r : {r : ℝ // 0 < r})
    (φ : SchwartzMap V ℂ) (z : V) :
    sUnitRadialSchwartzCLM K S r φ z =
      φ ((r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • z) := by
  change φ (traceUnitMulEquiv K (sLocalNormSection K S r).1 z) = _
  apply congrArg φ
  apply (traceToMixed K).injective
  rw [traceToMixed_traceUnitMulEquiv, map_smul]
  change algebraMap ℝ W (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) *
    traceToMixed K z = (r.val ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • traceToMixed K z
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

/-- Radial composition affects only the infinite test; the actual finite
coordinates of the norm section are one. -/
theorem sLocalTensorTestFunction_radial_comp (φ : SchwartzMap V ℂ)
    (r : {r : ℝ // 0 < r}) (p : G) :
    sLocalTensorTestFunction K S (sUnitRadialSchwartzCLM K S r φ) ψ p =
      sLocalTensorTestFunction K S φ ψ (sLocalNormSection K S r * p) := by
  have harch : traceUnitMulEquiv K (sLocalNormSection K S r).1
      ((traceToMixed K).symm (p.1 : W)) =
      (traceToMixed K).symm ((sLocalNormSection K S r * p).1 : W) := by
    apply (traceToMixed K).injective
    rw [traceToMixed_traceUnitMulEquiv, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hfin : (fun v : S => ((sLocalNormSection K S r * p).2 v).val) =
      fun v : S => (p.2 v).val := by
    funext v
    change (1 * p.2 v).val = (p.2 v).val
    simp only [one_mul]
  change φ (traceUnitMulEquiv K (sLocalNormSection K S r).1
    ((traceToMixed K).symm (p.1 : W))) * ψ (fun v : S => (p.2 v).val) = _
  unfold sLocalTensorTestFunction
  rw [harch, hfin]

/-- The actual profile at every positive radius is the radius-one functional
applied to the radial composition; no change of Haar normalization occurs. -/
theorem sUnitOrbitalProfile_eq_oneCLM_radial_comp (hψ : Continuous ψ)
    (hψsupport : HasCompactSupport ψ) (φ : SchwartzMap V ℂ)
    (r : {r : ℝ // 0 < r}) :
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r =
      sUnitProfileOneCLM K S Γ ψ hψ hψsupport (sUnitRadialSchwartzCLM K S r φ) := by
  rw [sUnitProfileOneCLM_apply]
  unfold sUnitOrbitalProfile sUnitOrbitalIntegral
  simp only [sLocalNormSection_one, one_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x : T =>
    (sLocalTensorTestFunction_radial_comp K S ψ φ r (x : G)).symm)

/-- The common orbital profile is a continuous linear functional at every
fixed positive radius. The radius-one functional is the only Haar integral
used in this definition. -/
def sUnitProfileCLM (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) : SchwartzMap V ℂ →L[ℂ] ℂ :=
  (sUnitProfileOneCLM K S Γ ψ hψ hψsupport).comp (sUnitRadialSchwartzCLM K S r)

@[simp] theorem sUnitProfileCLM_apply (hψ : Continuous ψ)
    (hψsupport : HasCompactSupport ψ) (r : {r : ℝ // 0 < r}) (φ : SchwartzMap V ℂ) :
    sUnitProfileCLM K S Γ ψ hψ hψsupport r φ =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ) r :=
  (sUnitOrbitalProfile_eq_oneCLM_radial_comp K S Γ ψ hψ hψsupport φ r).symm

end HeckeGeneral.Analysis
