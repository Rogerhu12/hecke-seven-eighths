import HeckeGeneral.Analysis.SUnitHaar
import HeckeGeneral.Arithmetic.SLocalNormSection
import Mathlib.MeasureTheory.Group.Integral

/-!
# Independence of the norm-one component in an actual orbital integral

The integration group and Haar measure are those constructed for the actual
S-local product. Multiplying the base point by a norm-one element translates
the integration variable. Thus two base points with the same product norm
give the same orbital integral, and integrability at either base point implies
integrability at the other. This is the measure-theoretic common-profile
identity; decay and absolute convergence for Schwartz inputs are separate.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The orbit integral uses the actual upstairs Haar measure, without a
quotient-volume factor or a chosen norm section. -/
def sUnitOrbitalIntegral (f : G → E) (x : G) : E :=
  ∫ t : T, f (x * (t : G)) ∂sUnitHaarMeasure K S

theorem sUnitOrbitalIntegral_mul_normOne (f : G → E) (x : G) (u : T) :
    sUnitOrbitalIntegral K S f (x * (u : G)) = sUnitOrbitalIntegral K S f x := by
  simpa only [sUnitOrbitalIntegral, Subgroup.coe_mul, mul_assoc] using
    (integral_mul_left_eq_self (μ := sUnitHaarMeasure K S)
      (fun t : T => f (x * (t : G))) u)

omit [NormedSpace ℝ E] in
theorem integrable_sUnitOrbit_mul_normOne {f : G → E} {x : G}
    (hf : Integrable (fun t : T => f (x * (t : G))) (sUnitHaarMeasure K S)) (u : T) :
    Integrable (fun t : T => f ((x * (u : G)) * (t : G))) (sUnitHaarMeasure K S) := by
  simpa only [Subgroup.coe_mul, mul_assoc] using hf.comp_mul_left u

omit [MeasurableSpace T] [BorelSpace T] in
private theorem exists_normOne_translate_of_norm_eq (x y : G)
    (hxy : sLocalProductNorm K S x = sLocalProductNorm K S y) :
    ∃ u : T, x = y * (u : G) := by
  have heq : sLocalProductNormHom K S x = sLocalProductNormHom K S y :=
    Units.ext hxy
  have hu : y⁻¹ * x ∈ sLocalNormOneGroup K S := by
    change sLocalProductNormHom K S (y⁻¹ * x) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  refine ⟨⟨y⁻¹ * x, hu⟩, ?_⟩
  simp

/-- Equal actual norms identify the common orbital profile by Haar translation. -/
theorem sUnitOrbitalIntegral_eq_of_norm_eq (f : G → E) (x y : G)
    (hxy : sLocalProductNorm K S x = sLocalProductNorm K S y) :
    sUnitOrbitalIntegral K S f x = sUnitOrbitalIntegral K S f y := by
  obtain ⟨u, rfl⟩ := exists_normOne_translate_of_norm_eq K S x y hxy
  exact sUnitOrbitalIntegral_mul_normOne K S f y u

omit [NormedSpace ℝ E] in
theorem integrable_sUnitOrbit_iff_of_norm_eq (f : G → E) (x y : G)
    (hxy : sLocalProductNorm K S x = sLocalProductNorm K S y) :
    Integrable (fun t : T => f (x * (t : G))) (sUnitHaarMeasure K S) ↔
      Integrable (fun t : T => f (y * (t : G))) (sUnitHaarMeasure K S) := by
  constructor
  · intro hf
    obtain ⟨u, rfl⟩ := exists_normOne_translate_of_norm_eq K S y x hxy.symm
    exact integrable_sUnitOrbit_mul_normOne K S hf u
  · intro hf
    obtain ⟨u, rfl⟩ := exists_normOne_translate_of_norm_eq K S x y hxy
    exact integrable_sUnitOrbit_mul_normOne K S hf u

/-- A common radial profile on positive arguments; there is no value at zero. -/
def sUnitOrbitalProfile (f : G → E) (r : {r : ℝ // 0 < r}) : E :=
  sUnitOrbitalIntegral K S f (sLocalNormSection K S r)

theorem sUnitOrbitalIntegral_eq_profile (f : G → E) (x : G) :
    sUnitOrbitalIntegral K S f x =
      sUnitOrbitalProfile K S f
        ⟨sLocalProductNorm K S x, sLocalProductNorm_pos K S x⟩ := by
  apply sUnitOrbitalIntegral_eq_of_norm_eq
  exact (sLocalProductNorm_section K S
    ⟨sLocalProductNorm K S x, sLocalProductNorm_pos K S x⟩).symm

end HeckeGeneral.Analysis
