import HeckeGeneral.Analysis.SUnitHaar
import HeckeGeneral.Arithmetic.SLocalNormSectionAlgebra
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
The actual S-local product norm splits by the existing arithmetic section.
The radial measure uses precisely sUnitHaarMeasure and ordinary Lebesgue
measure in log radius. Haar uniqueness retains its strictly positive scalar;
no normalization of that scalar to one is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SLocalRadialHaarDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open MeasureTheory MeasureTheory.Measure Topology
open scoped Classical NNReal

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def logNormSection (r : Multiplicative ℝ) : sLocalMultiplicativeGroup K S :=
  sLocalNormSection K S ⟨Real.exp r.toAdd, Real.exp_pos _⟩

@[simp] theorem productNorm_logNormSection (r : Multiplicative ℝ) :
    sLocalProductNorm K S (logNormSection K S r) = Real.exp r.toAdd :=
  sLocalProductNorm_section K S _

@[simp] theorem logNormSection_one : logNormSection K S 1 = 1 := by
  simpa only [logNormSection, toAdd_one, Real.exp_zero] using
    sLocalNormSection_one K S

theorem logNormSection_mul (r q : Multiplicative ℝ) :
    logNormSection K S (r * q) = logNormSection K S r * logNormSection K S q := by
  simpa only [logNormSection, toAdd_mul, Real.exp_add] using
    sLocalNormSection_mul K S
      ⟨Real.exp r.toAdd, Real.exp_pos _⟩ ⟨Real.exp q.toAdd, Real.exp_pos _⟩

theorem continuous_logNormSection : Continuous (logNormSection K S) :=
  (continuous_sLocalNormSection K S).comp
    ((Real.continuous_exp.comp continuous_toAdd).subtype_mk _)

theorem productNorm_inv (x : sLocalMultiplicativeGroup K S) :
    sLocalProductNorm K S x⁻¹ = (sLocalProductNorm K S x)⁻¹ := by
  exact congrArg Units.val ((sLocalProductNormHom K S).map_inv x)

def normOnePart (x : sLocalMultiplicativeGroup K S) : sLocalNormOneGroup K S :=
  ⟨x * (logNormSection K S (Multiplicative.ofAdd
    (Real.log (sLocalProductNorm K S x))))⁻¹, by
    apply (mem_sLocalNormOneGroup K S _).mpr
    rw [sLocalProductNorm_mul, productNorm_inv, productNorm_logNormSection]
    simp only [toAdd_ofAdd,
      Real.exp_log (sLocalProductNorm_pos K S x)]
    exact mul_inv_cancel₀ (sLocalProductNorm_pos K S x).ne'⟩

theorem continuous_normOnePart : Continuous (normOnePart K S) := by
  apply Continuous.subtype_mk
  exact continuous_id.mul
    ((continuous_logNormSection K S).comp
      (continuous_ofAdd.comp
        ((continuous_sLocalProductNorm K S).log
          (fun x => (sLocalProductNorm_pos K S x).ne')))).inv

/-- Literal log-radius splitting of the actual arithmetic S-local group. -/
def sLocalLogRadialEquiv :
    (sLocalNormOneGroup K S × Multiplicative ℝ) ≃ₜ* sLocalMultiplicativeGroup K S where
  toFun p := (p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2
  invFun x := (normOnePart K S x,
    Multiplicative.ofAdd (Real.log (sLocalProductNorm K S x)))
  left_inv p := by
    have hp : sLocalProductNorm K S
        ((p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2) =
        Real.exp p.2.toAdd := by
      rw [sLocalProductNorm_mul,
        (mem_sLocalNormOneGroup K S _).mp p.1.property,
        productNorm_logNormSection, one_mul]
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2 *
        (logNormSection K S (Multiplicative.ofAdd (Real.log
          (sLocalProductNorm K S
            ((p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2)))))⁻¹ = _
      rw [hp, Real.log_exp, ofAdd_toAdd]
      exact mul_inv_cancel_right _ _
    · change Multiplicative.ofAdd (Real.log (sLocalProductNorm K S
        ((p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2))) = p.2
      rw [hp, Real.log_exp, ofAdd_toAdd]
  right_inv x := by
    change x * (logNormSection K S (Multiplicative.ofAdd
      (Real.log (sLocalProductNorm K S x))))⁻¹ *
        logNormSection K S (Multiplicative.ofAdd
          (Real.log (sLocalProductNorm K S x))) = x
    exact inv_mul_cancel_right _ _
  map_mul' p q := by
    change ((p.1 : sLocalMultiplicativeGroup K S) * q.1) *
      logNormSection K S (p.2 * q.2) =
      ((p.1 : sLocalMultiplicativeGroup K S) * logNormSection K S p.2) *
        ((q.1 : sLocalMultiplicativeGroup K S) * logNormSection K S q.2)
    rw [logNormSection_mul]
    ac_rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul
    ((continuous_logNormSection K S).comp continuous_snd)
  continuous_invFun := (continuous_normOnePart K S).prodMk
    (continuous_ofAdd.comp ((continuous_sLocalProductNorm K S).log
      (fun x => (sLocalProductNorm_pos K S x).ne')))

@[simp] theorem sLocalLogRadialEquiv_apply
    (t : sLocalNormOneGroup K S) (r : ℝ) :
    sLocalLogRadialEquiv K S (t, Multiplicative.ofAdd r) =
      (t : sLocalMultiplicativeGroup K S) *
        sLocalNormSection K S ⟨Real.exp r, Real.exp_pos r⟩ := rfl

@[simp] theorem productNorm_sLocalLogRadialEquiv
    (t : sLocalNormOneGroup K S) (r : ℝ) :
    sLocalProductNorm K S
      (sLocalLogRadialEquiv K S (t, Multiplicative.ofAdd r)) = Real.exp r := by
  rw [sLocalLogRadialEquiv_apply, sLocalProductNorm_mul,
    (mem_sLocalNormOneGroup K S _).mp t.property,
    sLocalProductNorm_section, one_mul]

-- The type tag changes only the operation, not the underlying Borel space.
local instance : MeasurableSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasurableSpace ℝ)
local instance : BorelSpace (Multiplicative ℝ) := inferInstanceAs (BorelSpace ℝ)

/-- Ordinary Lebesgue measure in the additive logarithmic coordinate. -/
def logRadiusVolume : Measure (Multiplicative ℝ) := (volume : Measure ℝ)

instance logRadiusVolume_isHaarMeasure : IsHaarMeasure logRadiusVolume where
  toIsFiniteMeasureOnCompacts :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  toIsOpenPosMeasure := inferInstanceAs (IsOpenPosMeasure (volume : Measure ℝ))
  toIsMulLeftInvariant := ⟨fun r => by
    change Measure.map (fun x : ℝ => r.toAdd + x) volume = volume
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self r.toAdd⟩

instance logRadiusVolume_sigmaFinite : SigmaFinite logRadiusVolume :=
  inferInstanceAs (SigmaFinite (volume : Measure ℝ))

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [MeasurableSpace (sLocalMultiplicativeGroup K S)]
  [BorelSpace (sLocalMultiplicativeGroup K S)]

/-- Uses precisely the norm-one Haar fixed in the physical probe. -/
def sLocalRadialMeasure : Measure (sLocalMultiplicativeGroup K S) :=
  Measure.map (sLocalLogRadialEquiv K S)
    ((sUnitHaarMeasure K S).prod logRadiusVolume)

instance sLocalRadialMeasure_isHaarMeasure : IsHaarMeasure (sLocalRadialMeasure K S) := by
  unfold sLocalRadialMeasure
  infer_instance

/-- The comparison is valid for any genuine ambient Haar measure, including
the product of the local multiplicative Haar measures once transported to G. -/
def radialHaarScalar (ν : Measure (sLocalMultiplicativeGroup K S)) [ν.IsHaarMeasure] : ℝ≥0 :=
  haarScalarFactor (sLocalRadialMeasure K S) ν

theorem radialHaarScalar_pos (ν : Measure (sLocalMultiplicativeGroup K S))
    [ν.IsHaarMeasure] : 0 < radialHaarScalar K S ν :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

theorem sLocalRadialMeasure_eq_smul (ν : Measure (sLocalMultiplicativeGroup K S))
    [ν.IsHaarMeasure] :
    sLocalRadialMeasure K S = radialHaarScalar K S ν • ν :=
  isMulLeftInvariant_eq_smul _ _

/-- In particular, no choice or compatibility premise is needed for the
actual ambient Mathlib Haar measure. -/
theorem exists_pos_radialMeasure_eq_ambientHaar :
    ∃ c : ℝ≥0, 0 < c ∧
      sLocalRadialMeasure K S =
        c • (Measure.haar : Measure (sLocalMultiplicativeGroup K S)) :=
  ⟨radialHaarScalar K S Measure.haar, radialHaarScalar_pos K S Measure.haar,
    sLocalRadialMeasure_eq_smul K S Measure.haar⟩

theorem integral_sLocalRadialMeasure
    (f : sLocalMultiplicativeGroup K S → ℂ) :
    (∫ x, f x ∂sLocalRadialMeasure K S) =
      ∫ p : sLocalNormOneGroup K S × Multiplicative ℝ,
        f (sLocalLogRadialEquiv K S p)
          ∂((sUnitHaarMeasure K S).prod logRadiusVolume) := by
  exact (sLocalLogRadialEquiv K S).toHomeomorph.measurableEmbedding.integral_map f

/-- Positive scalar comparison of actual measures and their Bochner integrals.
This does not exchange the two integrations or assert weighted integrability. -/
theorem integral_sLocalRadialMeasure_eq_scalar_mul
    (ν : Measure (sLocalMultiplicativeGroup K S)) [ν.IsHaarMeasure]
    (f : sLocalMultiplicativeGroup K S → ℂ) :
    (∫ x, f x ∂sLocalRadialMeasure K S) =
      ((radialHaarScalar K S ν : ℝ) : ℂ) * ∫ x, f x ∂ν := by
  rw [sLocalRadialMeasure_eq_smul K S ν, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul]

end HeckeGeneral.Analysis.SLocalRadialHaarDraft
