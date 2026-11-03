import CubicSieve.ProfileBridge
import CubicSieve.ProfileLower

/-! Concrete common smoothing data: the fixed positive annular tensor, the
canonical trace Fourier transform, its actual norm-one orbital profile, and
proved all-radius decay. No majorant or small-radius bound is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeAxiom.ProbeUnits
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance profileLocalInstance1 : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance profileLocalInstance2 : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩
local instance profileLocalInstance3 (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (v.adicCompletion K) := borel _
local instance profileLocalInstance4 (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (v.adicCompletion K) := ⟨rfl⟩
local instance profileLocalInstance5 : MeasurableSpace (SLocalProduct K A.Sf) := borel _
local instance profileLocalInstance6 : BorelSpace (SLocalProduct K A.Sf) := ⟨rfl⟩

def canonicalCharacters (v : ↥A.Sf) : AddChar (v.val.adicCompletion K) Circle :=
  ResidueTrace.localTraceCharacter v.val

theorem canonicalCharacters_continuous (v : ↥A.Sf) : Continuous (canonicalCharacters A v) :=
  ResidueTrace.continuous_localTraceCharacter v.val

theorem canonicalCharacters_ne_one (v : ↥A.Sf) : canonicalCharacters A v ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := SArithmeticData.localTraceCharacter_exists_ne_one v.val
  exact hx (by simpa [canonicalCharacters] using DFunLike.congr_fun h x)

theorem canonicalAdditiveMeasure_isHaar :
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A).IsAddHaarMeasure := by
  have : (PoissonArch.traceMeasure K).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume
      (ENNReal.ofReal_pos.mpr (PoissonArch.haarScalar_pos K)).ne' ENNReal.ofReal_ne_top
  have := HeckeAxiom.ProbeTestChoice.localHaar_isAddHaar A
  have := HeckeAxiom.ProbeTestChoice.sigmaFinite_localHaar A
  have : (PoissonS.productMeasure K A.Sf
      (HeckeAxiom.ProbeTestChoice.localHaar A)).IsAddHaarMeasure := by
    unfold PoissonS.productMeasure
    exact Measure.prod.instIsAddHaarMeasure _ _
  unfold HeckeAxiom.ProbeTestChoice.additiveMeasure NormalizedProbe.poissonAdditiveMeasure
  apply AddEquiv.isAddHaarMeasure_map
  · exact (HeckeAxiom.ProbeFourier.poissonHomeomorph A).continuous
  · exact (HeckeAxiom.ProbeFourier.poissonHomeomorph A).symm.continuous

def canonicalFourier : SLocalProduct K A.Sf → ℂ :=
  ProbeWeight.fourier K A.Sf (canonicalCharacters A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (originalTest A)

def dualLogFunction (w : InfinitePlace K) (k : ℕ)
    (x : sLocalMultiplicativeGroup K S) : ℂ :=
  ProbeSheetFourierMellinBounds.logDerivativeRaw A w k (canonicalFourier A) (toUnits A x).val

def dualProfile (r : {r : ℝ // 0 < r}) : ℂ :=
  sUnitOrbitalProfile K S (fun x => canonicalFourier A (toUnits A x).val) r

theorem canonical_dual_log_decay (w : InfinitePlace K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r),
      Integrable (fun t : sLocalNormOneGroup K S => dualLogFunction A w k
        ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨r, hr⟩))
        (sUnitHaarMeasure K S) ∧
      ‖sUnitOrbitalProfile K S (dualLogFunction A w k) ⟨r, hr⟩‖ ≤
        C * r ^ (-(1 / 6 : ℝ)) / (1 + r) ^ 3 :=
  orbital_log_derivative_decay A (canonicalCharacters A)
    (canonicalCharacters_continuous A) (canonicalCharacters_ne_one A)
    (HeckeAxiom.ProbeTestChoice.additiveMeasure A) (canonicalAdditiveMeasure_isHaar A)
    w (originalTest A) (originalTest_annular A)
    (originalTest_compact_unit_support A).1 (originalTest_compact_unit_support A).2 k

theorem dualLogFunction_zero (w : InfinitePlace K) (x : sLocalMultiplicativeGroup K S) :
    dualLogFunction A w 0 x = canonicalFourier A (toUnits A x).val :=
  ProbeSheet.logDerivative_zero A w (canonicalFourier A) _

theorem canonical_dualProfile_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r),
      ‖dualProfile A ⟨r, hr⟩‖ ≤ C * r ^ (-(1 / 6 : ℝ)) / (1 + r) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := canonical_dual_log_decay A (Classical.arbitrary (InfinitePlace K)) 0
  refine ⟨C, hC, fun r hr => ?_⟩
  simpa only [dualProfile, show dualLogFunction A (Classical.arbitrary (InfinitePlace K)) 0 =
      (fun x => canonicalFourier A (toUnits A x).val) from
      funext (dualLogFunction_zero A _)] using (hbound r hr).2

end CubicSieve.Profile
