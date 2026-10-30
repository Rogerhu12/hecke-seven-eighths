import CubicSieve.ProfileDecay
import HeckeAxiom.ProbeTestChoice
import HeckeGeneral.Analysis.SUnitOrbitalIntegral

/-! Exact transport of the all-radius Fourier-sheet bounds to the skeleton's
actual norm-one Haar measure and orbital profile. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Profile

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeAxiom.ProbeUnits
open scoped Classical NumberField

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)

local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local instance : MeasurableSpace (sLocalNormOneGroup K S) := borel _
local instance : BorelSpace (sLocalNormOneGroup K S) := ⟨rfl⟩
local instance : MeasurableSpace A.G1 := borel _
local instance : BorelSpace A.G1 := ⟨rfl⟩

theorem sheetPointRaw_normOneEquiv (r : ℝ) (hr : 0 < r)
    (t : sLocalNormOneGroup K S) :
    ProbeSheetFourierMellinBounds.sheetPointRaw A r (normOneEquiv A t) =
      toUnits A ((t : sLocalMultiplicativeGroup K S) * sLocalNormSection K S ⟨r, hr⟩) :=
  sheetPoint_normOneEquiv A r hr t

theorem normOne_sheet_integral (f : SLocalProduct K A.Sf → ℂ)
    (r : ℝ) (hr : 0 < r) :
    (∫ t : A.G1, f (ProbeSheetFourierMellinBounds.sheetPointRaw A r t).val
      ∂HeckeAxiom.ProbeTestChoice.normOneMeasure A) =
      sUnitOrbitalProfile K S (fun x => f (toUnits A x).val) ⟨r, hr⟩ := by
  unfold HeckeAxiom.ProbeTestChoice.normOneMeasure
  rw [integral_map_equiv]
  unfold sUnitOrbitalProfile sUnitOrbitalIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change f (ProbeSheetFourierMellinBounds.sheetPointRaw A r (normOneEquiv A t)).val = _
    rw [sheetPointRaw_normOneEquiv A r hr t, mul_comm]

theorem normOne_sheet_integrable (f : SLocalProduct K A.Sf → ℂ)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun t : A.G1 =>
      f (ProbeSheetFourierMellinBounds.sheetPointRaw A r t).val)
      (HeckeAxiom.ProbeTestChoice.normOneMeasure A) ↔
      Integrable (fun t : sLocalNormOneGroup K S =>
        f (toUnits A ((t : sLocalMultiplicativeGroup K S) *
          sLocalNormSection K S ⟨r, hr⟩)).val) (sUnitHaarMeasure K S) := by
  unfold HeckeAxiom.ProbeTestChoice.normOneMeasure
  rw [integrable_map_equiv]
  change Integrable (fun t : sLocalNormOneGroup K S =>
    f (ProbeSheetFourierMellinBounds.sheetPointRaw A r (normOneEquiv A t)).val) _ ↔ _
  simp_rw [sheetPointRaw_normOneEquiv A r hr]

/-- Each actual orbital logarithmic derivative has the same common radial
majorant, with only the constant depending on the derivative order. -/
theorem orbital_log_derivative_decay
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion K) Circle)
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, e v ≠ 1)
    (μ : @Measure (SLocalProduct K A.Sf) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (SLocalProduct K A.Sf) _ _ (borel _) μ)
    (w : InfinitePlace K) (W₀ : SLocalProduct K A.Sf → ℂ)
    (hW₀ : ProbeWeight.IsAnnularTensor K A.Sf W₀)
    (hcompact : HasCompactSupport W₀) (hannular : tsupport W₀ ⊆ {x | IsUnit x})
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r),
      Integrable (fun t : sLocalNormOneGroup K S =>
        ProbeSheetFourierMellinBounds.logDerivativeRaw A w k
          (ProbeWeight.fourier K A.Sf e μ W₀)
          (toUnits A ((t : sLocalMultiplicativeGroup K S) *
            sLocalNormSection K S ⟨r, hr⟩)).val) (sUnitHaarMeasure K S) ∧
      ‖sUnitOrbitalProfile K S (fun x => ProbeSheetFourierMellinBounds.logDerivativeRaw A w k
          (ProbeWeight.fourier K A.Sf e μ W₀) (toUnits A x).val) ⟨r, hr⟩‖ ≤
        C * r ^ (-(1 / 6 : ℝ)) / (1 + r) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := sheet_log_derivative_decay A e he hne μ
    (HeckeAxiom.ProbeTestChoice.normOneMeasure A) hμ
    (HeckeAxiom.ProbeTestChoice.normOneMeasure_isHaar A) w W₀ hW₀ hcompact hannular k
  refine ⟨C, hC, fun r hr => ⟨(normOne_sheet_integrable A _ r hr).mp (hbound r hr).1, ?_⟩⟩
  rw [← normOne_sheet_integral A _ r hr]
  exact (norm_integral_le_integral_norm _).trans (hbound r hr).2

end CubicSieve.Profile
