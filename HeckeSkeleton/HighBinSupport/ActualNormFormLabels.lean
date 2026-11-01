import HeckeSkeleton.HighBinSupport.ActualNormFormIntegral
import HeckeSkeleton.HighBinSupport.HighNormFormPacket

/-!
Finite labels for the actual complete-slot row integrals.

The selector below is chosen from the actual amplitude objects constructed
by the rowwise theorem. Its fibers partition any fixed retained row family,
and their exact sums are the original rowContourBox sums. The label mean is
the mean of the actual complete-slot amplitudes. No row-count estimate and
no bound on a proposed presentation is assumed.

The original prime normalizer is bounded by the proved actual prime-window
theorem through ActualNormFormNormalization. These complete-slot fibers
are separate from the physical source's main-polynomial amplitude labels.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormLabels

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary HighBinBoundary.ActualIntegrability
open NormFormAmplitudeGrid
open scoped Classical BigOperators Topology

/-- The mean attached to a fixed finite complete-slot label. -/
def actualFullSlotLabelMean (g : PrimeWindowGeometry) (a theta : ℝ) (N : ℕ)
    (label : Fin g.slots → Fin (N + 1)) : ℝ :=
  (∑ i, min (((label i).val : ℝ) * theta) (a - 1 / 2)) / g.slots

/-- The full label set has a scale-independent cardinality. -/
theorem actualFullSlotLabel_card (g : PrimeWindowGeometry) (N : ℕ) :
    Fintype.card (Fin g.slots → Fin (N + 1)) = (N + 1) ^ g.slots := by
  simp

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The actual finite-label norm form. Constants, the grid and the height
ceiling are fixed before the scale, shell, bin and retained finite row set.
Each selected label has an actual complete-slot witness, its row contribution
is the original contour integral, and the exact total is preserved. -/
theorem exists_actual_labelled_rowContour_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e lam : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ F : Finset (FrequencyRow K S₀),
      (∀ u ∈ F, Z ^ d ≤ frequencyRowNorm K S₀ u ∧
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d ∧
        rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
          (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e)) →
      ∃ selector : FrequencyRow K S₀ → (Fin g.slots → Fin (N + 1)),
        (∀ u ∈ F, ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N,
          A.label = selector u) ∧
        (∀ label : Fin g.slots → Fin (N + 1),
          (∑ u ∈ NormForm.labelledRows F selector label,
            ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖) ≤
          C * ((NormForm.labelledRows F selector label).card : ℝ) *
            Z ^ (NormForm.rowExponent d a (actualFullSlotLabelMean g a theta N label) + lam / 4)) ∧
        (∑ label : Fin g.slots → Fin (N + 1),
          ∑ u ∈ NormForm.labelledRows F selector label,
            rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)) =
          ∑ u ∈ F,
            rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
              (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  classical
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hrow⟩ :=
    NormFormIntegral.exists_actual_rowContour_normForm_quarter_loss K S μ
      psi companions hcomp P g hcal hpsi he he1 hlam heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 a ha ha1 F hF
  have hrowF (u : {u : FrequencyRow K S₀ // u ∈ F}) :
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u.val Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u.val Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) + lam / 4) :=
    hrow Z T hZ hT hTceiling d hd hd1 u.val (hF u.val u.property).1
      (hF u.val u.property).2.1 a ha ha1 (hF u.val u.property).2.2
  choose A hA using hrowF
  let selector : FrequencyRow K S₀ → (Fin g.slots → Fin (N + 1)) := fun u =>
    if hu : u ∈ F then (A ⟨u, hu⟩).label else fun _ => ⟨0, Nat.succ_pos N⟩
  have hselector (u : FrequencyRow K S₀) (hu : u ∈ F) :
      selector u = (A ⟨u, hu⟩).label := by
    simp only [selector, dif_pos hu]
  refine ⟨selector, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨A ⟨u, hu⟩, (hselector u hu).symm⟩
  · intro label
    calc
      _ ≤ ∑ _u ∈ NormForm.labelledRows F selector label,
          C * Z ^ (NormForm.rowExponent d a (actualFullSlotLabelMean g a theta N label) + lam / 4) := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨huF, hulabel⟩ := (NormForm.mem_labelledRows F selector label u).mp hu
        have hlabel : (A ⟨u, huF⟩).label = label := (hselector u huF).symm.trans hulabel
        have hmean : ActualFullSlotAmplitude.mean K S₀ (A ⟨u, huF⟩) =
            actualFullSlotLabelMean g a theta N label := by
          unfold ActualFullSlotAmplitude.mean ActualFullSlotAmplitude.amplitude
            actualFullSlotLabelMean
          rw [hlabel]
        simpa only [hmean] using hA ⟨u, huF⟩
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  · exact NormForm.sum_labelledRows F selector (fun u =>
      rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
        (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50))

end HighBinVerified.NormFormLabels

#print axioms HighBinVerified.NormFormLabels.actualFullSlotLabel_card
#print axioms HighBinVerified.NormFormLabels.exists_actual_labelled_rowContour_normForm
