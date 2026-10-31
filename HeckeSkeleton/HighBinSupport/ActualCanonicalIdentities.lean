import HeckeSkeleton.HighBinSupport.ActualCanonicalHighBin
import HeckeSkeleton.HighBinSupport.ActualFinalContourIntegrability

/-!
Exact identities for the constructed HIGHBIN blocks at every positive
scale and every external height at least one.  The actual zero detector
makes the final kernel integrable on its compact height box, including
when the denominator character has a norm pole.  Consequently the
integrability filter retains every assigned row before any eventual
norm-form estimate is invoked.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonical

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry HeckeSkeleton.HighBinCanonicalBoundary
open HighBinVerified HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormRegionPacket
open HighBinVerified.NormFormComputedPacket
open HighBinBoundary.ActualIntegrability HighBinBoundary.ActualFinalIntegrability
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)] [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]
variable (P : ProbeData K S₀) (ψ : HeckeCharacter K)
variable (Θ : Finset (HeckeCharacter K)) (R : Finset (FrequencyRow K S₀))
variable (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
variable (hcommon : ∀ u : FrequencyRow K S₀, ∀ height : ℝ,
  rowZeroBelow K S₀ ψ Θ P (arithmeticHighEulerData K S₀ P ψ) u height B)

/-- Every original assigned row is integrable on the full final box.
No row-size cutoff or norm-form conclusion is needed. -/
theorem canonicalRows_integrable (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    (Z T κ d : ℝ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (k : DetectorIndex (detectorDepth e))
    (u : FrequencyRow K S₀)
    (hu : u ∈ canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k) :
    IntegrableOn (actualRegionKernel K S μ P ψ g u Z (gridRealPart e k.2.val) e)
      (heightBox (NormForm.internalHeight Z T κ)) := by
  have hs := canonicalRows_detectorSpec K S₀ P ψ Θ R B e he hB hcommon Z T κ d k u hu
  let H := NormForm.internalHeight Z T κ
  let U := upperHeight (2 * H) k.1.val
  have hH : 1 ≤ H := hT.trans (NormForm.le_internalHeight Z T κ)
  have hHU : H ≤ U := by
    have hg := (internal_detector_geometry Z T κ hT k.1.val).2.2
    change 2 * H + 2 ≤ U at hg
    linarith
  exact compensatedRowMellinKernel_integrableOn_final_heightBox K S μ P ψ g ∅ Θ hΘ u
    Z (gridRealPart e k.2.val) e H U hZ hs.1 (hs.2.1.trans hB1)
    he he1 hHU hs.2.2.2

/-- The row filter is exactly the original assigned fiber at all
positive scales, before choosing any asymptotic threshold. -/
theorem canonicalRows_integrableRows_eq (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    (Z T κ d : ℝ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (k : DetectorIndex (detectorDepth e)) :
    integrableRows K S μ P ψ g
      (canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k)
      Z (gridRealPart e k.2.val) e (NormForm.internalHeight Z T κ) =
        canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k :=
  integrableRows_eq K S μ P ψ g _ Z (gridRealPart e k.2.val) e
    (NormForm.internalHeight Z T κ)
    (canonicalRows_integrable K S μ P ψ Θ R B e he hB hcommon hΘ g
      he1 hB1 Z T κ d hZ hT k)

/-- The block value is the complete final contour integral over its
literal assigned fiber, at every positive scale. -/
theorem canonicalBlock_value_eq_final (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    (Z T κ d θ : ℝ) (N : ℕ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (k : CanonicalBlockIndex K S₀ P ψ Θ R B e he hB hcommon Z T κ d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    (canonicalBlock K S μ P ψ Θ R B e he hB hcommon g Z T κ d θ N k sc sub).value =
      ∑ u ∈ canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k.val,
        rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g ∅ u Z
          (NormForm.internalHeight Z T κ) (gridRealPart e k.val.2.val + 16 * e)
          (1 - gridRealPart e k.val.2.val - 6 * e) (17 / 50) := by
  change (∑ u ∈ integrableRows K S μ P ψ g
    (canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k.val)
    Z (gridRealPart e k.val.2.val) e (NormForm.internalHeight Z T κ), _) = _
  rw [canonicalRows_integrableRows_eq K S μ P ψ Θ R B e he hB hcommon
    hΘ g he1 hB1 Z T κ d hZ hT k.val]

/-- The same initial-minus-final row boundary is the initial contour
minus the computed block, with no change of row set at any scale. -/
theorem maskedBoundaryPiece_eq_initial_sub_block
    (hΘ : 1 ∈ Θ) (g : PrimeWindowGeometry)
    (he1 : e ≤ 1 / 10000) (hB1 : B ≤ 1)
    (Z T κ d θ : ℝ) (N : ℕ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (k : CanonicalBlockIndex K S₀ P ψ Θ R B e he hB hcommon Z T κ d)
    (sc : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    maskedBoundaryPiece K S μ P ψ Θ g B e he hB hcommon ∅ R Z T κ d k.val =
      (∑ u ∈ canonicalRows K S₀ P ψ Θ R B e he hB hcommon Z T κ d k.val,
        rowContourBox K S₀ μ P ψ (arithmeticHighEulerData K S₀ P ψ) g ∅ u Z
          (NormForm.internalHeight Z T κ) (B + 20 * e)
          (1 - gridRealPart e k.val.2.val - 6 * e) (17 / 50)) -
        (canonicalBlock K S μ P ψ Θ R B e he hB hcommon g Z T κ d θ N k sc sub).value := by
  rw [canonicalBlock_value_eq_final K S μ P ψ Θ R B e he hB hcommon
    hΘ g he1 hB1 Z T κ d θ N hZ hT k sc sub]
  rfl

end HeckeSkeleton.HighBinCanonical

#print axioms HeckeSkeleton.HighBinCanonical.canonicalRows_integrableRows_eq
#print axioms HeckeSkeleton.HighBinCanonical.canonicalBlock_value_eq_final
#print axioms HeckeSkeleton.HighBinCanonical.maskedBoundaryPiece_eq_initial_sub_block
