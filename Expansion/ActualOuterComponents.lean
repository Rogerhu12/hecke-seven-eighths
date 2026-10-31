import Expansion.ActualOuterHeightBudget
import Expansion.PhysicalInitialRowTruncation

/-!
# Literal outer remainders for the final four-component expansion

Every term is an integral or sum already fixed by the original row set
and original contours.  The common exterior-height tail is restricted to
nonprincipal rows; each moderate face sum retains exactly its prescribed
finite bin.  No final vertical contribution is included in these tails.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open Expansion.PhysicalInitialMellin Expansion.PhysicalRapidTruncation
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]

def actualNonprincipalInitialTailSum
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H : ℝ) : ℂ :=
  ∑' u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u},
    actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val

def actualModerateInitialFaces
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (rows : Finset (FrequencyRow K Sset)) (Z H B e a : ℝ) : ℂ :=
  ∑ u ∈ rows, actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
    (B + 20 * e) (1 - a - 6 * e) (17 / 50)

variable [IsTotallyComplex K]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]

include nu in
/-- Actual absolute convergence of the complete nonprincipal exterior
tail, at every positive original scale and every common height. -/
theorem summable_norm_actualNonprincipalInitialTail
    (P : ProbeData K Sset) (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    Summable (fun u : {u : FrequencyRow K Sset // ¬principalFrequencyRow K Sset u} =>
      ‖actualInitialRowTailIntegral K S mu P psi g ∅ Z H u.val‖) :=
  (summable_norm_actualInitialRestriction K S mu nu P hAllowed psi hcal hunram g ∅ hZ
    (heightCube H)ᶜ).subtype (fun u => ¬principalFrequencyRow K Sset u)

end Expansion.Project

#print axioms Expansion.Project.summable_norm_actualNonprincipalInitialTail
