import Expansion.ActualRecipeData
import Expansion.PhysicalInitialTailBound

/-!
# The actual recipe tail and the original whole-bin boundary hypothesis

All five other tail summands have independent actual arithmetic proofs.
The remaining assumption is precisely the same whole-bin contour
difference allowed by the original EX-TAIL interface.  Its identification
with the named presentation is supplied by the presentation consumer.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.HighBinActualEuler

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

include nu in
theorem actualSmall_horizontal_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualSmallRowHorizontalFaces K S mu P psi g ∅ Z H B e) := by
  apply PowerHeightTailBound.of_uniform_one_add_decay
    (R := outerBoundaryScalePower 5 5 3 + 163 / 800)
  exact exists_actual_small_horizontal_sum_bound K S mu nu hcomplex P omega psi hpsi
    hAllowed hcal hunram g hB hB1 he he1 hboundary

include nu in
theorem actualLarge_horizontal_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) :
    PowerHeightTailBound (fun Z H => actualLargeHorizontalFaces K S mu P psi g Z H zeta) := by
  apply PowerHeightTailBound.of_uniform_one_add_decay
    (R := outerBoundaryScalePower 5 5 (largeSweepUpper zeta) +
      (13 / 16 + zeta) * (largeSweepRowPower zeta + 1))
  intro N
  obtain ⟨C, Z0, hC, hZ0, hb⟩ :=
    exists_actual_large_horizontal_sum_bound K S mu nu hcomplex P psi hcal hunram g hzeta N
  exact ⟨C, Z0, hC, hZ0, fun Z H hZ hH => (hb Z H hZ hH).2⟩

include nu in
/-- Exactly the original boundary hypothesis, after identifying its rows
and contours with this recipe, is sufficient for its entire literal tail. -/
theorem actualPhysicalExpansionTail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e zeta : ℝ}
    (hB0 : 51 / 100 ≤ B) (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hzeta : 0 < zeta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (hmove : PowerHeightTailBound
      (physicalScheduledWholeBoundary K S mu P (arithmeticHighEulerData K Sset P psi)
        omega psi hpsi hB0 hB1 he hboundary g zeta)) :
    PowerHeightTailBound
      (actualPhysicalExpansionTail K S mu P omega psi g hpsi hB0 hB1 hboundary he zeta) := by
  have heSmall : e < 1 / 1000 := by linarith
  have hp := actualPrincipal_tail_bound K S mu nu hcomplex P omega psi hpsi
    hAllowed hunram g hB hB1 he heSmall hboundary
  have hi := actualNonprincipal_initial_tail K S mu nu hcomplex P psi hcal hunram g
  have hs := actualSmall_horizontal_tail K S mu nu hcomplex P omega psi hpsi
    hAllowed hcal hunram g hB hB1 he heSmall hboundary
  have hl := actualLarge_horizontal_tail K S mu nu hcomplex P psi hcal hunram g hzeta
  have hm := physicalScheduledModerateFaces_powerHeightTailBound K S mu nu P
    (arithmeticHighEulerData K Sset P psi) omega psi hpsi hB0 hB1 he hboundary g
    hcomplex hAllowed hB he1 hzeta.le
  exact ((((hp.add hi).add hs).add hl).add hm).add hmove

end Expansion.Project

#print axioms Expansion.Project.actualSmall_horizontal_tail
#print axioms Expansion.Project.actualLarge_horizontal_tail
#print axioms Expansion.Project.actualPhysicalExpansionTail_bound
