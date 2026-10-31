import Expansion.PhysicalProbePoisson
import Expansion.PhysicalAdditiveOrigin
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The completed physical probe before Mellin inversion

The completed Gaussian theta coefficient is kept literally, with its
squarefree and whole-index masks.  Its proved absolute ideal summability
and the actual Schwartz orbital summability justify the interchange of
completed ideals with the original orbit sum.  The outer denominator
series has the original annular finite support.

Thus the original physical Haar integral is assembled from the actual
Gauss-symbol Poisson identities.  The only zero-transform condition used
at the final endpoint is the existing physical test's `fourier_zero`;
the original additive-origin term is proved zero from the test itself.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualDenominatorAbsoluteDraft
open HeckeSkeleton.HighBinActualAbsolute
open Expansion.PhysicalFourierNormalization Expansion.PhysicalFinitePoisson
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K Sset
local notation "G" => sLocalMultiplicativeGroup K Sset
local notation "T" => sLocalNormOneGroup K Sset
local notation "N" => NonzeroRingElements (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
local notation "CN" => ExteriorIdeal K Sset × ExteriorIdeal K Sset
local notation "O" => ActualSIntegerOrbit K Sset

local instance : Γ.FiniteIndex := sUnit_power_range_finiteIndex K Sset 6 (by decide)

/-- At m=1 the actual symbol is one, so this is precisely the original
completed coefficient before its S-integer symbol is inserted. -/
def physicalCompletedWeight (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (Z : ℝ) (cn : CN) : ℂ :=
  completedTerm K Sset P.arithmetic (thetaPeriod K Sset P ψ) 1
    (primeSetIdeal K Sset ∅) Q logGaussianProfile Z cn

theorem completedTerm_eq_physicalCompletedWeight (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) (Z : ℝ)
    (m : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)
    (cn : CN) :
    completedTerm K Sset P.arithmetic (thetaPeriod K Sset P ψ) m
        (primeSetIdeal K Sset ∅) Q logGaussianProfile Z cn =
      physicalCompletedWeight K S P ψ Q Z cn *
        idealSymbol K Sset P.arithmetic (completedIdeal K Sset cn.1 cn.2) m := by
  have hOne (A : ExteriorIdeal K Sset) : idealSymbol K Sset P.arithmetic A 1 = 1 := by
    simp only [idealSymbol, sIntegerSexticIdealEvaluation_one]
  unfold physicalCompletedWeight completedTerm
  dsimp only
  split_ifs <;> simp only [hOne, mul_one, zero_mul] <;> ring

theorem summable_norm_physicalCompletedWeight (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) {Z : ℝ} (hZ : 0 < Z) :
    Summable (fun cn : CN => ‖physicalCompletedWeight K S P ψ Q Z cn‖) :=
  absolutelySummable_completedTerm K Sset P.arithmetic (thetaPeriod K Sset P ψ) 1
    (primeSetIdeal K Sset ∅) Q hZ

theorem norm_gaussSymbolOrbitWeight_le (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (q : O) :
    ‖gaussSymbolOrbitWeight K Sset P den A q‖ ≤ exteriorNorm K Sset den := by
  unfold gaussSymbolOrbitWeight
  rw [norm_mul]
  exact (mul_le_mul (norm_probeGauss_le_norm K Sset P den (-q.out.val))
    (norm_idealSymbol_le_one K Sset P.arithmetic A q.out.val)
    (norm_nonneg _) (idealNorm_pos K den.val).le).trans_eq (mul_one _)

def physicalCompletedOrbitWeight (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (Z : ℝ) (den : ExteriorIdeal K Sset) (q : O) : ℂ :=
  ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
    gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q

theorem physicalCompletedOrbitWeight_mk (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (Z : ℝ) (den : ExteriorIdeal K Sset) (m : N) :
    physicalCompletedOrbitWeight K S P ψ Q Z den (Quotient.mk _ m) =
      probeGauss K Sset P den (-m.val) *
        completedThetaSum K Sset P.arithmetic (thetaPeriod K Sset P ψ) m.val
          (primeSetIdeal K Sset ∅) Q logGaussianProfile Z := by
  unfold physicalCompletedOrbitWeight completedThetaSum
  simp_rw [gaussSymbolOrbitWeight_mk, completedTerm_eq_physicalCompletedWeight]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro cn
  ring

theorem summable_norm_physicalCompletedOrbitWeight_terms (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) {Z : ℝ} (hZ : 0 < Z)
    (den : ExteriorIdeal K Sset) (q : O) :
    Summable (fun cn : CN => ‖physicalCompletedWeight K S P ψ Q Z cn *
      gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q‖) := by
  apply ((summable_norm_physicalCompletedWeight K S P ψ Q hZ).mul_left
    (exteriorNorm K Sset den)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro cn
  rw [norm_mul, mul_comm (exteriorNorm K Sset den)]
  exact mul_le_mul_of_nonneg_left (norm_gaussSymbolOrbitWeight_le K S P den _ q)
    (norm_nonneg _)

theorem norm_physicalCompletedOrbitWeight_le (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) {Z : ℝ} (hZ : 0 < Z)
    (den : ExteriorIdeal K Sset) (q : O) :
    ‖physicalCompletedOrbitWeight K S P ψ Q Z den q‖ ≤
      exteriorNorm K Sset den * ∑' cn : CN, ‖physicalCompletedWeight K S P ψ Q Z cn‖ := by
  have hsum := summable_norm_physicalCompletedOrbitWeight_terms K S P ψ Q hZ den q
  unfold physicalCompletedOrbitWeight
  apply (norm_tsum_le_tsum_norm hsum).trans
  rw [← tsum_mul_left]
  apply hsum.tsum_le_tsum _
    ((summable_norm_physicalCompletedWeight K S P ψ Q hZ).mul_left (exteriorNorm K Sset den))
  intro cn
  rw [norm_mul, mul_comm (exteriorNorm K Sset den)]
  exact mul_le_mul_of_nonneg_left (norm_gaussSymbolOrbitWeight_le K S P den _ q)
    (norm_nonneg _)

variable [MeasurableSpace T] [BorelSpace T]

theorem summable_norm_physicalPrimalProfile (test : AdditiveProbeTest K Sset)
    (ρ : {r : ℝ // 0 < r}) :
    Summable (fun q : O => ‖sUnitOrbitalProfile K Sset (additiveTest K Sset test)
      ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ q).val,
        mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ q).property⟩‖) := by
  have hc := continuous_sIntegerFiniteTestFunction K S (finiteExtension K S test)
    (finiteExtension_locallyConstant K S test)
  have hs := hasCompactSupport_sIntegerFiniteTestFunction K S (finiteExtension K S test)
    (finiteExtension_compactSupport K S test)
  have h := (hasSum_sIntegerOrbitalProfile_weighted K Sset Γ test.infiniteTest
    (sIntegerFiniteTestFunction K S (finiteExtension K S test)) hc hs ρ (fun _ => 1)
    1 (fun _ => by simp)).summable.norm
  simpa only [one_mul, ← additiveTest_eq_tensor] using h

/-- The two infinite primal indices commute only after the absolute
product majorant has been established from genuine theta and orbit sums. -/
theorem physicalCompletedOrbitalSeries_eq_ideal_sum (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset)) {Z : ℝ} (hZ : 0 < Z)
    (den : ExteriorIdeal K Sset) (ρ : {r : ℝ // 0 < r}) :
    weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive) ρ
        (physicalCompletedOrbitWeight K S P ψ Q Z den) =
      ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
        weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive) ρ
          (gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2)) := by
  let profile : O → ℂ := fun q => sUnitOrbitalProfile K Sset (additiveTest K Sset P.additive)
    ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ q).val,
      mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ q).property⟩
  have hc := summable_norm_physicalCompletedWeight K S P ψ Q hZ
  have hp : Summable (fun q : O => ‖profile q‖) := summable_norm_physicalPrimalProfile K S P.additive ρ
  have hprod : Summable (fun x : CN × O =>
      physicalCompletedWeight K S P ψ Q Z x.1 *
        gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset x.1.1 x.1.2) x.2 *
          profile x.2) := by
    apply ((hc.mul_of_nonneg hp (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left
      (exteriorNorm K Sset den)).of_norm_bounded
    intro x
    simp only [norm_mul]
    calc
      _ ≤ (‖physicalCompletedWeight K S P ψ Q Z x.1‖ * exteriorNorm K Sset den) * ‖profile x.2‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_gaussSymbolOrbitWeight_le K S P den _ x.2)
            (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  change (∑' q : O, (∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
    gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q) * profile q) =
      ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
        ∑' q : O, gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q * profile q
  calc
    _ = ∑' q : O, ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
        gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q * profile q := by
      apply tsum_congr
      intro q
      rw [tsum_mul_right]
    _ = ∑' cn : CN, ∑' q : O, physicalCompletedWeight K S P ψ Q Z cn *
        gaussSymbolOrbitWeight K Sset P den (completedIdeal K Sset cn.1 cn.2) q * profile q :=
      hprod.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro cn
      simp only [mul_assoc, tsum_mul_left]

def physicalDenominatorPrefactor (P : ProbeData K Sset) (X Y : ℝ)
    (den : ExteriorIdeal K Sset) : ℂ :=
  (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K Sset den / Y) *
    (Real.sqrt (exteriorNorm K Sset den * X) : ℂ)⁻¹ *
      (Real.sqrt (exteriorNorm K Sset den) : ℂ)⁻¹

theorem probeDenominatorTerm_eq_completedOrbitWeight (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (den : ExteriorIdeal K Sset) (t : T) :
    probeDenominatorTerm K Sset P ψ Q X Y Z t den =
      physicalDenominatorPrefactor K S P X Y den *
        ∑' m : N, physicalCompletedOrbitWeight K S P ψ Q Z den (Quotient.mk _ m) *
          additiveTest K Sset P.additive
            (sLocalNonzeroIntegerDiagonal K Sset m /
              ((t : G) * sLocalNormSection K Sset
                ⟨exteriorNorm K Sset den * X, mul_pos (idealNorm_pos K den.val) hX⟩)) := by
  have hscale : 0 < exteriorNorm K Sset den * X := mul_pos (idealNorm_pos K den.val) hX
  let L : ℂ := (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K Sset den / Y) *
    (Real.sqrt (exteriorNorm K Sset den * X) : ℂ)⁻¹
  change L * (∑' m : N, probeRowTerm K Sset P ψ Q X Z t den m) =
    (L * (Real.sqrt (exteriorNorm K Sset den) : ℂ)⁻¹) * _
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [physicalCompletedOrbitWeight_mk]
  simp only [probeRowTerm, dif_pos hscale]
  ring

theorem physicalDenominatorIntegral_eq_completedGauss (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (den : ExteriorIdeal K Sset) :
    (∫ t in sUnitFundamentalDomain K Sset Γ,
      probeDenominatorTerm K Sset P ψ Q X Y Z t den ∂sUnitHaarMeasure K Sset) =
      physicalDenominatorPrefactor K S P X Y den *
        ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
          physicalGaussSymbolIntegral K S P den (completedIdeal K Sset cn.1 cn.2) X hX := by
  have hc := continuous_sIntegerFiniteTestFunction K S (finiteExtension K S P.additive)
    (finiteExtension_locallyConstant K S P.additive)
  have hs := hasCompactSupport_sIntegerFiniteTestFunction K S (finiteExtension K S P.additive)
    (finiteExtension_compactSupport K S P.additive)
  have h := hasSum_sIntegerOrbitalProfile_weighted_inverse K Sset Γ P.additive.infiniteTest
    (sIntegerFiniteTestFunction K S (finiteExtension K S P.additive)) hc hs
    (physicalPrimalRadius K S den X hX) (physicalCompletedOrbitWeight K S P ψ Q Z den)
    (exteriorNorm K Sset den * ∑' cn : CN, ‖physicalCompletedWeight K S P ψ Q Z cn‖)
    (norm_physicalCompletedOrbitWeight_le K S P ψ Q hZ den)
  have he := h.tsum_eq
  rw [← additiveTest_eq_tensor] at he
  simp_rw [probeDenominatorTerm_eq_completedOrbitWeight K S P ψ Q X Y Z hX]
  rw [integral_const_mul]
  congr 1
  calc
    _ = weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive)
        (physicalPrimalRadius K S den X hX) (physicalCompletedOrbitWeight K S P ψ Q Z den) := by
      rw [weightedPhysicalOrbitalSeries, he]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => tsum_congr (fun m => by
        rw [physicalPrimalSchwartzTerm]))
    _ = _ := by
      rw [physicalCompletedOrbitalSeries_eq_ideal_sum K S P ψ Q hZ]
      apply tsum_congr
      intro cn
      rw [physicalGaussSymbolIntegral_eq_orbital]

/-- The outer integral/sum exchange uses the actual annular finite support. -/
theorem physicalProbe_eq_sum_denominatorIntegrals (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hY : 0 < Y) :
    physicalProbe K Sset P ψ Q X Y Z =
      ∑' den : ExteriorIdeal K Sset, ∫ t in sUnitFundamentalDomain K Sset Γ,
        probeDenominatorTerm K Sset P ψ Q X Y Z t den ∂sUnitHaarMeasure K Sset := by
  have hfinite : Set.Finite
      ((fun den : ExteriorIdeal K Sset => den.val) ⁻¹'
        (dyadicIdealSupport K (P.denominator.upper * Y / 2) : Set (NonzeroIdeal K))) :=
    (dyadicIdealSupport K (P.denominator.upper * Y / 2)).finite_toSet.preimage
      Subtype.val_injective.injOn
  let D := hfinite.toFinset
  have hz (den : ExteriorIdeal K Sset) (hden : den ∉ D) (t : T) :
      probeDenominatorTerm K Sset P ψ Q X Y Z t den = 0 := by
    by_contra hne
    exact hden (hfinite.mem_toFinset.mpr
      (probeDenominatorTerm_support_subset K Sset P ψ Q X Y Z hY t hne))
  have hsum (t : T) : probeIntegrand K Sset P ψ Q X Y Z t =
      ∑ den ∈ D, probeDenominatorTerm K Sset P ψ Q X Y Z t den :=
    tsum_eq_sum (fun den hden => hz den hden t)
  have hC := isCompact_closure_sUnitFundamentalDomain K Sset Γ
  have hint (den : ExteriorIdeal K Sset) : IntegrableOn
      (fun t => probeDenominatorTerm K Sset P ψ Q X Y Z t den)
      (sUnitFundamentalDomain K Sset Γ) (sUnitHaarMeasure K Sset) :=
    (ContinuousOn.integrableOn_compact hC
      (continuousOn_probeDenominatorTerm K Sset P ψ Q X Y Z den _ hC)).mono_set subset_closure
  unfold physicalProbe
  simp_rw [hsum]
  rw [integral_finset_sum D (fun den _ => hint den)]
  symm
  apply tsum_eq_sum
  intro den hden
  simp only [hz den hden, integral_zero]

theorem physicalProbe_eq_completedGauss (P : ProbeData K Sset)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      ∑' den : ExteriorIdeal K Sset, physicalDenominatorPrefactor K S P X Y den *
        ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
          physicalGaussSymbolIntegral K S P den (completedIdeal K Sset cn.1 cn.2) X hX := by
  rw [physicalProbe_eq_sum_denominatorIntegrals K S P ψ Q X Y Z hY]
  exact tsum_congr (physicalDenominatorIntegral_eq_completedGauss K S P ψ Q X Y Z hX hZ)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Full literal physical probe after genuine Poisson, before Mellin.
Every completed ideal, denominator, row and amplifier is retained. -/
theorem physicalProbe_eq_completedFrequencyProfiles (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      ∑' den : ExteriorIdeal K Sset, physicalDenominatorPrefactor K S P X Y den *
        ∑' cn : CN, physicalCompletedWeight K S P ψ Q Z cn *
          (((physicalPoissonScalar K : ℂ) * (X : ℂ) /
              (exteriorNorm K Sset (completedIdeal K Sset cn.1 cn.2) : ℂ) *
              (exteriorNorm K Sset den : ℂ)) *
            ∑' u : FrequencyRow K Sset, ∑' r : ExteriorIdeal K Sset,
              physicalFrequencyProfileTerm K S μv P den (completedIdeal K Sset cn.1 cn.2)
                ⟨X / exteriorNorm K Sset (completedIdeal K Sset cn.1 cn.2),
                  div_pos hX (idealNorm_pos K _)⟩ u r) := by
  rw [physicalProbe_eq_completedGauss K S P ψ Q X Y Z hX hY hZ]
  apply tsum_congr
  intro den
  congr 1
  apply tsum_congr
  intro cn
  have hp := physicalGaussSymbolIntegral_eq_rows K S μv ν μ P den
    (completedIdeal K Sset cn.1 cn.2) X hX
  dsimp only at hp
  simp only [hzero, additiveValueAtZero_eq_zero, mul_zero, sub_zero, add_zero] at hp
  rw [hp]

end Expansion.Project

#print axioms Expansion.Project.physicalProbe_eq_completedFrequencyProfiles
