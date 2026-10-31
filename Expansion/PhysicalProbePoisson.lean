import Expansion.PhysicalFrequencyReindex
import HeckeSkeleton.AllowedGeneratorNorm
import HeckeSkeleton.ActualProbeThetaAbsolute
import HeckeSkeleton.ActualProbeIntegrable

/-!
# The original physical Haar variable in actual Poisson summation

The input on the left below is the literal Gauss-symbol lattice sum at
`m / (t * section(Nden * X))`, on the original sixth-unit fundamental
domain.  Inverse Haar unfolding identifies it with the common orbital
profile, and actual Poisson then gives every physical row and amplifier.
Both additive zero terms remain explicit until their genuine vanishing
has been proved for the chosen test.
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
open HeckeSkeleton.HighBinActualAbsolute
open Expansion.PhysicalFourierNormalization Expansion.PhysicalFinitePoisson
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K Sset
local notation "G" => sLocalMultiplicativeGroup K Sset
local notation "T" => sLocalNormOneGroup K Sset
local notation "N" => NonzeroRingElements (Sset.integer K)

local instance : Γ.FiniteIndex := sUnit_power_range_finiteIndex K Sset 6 (by decide)

variable [MeasurableSpace T] [BorelSpace T]

def physicalPrimalRadius (den : ExteriorIdeal K Sset) (X : ℝ) (hX : 0 < X) :
    {r : ℝ // 0 < r} :=
  ⟨(exteriorNorm K Sset den * X)⁻¹,
    inv_pos.mpr (mul_pos (idealNorm_pos K den.val) hX)⟩

/-- The exact lattice sum appearing after expansion of one completed ideal. -/
def physicalGaussSymbolIntegral (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (X : ℝ) (hX : 0 < X) : ℂ :=
  ∫ t in sUnitFundamentalDomain K Sset Γ, ∑' m : N,
    (probeGauss K Sset P den (-m.val) * idealSymbol K Sset P.arithmetic A m.val) *
      additiveTest K Sset P.additive
        (sLocalNonzeroIntegerDiagonal K Sset m /
          ((t : G) * sLocalNormSection K Sset
            ⟨exteriorNorm K Sset den * X, mul_pos (idealNorm_pos K den.val) hX⟩))
    ∂sUnitHaarMeasure K Sset

theorem physicalPrimalSchwartzTerm (W : AdditiveProbeTest K Sset)
    (den : ExteriorIdeal K Sset) (X : ℝ) (hX : 0 < X) (m : N) (t : T) :
    sIntegerSchwartzTerm K Sset W.infiniteTest
        (sIntegerFiniteTestFunction K S (finiteExtension K S W))
        (physicalPrimalRadius K S den X hX) m t⁻¹ =
      additiveTest K Sset W
        (sLocalNonzeroIntegerDiagonal K Sset m /
          ((t : G) * sLocalNormSection K Sset
            ⟨exteriorNorm K Sset den * X, mul_pos (idealNorm_pos K den.val) hX⟩)) := by
  unfold sIntegerSchwartzTerm physicalPrimalRadius
  rw [← additiveTest_eq_tensor, sLocalNormSection_inv, Subgroup.coe_inv]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- Inverse unfolding is on the actual fundamental domain, without any
assumption that inversion preserves that chosen set of representatives. -/
theorem physicalGaussSymbolIntegral_eq_orbital (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (X : ℝ) (hX : 0 < X) :
    physicalGaussSymbolIntegral K S P den A X hX =
      weightedPhysicalOrbitalSeries K S Γ (additiveTest K Sset P.additive)
        (physicalPrimalRadius K S den X hX) (gaussSymbolOrbitWeight K Sset P den A) := by
  have hlocal := continuous_sIntegerFiniteTestFunction K S
    (finiteExtension K S P.additive)
    (finiteExtension_locallyConstant K S P.additive)
  have hsupport := hasCompactSupport_sIntegerFiniteTestFunction K S
    (finiteExtension K S P.additive)
    (finiteExtension_compactSupport K S P.additive)
  have hbound (q : ActualSIntegerOrbit K Sset) :
      ‖gaussSymbolOrbitWeight K Sset P den A q‖ ≤ exteriorNorm K Sset den := by
    unfold gaussSymbolOrbitWeight
    rw [norm_mul]
    exact (mul_le_mul (norm_probeGauss_le_norm K Sset P den (-q.out.val))
      (norm_idealSymbol_le_one K Sset P.arithmetic A q.out.val)
      (norm_nonneg _) (idealNorm_pos K den.val).le).trans_eq (mul_one _)
  have h := hasSum_sIntegerOrbitalProfile_weighted_inverse K Sset Γ
    P.additive.infiniteTest
    (sIntegerFiniteTestFunction K S (finiteExtension K S P.additive))
    hlocal hsupport (physicalPrimalRadius K S den X hX)
    (gaussSymbolOrbitWeight K Sset P den A) (exteriorNorm K Sset den) hbound
  have he := h.tsum_eq
  rw [← additiveTest_eq_tensor] at he
  unfold weightedPhysicalOrbitalSeries physicalGaussSymbolIntegral
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => tsum_congr (fun m => by
    rw [gaussSymbolOrbitWeight_mk, physicalPrimalSchwartzTerm]))

/-- The finite quotient modulus has exactly the two original ideal norms. -/
theorem poissonModulus_norm (P : ProbeData K Sset) (den A : ExteriorIdeal K Sset) :
    (sIntegerElementNorm K Sset
      ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩).val =
      exteriorNorm K Sset den * exteriorNorm K Sset A := by
  change sLocalProductNorm K Sset
    (sLocalNonzeroIntegerDiagonal K Sset
      (sIntegerNonzeroMul K Sset
        ⟨P.arithmetic.generator den, P.arithmetic.generator_ne_zero den⟩
        ⟨P.arithmetic.generator A, P.arithmetic.generator_ne_zero A⟩)) = _
  rw [sLocalNonzeroIntegerDiagonal_nonzeroMul, sLocalProductNorm_mul,
    thetaGenerator_productNorm, thetaGenerator_productNorm]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- Actual physical Poisson at the physical radius, retaining both zero
terms and the exact positive discriminant scalar. -/
theorem physicalGaussSymbolIntegral_eq_rows (P : ProbeData K Sset)
    (den A : ExteriorIdeal K Sset) (X : ℝ) (hX : 0 < X) :
    let C : ℂ := (physicalPoissonScalar K : ℂ) * (X : ℂ) /
      (exteriorNorm K Sset A : ℂ)
    let ρ : {r : ℝ // 0 < r} :=
      ⟨X / exteriorNorm K Sset A, div_pos hX (idealNorm_pos K A.val)⟩
    physicalGaussSymbolIntegral K S P den A X hX =
      (C * (exteriorNorm K Sset den : ℂ)) *
        (∑' u : FrequencyRow K Sset, ∑' r : ExteriorIdeal K Sset,
          physicalFrequencyProfileTerm K S μv P den A ρ u r) +
      ((sUnitHaarCovolume K Sset Γ).toReal : ℂ) *
        (C * ((exteriorNorm K Sset den : ℂ) * finitePoissonFactor K Sset P den A 0 *
          additiveFourierAtZero K Sset (fun v => μv v.val) P.additive) -
          (probeGauss K Sset P den 0 * idealSymbol K Sset P.arithmetic A 0) *
            additiveValueAtZero K S P.additive) := by
  have hd : exteriorNorm K Sset den ≠ 0 := (idealNorm_pos K den.val).ne'
  have hA : exteriorNorm K Sset A ≠ 0 := (idealNorm_pos K A.val).ne'
  have h := gaussSymbolOrbitalPoisson K S μv ν μ P den A
    (physicalPrimalRadius K S den X hX)
  rw [← physicalGaussSymbolIntegral_eq_orbital] at h
  dsimp only at h ⊢
  have hq := poissonModulus_norm K S P den A
  have hρ :
      (physicalPrimalRadius K S den X hX).val *
        (sIntegerElementNorm K Sset
          ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩).val =
        exteriorNorm K Sset A / X := by
    rw [hq]
    dsimp only [physicalPrimalRadius]
    field_simp [hd, hX.ne']
  have hrad :
      (⟨((physicalPrimalRadius K S den X hX).val *
        (sIntegerElementNorm K Sset
          ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩).val)⁻¹,
        inv_pos.mpr (mul_pos (physicalPrimalRadius K S den X hX).property
          (sIntegerElementNorm K Sset
            ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩).property)⟩ :
          {r : ℝ // 0 < r}) =
        ⟨X / exteriorNorm K Sset A, div_pos hX (idealNorm_pos K A.val)⟩ := by
    apply Subtype.ext
    rw [hρ, inv_div]
  have hC : ((physicalPrimalRadius K S den X hX).val : ℂ)⁻¹ *
      (physicalPoissonScalar K : ℂ) *
      ((sIntegerElementNorm K Sset
        ⟨poissonModulus K Sset P den A, poissonModulus_ne_zero K Sset P den A⟩).val : ℂ)⁻¹ =
      (physicalPoissonScalar K : ℂ) * (X : ℂ) / (exteriorNorm K Sset A : ℂ) := by
    rw [hq]
    dsimp only [physicalPrimalRadius]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hd, Complex.ofReal_ne_zero.mpr hA,
      Complex.ofReal_ne_zero.mpr hX.ne']
    <;> ring
  rw [hrad, hC] at h
  have hweight : weightedPhysicalOrbitalSeries K S Γ
      (additiveFourier K Sset (fun v => μv v.val) P.additive)
      ⟨X / exteriorNorm K Sset A, div_pos hX (idealNorm_pos K A.val)⟩
      (fun q => (exteriorNorm K Sset den : ℂ) * finitePoissonOrbitWeight K Sset P den A q) =
      (exteriorNorm K Sset den : ℂ) *
        weightedPhysicalOrbitalSeries K S Γ
          (additiveFourier K Sset (fun v => μv v.val) P.additive)
          ⟨X / exteriorNorm K Sset A, div_pos hX (idealNorm_pos K A.val)⟩
          (finitePoissonOrbitWeight K Sset P den A) := by
    simp only [weightedPhysicalOrbitalSeries, mul_assoc, tsum_mul_left]
  rw [hweight, physicalFourierOrbitSeries_eq_rows K S μv ν] at h
  simpa only [mul_assoc] using h

end Expansion.Project

#print axioms Expansion.Project.physicalGaussSymbolIntegral_eq_orbital
#print axioms Expansion.Project.physicalGaussSymbolIntegral_eq_rows
