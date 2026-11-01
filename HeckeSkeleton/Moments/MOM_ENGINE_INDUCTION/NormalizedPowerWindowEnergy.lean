import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PowerWindowEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.NormalizedReflectionDensity

/-!
# Exact normalized row calibration for the common reflection kernel

The original dual row is divided by the same scalar whose amplitude was
inserted into the genuine reflection density.  This cancellation is
pointwise, before any integral or inequality.  Its finite row energy is
exactly the energy of the literal normalized child data, with the same
original row set and the same complete common mask.

Continuity and L2 follow from the actual finite polynomials.  Their
possibly large absolute bounds are used only for integrability, never
as a factor in the common kernel mass.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The exact original dual row divided by its common frequency envelope. -/
def normalizedOrdinaryDualRow (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time E0 : ℝ)
    (J : ℕ) (u : NonzeroIdeal K) (frequency : ℝ) : ℂ :=
  ((ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2) : ℝ) : ℂ)⁻¹ *
    ordinaryDualRow d a first sigma length U time u frequency

/-- The removed factor is the exact full plain-and-slot amplitude. -/
theorem normalizedOrdinaryDualRow_norm (d : MomentData K omegaCharacter psiCharacter)
    (a : RealParameters) (first : Bool) (sigma length U time E0 : ℝ)
    (hE0 : 1 ≤ E0) (J : ℕ) (u : NonzeroIdeal K) (frequency : ℝ) :
    ‖normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency‖ =
      (ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2))⁻¹ *
        ‖ordinaryDualRow d a first sigma length U time u frequency‖ := by
  rw [normalizedOrdinaryDualRow, norm_mul, norm_inv, Complex.norm_of_nonneg
    (pow_nonneg (zero_le_one.trans (one_le_ordinaryProfileEnvelope hE0 J frequency)) _)]

theorem continuous_normalizedOrdinaryDualRow
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (u : NonzeroIdeal K) :
    Continuous (normalizedOrdinaryDualRow d a first sigma length U time E0 J u) := by
  have he : Continuous (ordinaryProfileEnvelope E0 J) :=
    continuous_const.mul ((continuous_const.add continuous_abs).pow J)
  have hn (frequency : ℝ) :
      ((ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _
      (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE0 J frequency)).ne')
  exact ((Complex.continuous_ofReal.comp (he.pow (d.geometry.slotCount + 2))).inv₀ hn).mul
    (continuous_ordinaryDualRow d a first sigma length U time u)

/-- Dividing by an envelope at least one preserves the actual finite-row
L2 property in every finite positive frequency measure. -/
theorem normalizedOrdinaryDualRow_memLp
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (hU : 0 < U) (u : NonzeroIdeal K) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    MemLp (normalizedOrdinaryDualRow d a first sigma length U time E0 J u) 2 mu := by
  obtain ⟨B, hB⟩ := ordinaryDualRow_bounded d a first sigma length U time hU u
  apply MemLp.of_bound
    (continuous_normalizedOrdinaryDualRow d a first sigma length U time E0 hE0 J u).aestronglyMeasurable B
  filter_upwards [] with frequency
  rw [normalizedOrdinaryDualRow_norm d a first sigma length U time E0 hE0 J u frequency]
  calc
    _ ≤ 1 * ‖ordinaryDualRow d a first sigma length U time u frequency‖ :=
      mul_le_mul_of_nonneg_right
        (inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_ordinaryProfileEnvelope hE0 J frequency)))
        (norm_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hB frequency

/-- The whole original finite row sum equals the literal normalized child
energy.  Conjugation only reverses frequency, whose envelope is even. -/
theorem normalizedOrdinaryDualRow_energy
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (frequency : ℝ) :
    (∑ u ∈ pairedRows d a U,
      ‖normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency‖ ^ 2) =
      pairedEnergy (normalizedOrdinaryPowerChild d first sigma (-frequency) E0 hE0 J)
        (ordinaryPowerParameters a first length) U time := by
  simp_rw [normalizedOrdinaryDualRow_norm d a first sigma length U time E0 hE0 J,
    mul_pow]
  rw [← Finset.mul_sum, ordinaryDualRow_energy]
  unfold normalizedOrdinaryPowerChild
  rw [pairedEnergy_scaledMomentProfiles, ordinaryProfileEnvelope_neg]
  simp only [ordinaryPowerChild, inv_pow, pow_mul]

/-- This is numerical energy integrability; no measurable structure on
the type of whole moment models is requested or used. -/
theorem normalizedOrdinaryPowerChild_energy_integrable
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (hU : 0 < U) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Integrable (fun frequency : ℝ =>
      pairedEnergy (normalizedOrdinaryPowerChild d first sigma (-frequency) E0 hE0 J)
        (ordinaryPowerParameters a first length) U time) mu := by
  simp_rw [← normalizedOrdinaryDualRow_energy d a first sigma length U time E0 hE0 J]
  exact integrable_finsetSum _ (fun u _ =>
    (normalizedOrdinaryDualRow_memLp d a first sigma length U time E0 hE0 J hU u mu).norm.integrable_sq)

/-- The original complex integrand is unchanged.  This precedes weighted
Cauchy and does not assume any child energy estimate. -/
theorem normalizedOrdinaryDualRow_integrand
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (u : NonzeroIdeal K) (frequency : ℝ)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (b bi : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (Q X N : ℝ) :
    normalizedOrdinaryReflectionDensity K E0 J d.geometry.slotCount χ V b bi S Q X N sigma frequency *
        normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency =
      ordinaryReflectionDensity K χ V b bi S Q X N sigma frequency *
        ordinaryDualRow d a first sigma length U time u frequency := by
  have hn : ((ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _
      (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE0 J frequency)).ne')
  unfold normalizedOrdinaryReflectionDensity normalizedOrdinaryDualRow
  calc
    _ = (((ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2) : ℝ) : ℂ) *
        ((ordinaryProfileEnvelope E0 J frequency ^ (d.geometry.slotCount + 2) : ℝ) : ℂ)⁻¹) *
        (ordinaryReflectionDensity K χ V b bi S Q X N sigma frequency *
          ordinaryDualRow d a first sigma length U time u frequency) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn, one_mul]

/-- Actual normalized density times the actual normalized row is L1.
The original finite polynomial bound is used only to establish this
property, not to bound the common kernel mass. -/
theorem integrable_normalizedOrdinaryDualRow_integrand
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (hU : 0 < U) (u : NonzeroIdeal K)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    {b bi : Ideal (𝓞 K) → ℂ} (hb : IdealCoeff b) (hbi : IdealCoeff bi)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    {δ Q X N : ℝ} (hδ : 0 < δ) (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : 1 / 4 ≤ sigma) (hhi : sigma ≤ 3 / 4) :
    Integrable (fun frequency : ℝ =>
      normalizedOrdinaryReflectionDensity K E0 J d.geometry.slotCount χ V b bi S Q X N sigma frequency *
        normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency) := by
  obtain ⟨B, hB⟩ := ordinaryDualRow_bounded d a first sigma length U time hU u
  have hbounded (frequency : ℝ) :
      ‖normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency‖ ≤ B := by
    rw [normalizedOrdinaryDualRow_norm d a first sigma length U time E0 hE0 J u frequency]
    calc
      _ ≤ 1 * ‖ordinaryDualRow d a first sigma length U time u frequency‖ :=
        mul_le_mul_of_nonneg_right
          (inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_ordinaryProfileEnvelope hE0 J frequency)))
          (norm_nonneg _)
      _ ≤ B := by simpa only [one_mul] using hB frequency
  exact (integrable_normalizedOrdinaryReflectionDensity K hcomplex χ V hE0 hδ J
    d.geometry.slotCount hb hbi S hS hQ hX hN hlo hhi).mul_bdd
      (continuous_normalizedOrdinaryDualRow d a first sigma length U time E0 hE0 J u).aestronglyMeasurable
      (Filter.Eventually.of_forall hbounded)

/-- A literal original row identity can be rewritten term by term using
this equality; finite dyadic labels and both fixed lines stay unchanged. -/
theorem ordinaryDualRow_integral_normalized
    (d : MomentData K omegaCharacter psiCharacter) (a : RealParameters)
    (first : Bool) (sigma length U time E0 : ℝ) (hE0 : 1 ≤ E0)
    (J : ℕ) (u : NonzeroIdeal K) (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (b bi : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (Q X N : ℝ) :
    (∫ frequency : ℝ,
      ordinaryReflectionDensity K χ V b bi S Q X N sigma frequency *
        ordinaryDualRow d a first sigma length U time u frequency) =
      ∫ frequency : ℝ,
        normalizedOrdinaryReflectionDensity K E0 J d.geometry.slotCount χ V b bi S Q X N sigma frequency *
          normalizedOrdinaryDualRow d a first sigma length U time E0 J u frequency := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun frequency =>
    (normalizedOrdinaryDualRow_integrand d a first sigma length U time E0 hE0 J
      u frequency χ V b bi S Q X N).symm)

end HeckeSkeleton.Moments.EngineInduction
