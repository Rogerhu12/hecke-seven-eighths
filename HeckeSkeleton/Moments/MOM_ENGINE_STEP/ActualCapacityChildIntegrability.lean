import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedChildKernel
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileEnvelopeNormalization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Integrability of the actual capacity children

The raw family here is the literal clipped family restricted to the
single removed-slot choice made by the capacity producer.  Restriction
commutes with normalization, so finite bounds on its original atoms
prove integrability of the actual produced children.  The density still
uses all live slots before removal.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- The actual retained family before dividing its profiles. -/
def rawData (ξ : V) : MomentData F ω ψ :=
  D.restrictedClippedData (Finset.univ \ out.removed) ξ

def retainedCount : ℕ := (Finset.univ \ out.removed).card

theorem raw_count (ξ : V) : (out.rawData ξ).geometry.slotCount = out.retainedCount :=
  D.restricted_count (Finset.univ \ out.removed) ξ

theorem data_eq_normalized_raw (ξ : V) :
    out.data ξ = normalizedMomentProfiles (out.rawData ξ) (G.radius ξ) (G.radius_pos ξ) := by
  exact (normalizedMomentProfiles_restrictSlots (D.clippedData ξ)
    (lengthSelection (D.clippedData ξ) s.allocation.keep.card (D.count ξ)
      (Finset.univ \ out.removed)) (G.radius ξ) (G.radius_pos ξ)).symm

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

section SingleFourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Polynomial density costs are paid with the original Schwartz
Fourier decay, using only bounds for the individual raw summands. -/
theorem actual_weighted_fourier_normalized_integrable
    {D : V → MomentData F ω ψ} {n : ℕ}
    {hcount : ∀ ξ, (D ξ).geometry.slotCount = n}
    {a : RealParameters} {Z : ℝ} {t : V → ℝ}
    (cal : ActualFiniteFamilyControl D n hcount a Z t) (Fker : 𝓢(V, ℂ))
    (envelope : V → ℝ) (hmeas : Measurable envelope)
    (hnonneg : ∀ ξ, 0 ≤ envelope ξ) (C : ℝ) (hC : 0 ≤ C) (J : ℕ)
    (hbound : ∀ ξ, envelope ξ ≤ C * (1 + ‖ξ‖) ^ J) :
    Integrable (fun ξ => normalizedPairedEnergy (D ξ) a Z (t ξ))
      ((actualFourierMeasure Fker).withDensity (fun ξ => ENNReal.ofReal (envelope ξ))) := by
  have hac : actualFourierMeasure Fker ≪ (volume : Measure V) :=
    withDensity_absolutelyContinuous _ _
  have henergyMeas := AEStronglyMeasurable.mono_ac hac cal.energy_aestronglyMeasurable
  have hmajor := (actualFourierMeasure_polynomial_integrable Fker
    (J + cal.energyOrder)).const_mul (C * cal.energyConstant)
  have hweighted : Integrable (fun ξ => envelope ξ * pairedEnergy (D ξ) a Z (t ξ))
      (actualFourierMeasure Fker) := by
    apply hmajor.mono' (hmeas.aestronglyMeasurable.mul henergyMeas)
    exact Filter.Eventually.of_forall fun ξ => by
      have hE : 0 ≤ pairedEnergy (D ξ) a Z (t ξ) :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg ξ) hE)]
      apply (mul_le_mul (hbound ξ) (cal.energy_polynomial_bound ξ) hE
        (mul_nonneg hC (pow_nonneg (by positivity) _))).trans_eq
      rw [pow_add]
      ring
  have hraw : Integrable (fun ξ => pairedEnergy (D ξ) a Z (t ξ))
      ((actualFourierMeasure Fker).withDensity (fun ξ => ENNReal.ofReal (envelope ξ))) := by
    apply (integrable_withDensity_iff_integrable_smul' hmeas.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ : V => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul] using hweighted
  exact hraw.div_const (Z ^ (a.m + a.q))

variable {HL HR : Type*} {k l : ℕ}
variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

/-- Individual profile-radius bounds determine the full density order;
there is no additional assumption about a child moment or its mass. -/
theorem normalizedCapacityPairEnvelope_polynomial_bound
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (J₁ J₂ : ℕ)
    (hleft : ∀ ξ, «GL».radius ξ ≤ C₁ * (1 + ‖ξ‖) ^ J₁)
    (hright : ∀ ξ, GR.radius ξ ≤ C₂ * (1 + ‖ξ‖) ^ J₂) (ξ : V) :
    normalizedCapacityPairEnvelope «GL» GR ξ ≤
      (C₁ ^ (sL.allocation.keep.card + 2) * C₂ ^ (sR.allocation.keep.card + 2)) *
        (1 + ‖ξ‖) ^
          (J₁ * (sL.allocation.keep.card + 2) + J₂ * (sR.allocation.keep.card + 2)) := by
  apply (mul_le_mul
    (pow_le_pow_left₀ («GL».radius_pos ξ).le (hleft ξ) (sL.allocation.keep.card + 2))
    (pow_le_pow_left₀ (GR.radius_pos ξ).le (hright ξ) (sR.allocation.keep.card + 2))
    (pow_nonneg (GR.radius_pos ξ).le _)
    (pow_nonneg (mul_nonneg hC₁ (pow_nonneg (by positivity) _)) _)).trans_eq
  simp only [mul_pow, pow_add, pow_mul]
  ring

/-- Both actual child energies and their Cauchy product are integrable
under the same exact envelope measure. -/
theorem normalized_capacity_children_actual_integrable
    (left : «GL».Child) (right : GR.Child) (Z : ℝ) (hZ : 0 < Z)
    (calL : ActualFiniteFamilyControl left.rawData left.retainedCount left.raw_count
      left.parameters Z DL.height)
    (calR : ActualFiniteFamilyControl right.rawData right.retainedCount right.raw_count
      right.parameters Z DR.height)
    (Fker : 𝓢(V, ℂ))
    (hleftMeas : Measurable «GL».radius) (hrightMeas : Measurable GR.radius)
    (hleftOne : ∀ ξ, 1 ≤ «GL».radius ξ) (hrightOne : ∀ ξ, 1 ≤ GR.radius ξ)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ)
    (hbound : ∀ ξ, normalizedCapacityPairEnvelope «GL» GR ξ ≤ C * (1 + ‖ξ‖) ^ J) :
    let μ := (actualFourierMeasure Fker).withDensity
      (fun ξ => ENNReal.ofReal (normalizedCapacityPairEnvelope «GL» GR ξ))
    Integrable (fun ξ => normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) μ ∧
      Integrable (fun ξ => normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ)) μ ∧
      Integrable (fun ξ =>
        Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
          Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))) μ := by
  have hm : Measurable (normalizedCapacityPairEnvelope «GL» GR) :=
    (hleftMeas.pow_const _).mul (hrightMeas.pow_const _)
  have hn := fun ξ => normalizedCapacityPairEnvelope_nonneg («GL» := «GL») (GR := GR) ξ
  let μ := (actualFourierMeasure Fker).withDensity
    (fun ξ => ENNReal.ofReal (normalizedCapacityPairEnvelope «GL» GR ξ))
  have hiL : Integrable
      (fun ξ => normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) μ := by
    simp_rw [left.data_eq_normalized_raw]
    exact normalized_profile_family_integrable μ left.rawData left.retainedCount left.raw_count
      «GL».radius «GL».radius_pos hleftOne hleftMeas left.parameters Z DL.height
      (actual_weighted_fourier_normalized_integrable calL Fker _ hm hn C hC J hbound)
  have hiR : Integrable
      (fun ξ => normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ)) μ := by
    simp_rw [right.data_eq_normalized_raw]
    exact normalized_profile_family_integrable μ right.rawData right.retainedCount right.raw_count
      GR.radius GR.radius_pos hrightOne hrightMeas right.parameters Z DR.height
      (actual_weighted_fourier_normalized_integrable calR Fker _ hm hn C hC J hbound)
  have hi : Integrable (fun ξ =>
      Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
        Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))) μ := by
    have hmeas :=
      (Real.continuous_sqrt.comp_aestronglyMeasurable hiL.aestronglyMeasurable).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hiR.aestronglyMeasurable)
    apply ((hiL.add hiR).div_const 2).mono' hmeas
    exact Filter.Eventually.of_forall fun ξ => by
      have hl := normalizedPairedEnergy_nonneg (left.data ξ) left.parameters Z (DL.height ξ) hZ
      have hr := normalizedPairedEnergy_nonneg (right.data ξ) right.parameters Z (DR.height ξ) hZ
      simp only [Pi.mul_apply, Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr, sq_nonneg
        (Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) -
          Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ)))]
  exact ⟨hiL, hiR, hi⟩

/-- This is the precise child integrability premise of the second
allocation assembly, proved for its actual retained data. -/
theorem normalized_capacity_pair_actual_integrable
    (left : «GL».Child) (right : GR.Child) (Z : ℝ) (hZ : 0 < Z)
    (calL : ActualFiniteFamilyControl left.rawData left.retainedCount left.raw_count
      left.parameters Z DL.height)
    (calR : ActualFiniteFamilyControl right.rawData right.retainedCount right.raw_count
      right.parameters Z DR.height)
    (Fker : 𝓢(V, ℂ))
    (hleftMeas : Measurable «GL».radius) (hrightMeas : Measurable GR.radius)
    (hleftOne : ∀ ξ, 1 ≤ «GL».radius ξ) (hrightOne : ∀ ξ, 1 ≤ GR.radius ξ)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ)
    (hbound : ∀ ξ, normalizedCapacityPairEnvelope «GL» GR ξ ≤ C * (1 + ‖ξ‖) ^ J) :
    Integrable (fun ξ => normalizedCapacityPairEnvelope «GL» GR ξ *
      (Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
        Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))))
      (actualFourierMeasure Fker) := by
  have hm : Measurable (normalizedCapacityPairEnvelope «GL» GR) :=
    (hleftMeas.pow_const _).mul (hrightMeas.pow_const _)
  have hn := fun ξ => normalizedCapacityPairEnvelope_nonneg («GL» := «GL») (GR := GR) ξ
  have hi := (normalized_capacity_children_actual_integrable left right Z hZ calL calR Fker
    hleftMeas hrightMeas hleftOne hrightOne C hC J hbound).2.2
  have hweighted := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ : V => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] using hweighted

/-- Original finite arithmetic weights preserve the just-derived
integrability, including zero-weight labels. -/
theorem normalized_capacity_pair_actual_label_integrable
    (left : «GL».Child) (right : GR.Child) (Z : ℝ) (hZ : 0 < Z)
    (calL : ActualFiniteFamilyControl left.rawData left.retainedCount left.raw_count
      left.parameters Z DL.height)
    (calR : ActualFiniteFamilyControl right.rawData right.retainedCount right.raw_count
      right.parameters Z DR.height)
    (Fker : 𝓢(V, ℂ)) (weight : ℝ)
    (hleftMeas : Measurable «GL».radius) (hrightMeas : Measurable GR.radius)
    (hleftOne : ∀ ξ, 1 ≤ «GL».radius ξ) (hrightOne : ∀ ξ, 1 ≤ GR.radius ξ)
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ)
    (hbound : ∀ ξ, normalizedCapacityPairEnvelope «GL» GR ξ ≤ C * (1 + ‖ξ‖) ^ J) :
    Integrable (fun ξ => normalizedCapacityPairEnvelope «GL» GR ξ *
      (Real.sqrt (normalizedPairedEnergy (left.data ξ) left.parameters Z (DL.height ξ)) *
        Real.sqrt (normalizedPairedEnergy (right.data ξ) right.parameters Z (DR.height ξ))))
      (ENNReal.ofReal weight • actualFourierMeasure Fker) :=
  (normalized_capacity_pair_actual_integrable left right Z hZ calL calR Fker
    hleftMeas hrightMeas hleftOne hrightOne C hC J hbound).smul_measure ENNReal.ofReal_ne_top

end SingleFourier

section NestedFourier

variable {U E HL HR : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {k l : ℕ}
variable {sL : ActualAllocatedSource A (WithLp 2 (U × E)) HL k}
variable {sR : ActualAllocatedSource A (WithLp 2 (U × E)) HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

/-- The original two Fourier measures can be kept as a product even
when the actual source dictionary uses their genuine Hilbert product.
The envelope is computed from the original live counts before deletion. -/
theorem normalized_capacity_children_nested_actual_integrable
    (left : «GL».Child) (right : GR.Child) (Z : ℝ) (hZ : 0 < Z)
    (calL : ActualFiniteFamilyControl (fun z => left.rawData (WithLp.toLp 2 z))
      left.retainedCount (fun z => left.raw_count (WithLp.toLp 2 z))
      left.parameters Z (fun z => DL.height (WithLp.toLp 2 z)))
    (calR : ActualFiniteFamilyControl (fun z => right.rawData (WithLp.toLp 2 z))
      right.retainedCount (fun z => right.raw_count (WithLp.toLp 2 z))
      right.parameters Z (fun z => DR.height (WithLp.toLp 2 z)))
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ z, «GL».radius (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁₁ J₁₂ z)
    (hrightRadius : ∀ z, GR.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₂₁ J₂₂ z) :
    let μ := (nestedFourierMeasure F₁ F₂).withDensity
      (fun z => ENNReal.ofReal (normalizedCapacityPairEnvelope «GL» GR (WithLp.toLp 2 z)))
    Integrable (fun z => normalizedPairedEnergy (left.data (WithLp.toLp 2 z))
      left.parameters Z (DL.height (WithLp.toLp 2 z))) μ ∧
      Integrable (fun z => normalizedPairedEnergy (right.data (WithLp.toLp 2 z))
        right.parameters Z (DR.height (WithLp.toLp 2 z))) μ ∧
      Integrable (fun z =>
        Real.sqrt (normalizedPairedEnergy (left.data (WithLp.toLp 2 z)) left.parameters Z
          (DL.height (WithLp.toLp 2 z))) *
        Real.sqrt (normalizedPairedEnergy (right.data (WithLp.toLp 2 z)) right.parameters Z
          (DR.height (WithLp.toLp 2 z)))) μ := by
  have hleftData (z : U × E) : left.data (WithLp.toLp 2 z) =
      normalizedFourierChild (fun z => left.rawData (WithLp.toLp 2 z)) B₁ hB₁ J₁₁ J₁₂ z := by
    simpa only [normalizedFourierChild, hleftRadius] using
      left.data_eq_normalized_raw (WithLp.toLp 2 z)
  have hrightData (z : U × E) : right.data (WithLp.toLp 2 z) =
      normalizedFourierChild (fun z => right.rawData (WithLp.toLp 2 z)) B₂ hB₂ J₂₁ J₂₂ z := by
    simpa only [normalizedFourierChild, hrightRadius] using
      right.data_eq_normalized_raw (WithLp.toLp 2 z)
  have henvelope (z : U × E) : normalizedCapacityPairEnvelope «GL» GR (WithLp.toLp 2 z) =
      pairedProfileEnvelope B₁ B₂ sL.allocation.keep.card sR.allocation.keep.card
        J₁₁ J₁₂ J₂₁ J₂₂ z := by
    simp only [normalizedCapacityPairEnvelope, pairedProfileEnvelope, hleftRadius, hrightRadius]
  dsimp only
  simp_rw [hleftData, hrightData, henvelope]
  exact normalizedFourierChild_pair_integrable_for_counts hZ calL calR F₁ F₂
    B₁ B₂ hB₁ hB₂ J₁₁ J₁₂ J₂₁ J₂₂ sL.allocation.keep.card sR.allocation.keep.card

/-- The same actual normalized pair is integrable before absorbing
the envelope into the original product Fourier measure. -/
theorem normalized_capacity_pair_nested_actual_integrable
    (left : «GL».Child) (right : GR.Child) (Z : ℝ) (hZ : 0 < Z)
    (calL : ActualFiniteFamilyControl (fun z => left.rawData (WithLp.toLp 2 z))
      left.retainedCount (fun z => left.raw_count (WithLp.toLp 2 z))
      left.parameters Z (fun z => DL.height (WithLp.toLp 2 z)))
    (calR : ActualFiniteFamilyControl (fun z => right.rawData (WithLp.toLp 2 z))
      right.retainedCount (fun z => right.raw_count (WithLp.toLp 2 z))
      right.parameters Z (fun z => DR.height (WithLp.toLp 2 z)))
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ))
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ z, «GL».radius (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁₁ J₁₂ z)
    (hrightRadius : ∀ z, GR.radius (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₂₁ J₂₂ z) :
    Integrable (fun z : U × E => normalizedCapacityPairEnvelope «GL» GR (WithLp.toLp 2 z) *
      (Real.sqrt (normalizedPairedEnergy (left.data (WithLp.toLp 2 z)) left.parameters Z
          (DL.height (WithLp.toLp 2 z))) *
        Real.sqrt (normalizedPairedEnergy (right.data (WithLp.toLp 2 z)) right.parameters Z
          (DR.height (WithLp.toLp 2 z)))))
      (nestedFourierMeasure F₁ F₂) := by
  have hi := (normalized_capacity_children_nested_actual_integrable left right Z hZ calL calR
    F₁ F₂ B₁ B₂ hB₁ hB₂ J₁₁ J₁₂ J₂₁ J₂₂ hleftRadius hrightRadius).2.2
  have hm : Measurable
      (fun z : U × E => normalizedCapacityPairEnvelope «GL» GR (WithLp.toLp 2 z)) := by
    simpa only [normalizedCapacityPairEnvelope, hleftRadius, hrightRadius, pairedProfileEnvelope] using
      (pairedProfileEnvelope_continuous (V := U) (E := E) B₁ B₂
        sL.allocation.keep.card sR.allocation.keep.card J₁₁ J₁₂ J₂₁ J₂₂).measurable
  have hn := fun z : U × E => normalizedCapacityPairEnvelope_nonneg
    («GL» := «GL») (GR := GR) (WithLp.toLp 2 z)
  have hweighted := (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ : U × E => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] using hweighted

end NestedFourier

/-- Using a Hilbert product for the source dictionary only transports
the original product Fourier measure by its canonical homeomorphism. -/
theorem integrable_mapped_nested_fourier_iff
    {U E : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (f : WithLp 2 (U × E) → ℝ) :
    Integrable f (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂)) ↔
      Integrable (fun z => f (WithLp.toLp 2 z)) (nestedFourierMeasure F₁ F₂) :=
  (WithLp.homeomorphProd 2 U E).symm.measurableEmbedding.integrable_map_iff

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_pair_actual_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_children_actual_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_pair_actual_label_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_pair_nested_actual_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_capacity_children_nested_actual_integrable

