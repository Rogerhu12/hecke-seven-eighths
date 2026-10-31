import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityCanonicalBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityChildIntegrability
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProfileMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalCapacityKernelMass

/-!
# Arithmetic mass for the same normalized capacity choice

The normalized family chooses a deletion once. We recover the raw
capacity presentation with that exact deletion by the proved profile
homogeneity and the removed/retained cardinality identity. No second
capacity choice is made.

Consequently the literal weight and the original two-Fourier kernel
mass agree with the arithmetic mass theorem on these same children.
The calibration must already be the arithmetic calibration before
constructing the family; an arbitrary inflated cost is never replaced
after the choice.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

namespace ActualAllocatedSource.Calibration.CapacityInput

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} (I : D.CapacityInput)
variable (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
variable (bounds : Fin s.allocation.keep.card → ℝ) (hbounds : ∀ i, 0 ≤ bounds i)
variable (hfactor : ∀ ξ i, I.primeBound ξ i = amplitude ξ ^ 2 * bounds i)
variable (out : (I.normalized amplitude hpos bounds hbounds hfactor).Child)

/-- The removed prime factors and retained child profiles recover
exactly the original pre-removal degree. -/
theorem raw_cost_energy (ξ : V) :
    D.mass * I.allowance out.removed ξ *
        pairedEnergy (out.rawData ξ) out.parameters s.base (D.height ξ) =
      out.weight * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
        pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ) := by
  rw [pairedEnergy_profile_factor (out.rawData ξ) out.parameters (amplitude ξ)
    (hpos ξ) s.base (D.height ξ), out.raw_count]
  have hdata := out.data_eq_normalized_raw ξ
  change out.data ξ =
    normalizedMomentProfiles (out.rawData ξ) (amplitude ξ) (hpos ξ) at hdata
  rw [← hdata]
  have he := removed_profile_envelope_degree out.removed bounds (amplitude ξ)
    (Finset.univ \ out.removed).card s.allocation.keep.card (removed_retained_card out.removed)
  change
    (D.mass * ((∏ i ∈ out.removed, I.primeBound ξ i) * s.base ^ I.exponent)) *
        (amplitude ξ ^ (((Finset.univ \ out.removed).card + 2) * 2) *
          pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ)) =
      (D.mass * ((∏ i ∈ out.removed, bounds i) * s.base ^ I.exponent)) *
        amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
          pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ)
  simp_rw [hfactor ξ]
  calc
    _ = (D.mass * s.base ^ I.exponent) *
        ((∏ i ∈ out.removed, amplitude ξ ^ 2 * bounds i) *
          amplitude ξ ^ (((Finset.univ \ out.removed).card + 2) * 2)) *
        pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ) := by ring
    _ = _ := by rw [he]; ring

/-- A presentation of the already chosen child. Its energy statement
is recovered from the actual normalized theorem, not assumed. -/
def rawChild : D.CapacityChild I where
  removed := out.removed
  width_nonneg := out.width_nonneg
  width_le := out.width_drop
  width_lt := by linarith [out.width_drop, I.gap_pos]
  left_nonneg := out.plain_left_nonneg
  right_nonneg := out.plain_right_nonneg
  kappa_eq := rfl
  width_eq := rfl
  z_nonneg := D.restricted_z_nonneg _
  z_le := D.restricted_z_le _
  capacity := out.capacity
  zero_inherited hz := (D.restricted_zero_inherited _ hz).1
  slot_count ξ := D.restricted_count_le _ ξ
  actual_z ξ := D.restricted_z _ ξ
  mesh ξ := D.restricted_mesh _ ξ I.mesh I.mesh_bound
  theta ξ i := D.restricted_slot_in_theta _ ξ i
  energy_bound ξ := (out.energy ξ).trans_eq
    (I.raw_cost_energy amplitude hpos bounds hbounds hfactor out ξ).symm

@[simp] theorem rawChild_removed :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).removed = out.removed := rfl

@[simp] theorem rawChild_parameters :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).parameters = out.parameters := rfl

@[simp] theorem rawChild_envelopeFreeCost :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).envelopeFreeCost bounds =
      out.weight := rfl

/-- This round trip identifies every proof field by proof irrelevance.
There is only the original normalized choice. -/
theorem normalizedChild_rawChild :
    I.normalizedChild amplitude hpos bounds hbounds hfactor
      (I.rawChild amplitude hpos bounds hbounds hfactor out) = out := by
  cases out
  rfl

theorem rawChild_normalizedData (ξ : V) :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).normalizedData
        canonicalProfileNormalizationInput amplitude hpos ξ = out.data ξ := by
  rw [CapacityChild.normalizedData, canonicalProfileNormalizationInput_normalize]
  exact (out.data_eq_normalized_raw ξ).symm

end ActualAllocatedSource.Calibration.CapacityInput

namespace CanonicalCapacityKernelMass

variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)

local notation "LC" => left.arithmeticCalibration calL W BL
local notation "RC" => right.arithmeticCalibration calR W BR

variable (li : LC.CapacityInput) (ri : RC.CapacityInput)
variable (amplitudeL amplitudeR : V → ℝ)
variable (hposL : ∀ ξ, 0 < amplitudeL ξ) (hposR : ∀ ξ, 0 < amplitudeR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hbL : ∀ i, 0 ≤ boundsL i) (hbR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, li.primeBound ξ i = amplitudeL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, ri.primeBound ξ i = amplitudeR ξ ^ 2 * boundsR i)
variable (outL : (li.normalized amplitudeL hposL boundsL hbL hfL).Child)
variable (outR : (ri.normalized amplitudeR hposR boundsR hbR hfR).Child)

local notation "rawL" => li.rawChild amplitudeL hposL boundsL hbL hfL outL
local notation "rawR" => ri.rawChild amplitudeR hposR boundsR hbR hfR outR

/-- The literal normalized-family scalar equals the arithmetic scalar
for this exact deletion on each side. -/
theorem chosen_weight_eq (Z parentWidth : ℝ) (hZ : 0 < Z) :
    normalizedCapacityPairWeight outL outR left.normalizer right.normalizer Z parentWidth =
      actualCapacityPairWeight left right calL calR W BL BR rawL rawR
        boundsL boundsR Z parentWidth := by
  have hl : ‖left.normalizer‖ = (Real.sqrt left.normalizationScale)⁻¹ :=
    extraGaussNormalizer_norm _ _ _ left.gaussScale₁_pos left.gaussScale₂_pos left.gaussSlotScale_pos
  have hr : ‖right.normalizer‖ = (Real.sqrt right.normalizationScale)⁻¹ :=
    extraGaussNormalizer_norm _ _ _ right.gaussScale₁_pos right.gaussScale₂_pos right.gaussSlotScale_pos
  have hsqrt (x : ℝ) : Real.sqrt (Z ^ x) = Z ^ (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hp :
      Real.sqrt (Z ^ (outL.parameters.m + outL.parameters.q)) *
        Real.sqrt (Z ^ (outR.parameters.m + outR.parameters.q)) =
      Z ^ ((outL.parameters.m + outL.parameters.q +
        (outR.parameters.m + outR.parameters.q)) / 2) := by
    rw [hsqrt, hsqrt, ← Real.rpow_add hZ]
    congr 1
    ring
  unfold normalizedCapacityPairWeight actualCapacityPairWeight
  rw [li.rawChild_envelopeFreeCost, ri.rawChild_envelopeFreeCost,
    li.rawChild_parameters, ri.rawChild_parameters, hl, hr]
  calc
    _ = (Real.sqrt outL.weight * Real.sqrt outR.weight /
        (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
      (Real.sqrt (Z ^ (outL.parameters.m + outL.parameters.q)) *
        Real.sqrt (Z ^ (outR.parameters.m + outR.parameters.q))) / Z ^ parentWidth := by ring
    _ = _ := by rw [hp]

end CanonicalCapacityKernelMass


namespace CanonicalCapacityKernelMass

section ProductKernel

variable {U E H ι : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {k l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .left k)
variable (right : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)

local notation "LC" => left.arithmeticCalibration calL W BL
local notation "RC" => right.arithmeticCalibration calR W BR

variable (li : LC.CapacityInput) (ri : RC.CapacityInput)
variable (amplitudeL amplitudeR : WithLp 2 (U × E) → ℝ)
variable (hposL : ∀ ξ, 0 < amplitudeL ξ) (hposR : ∀ ξ, 0 < amplitudeR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hbL : ∀ i, 0 ≤ boundsL i) (hbR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, li.primeBound ξ i = amplitudeL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, ri.primeBound ξ i = amplitudeR ξ ^ 2 * boundsR i)
variable (outL : (li.normalized amplitudeL hposL boundsL hbL hfL).Child)
variable (outR : (ri.normalized amplitudeR hposR boundsR hbR hfR).Child)

local notation "rawL" => li.rawChild amplitudeL hposL boundsL hbL hfL outL
local notation "rawR" => ri.rawChild amplitudeR hposR boundsR hbR hfR outR

/-- The mass in the actual Hilbert-family kernel is exactly the mass
to which the canonical arithmetic theorem applies. The original outer
scalar, two Fourier kernels and same selected deletions are retained. -/
theorem chosen_kernel_mass_eq
    (outer Z parentWidth : ℝ) (houter : 0 ≤ outer) (hZ : 0 < Z)
    (F₁ : 𝓢(U, ℂ)) (F₂ : 𝓢(E, ℂ)) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (J₁ J₂ : ℕ)
    (hleftRadius : ∀ z, amplitudeL (WithLp.toLp 2 z) = polynomialProfileRadius B₁ J₁ J₂ z)
    (hrightRadius : ∀ z, amplitudeR (WithLp.toLp 2 z) = polynomialProfileRadius B₂ J₁ J₂ z) :
    (ENNReal.ofReal outer • normalizedCapacityPairKernel
      (Measure.map (WithLp.toLp 2) (nestedFourierMeasure F₁ F₂))
      outL outR left.normalizer right.normalizer Z parentWidth).real Set.univ =
    (kernel left right calL calR W BL BR rawL rawR boundsL boundsR
      outer Z parentWidth F₁ F₂ B₁ B₂ J₁ J₂).real Set.univ := by
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal houter]
  rw [normalizedCapacityPairKernel_nested_mass_eq B₁ B₂ J₁ J₂ J₁ J₂
    hleftRadius hrightRadius F₁ F₂ hB₁ hB₂ outL outR
    left.normalizer right.normalizer Z parentWidth hZ]
  rw [chosen_weight_eq left right calL calR W BL BR li ri
    amplitudeL amplitudeR hposL hposR boundsL boundsR hbL hbR hfL hfR outL outR
    Z parentWidth hZ]
  rw [kernel_mass left right calL calR W BL BR rawL rawR boundsL boundsR
    outer Z parentWidth houter hZ]
  change outer * (_ * (normalizedPairMeasure F₁ F₂
      left.source.allocation.keep.card right.source.allocation.keep.card B₁ B₂ J₁ J₂).real Set.univ) =
    outer * _ * (normalizedPairMeasure F₁ F₂
      left.source.allocation.keep.card right.source.allocation.keep.card B₁ B₂ J₁ J₂).real Set.univ
  ring

end ProductKernel
end CanonicalCapacityKernelMass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.rawChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.normalizedChild_rawChild
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.chosen_weight_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalCapacityKernelMass.chosen_kernel_mass_eq

