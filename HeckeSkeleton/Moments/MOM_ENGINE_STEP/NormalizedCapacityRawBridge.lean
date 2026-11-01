import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget

/-!
# The normalized family uses the same capacity deletion as its mass bound

The finite family has already selected a normalized child.  We recover
the raw presentation with exactly that removed set, by the exact
profile homogeneity identity.  This is a change of presentation, not a
second invocation of a capacity producer.  Its weight and parameters
are the literal ones required by the canonical arithmetic estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}
variable {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration.CapacityInput

variable {D : s.Calibration (σ := σ) ω ψ} (I : D.CapacityInput)
variable (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
variable (bounds : Fin s.allocation.keep.card → ℝ) (hbounds : ∀ i, 0 ≤ bounds i)
variable (hfactor : ∀ ξ i, I.primeBound ξ i = amplitude ξ ^ 2 * bounds i)
variable (out : (I.normalized amplitude hpos bounds hbounds hfactor).Child)

theorem normalized_child_raw_energy (ξ : V) :
    D.mass * I.allowance out.removed ξ *
      pairedEnergy (out.rawData ξ) out.parameters s.base (D.height ξ) =
        out.weight * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
          pairedEnergy (out.data ξ) out.parameters s.base (D.height ξ) := by
  have hn := pairedEnergy_profile_factor (out.rawData ξ) out.parameters
    (amplitude ξ) (hpos ξ) s.base (D.height ξ)
  rw [out.raw_count ξ, ← out.data_eq_normalized_raw ξ] at hn
  rw [hn]
  change D.mass * ((∏ i ∈ out.removed, I.primeBound ξ i) * s.base ^ I.exponent) *
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
    _ = _ := by rw [removed_retained_profile_energy]; ring

/-- All fields are recovered from the same normalized output. The
source bound follows by the preceding equality, not by a new choice. -/
def rawChild : D.CapacityChild I where
  removed := out.removed
  width_nonneg := out.width_nonneg
  width_le := out.width_drop
  width_lt := lt_of_le_of_lt out.width_drop (by linarith [I.gap_pos])
  left_nonneg := out.plain_left_nonneg
  right_nonneg := out.plain_right_nonneg
  kappa_eq := out.kappa_eq
  width_eq := out.width_eq
  z_nonneg := out.length_nonneg
  z_le := out.length_le
  capacity := out.capacity
  zero_inherited := fun h => (out.zero_length_inherited h).1
  slot_count := fun ξ => D.restricted_count_le _ ξ
  actual_z := fun ξ => D.restricted_z _ ξ
  mesh := fun ξ => D.restricted_mesh _ ξ I.mesh I.mesh_bound
  theta := fun ξ i => D.restricted_slot_in_theta _ ξ i
  energy_bound := fun ξ => (out.energy ξ).trans_eq
    (I.normalized_child_raw_energy amplitude hpos bounds hbounds hfactor out ξ).symm

theorem rawChild_removed :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).removed = out.removed := rfl

theorem rawChild_parameters :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).parameters = out.parameters := rfl

theorem rawChild_cost :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).envelopeFreeCost bounds = out.weight := rfl

theorem rawChild_data (ξ : V) :
    (I.rawChild amplitude hpos bounds hbounds hfactor out).data ξ = out.rawData ξ := rfl

end ActualAllocatedSource.Calibration.CapacityInput

section Pair

variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {l kLeft kRight : ℕ}
variable (left : SecondSideFrame (V := V) C R Ray .left k)
variable (right : SecondSideFrame (V := V) C R Ray .right l)
variable (calL : left.source.Calibration (σ := σ) ω ψ)
variable (calR : right.source.Calibration (σ := σ) ω ψ)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds)
variable (IL : (left.arithmeticCalibration calL W BL).CapacityInput)
variable (IR : (right.arithmeticCalibration calR W BR).CapacityInput)
variable (AL AR : V → ℝ) (hAL : ∀ ξ, 0 < AL ξ) (hAR : ∀ ξ, 0 < AR ξ)
variable (boundsL : Fin left.source.allocation.keep.card → ℝ)
variable (boundsR : Fin right.source.allocation.keep.card → ℝ)
variable (hBL : ∀ i, 0 ≤ boundsL i) (hBR : ∀ i, 0 ≤ boundsR i)
variable (hfL : ∀ ξ i, IL.primeBound ξ i = AL ξ ^ 2 * boundsL i)
variable (hfR : ∀ ξ i, IR.primeBound ξ i = AR ξ ^ 2 * boundsR i)
variable (lc : (IL.normalized AL hAL boundsL hBL hfL).Child)
variable (rc : (IR.normalized AR hAR boundsR hBR hfR).Child)

/-- The finite family's two original complex normalizers give exactly
the two canonical positive Gauss denominators. -/
theorem normalized_pair_weight_eq_canonical (Z parentWidth : ℝ) (hZ : 0 < Z) :
    normalizedCapacityPairWeight lc rc left.normalizer right.normalizer Z parentWidth =
      actualCapacityPairWeight left right calL calR W BL BR
        (IL.rawChild AL hAL boundsL hBL hfL lc) (IR.rawChild AR hAR boundsR hBR hfR rc)
        boundsL boundsR Z parentWidth := by
  have hn : ‖left.normalizer‖ * ‖right.normalizer‖ =
      1 / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) :=
    extraGaussNormalizer_pair_norm left.gaussScale₁ left.gaussScale₂
      right.gaussScale₁ right.gaussScale₂ left.gaussSlotScale right.gaussSlotScale
      left.gaussScale₁_pos left.gaussScale₂_pos left.gaussSlotScale_pos
      right.gaussScale₁_pos right.gaussScale₂_pos right.gaussSlotScale_pos
  have hp : Real.sqrt (Z ^ (lc.parameters.m + lc.parameters.q)) *
      Real.sqrt (Z ^ (rc.parameters.m + rc.parameters.q)) =
        Z ^ ((lc.parameters.m + lc.parameters.q + (rc.parameters.m + rc.parameters.q)) / 2) := by
    rw [← Real.sqrt_mul (Real.rpow_nonneg hZ.le _), ← Real.rpow_add hZ,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  unfold normalizedCapacityPairWeight actualCapacityPairWeight
  rw [IL.rawChild_cost, IR.rawChild_cost, IL.rawChild_parameters, IR.rawChild_parameters]
  calc
    _ = (‖left.normalizer‖ * ‖right.normalizer‖) *
        (Real.sqrt lc.weight * Real.sqrt rc.weight) *
        (Real.sqrt (Z ^ (lc.parameters.m + lc.parameters.q)) *
          Real.sqrt (Z ^ (rc.parameters.m + rc.parameters.q))) / Z ^ parentWidth := by ring
    _ = _ := by rw [hn, hp]; ring

end Pair
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.rawChild
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_pair_weight_eq_canonical
