import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveFrames
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNonzero

/-!
# Passive branches on the same finite row measure

The old second allocation contributes a fixed translation through its
two plain divisors.  It is retained in the polynomial identity and then
removed from the square norm by the unit modulus of the Fourier phase.
Each nonzero passive label is subsequently bounded by its two actual
rectangle frames.  Rows, frequencies, allocation witnesses and the
continuous Fourier parameter are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveFrameEnergy

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveEnergy
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveNonzero

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

private theorem plain_mul (firstSign : ℝ)
    (I J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralLocations.plain firstSign (I * J) =
      CanonicalLiteralLocations.plain firstSign I +
        CanonicalLiteralLocations.plain firstSign J := by
  unfold CanonicalLiteralLocations.plain
  rw [CanonicalLiteralProfileData.idealNorm_mul,
    Real.log_mul (ne_of_gt (idealNorm_pos K I)) (ne_of_gt (idealNorm_pos K J)),
    neg_add, add_smul]

private theorem oriented_add (negative : Bool) (x y : WithLp 2 (ℝ × ℝ)) :
    CanonicalLiteralProfileData.orientedLocation negative (x + y) =
      CanonicalLiteralProfileData.orientedLocation negative x +
        CanonicalLiteralProfileData.orientedLocation negative y := by
  cases negative <;> simp only [CanonicalLiteralProfileData.orientedLocation,
    Bool.false_eq_true, if_false, if_true, neg_add]

variable (B : ActualColumnAllocation K k)

def plainTranslation (firstSign : ℝ) (negative : Bool) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0)) +
    CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0)))

/-- The translation is independent of every residual column. -/
theorem shifted_location (firstSign : ℝ) (negative : Bool)
    (i : AllocationColumn K B.keep.card) :
    rawSourceLocation (plainLocation₁ B firstSign negative)
      (plainLocation₂ B firstSign negative)
      (CanonicalLiteralPassiveSource.slotLocation B firstSign negative) i =
        plainTranslation B firstSign negative + canonicalPoint firstSign negative i := by
  simp only [rawSourceLocation, childCartesianLocation, plainLocation₁, plainLocation₂,
    CanonicalLiteralPassiveSource.slotLocation, plain_mul, oriented_add,
    plainTranslation, canonicalPoint, CanonicalLiteralLocations.prime]
  abel

private theorem joint_translation {J V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (columns : Finset J) (c : J → ℂ) (x : J → V) (z ξ : V) :
    jointFourierColumn columns c (fun i => z + x i) ξ =
      jointPhase ξ z * jointFourierColumn columns c x ξ := by
  simp only [jointFourierColumn, jointPhase_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Only the common Fourier phase is discarded; the coefficient and
the actual allocation carrier remain the same. -/
theorem shifted_energy {H : Type*} (rows : Finset H)
    (columns : Finset (AllocationColumn K B.keep.card))
    (weight : H → ℂ) (c : H → AllocationColumn K B.keep.card → ℂ)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    jointColumnEnergy rows columns weight c
      (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative)
        (CanonicalLiteralPassiveSource.slotLocation B firstSign negative)) ξ =
      jointColumnEnergy rows columns weight c
        (fun _ => canonicalPoint firstSign negative) ξ := by
  have hlocation : rawSourceLocation (plainLocation₁ B firstSign negative)
      (plainLocation₂ B firstSign negative)
      (CanonicalLiteralPassiveSource.slotLocation B firstSign negative) =
        fun i => plainTranslation B firstSign negative + canonicalPoint firstSign negative i :=
    funext (shifted_location B firstSign negative)
  rw [hlocation]
  simp only [jointColumnEnergy, joint_translation, norm_mul, norm_jointPhase, one_mul]

private theorem energy_scalar {H J V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (rows : Finset H) (columns : Finset J) (weight : H → ℂ)
    (c : H → J → ℂ) (x : H → J → V) (ξ : V) (z : ℂ) :
    jointColumnEnergy rows columns weight (fun h i => z * c h i) x ξ =
      ‖z‖ ^ 2 * jointColumnEnergy rows columns weight c x ξ := by
  have hcolumn (h : H) :
      jointFourierColumn columns (fun i => z * c h i) (x h) ξ =
        z * jointFourierColumn columns (c h) (x h) ξ := by
    simp only [jointFourierColumn, Finset.mul_sum, mul_assoc]
  unfold jointColumnEnergy
  simp only [hcolumn, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (paid : FixedChildCharacters K B.keep.card)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- This is the source energy of the stored frame, with its complete
original Gauss normalizer already included in the frequency term. -/
theorem frame_energy (firstSign : ℝ) (negative rectangle : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (frame W B A paid C R (if negative then .right else .left)
      M a firstSign rectangle).energy ξ =
      jointColumnEnergy (Finset.univ : Finset R.live) (branch W B A M a).columns
        (fun h => R.weight h.val * R.correlation h.val)
        (fun h => (table W B A paid).frequencyTerm (σ := σ)
          (if negative then -(R.factor C h.val) else R.factor C h.val)
          (R.extractedRow C h).element rectangle)
        (fun _ => canonicalPoint firstSign negative) ξ := by
  let c := fun h : R.live => rawSourceCoefficient (σ := σ) paid
    (if negative then -(R.factor C h.val) else R.factor C h.val)
    (R.extractedRow C h).element
    ((table W B A paid).scale₁ rectangle) ((table W B A paid).scale₂ rectangle)
    (table W B A paid).base (table W B A paid).length
    ((table W B A paid).rectangleLeftWeight rectangle)
    ((table W B A paid).rightWeight rectangle) (table W B A paid).slotWeight
  calc
    _ = ‖(table W B A paid).normalizer‖ ^ 2 *
        jointColumnEnergy (Finset.univ : Finset R.live) (branch W B A M a).columns
          (fun h => R.weight h.val * R.correlation h.val) c
          (fun _ => canonicalPoint firstSign negative) ξ := by
      rw [(frame W B A paid C R (if negative then .right else .left)
        M a firstSign rectangle).energy_eq_source]
      cases negative <;> rfl
    _ = _ := by
      change ‖(table W B A paid).normalizer‖ ^ 2 *
          jointColumnEnergy (Finset.univ : Finset R.live) (branch W B A M a).columns
            (fun h => R.weight h.val * R.correlation h.val) c
            (fun _ => canonicalPoint firstSign negative) ξ =
        jointColumnEnergy (Finset.univ : Finset R.live) (branch W B A M a).columns
          (fun h => R.weight h.val * R.correlation h.val)
          (fun h i => (table W B A paid).normalizer * c h i)
          (fun _ => canonicalPoint firstSign negative) ξ
      exact (energy_scalar _ _ _ c _ ξ _).symm

/-- The complete difference is split only after the passive source
identity and its fixed translation have been proved. -/
theorem sqrt_branch_le_frames (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy (Finset.univ : Finset R.live)
      (branch W B A M a).columns (fun h => R.weight h.val * R.correlation h.val)
      (fun h => (table W B A paid).frequencyWhole (σ := σ)
        (if negative then -(R.factor C h.val) else R.factor C h.val)
        (R.extractedRow C h).element)
      (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative)
        (CanonicalLiteralPassiveSource.slotLocation B firstSign negative)) ξ) ≤
      Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
        M a firstSign false).energy ξ) +
        Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
          M a firstSign true).energy ξ) := by
  rw [shifted_energy, frame_energy B W paid C R M a firstSign negative false ξ,
    frame_energy B W paid C R M a firstSign negative true ξ]
  exact sqrt_joint_energy_sub _ _ _ _ _ _ _

/-- Every retained label is the original label and allocation. The
nonzero filter supplies squarefreeness for the later scalar bounds. -/
theorem sqrt_passiveColumn_le_frames (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) W B paid M
        (if negative then -(R.factor C h.val) else R.factor C h.val)
        (R.extractedRow C h).element firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ nonzeroLabels W B A M,
        (Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
          M a firstSign false).energy ξ) +
          Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
            M a firstSign true).energy ξ)) := by
  refine (sqrt_passiveColumn_le_nonzero W B A M paid
    (Finset.univ : Finset R.live) (fun h => R.weight h.val * R.correlation h.val)
    (fun h => if negative then -(R.factor C h.val) else R.factor C h.val)
    (fun h => (R.extractedRow C h).element) firstSign negative ξ).trans ?_
  apply Finset.sum_le_sum
  intro a _
  exact sqrt_branch_le_frames B W paid C R M a firstSign negative ξ

end CanonicalLiteralPassiveFrameEnergy
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrameEnergy.shifted_location
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrameEnergy.shifted_energy
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrameEnergy.frame_energy
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrameEnergy.sqrt_branch_le_frames
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrameEnergy.sqrt_passiveColumn_le_frames
