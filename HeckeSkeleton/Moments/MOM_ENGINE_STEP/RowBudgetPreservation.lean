import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

/-!
# The real moving deletion budget in the final admissible family

The extra deletion ideal is tied to every value of the original Boolean
mask. The original complete S/6 and full-row mask is retained literally.
Only the extra ideal's norm is multiplied by the actual row norm before
comparison with the single child width.

Normalization, clipping, slot deletion and freezing preserve the mask
and allowed-row predicate. The budget therefore survives every actual
child operation, including the enlarged nonexceptional row predicate
when the last slot is removed. This uses all allowed rows, rather than
only the previous pairedRows set.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}

/-- A primitive arithmetic property of the actual child. It does not
assert a reflection estimate or any moment bound. -/
def ActualRowMaskAdmissible (A : SArithmeticData K)
    (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ) : Prop :=
  ∃ support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior,
    (∀ u, Squarefree (support u).val) ∧
    (∀ u I, d.commonMask u I =
      (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
        decide (IsCoprime I (support u).val))) ∧
    ∀ u, d.allowedRow u →
      idealNorm K u * A.exteriorNorm (support u) ≤ Z ^ (a.m + a.q)

/-- The final analytic/arithmetic family is fixed before the Fourier
parameter. The two constraints refer to the same actual child data. -/
def EngineChildAdmissible (A : SArithmeticData K)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) (Z : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop :=
  InFixedProfileWindow rowDomain Set.univ window seminorms d ∧
    ActualRowMaskAdmissible A d a Z

namespace ActualRowMaskAdmissible

variable {d e : MomentData K ω ψ} {a b : RealParameters} {Z : ℝ}

/-- The original complete-row recipe uses extra ideal one. Its original
row norm bound supplies the joint budget without charging the row again. -/
theorem of_completeMask
    (hmask : ∀ u I, d.commonMask u I =
      completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I)
    (hbudget : ∀ u, d.allowedRow u → idealNorm K u ≤ Z ^ (a.m + a.q)) :
    ActualRowMaskAdmissible A d a Z := by
  let M : ActualMovingMaskRecipe A (fun _ : Unit => d) :=
    ActualMovingMaskRecipe.ofCompleteMask (fun _ u I => hmask u I)
  refine ⟨M.support, M.squarefree, M.mask (), ?_⟩
  intro u hu
  have hone : A.exteriorNorm (M.support u) = 1 :=
    ActualMovingMaskRecipe.ofCompleteMask_support_norm
      (fun _ : Unit => hmask) u
  simpa only [hone, mul_one] using hbudget u hu

theorem of_mask_allowed_width (h : ActualRowMaskAdmissible A d a Z)
    (hmask : e.commonMask = d.commonMask)
    (hallowed : ∀ u, e.allowedRow u → d.allowedRow u)
    (hwidth : b.m + b.q = a.m + a.q) : ActualRowMaskAdmissible A e b Z := by
  obtain ⟨support, hsquarefree, hrecipe, hbudget⟩ := h
  refine ⟨support, hsquarefree, ?_, ?_⟩
  · intro u I
    rw [hmask]
    exact hrecipe u I
  · intro u hu
    rw [hwidth]
    exact hbudget u (hallowed u hu)

theorem normalized (h : ActualRowMaskAdmissible A d a Z)
    (B : ℝ) (hB : 0 < B) :
    ActualRowMaskAdmissible A (normalizedMomentProfiles d B hB) a Z :=
  h.of_mask_allowed_width rfl (fun _ hu => hu) rfl

theorem clipped (h : ActualRowMaskAdmissible A d a Z) (hZ : 0 < Z) :
    ActualRowMaskAdmissible A (clipPlainData d a Z hZ) (clipPlainParameters a) Z :=
  h.of_mask_allowed_width rfl (fun _ hu => hu) rfl

theorem restricted (h : ActualRowMaskAdmissible A d a Z)
    (keep : Finset (Fin d.geometry.slotCount)) :
    ActualRowMaskAdmissible A (d.restrictSlots keep) (remainingParameters d a keep) Z :=
  h.of_mask_allowed_width rfl (fun _ hu => hu) rfl

theorem frozen (h : ActualRowMaskAdmissible A d a Z) (t : ℝ) :
    ActualRowMaskAdmissible A (frozenMomentProfiles d t) a Z :=
  h.of_mask_allowed_width rfl (fun _ hu => hu) rfl

/-- Every enumerated row, at any enumeration radius, inherits the
combined budget. No independent extra factor Z^q is introduced. -/
theorem rows (h : ActualRowMaskAdmissible A d a Z) :
    ∃ support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior,
      (∀ u, Squarefree (support u).val) ∧
      (∀ u I, d.commonMask u I =
        (completeIdealCommonMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u I &&
          decide (IsCoprime I (support u).val))) ∧
      ∀ X u, u ∈ d.rows X →
        idealNorm K u * A.exteriorNorm (support u) ≤ Z ^ (a.m + a.q) := by
  obtain ⟨support, hs, hm, hb⟩ := h
  refine ⟨support, hs, hm, ?_⟩
  intro X u hu
  exact hb u ((d.rows_spec X u).mp hu).1

end ActualRowMaskAdmissible

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- The constructed retained child has exactly the same actual mask
and allowed-row budget as its raw calibration, including in zero slots. -/
theorem rowMaskAdmissible
    (M : ActualMovingMaskRecipe A D.data)
    (hbudget : ∀ ξ u, (D.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm (M.support u) ≤
        s.base ^ (D.parameters.m + D.parameters.q)) (ξ : V) :
    ActualRowMaskAdmissible A (out.frozenData ξ) out.parameters s.base := by
  refine ⟨M.support, M.squarefree, ?_, ?_⟩
  · intro u I
    change (D.data ξ).commonMask u I = _
    exact M.mask ξ u I
  · intro u hu
    change (D.data ξ).allowedRow u at hu
    change idealNorm K u * A.exteriorNorm (M.support u) ≤
      s.base ^ (D.parameters.m + D.parameters.q)
    exact hbudget ξ u hu

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ) (M : ActualMovingMaskRecipe A D.data)
variable (hsource : ∀ h ∈ s.rows,
  A.exteriorNorm (s.originalIdeal h) *
    A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
      s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q))

/-- This is the actual filtered-calibration instance. Its full allowed
row budget is proved from the engine's row filter, not requested again. -/
theorem filtered_normalized_child_admissible
    {G : (D.withJointRowBudget M hsource).NormalizedCapacityData}
    (out : G.Child) (ξ : V) :
    ActualRowMaskAdmissible A (out.frozenData ξ) out.parameters s.base := by
  apply out.rowMaskAdmissible (D.withJointRowBudget_maskRecipe M hsource)
  intro z u hu
  exact jointRowBudgetData_allowed (D.data z) M.support
    (s.base ^ (D.parameters.m + D.parameters.q)) u hu

end ActualAllocatedSource.Calibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualRowMaskAdmissible.rows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualRowMaskAdmissible.of_completeMask
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.filtered_normalized_child_admissible
