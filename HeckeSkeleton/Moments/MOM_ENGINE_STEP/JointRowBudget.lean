import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider
import HeckeGeneral.Analysis.DecomposedZeroSlotMomentData

/-!
# Actual source rows retain their joint row and moving-mask budget

The extra moving support is a squarefree exterior ideal, tied to the
original Boolean mask at every individual ideal. The complete original
S/6 mask and coprimality to the full row ideal are retained literally.
Only the additional deletion ideal enters the moving-support budget;
the row's own radical is not charged a second time.

The child row predicate is filtered by the product of the actual row
norm and this same moving-support norm.  A source row survives because
its genuine extraction factor cancels from the original row-product
budget.  Characters, masks, polynomial atoms and profile windows are
unchanged; the finite energy comparison is proved by the existing
single-term calibration on these new actual rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

/-- The extra deletion is bound to the original individual-ideal mask.
The complete row mask already includes coprimality to the row ideal.
The support here is only the remaining deletion, fixed before the
Fourier parameters and exterior to the original fixed arithmetic set. -/
structure ActualMovingMaskRecipe (A : SArithmeticData F)
    {X : Type*} (data : X → MomentData F ω ψ) where
  support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior
  squarefree : ∀ u, Squarefree (support u).val
  mask : ∀ ξ u I, (data ξ).commonMask u I =
    (completeIdealCommonMask F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) u I &&
      decide (IsCoprime I (support u).val))

/-- The finite row enumeration remains exhaustive for its explicitly
filtered arithmetic predicate.  No polynomial factor is altered. -/
def jointRowBudgetData (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) : MomentData F ω ψ :=
  { d with
    allowedRow := fun u => d.allowedRow u ∧
      idealNorm F u * A.exteriorNorm (support u) ≤ budget
    rows := fun X => (d.rows X).filter (fun u =>
      idealNorm F u * A.exteriorNorm (support u) ≤ budget)
    rows_spec := by
      intro X u
      rw [Finset.mem_filter, d.rows_spec]
      tauto }

theorem jointRowBudgetData_allowed
    (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) (u : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hu : (jointRowBudgetData d support budget).allowedRow u) :
    idealNorm F u * A.exteriorNorm (support u) ≤ budget := hu.2

theorem jointRowBudgetData_rows_budget
    (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget X : ℝ) (u : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hu : u ∈ (jointRowBudgetData d support budget).rows X) :
    idealNorm F u * A.exteriorNorm (support u) ≤ budget :=
  (Finset.mem_filter.mp hu).2

theorem pairedRows_jointRowBudgetData
    (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) (a : RealParameters) (Z : ℝ) :
    pairedRows (jointRowBudgetData d support budget) a Z =
      (pairedRows d a Z).filter (fun u =>
        idealNorm F u * A.exteriorNorm (support u) ≤ budget) := by
  dsimp only [pairedRows, jointRowBudgetData]
  convert Finset.filter_comm
    (fun u : HeckeGeneral.Analysis.NonzeroIdeal F =>
      idealNorm F u * A.exteriorNorm (support u) ≤ budget)
    (fun u : HeckeGeneral.Analysis.NonzeroIdeal F =>
      if a.z = 0 then d.plainBackground * d.rowCharacter u ≠ 1
      else d.rowCharacter u ∉ d.theta)
    (d.rows (Z ^ (a.m + a.q))) using 1 <;> congr 1

theorem jointRowBudgetData_paired_budget
    (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) (a : RealParameters) (Z : ℝ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hu : u ∈ pairedRows (jointRowBudgetData d support budget) a Z) :
    idealNorm F u * A.exteriorNorm (support u) ≤ budget := by
  rw [pairedRows_jointRowBudgetData] at hu
  exact (Finset.mem_filter.mp hu).2

theorem jointRowBudgetData_mask
    (d : MomentData F ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal F → A.Exterior)
    (budget : ℝ) :
    (jointRowBudgetData d support budget).commonMask = d.commonMask := rfl

/-- This cancellation uses the actual frequency ideal factorization.
There is no independent extra factor Z^q. -/
theorem ActualChildRow.joint_norm_le
    {Ih : A.Exterior} {h g : A.R} {Q : ℝ}
    (r : ActualChildRow Ih h g Q) (moving : A.Exterior) (X : ℝ)
    (hX : A.exteriorNorm Ih * A.exteriorNorm moving ≤ Q * X) :
    idealNorm F r.momentIdeal * A.exteriorNorm moving ≤ X := by
  apply le_of_mul_le_mul_left _ r.factor_pos
  change Q * (A.exteriorNorm r.ideal * A.exteriorNorm moving) ≤ Q * X
  rw [← mul_assoc, ← r.norm_factor]
  exact hX

namespace ActualMovingMaskRecipe

variable {X : Type*} {data : X → MomentData F ω ψ}

/-- An original complete-row mask has no extra deletion. In particular
its row coprimality does not contribute another ideal norm. -/
def ofCompleteMask
    (hmask : ∀ ξ u I, (data ξ).commonMask u I =
      completeIdealCommonMask F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) u I) :
    ActualMovingMaskRecipe A data where
  support _ := unitExterior A
  squarefree _ := by
    simpa only [unitExterior, Ideal.one_eq_top] using
      (squarefree_one : Squarefree (1 : Ideal (𝓞 F)))
  mask ξ u I := by
    rw [hmask ξ u I]
    change _ = (_ && decide (IsCoprime I (⊤ : Ideal (𝓞 F))))
    simp only [← Ideal.one_eq_top, isCoprime_one_right, decide_true, Bool.and_true]

@[simp] theorem ofCompleteMask_support
    (hmask : ∀ ξ u I, (data ξ).commonMask u I =
      completeIdealCommonMask F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) u I)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) :
    (ofCompleteMask hmask).support u = unitExterior A := rfl

/-- The extra-deletion norm of the complete original row is one. -/
@[simp] theorem ofCompleteMask_support_norm
    (hmask : ∀ ξ u I, (data ξ).commonMask u I =
      completeIdealCommonMask F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) u I)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F) :
    A.exteriorNorm ((ofCompleteMask hmask).support u) = 1 := by
  change (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℝ) = 1
  simp only [← Ideal.one_eq_top, map_one, Nat.cast_one]

variable (M : ActualMovingMaskRecipe A data)

/-- Row restriction retains the identical actual moving-support
presentation of the unchanged common mask. -/
def withJointRowBudget (budget : ℝ) :
    ActualMovingMaskRecipe A (fun ξ => jointRowBudgetData (data ξ) M.support budget) where
  support := M.support
  squarefree := M.squarefree
  mask := M.mask

end ActualMovingMaskRecipe

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
variable {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)
variable (M : ActualMovingMaskRecipe A D.data)

/-- The source budget concerns the original ideal and the actual
moving mask of its extracted row, before division by the genuine
extraction norm.  All transformed child bounds are derived internally. -/
def withJointRowBudget
    (hsource : ∀ h ∈ s.rows,
      A.exteriorNorm (s.originalIdeal h) *
        A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
          s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q)) :
    s.Calibration (σ := σ) ω ψ where
  data ξ := jointRowBudgetData (D.data ξ) M.support
    (s.base ^ (D.parameters.m + D.parameters.q))
  parameters := D.parameters
  height := D.height
  count := D.count
  lengths := D.lengths
  left_scale := D.left_scale
  right_scale := D.right_scale
  slot_sum := D.slot_sum
  dictionary ξ h :=
    { fixedRay_mem_theta := (D.dictionary ξ h).fixedRay_mem_theta
      plain := (D.dictionary ξ h).plain
      slot := (D.dictionary ξ h).slot }
  left_support := D.left_support
  right_support := D.right_support
  slot_support := D.slot_support
  left_profile := D.left_profile
  right_profile := D.right_profile
  slot_profile := D.slot_profile
  allowed ξ h hh :=
    ⟨D.allowed ξ h hh, (s.row h).joint_norm_le (M.support (s.row h).momentIdeal)
      (s.base ^ (D.parameters.m + D.parameters.q)) (hsource h hh)⟩
  cutoff := D.cutoff
  nonexceptional := D.nonexceptional
  rowBound := D.rowBound
  rowBound_nonneg := D.rowBound_nonneg
  row_bound := D.row_bound
  scalarBound := D.scalarBound
  scalarBound_nonneg := D.scalarBound_nonneg
  scalar_bound := D.scalar_bound
  fiberBound := D.fiberBound
  fibers := D.fibers
  principal_in_theta := D.principal_in_theta
  slot_in_theta := D.slot_in_theta

variable (hsource : ∀ h ∈ s.rows,
  A.exteriorNorm (s.originalIdeal h) *
    A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
      s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q))

@[simp] theorem withJointRowBudget_mass :
    (D.withJointRowBudget M hsource).mass = D.mass := rfl

@[simp] theorem withJointRowBudget_parameters :
    (D.withJointRowBudget M hsource).parameters = D.parameters := rfl

/-- Every row of the actual child, including any row not in the
original source image, satisfies the same combined budget. -/
theorem withJointRowBudget_all_rows (ξ : V)
    (u : HeckeGeneral.Analysis.NonzeroIdeal F)
    (hu : u ∈ pairedRows ((D.withJointRowBudget M hsource).data ξ)
      (D.withJointRowBudget M hsource).parameters s.base) :
    idealNorm F u * A.exteriorNorm (M.support u) ≤
      s.base ^ (D.parameters.m + D.parameters.q) :=
  jointRowBudgetData_paired_budget (D.data ξ) M.support _ D.parameters s.base u hu

/-- The comparison is for the source's actual energy and the newly
filtered genuine child.  No previously proved energy bound is assumed. -/
theorem energy_le_withJointRowBudget (ξ : V) :
    s.energy (σ := σ) ξ ≤ D.mass *
      pairedEnergy ((D.withJointRowBudget M hsource).data ξ)
        D.parameters s.base (D.height ξ) :=
  (D.withJointRowBudget M hsource).energy_le ξ

def withJointRowBudget_maskRecipe :
    ActualMovingMaskRecipe A (D.withJointRowBudget M hsource).data :=
  M.withJointRowBudget (s.base ^ (D.parameters.m + D.parameters.q))

end ActualAllocatedSource.Calibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualChildRow.joint_norm_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualMovingMaskRecipe.ofCompleteMask
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withJointRowBudget
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.energy_le_withJointRowBudget
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withJointRowBudget_all_rows

