import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CompleteMovingRowRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotCompleteEngineOutput

/-!
# Original moving factors in the same selected engine children

The complete internal moment class retains the actual fixed moving
factors as well as the varying complete row.  Their displayed support
is charged to q.  The full deletion support, including the fixed
remaining ideal, satisfies the single joint row-width budget.

Both budgets and the exact character and mask identities are transported
from the original calibration through the already selected capacity
children.  No new removal, source, row sector, or Fourier kernel is
chosen.  In particular the fixed remaining ideal is independent of the
row, and no factor is moved into the original finite theta family.

The public admissibility below also retains the existing complete-mask
engine condition, original norm profiles, single-ideal arithmetic and
the actual injection into the original slots.  These are structural
facts; this file asserts no parent estimate or total kernel mass.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- Evaluation at the Fourier parameter changes none of the original
arithmetic choices. -/
def at (ξ : X) : CompleteMovingRowRecipe A P R (fun _ : PUnit => data ξ) where
  moving := Q.moving
  correction := Q.correction
  correction_mem _ := Q.correction_mem ξ
  sector := Q.sector
  exterior _ := Q.exterior ξ
  character _ := Q.character ξ
  remaining := Q.remaining
  mask _ := Q.mask ξ

theorem at_supportBudget (Z q : ℝ) (h : Q.SupportBudget Z q) (ξ : X) :
    (Q.at ξ).SupportBudget Z q := h

theorem at_fullJointBudget (Z width : ℝ) (h : Q.FullJointBudget Z width) (ξ : X) :
    (Q.at ξ).FullJointBudget Z width := fun _ u hu => h ξ u hu

end CompleteMovingRowRecipe

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- All allowed rows, including those exposed by removal of the last
slot, retain the original full moving arithmetic. -/
def completeMovingRowRecipe (Q : CompleteMovingRowRecipe A P R D.data) :
    CompleteMovingRowRecipe A P R out.frozenData :=
  Q.ofAllowedSubset (fun _ _ hu => hu)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem completeMovingRowRecipe_moving (Q : CompleteMovingRowRecipe A P R D.data) :
    (out.completeMovingRowRecipe Q).moving = Q.moving := rfl

theorem completeMovingRowRecipe_remaining (Q : CompleteMovingRowRecipe A P R D.data) :
    (out.completeMovingRowRecipe Q).remaining = Q.remaining := rfl

theorem completeMovingRowRecipe_supportBudget
    (Q : CompleteMovingRowRecipe A P R D.data) (Z : ℝ)
    (h : Q.SupportBudget Z D.parameters.q) :
    (out.completeMovingRowRecipe Q).SupportBudget Z out.parameters.q := h

theorem completeMovingRowRecipe_fullJointBudget
    (Q : CompleteMovingRowRecipe A P R D.data) (Z : ℝ)
    (h : Q.FullJointBudget Z (D.parameters.m + D.parameters.q)) :
    (out.completeMovingRowRecipe Q).FullJointBudget Z
      (out.parameters.m + out.parameters.q) := by
  intro ξ u hu
  exact h ξ u hu

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

/-- The full original internal class: fixed displayed moving factors,
fixed remaining mask, their combined budget, and the same analytic and
slot dictionaries needed for the next engine or reflection call. -/
structure MovingEngineChildAdmissible (A : SArithmeticData K)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
    (Q : Type*) (parent : MomentData K ω ψ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) (Z : ℝ)
    (d : MomentData K ω ψ) (a : RealParameters) : Prop where
  engine : EngineChildAdmissible A rowDomain window seminorms Z d a
  rows : ∃ recipe : CompleteMovingRowRecipe A P R (fun _ : PUnit.{1} => d),
    recipe.SupportBudget Z a.q ∧ recipe.FullJointBudget Z (a.m + a.q)
  plain_background : d.plainBackground = parent.plainBackground ∨
    d.plainBackground = parent.plainBackground⁻¹
  profiles : Nonempty (NormProfileRecipe (fun _ : PUnit.{1} => d))
  arithmetic : Nonempty (ParentArithmeticAtoms Q d)
  slots : Nonempty (SlotLengthEmbedding parent d)

namespace MovingEngineChildAdmissible

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*} {parent d : MomentData K ω ψ} {a : RealParameters} {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}
variable (h : MovingEngineChildAdmissible A P R Q parent
  rowDomain window seminorms Z d a)

def rowRecipe : CompleteMovingRowRecipe A P R (fun _ : PUnit => d) :=
  Classical.choose h.rows

theorem supportBudget : h.rowRecipe.SupportBudget Z a.q :=
  (Classical.choose_spec h.rows).1

theorem fullJointBudget : h.rowRecipe.FullJointBudget Z (a.m + a.q) :=
  (Classical.choose_spec h.rows).2

/-- Reflection receives the real complete varying row, the original
moving product, and the original finite correction separately. -/
theorem identify (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows d a Z) :
    completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u ∧
      d.rowCharacter u = h.rowRecipe.correction * h.rowRecipe.moving.character *
        completeIdealRowCharacter K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          P R (h.rowRecipe.sector u) u := by
  have hallowed := ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  exact ⟨h.rowRecipe.exterior PUnit.unit u hallowed,
    h.rowRecipe.character PUnit.unit u hallowed⟩

theorem paired_fullJointBudget (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ pairedRows d a Z) :
    idealNorm K u * idealNorm K
      (h.rowRecipe.moving.fullMaskSupport h.rowRecipe.remaining) ≤ Z ^ (a.m + a.q) :=
  h.fullJointBudget PUnit.unit u
    (((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

def slotEmbedding : SlotLengthEmbedding parent d := Classical.choice h.slots

include h in
theorem fitsMesh {mesh : ℝ} (hparent : parent.geometry.fitsMesh mesh) :
    d.geometry.fitsMesh mesh := h.slotEmbedding.fitsMesh hparent

include h in
theorem slot_count : d.geometry.slotCount ≤ parent.geometry.slotCount :=
  h.slotEmbedding.slotCount_le

def constantAtoms (next : RealParameters) (base time : ℝ) :
    ParentConstantAtoms Q d next base time :=
  (Classical.choice h.arithmetic).constantAtoms (Classical.choice h.profiles) next base time

end MovingEngineChildAdmissible

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {V Λ Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- Literal raw arithmetic and original norm windows.  All inputs
precede the active carrier and its actual capacity choices. -/
structure MovingRowInputs where
  left : ∀ b ∈ labels, CompleteMovingRowRecipe A P R (family.leftCalibration b).data
  right : ∀ b ∈ labels, CompleteMovingRowRecipe A P R (family.rightCalibration b).data
  left_support : ∀ b (hb : b ∈ labels),
    (left b hb).SupportBudget Z (family.leftCalibration b).parameters.q
  right_support : ∀ b (hb : b ∈ labels),
    (right b hb).SupportBudget Z (family.rightCalibration b).parameters.q
  left_full : ∀ b (hb : b ∈ labels), (left b hb).FullJointBudget Z
    ((family.leftCalibration b).parameters.m + (family.leftCalibration b).parameters.q)
  right_full : ∀ b (hb : b ∈ labels), (right b hb).FullJointBudget Z
    ((family.rightCalibration b).parameters.m + (family.rightCalibration b).parameters.q)

namespace MovingRowInputs

variable {family labels} (raw : family.MovingRowInputs (P := P) (R := R) labels)

def leftRecipe (b : family.active labels) :
    CompleteMovingRowRecipe A P R (family.leftData labels b) :=
  (family.leftChild labels b).completeMovingRowRecipe
    (raw.left b.val (Finset.mem_filter.mp b.property).1)

def rightRecipe (b : family.active labels) :
    CompleteMovingRowRecipe A P R (family.rightData labels b) :=
  (family.rightChild labels b).completeMovingRowRecipe
    (raw.right b.val (Finset.mem_filter.mp b.property).1)

theorem left_supportBudget (b : family.active labels) :
    (raw.leftRecipe b).SupportBudget Z (family.leftParameters labels b).q :=
  (family.leftChild labels b).completeMovingRowRecipe_supportBudget _ Z
    (raw.left_support b.val (Finset.mem_filter.mp b.property).1)

theorem right_supportBudget (b : family.active labels) :
    (raw.rightRecipe b).SupportBudget Z (family.rightParameters labels b).q :=
  (family.rightChild labels b).completeMovingRowRecipe_supportBudget _ Z
    (raw.right_support b.val (Finset.mem_filter.mp b.property).1)

theorem left_fullJointBudget (b : family.active labels) :
    (raw.leftRecipe b).FullJointBudget Z
      ((family.leftParameters labels b).m + (family.leftParameters labels b).q) :=
  (family.leftChild labels b).completeMovingRowRecipe_fullJointBudget _ Z
    (raw.left_full b.val (Finset.mem_filter.mp b.property).1)

theorem right_fullJointBudget (b : family.active labels) :
    (raw.rightRecipe b).FullJointBudget Z
      ((family.rightParameters labels b).m + (family.rightParameters labels b).q) :=
  (family.rightChild labels b).completeMovingRowRecipe_fullJointBudget _ Z
    (raw.right_full b.val (Finset.mem_filter.mp b.property).1)

end MovingRowInputs

variable {family labels} {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {window : Set ℝ}
variable {seminorms : Finset (ℕ × ℕ)}

theorem moving_left_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.MovingRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (slots : family.ParentSlotDictionaries labels parent)
    (b : family.active labels) (ξ : V) :
    MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.leftData labels b ξ) (family.leftParameters labels b) where
  engine := geometry.left_admissible b ξ
  rows := ⟨(rows.leftRecipe b).at ξ,
    (rows.leftRecipe b).at_supportBudget _ _ (rows.left_supportBudget b) ξ,
    (rows.leftRecipe b).at_fullJointBudget _ _ (rows.left_fullJointBudget b) ξ⟩
  plain_background := characters.left_background b ξ
  profiles := ⟨(profiles.leftRecipe b).at ξ⟩
  arithmetic := ⟨arithmetic.leftAtoms b ξ⟩
  slots := ⟨slots.leftEmbedding b ξ⟩

theorem moving_right_admissible
    (geometry : family.OutputGeometry labels parent a step rowDomain window seminorms)
    (rows : family.MovingRowInputs (P := P) (R := R) labels)
    (characters : family.ParentCharacterInputs labels parent)
    (profiles : family.NormProfileInputs labels)
    (arithmetic : family.ArithmeticAtomInputs labels Q)
    (slots : family.ParentSlotDictionaries labels parent)
    (b : family.active labels) (ξ : V) :
    MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      (family.rightData labels b ξ) (family.rightParameters labels b) where
  engine := geometry.right_admissible b ξ
  rows := ⟨(rows.rightRecipe b).at ξ,
    (rows.rightRecipe b).at_supportBudget _ _ (rows.right_supportBudget b) ξ,
    (rows.rightRecipe b).at_fullJointBudget _ _ (rows.right_fullJointBudget b) ξ⟩
  plain_background := characters.right_background b ξ
  profiles := ⟨(profiles.rightRecipe b).at ξ⟩
  arithmetic := ⟨arithmetic.rightAtoms b ξ⟩
  slots := ⟨slots.rightEmbedding b ξ⟩

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.completeMovingRowRecipe_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.MovingEngineChildAdmissible.paired_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.MovingEngineChildAdmissible.fitsMesh
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.moving_left_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.moving_right_admissible
