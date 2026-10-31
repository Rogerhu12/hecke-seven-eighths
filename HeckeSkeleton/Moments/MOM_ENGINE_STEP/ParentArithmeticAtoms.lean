import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentConstantSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormIndependentProfiles

/-!
# Separate original arithmetic atoms from their norm profiles

The arithmetic identities concern one ideal or one prime and include
the complete Boolean mask and its zero extension.  They hold on every
allowed row, not just a previously selected finite physical row set.
The norm recipe then constructs ParentConstantAtoms at every time and
every pair of independent comparison scales.

The orbit type and its phase arrays remain original MOM_BASE data.
Their identification with the genuine periodic columns is still the
separate single-column arithmetic dictionary used by actualCalibration.
No mixed Gram identity, convergence or moment estimate is a field here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

structure ParentArithmeticAtoms (Q : Type*) (d : MomentData K ω ψ) where
  rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q
  leftArithmetic : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightArithmetic : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primeArithmetic : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  leftPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primePhase : Q → Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  left : ∀ u, d.allowedRow u → ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      leftArithmetic I * leftPhase (rowMap u) I
  right : ∀ u, d.allowedRow u → ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I * maskValue d u I.val =
      rightArithmetic I * rightPhase (rowMap u) I
  prime : ∀ u, d.allowedRow u → ∀ i p,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p * maskValue d u p.asIdeal =
      primeArithmetic i p * primePhase (rowMap u) i p

namespace ParentArithmeticAtoms

variable {Q : Type*} {d : MomentData K ω ψ}
variable (T : ParentArithmeticAtoms Q d)

/-- Transport only the literal original arithmetic fields.  A slot is
selected by its actual original index and the allowed rows may shrink. -/
def transport (other : MomentData K ω ψ)
    (index : Fin other.geometry.slotCount → Fin d.geometry.slotCount)
    (allowed : ∀ u, other.allowedRow u → d.allowedRow u)
    (background : other.plainBackground = d.plainBackground)
    (row : other.rowCharacter = d.rowCharacter)
    (mask : other.commonMask = d.commonMask)
    (slot : ∀ i, other.slotCoefficient i = d.slotCoefficient (index i)) :
    ParentArithmeticAtoms Q other where
  rowMap := T.rowMap
  leftArithmetic := T.leftArithmetic
  rightArithmetic := T.rightArithmetic
  primeArithmetic i := T.primeArithmetic (index i)
  leftPhase := T.leftPhase
  rightPhase := T.rightPhase
  primePhase q i := T.primePhase q (index i)
  left u hu I := by
    simpa only [background, row, maskValue, mask] using T.left u (allowed u hu) I
  right u hu I := by
    simpa only [background, row, maskValue, mask] using T.right u (allowed u hu) I
  prime u hu i p := by
    simpa only [row, slot, maskValue, mask] using T.prime u (allowed u hu) (index i) p

def clipped (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    ParentArithmeticAtoms Q (clipPlainData d a Z hZ) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

def normalized (B : ℝ) (hB : 0 < B) :
    ParentArithmeticAtoms Q (normalizedMomentProfiles d B hB) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

def frozen (t : ℝ) : ParentArithmeticAtoms Q (frozenMomentProfiles d t) :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

def restricted (keep : Finset (Fin d.geometry.slotCount)) :
    ParentArithmeticAtoms Q (d.restrictSlots keep) :=
  T.transport _ (selectedSlotIndex keep) (fun _ h => h) rfl rfl rfl (fun _ => rfl)

def jointRows {A : SArithmeticData K}
    (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior) (budget : ℝ) :
    ParentArithmeticAtoms Q (jointRowBudgetData d support budget) :=
  T.transport _ id (fun _ h => h.1) rfl rfl rfl (fun _ => rfl)

def withPlainTests (left right : IdealTest K) :
    ParentArithmeticAtoms (ω := ω) (ψ := ψ) Q { d with plainTest₁ := left, plainTest₂ := right } :=
  T.transport _ id (fun _ h => h) rfl rfl rfl (fun _ => rfl)

/-- The source atoms are constructed from the original per-ideal
arithmetic and norm-profile identities.  In particular the whole
centered coefficient is not a primitive calibration field. -/
def constantAtoms (W : NormProfileRecipe (fun _ : PUnit => d))
    (a : RealParameters) (Z t : ℝ) : ParentConstantAtoms Q d a Z t where
  rowMap := T.rowMap
  leftArithmetic := T.leftArithmetic
  rightArithmetic := T.rightArithmetic
  primeArithmetic := T.primeArithmetic
  leftPhase := T.leftPhase
  rightPhase := T.rightPhase
  primePhase := T.primePhase
  leftProfile := W.left PUnit.unit t
  rightProfile := W.right PUnit.unit t
  left_arithmetic u hu := T.left u ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  right_arithmetic u hu := T.right u ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  prime_arithmetic u hu := T.prime u ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  left_profile u hu y := W.left_eq PUnit.unit u
    ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1 t y
  right_profile u hu y := W.right_eq PUnit.unit u
    ((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1 t y

end ParentArithmeticAtoms

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ} {G : D.NormalizedCapacityData}
variable (out : G.Child)

/-- The original arithmetic dictionary follows the same actual removed
set.  Its phase arrays and zero masks are not changed by normalization. -/
def parentArithmeticAtoms (T : ∀ ξ, ParentArithmeticAtoms Q (D.data ξ))
    (ξ : V) : ParentArithmeticAtoms Q (out.frozenData ξ) :=
  ((((T ξ).clipped D.parameters s.base (zero_lt_one.trans s.base_gt_one)).normalized
      (G.radius ξ) (G.radius_pos ξ)).restricted
        (lengthSelection (G.normalizedData ξ) s.allocation.keep.card (D.count ξ)
          (Finset.univ \ out.removed))).frozen (D.height ξ)

def parentConstantAtoms (T : ∀ ξ, ParentArithmeticAtoms Q (D.data ξ))
    (W : NormProfileRecipe D.data) (ξ : V) (a : RealParameters) (Z t : ℝ) :
    ParentConstantAtoms Q (out.frozenData ξ) a Z t :=
  (out.parentArithmeticAtoms T ξ).constantAtoms ((out.normProfileRecipe W).at ξ) a Z t

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

namespace ActualNormalizedPairFamily

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V Λ Q : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- The raw one-ideal/one-prime dictionary precedes the next source
call.  It contains neither a child moment nor an admissibility field. -/
structure ArithmeticAtomInputs (Q : Type*) where
  left : ∀ b ∈ labels, ∀ ξ, ParentArithmeticAtoms Q ((family.leftCalibration b).data ξ)
  right : ∀ b ∈ labels, ∀ ξ, ParentArithmeticAtoms Q ((family.rightCalibration b).data ξ)

namespace ArithmeticAtomInputs

variable {family labels} (raw : family.ArithmeticAtomInputs labels Q)

def leftAtoms (b : family.active labels) (ξ : V) :
    ParentArithmeticAtoms Q (family.leftData labels b ξ) :=
  (family.leftChild labels b).parentArithmeticAtoms
    (raw.left b.val (Finset.mem_filter.mp b.property).1) ξ

def rightAtoms (b : family.active labels) (ξ : V) :
    ParentArithmeticAtoms Q (family.rightData labels b ξ) :=
  (family.rightChild labels b).parentArithmeticAtoms
    (raw.right b.val (Finset.mem_filter.mp b.property).1) ξ

end ArithmeticAtomInputs
end ActualNormalizedPairFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentArithmeticAtoms.constantAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.NormalizedCapacityData.Child.parentConstantAtoms
