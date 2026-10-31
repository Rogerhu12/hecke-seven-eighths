import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceFactorExtraction

/-!
# Actual allocated columns become the fixed child source family

The branch data consists only of its actual divisor allocation, original
finite supports and a witness of nonemptiness.  All quotient ideals and
live slots are computed.  The complete polynomial and its row energy
are then transported to the fixed child source, with an explicit frozen
scalar.  This connects directly to fixed_child_family_energy_from_terms;
there is no aggregate polynomial or parent-to-child estimate premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

/-- The harmless value at zero is never used on an actual source or
quotient support; all subsequent reindexing proves nonvanishing. -/
def sourceMomentIdeal (I : Ideal (𝓞 F)) : HeckeGeneral.Analysis.NonzeroIdeal F :=
  if hI : I ≠ 0 then ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ else 1

@[simp] theorem sourceMomentIdeal_coe (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    sourceMomentIdeal I.val = I := by
  unfold sourceMomentIdeal
  rw [dif_pos (nonZeroDivisors.coe_ne_zero I)]
  exact Subtype.ext rfl

@[simp] theorem sourceMomentIdeal_mul_val (B I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    sourceMomentIdeal (B.val * I.val) = B * I := sourceMomentIdeal_coe (B * I)

def rawSourceCoefficient {k : ℕ} (T : FixedChildCharacters F k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x : (Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F))) : ℂ :=
  T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w
    ((sourceMomentIdeal x.1.1, sourceMomentIdeal x.1.2), x.2)

def rawSourceLocation {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V)
    (v : (Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F))) : V :=
  childCartesianLocation x₁ x₂ x
    ((sourceMomentIdeal v.1.1, sourceMomentIdeal v.1.2), v.2)

/-- A genuine nonempty inclusion-exclusion branch. -/
structure ActualColumnAllocation (F : Type) [Field F] [NumberField F] (k : ℕ) where
  divisor : Ideal (𝓞 F)
  selection : primeSupport divisor → Finset (Fin (k + 2))
  plain₁ : Finset (Ideal (𝓞 F))
  plain₂ : Finset (Ideal (𝓞 F))
  slots : Fin k → Finset (HeightOneSpectrum (𝓞 F))
  plain₁_nonzero : ∀ I ∈ plain₁, I ≠ 0
  plain₂_nonzero : ∀ I ∈ plain₂, I ≠ 0
  witness : (Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F))
  witness_mem : witness ∈ pairedAllocatedColumns divisor selection
    plain₁ plain₂ slots id id HeightOneSpectrum.asIdeal

namespace ActualColumnAllocation

variable {k : ℕ}

def keep (B : ActualColumnAllocation F k) : Finset (Fin k) :=
  AllocatedSubsupport.liveSlots B.divisor B.selection

def plainDivisor (B : ActualColumnAllocation F k) (i : Fin (k + 2)) : HeckeGeneral.Analysis.NonzeroIdeal F :=
  ⟨occurrenceDivisor B.divisor B.selection i,
    mem_nonZeroDivisors_of_ne_zero (occurrenceDivisor_ne_zero B.divisor B.selection i)⟩

def childPlain₁ (B : ActualColumnAllocation F k) : Finset (HeckeGeneral.Analysis.NonzeroIdeal F) :=
  nonzeroQuotientMomentSupport (B.plainDivisor 0).val B.plain₁

def childPlain₂ (B : ActualColumnAllocation F k) : Finset (HeckeGeneral.Analysis.NonzeroIdeal F) :=
  nonzeroQuotientMomentSupport (B.plainDivisor (Fin.succ 0)).val B.plain₂

def childSlots (B : ActualColumnAllocation F k) :
    Fin B.keep.card → Finset (HeightOneSpectrum (𝓞 F)) :=
  fun j => B.slots (SlotRestriction.index B.keep j)

def columns (B : ActualColumnAllocation F k) :
    Finset ((Ideal (𝓞 F) × Ideal (𝓞 F)) × (Fin k → HeightOneSpectrum (𝓞 F))) :=
  pairedAllocatedColumns B.divisor B.selection B.plain₁ B.plain₂ B.slots
    id id HeightOneSpectrum.asIdeal

def childColumns (B : ActualColumnAllocation F k) :
    Finset ((HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) × (Fin B.keep.card → HeightOneSpectrum (𝓞 F))) :=
  childCartesianColumns B.childPlain₁ B.childPlain₂ B.childSlots

def scalar (B : ActualColumnAllocation F k) (T : FixedChildCharacters F k) (g h' : A.R)
    (Z : ℝ) (length : Fin k → ℝ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) : ℂ :=
  T.frozenScalar (σ := σ) g h' (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0))
    Z length B.keep B.witness.2 w

section Fourier
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The actual allocation produces the child polynomial, including the
frozen character and mask and the exact shifted normalizations. -/
theorem joint_polynomial (B : ActualColumnAllocation F k)
    (T : FixedChildCharacters F k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointFourierColumn B.columns
      (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      B.scalar (σ := σ) T g h' Z length w *
        jointPhase ξ (frozenSourceLocation B.keep B.witness.2 x) *
          jointFourierColumn B.childColumns
            ((T.restrictSlots B.keep).coefficient (σ := σ) g h'
              (N₁ / idealNorm F (B.plainDivisor 0))
              (N₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Z
              (fun j => length (SlotRestriction.index B.keep j))
              (fun I => w₁ (B.plainDivisor 0 * I))
              (fun J => w₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => w (SlotRestriction.index B.keep j)))
            (childCartesianLocation
              (fun I => x₁ (B.plainDivisor 0 * I))
              (fun J => x₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => x (SlotRestriction.index B.keep j))) ξ := by
  unfold jointFourierColumn
  rw [show B.columns = pairedAllocatedColumns B.divisor B.selection
    B.plain₁ B.plain₂ B.slots id id HeightOneSpectrum.asIdeal from rfl]
  rw [actual_allocated_polynomial_nonzero_subsupport
    B.divisor B.selection B.plain₁ B.plain₂ B.slots
    B.plain₁_nonzero B.plain₂_nonzero B.witness B.witness_mem]
  have hlift₁ (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
      sourceMomentIdeal (occurrenceDivisor B.divisor B.selection 0 * I.val) =
        B.plainDivisor 0 * I := sourceMomentIdeal_mul_val (B.plainDivisor 0) I
  have hlift₂ (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
      sourceMomentIdeal (occurrenceDivisor B.divisor B.selection (Fin.succ 0) * I.val) =
        B.plainDivisor (Fin.succ 0) * I :=
    sourceMomentIdeal_mul_val (B.plainDivisor (Fin.succ 0)) I
  simp only [rawSourceCoefficient, rawSourceLocation, hlift₁, hlift₂]
  exact extracted_source_joint_polynomial T g h'
    (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0)) N₁ N₂ Z length
    B.keep B.witness.2 B.childPlain₁ B.childPlain₂ B.childSlots w₁ w₂ w x₁ x₂ x ξ

/-- All allocations act on the centered coefficient before a norm is
taken.  Its two original rectangles remain one subtraction. -/
theorem centered_joint_polynomial (B : ActualColumnAllocation F k)
    (T : FixedChildCharacters F k) (g h' : A.R)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    jointFourierColumn B.columns
      (fun y => rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w y -
        rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w y)
      (rawSourceLocation x₁ x₂ x) ξ =
      B.scalar (σ := σ) T g h' Z length w *
        jointPhase ξ (frozenSourceLocation B.keep B.witness.2 x) *
          (jointFourierColumn B.childColumns
            ((T.restrictSlots B.keep).coefficient (σ := σ) g h'
              (X₁ / idealNorm F (B.plainDivisor 0))
              (X₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Z
              (fun j => length (SlotRestriction.index B.keep j))
              (fun I => w₁ (B.plainDivisor 0 * I))
              (fun J => w₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => w (SlotRestriction.index B.keep j)))
            (childCartesianLocation
              (fun I => x₁ (B.plainDivisor 0 * I))
              (fun J => x₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => x (SlotRestriction.index B.keep j))) ξ -
          jointFourierColumn B.childColumns
            ((T.restrictSlots B.keep).coefficient (σ := σ) g h'
              (Y₁ / idealNorm F (B.plainDivisor 0))
              (Y₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Z
              (fun j => length (SlotRestriction.index B.keep j))
              (fun I => v₁ (B.plainDivisor 0 * I))
              (fun J => v₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => w (SlotRestriction.index B.keep j)))
            (childCartesianLocation
              (fun I => x₁ (B.plainDivisor 0 * I))
              (fun J => x₂ (B.plainDivisor (Fin.succ 0) * J))
              (fun j => x (SlotRestriction.index B.keep j))) ξ) := by
  have hs : ∀ (c d : _ → ℂ),
      jointFourierColumn B.columns (fun y => c y - d y) (rawSourceLocation x₁ x₂ x) ξ =
        jointFourierColumn B.columns c (rawSourceLocation x₁ x₂ x) ξ -
          jointFourierColumn B.columns d (rawSourceLocation x₁ x₂ x) ξ := by
    intro c d
    simp only [jointFourierColumn, sub_mul, Finset.sum_sub_distrib]
  rw [hs, B.joint_polynomial, B.joint_polynomial, mul_sub]

/-- Exact energy transport.  The row weight includes the squared norm of
the computed frozen scalar; the common translation has norm one. -/
theorem joint_energy {H : Type*} (B : ActualColumnAllocation F k)
    (rows : Finset H) (T : H → FixedChildCharacters F k) (g h' : H → A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : H → Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → V)
    (x : H → Fin k → HeightOneSpectrum (𝓞 F) → V) (q : H → ℂ) (ξ : V) :
    jointColumnEnergy rows B.columns q
      (fun j => rawSourceCoefficient (σ := σ) (T j) (g j) (h' j)
        N₁ N₂ Z length (w₁ j) (w₂ j) (w j))
      (fun j => rawSourceLocation (x₁ j) (x₂ j) (x j)) ξ =
      jointColumnEnergy rows B.childColumns
        (fun j => q j * B.scalar (σ := σ) (T j) (g j) (h' j) Z length (w j) *
          star (B.scalar (σ := σ) (T j) (g j) (h' j) Z length (w j)))
        (fun j => ((T j).restrictSlots B.keep).coefficient (σ := σ) (g j) (h' j)
          (N₁ / idealNorm F (B.plainDivisor 0))
          (N₂ / idealNorm F (B.plainDivisor (Fin.succ 0))) Z
          (fun i => length (SlotRestriction.index B.keep i))
          (fun I => w₁ j (B.plainDivisor 0 * I))
          (fun J => w₂ j (B.plainDivisor (Fin.succ 0) * J))
          (fun i => w j (SlotRestriction.index B.keep i)))
        (fun j => childCartesianLocation
          (fun I => x₁ j (B.plainDivisor 0 * I))
          (fun J => x₂ j (B.plainDivisor (Fin.succ 0) * J))
          (fun i => x j (SlotRestriction.index B.keep i))) ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [B.joint_polynomial]
  simp only [norm_mul, norm_star, norm_jointPhase, mul_one, mul_pow]
  ring

end Fourier
end ActualColumnAllocation

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.joint_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.centered_joint_polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.joint_energy

