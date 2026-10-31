import HeckeSkeleton.Moments.MOM_INV_STEP.BackgroundCycle
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.MarkPriority

/-!
# Literal canonical child columns at a fixed puncture triple

The data of a child contain its original marks, a surviving subset, one
live Hecke background and one norm test. None can depend on its moving
row or averaged label. There is no additional residual coefficient on n.
The puncture is the actual old puncture times rad(q₀ t′ r).

Ideal rows are extended by zero outside the exterior ideals, so positive
row and label ranges may be enlarged without inventing a generator for
an inadmissible ideal. A sector is represented by its original S-unit.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => Set.integer S K
local notation "Ext" => ExteriorIdeal K S

def IsExterior (I : Ideal (𝓞 K)) : Prop :=
  I ≠ 0 ∧ ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S

def exteriorOf (I : Ideal (𝓞 K)) (hI : IsExterior K S I) : Ext :=
  ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI.1⟩, hI.2⟩

theorem exterior_isExterior (I : Ext) : IsExterior K S I.val.val :=
  ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩

variable (D : ThetaArithmeticData K S)

def labelRow (n : Ext) (f : Ideal (𝓞 K)) : ℂ :=
  if hf : IsExterior K S f then idealSymbol K S D n (D.generator (exteriorOf K S f hf)) else 0

def sectorRow {Sector : Type*} (sectorUnit : Sector → S.unit K)
    (n : Ext) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  if hk : IsExterior K S k.1 then
    idealSymbol K S D n ((S.unitEquivUnitsInteger K (sectorUnit k.2)).val *
      D.generator (exteriorOf K S k.1 hk)) else 0

theorem labelRow_exterior (n f : Ext) :
    labelRow K S D n f.val.val = idealSymbol K S D n (D.generator f) := by
  rw [labelRow, dif_pos (exterior_isExterior K S f)]
  rfl

theorem sectorRow_exterior {Sector : Type*} (sectorUnit : Sector → S.unit K)
    (n k : Ext) (s : Sector) :
    sectorRow K S D sectorUnit n (k.val.val, s) =
      idealSymbol K S D n ((S.unitEquivUnitsInteger K (sectorUnit s)).val * D.generator k) := by
  rw [sectorRow, dif_pos (exterior_isExterior K S k)]
  rfl

/-- Every field depending on the frozen triple is fixed over the
entire child row and label sum. Original individual mark coefficients
are shared by all children and are never replaced by new coefficients. -/
structure ColumnFamily (σ : Type*) (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K) where
  lambda : HeckeCharacter K
  background : OuterTriple K → HeckeCharacter K
  background_admissible : ∀ γ, BackgroundCycle.Admissible K Θ ψ (background γ)
  originalPuncture : Ideal (𝓞 K)
  originalSlots : Finset σ
  primeLists : σ → Finset (Ideal (𝓞 K))
  primeWeights : σ → Ideal (𝓞 K) → ℂ
  survivors : OuterTriple K → Finset σ
  survivors_subset : ∀ γ, survivors γ ⊆ originalSlots
  columns : OuterTriple K → Finset Ext
  columns_squarefree : ∀ γ n, n ∈ columns γ → Squarefree n.val.val
  cutoff : OuterTriple K → SchwartzMap ℝ ℂ
  base : ℝ
  columnLength : OuterTriple K → ℝ

variable {σ Sector : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def column (C : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) : ℂ :=
  ∑ n ∈ C.columns γ,
    CoefficientCycle.canonicalCoefficient K S D C.lambda n *
      heckeIdealCoefficient K (C.background γ) n.val *
      (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
      sectorRow K S D sectorUnit n k * labelRow K S D n f ^ 4 *
      divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val *
      C.cutoff γ ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength γ)

def childValue (C : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K) :
    SecondChild K Sector → ℂ := fun x => column K S D C sectorUnit x.1 x.2.1 x.2.2

/-- The child puncture contains the old puncture and precisely the
three frozen ideals, and remains independent of its moving label/row. -/
theorem child_puncture (C : ColumnFamily K S σ Θ ψ) (γ : OuterTriple K) (n : Ext) :
    IsCoprime n.val.val (childPuncture C.originalPuncture γ) ↔
      IsCoprime n.val.val C.originalPuncture ∧
        IsCoprime n.val.val γ.q0 ∧ IsCoprime n.val.val γ.quotient ∧
          IsCoprime n.val.val γ.residual := by
  simp only [childPuncture, IsCoprime.mul_right_iff,
    isCoprime_radical_right_iff, and_assoc]

/-- The actual normalized energy has one averaged label normalization
and one column normalization. Its row/label measures are the measures
proved by the reconstruction theorem. -/
def energy (C : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K)
    (V : ℝ) (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector)) (γ : OuterTriple K) : ℝ :=
  normalizedChildEnergy C.base (C.columnLength γ) V slotCap labels rows
    (childValue K S D C sectorUnit) γ

theorem energy_restore (C : ColumnFamily K S σ Θ ψ) (sectorUnit : Sector → S.unit K)
    (V : ℝ) (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector)) (γ : OuterTriple K) (hZ : 0 < C.base) :
    childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ =
      C.base ^ (C.columnLength γ + V) * energy K S D C sectorUnit V slotCap labels rows γ :=
  childEnergy_restore C.base (C.columnLength γ) V hZ slotCap labels rows _ γ

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren

end
