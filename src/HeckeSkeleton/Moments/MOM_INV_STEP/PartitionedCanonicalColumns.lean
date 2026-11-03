import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.SchwartzTestPartition
import Mathlib.Algebra.Order.Chebyshev

/-!
# The smooth finite partition as actual complete canonical columns

Each piece has its own positive scale and its own complete squarefree
norm pool.  The pool change is proved from the actual support of the
original test and of its smooth piece: every added or deleted summand
is zero.  The original canonical coefficient, Hecke background, marks,
puncture, row and averaged label are preserved literally.

The finite reconstruction and finite Cauchy inequality are statements
about the actual columns and their raw positive energies.  No new
coefficient depending on a moving ideal, no hard test indicator, and no
parent energy bound is supplied as input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PartitionedCanonicalColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

abbrev Index := SchwartzTestPartition.Index

def factor (i : Index) : ℝ :=
  SchwartzTestPartition.scale (SchwartzTestPartition.exponent i)

theorem factor_pos (i : Index) : 0 < factor i :=
  SchwartzTestPartition.scale_pos _

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

/-- A nonzero piece lies in both the original and its new full pool. -/
theorem piece_nonzero_bounds (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4)
    (U : ℝ) (hU : 0 < U) (i : Index) (n : Ext)
    (hne : SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
      (height K S n / (factor i * U)) ≠ 0) :
    height K S n ≤ 4 * U ∧ height K S n ≤ 4 * (factor i * U) := by
  have harg : factor i * (height K S n / (factor i * U)) = height K S n / U := by
    field_simp [(factor_pos i).ne', hU.ne'] <;> ring
  have hprod := hne
  rw [SchwartzTestPartition.piece_apply] at hprod
  change W (factor i * (height K S n / (factor i * U))) *
    SchwartzTestPartition.window (height K S n / (factor i * U)) ≠ 0 at hprod
  rw [harg] at hprod
  have hparent := hW (subset_closure
    (Function.mem_support.mpr (mul_ne_zero_iff.mp hprod).1))
  have hpiece := SchwartzTestPartition.piece_support W hW
    (SchwartzTestPartition.exponent i) (subset_closure (Function.mem_support.mpr hne))
  have hp : height K S n ≤ 2 * (factor i * U) :=
    (div_le_iff₀ (mul_pos (factor_pos i) hU)).mp hpiece.2
  refine ⟨(div_le_iff₀ hU).mp hparent.2, ?_⟩
  nlinarith [mul_pos (factor_pos i) hU]

/-- The finite squarefree pool really changes with the smooth scale.
The equality is proved in both directions, not by inserting an
indicator into the new canonical coefficient. -/
theorem piece_pool_change (A : Ext → ℂ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4)
    (U : ℝ) (hU : 0 < U) (i : Index) :
    (∑ n ∈ squarefreePool K S (2 * U),
      A n * SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
        (height K S n / (factor i * U))) =
    ∑ n ∈ squarefreePool K S (2 * (factor i * U)),
      A n * SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
        (height K S n / (factor i * U)) := by
  let P := squarefreePool K S (2 * U)
  let Q := squarefreePool K S (2 * (factor i * U))
  let F : Ext → ℂ := fun n =>
    A n * SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
      (height K S n / (factor i * U))
  have hsf (n : Ext) (hn : n ∈ P ∪ Q) : Squarefree n.val.val := by
    rcases Finset.mem_union.mp hn with hn | hn
    · exact squarefreePool_squarefree K S hn
    · exact squarefreePool_squarefree K S hn
  have hmem (n : Ext) (hn : Squarefree n.val.val) (hF : F n ≠ 0) : n ∈ P ∧ n ∈ Q := by
    have hb := piece_nonzero_bounds K S W hW U hU i n (mul_ne_zero_iff.mp hF).2
    constructor
    · apply (mem_squarefreePool K S (2 * U) n).mpr
      exact ⟨hn, by linarith [hb.1]⟩
    · apply (mem_squarefreePool K S (2 * (factor i * U)) n).mpr
      exact ⟨hn, by linarith [hb.2]⟩
  have hP : (∑ n ∈ P, F n) = ∑ n ∈ P ∪ Q, F n := by
    apply Finset.sum_subset Finset.subset_union_left
    intro n hn hnot
    by_contra hF
    exact hnot (hmem n (hsf n hn) hF).1
  have hQ : (∑ n ∈ Q, F n) = ∑ n ∈ P ∪ Q, F n := by
    apply Finset.sum_subset Finset.subset_union_right
    intro n hn hnot
    by_contra hF
    exact hnot (hmem n (hsf n hn) hF).2
  exact hP.trans hQ.symm

/-- Exact finite reconstruction, already in each piece's own complete
squarefree norm pool. -/
theorem finite_source_partition (A : Ext → ℂ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 / 512 : ℝ) 4) (U : ℝ) (hU : 0 < U) :
    (∑ n ∈ squarefreePool K S (2 * U), A n * W (height K S n / U)) =
      ∑ i : Index, ∑ n ∈ squarefreePool K S (2 * (factor i * U)),
        A n * SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
          (height K S n / (factor i * U)) := by
  calc
    _ = ∑ i : Index, ∑ n ∈ squarefreePool K S (2 * U),
        A n * SchwartzTestPartition.piece W (SchwartzTestPartition.exponent i)
          (height K S n / (factor i * U)) :=
      SchwartzTestPartition.finite_source_reconstruct (squarefreePool K S (2 * U))
        A (height K S) U W hW
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact piece_pool_change K S A W hW U hU i

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- Only the smooth norm test and its fixed scale/pool change.
Every original arithmetic field is inherited from C. -/
def family (C : ColumnFamily K S σ Θ ψ) (i : Index) : ColumnFamily K S σ Θ ψ :=
  { C with
    columns := fun γ => squarefreePool K S
      (2 * (factor i * C.base ^ C.columnLength γ))
    columns_squarefree := fun _ _ hn => squarefreePool_squarefree K S hn
    cutoff := fun γ => SchwartzTestPartition.piece (C.cutoff γ)
      (SchwartzTestPartition.exponent i)
    columnLength := fun γ => C.columnLength γ + Real.logb C.base (factor i) }

theorem family_scale (C : ColumnFamily K S σ Θ ψ) (hbase : 1 < C.base)
    (i : Index) (γ : OuterTriple K) :
    (family K S C i).base ^ (family K S C i).columnLength γ =
      factor i * C.base ^ C.columnLength γ := by
  change C.base ^ (C.columnLength γ + Real.logb C.base (factor i)) = _
  rw [Real.rpow_add (zero_lt_one.trans hbase),
    Real.rpow_logb (zero_lt_one.trans hbase) (ne_of_gt hbase) (factor_pos i), mul_comm]

theorem family_complete_pool (C : ColumnFamily K S σ Θ ψ) (hbase : 1 < C.base)
    (i : Index) (γ : OuterTriple K) :
    (family K S C i).columns γ =
      squarefreePool K S (2 * (family K S C i).base ^ (family K S C i).columnLength γ) := by
  rw [family_scale K S C hbase i γ]
  rfl

theorem family_test_support (C : ColumnFamily K S σ Θ ψ)
    (i : Index) (γ : OuterTriple K)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 512 : ℝ) 4) :
    tsupport ((family K S C i).cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 :=
  SchwartzTestPartition.piece_support (C.cutoff γ) hW (SchwartzTestPartition.exponent i)

variable (D : ThetaArithmeticData K S)
variable {Sector : Type*}

/-- The original canonical column is exactly the sum of the 24 new
canonical columns, with original marks and no residual ideal weight. -/
theorem column_eq_sum (C : ColumnFamily K S σ Θ ψ) (hbase : 1 < C.base)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 512 : ℝ) 4) :
    column K S D C sectorUnit γ f k =
      ∑ i : Index, column K S D (family K S C i) sectorUnit γ f k := by
  let U := C.base ^ C.columnLength γ
  have hU : 0 < U := Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _
  let A : Ext → ℂ := fun n =>
    CoefficientCycle.canonicalCoefficient K S D C.lambda n *
      heckeIdealCoefficient K (C.background γ) n.val *
      (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
      sectorRow K S D sectorUnit n k * labelRow K S D n f ^ 4 *
      divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val
  have hi (i : Index) :
      column K S D (family K S C i) sectorUnit γ f k =
        ∑ n ∈ squarefreePool K S (2 * (factor i * U)),
          A n * SchwartzTestPartition.piece (C.cutoff γ) (SchwartzTestPartition.exponent i)
            (height K S n / (factor i * U)) := by
    unfold column
    rw [family_scale K S C hbase i γ]
    rfl
  calc
    _ = ∑ n ∈ squarefreePool K S (2 * U), A n * C.cutoff γ (height K S n / U) := by
      rw [column, hpool]
      rfl
    _ = ∑ i : Index, ∑ n ∈ squarefreePool K S (2 * (factor i * U)),
          A n * SchwartzTestPartition.piece (C.cutoff γ) (SchwartzTestPartition.exponent i)
            (height K S n / (factor i * U)) :=
      finite_source_partition K S A (C.cutoff γ) hW U hU
    _ = _ := Finset.sum_congr rfl (fun i _ => (hi i).symm)

theorem column_norm_sq_le (C : ColumnFamily K S σ Θ ψ) (hbase : 1 < C.base)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 512 : ℝ) 4) :
    ‖column K S D C sectorUnit γ f k‖ ^ 2 ≤
      24 * ∑ i : Index, ‖column K S D (family K S C i) sectorUnit γ f k‖ ^ 2 := by
  rw [column_eq_sum K S D C hbase sectorUnit γ f k hpool hW]
  have hcard : (Finset.univ : Finset Index).card = 24 := by
    simp only [Finset.card_univ, Index, SchwartzTestPartition.Index, Fintype.card_fin]
  calc
    _ ≤ (∑ i : Index, ‖column K S D (family K S C i) sectorUnit γ f k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ ((Finset.univ : Finset Index).card : ℝ) *
        ∑ i : Index, ‖column K S D (family K S C i) sectorUnit γ f k‖ ^ 2 :=
      _root_.sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [hcard]; norm_num

/-- The finite Cauchy loss is the fixed number 24, and the original
positive row/label weights are retained exactly. -/
theorem raw_energy_le_sum (C : ColumnFamily K S σ Θ ψ) (hbase : 1 < C.base)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 512 : ℝ) 4) :
    FixedTripleEnergy.childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
      24 * ∑ i : Index, FixedTripleEnergy.childEnergy slotCap labels rows
        (childValue K S D (family K S C i) sectorUnit) γ := by
  unfold FixedTripleEnergy.childEnergy
  calc
    _ ≤ ∑ f ∈ labels, FixedTripleEnergy.labelDivisorWeight slotCap f *
        ∑ k ∈ rows, 24 *
          ∑ i : Index, ‖column K S D (family K S C i) sectorUnit γ f k‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro f hf
      apply mul_le_mul_of_nonneg_left _ (FixedTripleEnergy.labelDivisorWeight_nonneg slotCap f)
      apply Finset.sum_le_sum
      intro k hk
      exact column_norm_sq_le K S D C hbase sectorUnit γ f k hpool hW
    _ = _ := by
      simp only [Finset.mul_sum, childValue]
      simp_rw [Finset.sum_comm (s := rows) (t := (Finset.univ : Finset Index))]
      rw [Finset.sum_comm (s := labels) (t := (Finset.univ : Finset Index))]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro f hf
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Uniform control is chosen before every arithmetic family and all
moving rows/labels. The only change is a fixed smooth linear operator
on the original test. -/
theorem exists_test_seminorm_bound (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (F : ColumnFamily K S σ Θ ψ) (i : Index) (γ : OuterTriple K),
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((family K S F i).cutoff γ) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (F.cutoff γ) := by
  obtain ⟨s,C,hC,hb⟩ := SchwartzTestPartition.exists_finite_seminorm_bound t
  exact ⟨s,C,hC, fun F i γ => hb (F.cutoff γ) i⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.PartitionedCanonicalColumns

end
