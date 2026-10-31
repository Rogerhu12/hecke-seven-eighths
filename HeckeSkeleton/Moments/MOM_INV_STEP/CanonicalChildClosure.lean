import HeckeSkeleton.Moments.MOM_INV_STEP.ClippedChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.PartitionedCanonicalColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.PartitionedChildGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleEnergy

/-!
# Closing the actual child class under the two smooth inversions

The complete canonical column is first clipped by an exact Schwartz
dilation, then written as 24 actual complete columns with tests supported
on [1,2]. Only pieces with nonnegative column length use the smaller-child
induction hypothesis. A negative-length piece is bounded directly by its
unit-ideal summand and the actual row and divisor-weighted label counts.

The original coefficient, background, puncture and individual prime
weights are inherited without change. All test constants are fixed before
the source, moving rows and labels, and the frequency of the original
test. The harmless fixed-scale and terminal allowances are retained in
the exponent until the physical budget is applied.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildClosure

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

abbrev Index := SchwartzTestPartition.Index

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- Each actual child piece has a complete norm pool and a smooth
[1,2] test. Its arithmetic fields are those of the original family. -/
def pieceFamily (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base) (i : Index) :
    ColumnFamily K S σ Θ ψ :=
  PartitionedCanonicalColumns.family K S (ClippedChildren.clippedFamily K S C hZ) i

theorem pieceFamily_length (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (i : Index) (γ : OuterTriple K) :
    (pieceFamily K S C hZ i).columnLength γ =
      PartitionedChildGeometry.pieceLength C.base (C.columnLength γ) i := rfl

theorem pieceFamily_complete_pool (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (i : Index) (γ : OuterTriple K) :
    (pieceFamily K S C hZ i).columns γ =
      squarefreePool K S
        (2 * C.base ^ (pieceFamily K S C hZ i).columnLength γ) :=
  PartitionedCanonicalColumns.family_complete_pool K S
    (ClippedChildren.clippedFamily K S C hZ) hZ i γ

theorem clipped_support (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K)
    (hlive : 1 ≤ 4 * C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4) :
    tsupport ((ClippedChildren.clippedFamily K S C hZ).cutoff γ) ⊆
      Set.Icc (1 / 512 : ℝ) 4 := by
  have hU := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (C.columnLength γ)
  have ha := SchwartzDilation.clip_dilation_bounds _ hU hlive
  have hb := SchwartzDilation.tsupport_dilate_subset
    (max 1 (C.base ^ C.columnLength γ) / (C.base ^ C.columnLength γ))
    4 (1 / 128) 4
    (div_pos (zero_lt_one.trans_le (le_max_left _ _)) hU)
    ha.1 ha.2 (by norm_num) (C.cutoff γ) hW
  convert hb using 1 <;> norm_num

theorem pieceFamily_support (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (i : Index) (γ : OuterTriple K)
    (hlive : 1 ≤ 4 * C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4) :
    tsupport ((pieceFamily K S C hZ i).cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 :=
  PartitionedCanonicalColumns.family_test_support K S
    (ClippedChildren.clippedFamily K S C hZ) i γ (clipped_support K S C hZ γ hlive hW)

/-- Clipping and the fixed partition have one uniform finite-seminorm
cost. The lower scale bound comes from the actual overlap pool. -/
theorem exists_piece_seminorm_bound (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
        (γ : OuterTriple K), 1 ≤ 4 * C.base ^ C.columnLength γ →
      ∀ i : Index,
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((pieceFamily K S C hZ i).cutoff γ) ≤
        A * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (C.cutoff γ) := by
  obtain ⟨s, A, hA, hpart⟩ :=
    PartitionedCanonicalColumns.exists_test_seminorm_bound K S t
  obtain ⟨B, hB, hclip⟩ := SchwartzDilation.finite_seminorm_dilate_le 4 (by norm_num) s
  refine ⟨s, A * B, mul_nonneg hA hB, ?_⟩
  intro σ Θ ψ C hZ γ hlive i
  have hU := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (C.columnLength γ)
  have ha := SchwartzDilation.clip_dilation_bounds _ hU hlive
  have hc := hclip _ (div_pos (zero_lt_one.trans_le (le_max_left _ _)) hU)
    ha.1 ha.2 (C.cutoff γ)
  have hp := hpart (ClippedChildren.clippedFamily K S C hZ) i γ
  exact (hp.trans (mul_le_mul_of_nonneg_left hc hA)).trans_eq (by ring)

variable (D : ThetaArithmeticData K S)
variable {Sector : Type*} (sectorUnit : Sector → S.unit K)

/-- A row below unit norm is outside the exterior row class, so its
literal canonical column is zero even if a containing finite set lists it. -/
theorem column_eq_zero_of_row_norm_lt_one (C : ColumnFamily K S σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hk : (k.1.absNorm : ℝ) < 1) : column K S D C sectorUnit γ f k = 0 := by
  have hbad : ¬ IsExterior K S k.1 := by
    intro hgood
    have hpos : 0 < k.1.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨k.1, mem_nonZeroDivisors_of_ne_zero hgood.1⟩
    have hone : (1 : ℝ) ≤ (k.1.absNorm : ℝ) := by exact_mod_cast hpos
    linarith
  unfold column
  apply Finset.sum_eq_zero
  intro n hn
  simp only [sectorRow, dif_neg hbad, mul_zero, zero_mul]

/-- Negative row lengths are disposed of on the actual source. They
do not create a recursive child with a silently enlarged row length. -/
theorem raw_energy_eq_zero_of_negative_row_length
    (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (M : ℝ) (hM : M < 0)
    (hrows : ∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ C.base ^ M) :
    childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ = 0 := by
  unfold childEnergy
  apply Finset.sum_eq_zero
  intro f hf
  have hz : (∑ k ∈ rows, ‖childValue K S D C sectorUnit (γ, f, k)‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hc := column_eq_zero_of_row_norm_lt_one K S D sectorUnit C γ f k
      ((hrows k hk).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hZ hM))
    simp only [childValue, hc, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [hz, mul_zero]

/-- Exact clipping is applied to each actual column before finite
Cauchy. No child energy estimate is needed for this class conversion. -/
theorem raw_energy_le_pieces (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hlive : 1 ≤ 4 * C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4) :
    childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
      24 * ∑ i : Index,
        childEnergy slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ := by
  let C₀ := ClippedChildren.clippedFamily K S C hZ
  have hsupport : tsupport (C.cutoff γ) ⊆ Set.Icc (0 : ℝ) 4 := by
    intro x hx
    have h := hW hx
    exact ⟨by linarith [h.1], h.2⟩
  have he : childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ =
      childEnergy slotCap labels rows (childValue K S D C₀ sectorUnit) γ := by
    unfold childEnergy
    apply Finset.sum_congr rfl
    intro f hf
    apply congrArg (fun z : ℝ => labelDivisorWeight slotCap f * z)
    apply Finset.sum_congr rfl
    intro k hk
    have hh := ClippedChildren.column_eq_clipped K S D sectorUnit C hZ γ f k hpool hsupport
    change ‖column K S D C sectorUnit γ f k‖ ^ 2 =
      ‖column K S D C₀ sectorUnit γ f k‖ ^ 2
    rw [hh]
  have hpool₀ : C₀.columns γ = squarefreePool K S (2 * C₀.base ^ C₀.columnLength γ) := by
    change squarefreePool K S (2 * max 1 (C.base ^ C.columnLength γ)) =
      squarefreePool K S (2 * C.base ^ max 0 (C.columnLength γ))
    rw [ClippedChildren.clipped_scale C.base (C.columnLength γ) hZ.le]
  rw [he]
  exact PartitionedCanonicalColumns.raw_energy_le_sum K S D C₀ hZ sectorUnit γ
    slotCap labels rows hpool₀ (clipped_support K S C hZ γ hlive hW)

/-- The normalized comparison records the real scale of every smooth
piece. In particular the scale factors do not disappear when Cauchy is
applied to the 24-column reconstruction. -/
theorem normalized_energy_le_pieces (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
    (γ : OuterTriple K) (slotCap : ℕ) (V : ℝ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hpool : C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ))
    (hlive : 1 ≤ 4 * C.base ^ C.columnLength γ)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4) :
    normalizedChildEnergy C.base (max 0 (C.columnLength γ)) V slotCap labels rows
      (childValue K S D C sectorUnit) γ ≤
      24 * ∑ i : Index,
        C.base ^ ((pieceFamily K S C hZ i).columnLength γ - max 0 (C.columnLength γ)) *
          normalizedChildEnergy C.base ((pieceFamily K S C hZ i).columnLength γ) V
            slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ := by
  have hz : 0 < C.base := zero_lt_one.trans hZ
  have hscale (i : Index) :
      C.base ^ (-(max 0 (C.columnLength γ) + V)) *
        childEnergy slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ =
      C.base ^ ((pieceFamily K S C hZ i).columnLength γ - max 0 (C.columnLength γ)) *
        normalizedChildEnergy C.base ((pieceFamily K S C hZ i).columnLength γ) V
          slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ := by
    rw [normalizedChildEnergy_eq C.base _ V hz, ← mul_assoc, ← Real.rpow_add hz]
    congr 2
    ring
  rw [normalizedChildEnergy_eq C.base _ V hz]
  have hb := mul_le_mul_of_nonneg_left
    (raw_energy_le_pieces K S D sectorUnit C hZ γ slotCap labels rows hpool hlive hW)
    (Real.rpow_nonneg hz.le (-(max 0 (C.columnLength γ) + V)))
  apply hb.trans_eq
  rw [mul_left_comm _ (24 : ℝ), Finset.mul_sum]
  apply congrArg (fun x : ℝ => 24 * x)
  exact Finset.sum_congr rfl (fun i _ => hscale i)

/-- Uniform closure of the genuine child class. The only recursive
energy premises are the [1,2] pieces of nonnegative length. Pieces below
unit scale use the proved unit-column estimate and the actual norm boxes.
The 28h allowance is geometric and is paid in the physical budget below. -/
theorem exists_closed_raw_bound (slotCap : ℕ) (Vcap pi : ℝ)
    (hVcap : 0 ≤ Vcap) (hpi : 0 < pi) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 < A ∧
      ∀ {σ Sector : Type*} [Fintype Sector]
        {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (C : ColumnFamily K S σ Θ ψ) (hZ : 1 < C.base)
        (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K S D C.lambda G)
        (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
        (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
        (M V h eps Cih : ℝ),
      C.columns γ = squarefreePool K S (2 * C.base ^ C.columnLength γ) →
      1 ≤ 4 * C.base ^ C.columnLength γ →
      tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4 →
      0 ≤ V → V ≤ Vcap → 0 ≤ h → 2 ≤ C.base ^ h → 0 ≤ eps → 0 ≤ Cih →
      (∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ C.base ^ M) →
      (∀ f ∈ labels, (f.absNorm : ℝ) ≤ C.base ^ V) →
      (∀ j ∈ C.survivors γ, ∀ P ∈ C.primeLists j, Prime P) →
      (∀ i : Index, (pieceFamily K S C hZ i).columnLength γ < 0 → M ≤ V + 28 * h) →
      (∀ i : Index, 0 ≤ (pieceFamily K S C hZ i).columnLength γ →
        normalizedChildEnergy C.base ((pieceFamily K S C hZ i).columnLength γ) V
          slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ ≤
        Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          ((pieceFamily K S C hZ i).cutoff γ)) ^ 2 *
          C.base ^ ((pieceFamily K S C hZ i).columnLength γ + V + eps)) →
      childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
        A * (Cih + (Fintype.card Sector : ℝ)) *
          (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (C.cutoff γ)) ^ 2 *
          C.base ^ (2 * (max 0 (C.columnLength γ) + V) + 28 * h + eps + pi) := by
  let q := t ∪ {(0, 0)}
  obtain ⟨s, B, hB, htest⟩ := exists_piece_seminorm_bound K S q
  obtain ⟨A, hA, hsmall⟩ :=
    SmallScaleEnergy.exists_terminal_bound_with_allowance K S D slotCap Vcap pi hVcap hpi
  let E := 576 * A * (B + 1) ^ 2
  have hE : 0 < E := by
    have hApos : 0 < A := zero_lt_one.trans_le hA
    dsimp only [E]
    positivity
  refine ⟨s, E, hE, ?_⟩
  intro σ Sector _ Θ ψ C hZ G hcal sectorUnit γ labels rows M V h eps Cih
    hpool hlive hW hV hVc hh hwidth heps hCih hrows hlabels hprime hcapacity hih
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (C.cutoff γ)
  let N := max 0 (C.columnLength γ)
  let exponent := 2 * (N + V) + 28 * h + eps + pi
  let H := A * (Cih + (Fintype.card Sector : ℝ)) * ((B + 1) * Q) ^ 2 * C.base ^ exponent
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hz : 0 < C.base := zero_lt_one.trans hZ
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcoeff : 0 ≤ Cih + (Fintype.card Sector : ℝ) := add_nonneg hCih (Nat.cast_nonneg _)
  have hq (i : Index) :
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((pieceFamily K S C hZ i).cutoff γ) ≤
        (B + 1) * Q :=
    (htest C hZ γ hlive i).trans (mul_le_mul_of_nonneg_right (by linarith) hQ)
  have ht (i : Index) :
      t.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((pieceFamily K S C hZ i).cutoff γ) ≤
        (B + 1) * Q :=
    (Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) _).trans (hq i)
  have hzero (i : Index) :
      SchwartzMap.seminorm ℝ 0 0 ((pieceFamily K S C hZ i).cutoff γ) ≤ (B + 1) * Q := by
    have hmem : (0, 0) ∈ q := by simp [q]
    rw [← SchwartzMap.schwartzSeminormFamily_apply]
    exact (Seminorm.le_finset_sup_apply hmem).trans (hq i)
  have hpiece (i : Index) :
      childEnergy slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ ≤ H := by
    by_cases hN : 0 ≤ (pieceFamily K S C hZ i).columnLength γ
    · have hi := childEnergy_bound_of_normalized C.base
        ((pieceFamily K S C hZ i).columnLength γ) V eps
        (Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          ((pieceFamily K S C hZ i).cutoff γ)) ^ 2)
        hz slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ (hih i hN)
      have hlen := (PartitionedChildGeometry.piece_shift_bounds C.base h hZ hwidth i).2
      have hexp : 2 * ((pieceFamily K S C hZ i).columnLength γ + V) + eps ≤ exponent := by
        change Real.logb C.base (PartitionedCanonicalColumns.factor i) ≤ 5 * h at hlen
        dsimp only [pieceFamily, PartitionedCanonicalColumns.family,
          ClippedChildren.clippedFamily, exponent, N]
        linarith
      have hc : Cih ≤ A * (Cih + (Fintype.card Sector : ℝ)) := by
        calc
          _ ≤ Cih + (Fintype.card Sector : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
          _ ≤ _ := le_mul_of_one_le_left hcoeff hA
      have hpower := Real.rpow_le_rpow_of_exponent_le hZ.le hexp
      have hsquare := pow_le_pow_left₀ (apply_nonneg _ _) (ht i) 2
      exact hi.trans (mul_le_mul (mul_le_mul hc hsquare (sq_nonneg _) (mul_nonneg hA0 hcoeff))
        hpower (Real.rpow_nonneg hz.le _) (by positivity))
    · have hNneg : (pieceFamily K S C hZ i).columnLength γ < 0 := lt_of_not_ge hN
      have hp := hsmall (pieceFamily K S C hZ i) G hcal sectorUnit γ labels rows
        C.base M V (28 * h) hZ.le hV (by positivity) (hcapacity i hNneg) hVc
        hrows hlabels (pieceFamily_support K S C hZ i γ hlive hW)
        (Real.rpow_pos_of_pos hz _) (Real.rpow_lt_one_of_one_lt_of_neg hZ hNneg) hprime
      have hexp : 2 * V + 28 * h + pi ≤ exponent := by
        have hN0 : 0 ≤ N := le_max_left _ _
        dsimp only [exponent]
        linarith
      have hc : A * (Fintype.card Sector : ℝ) ≤ A * (Cih + (Fintype.card Sector : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCih) hA0
      have hpower := Real.rpow_le_rpow_of_exponent_le hZ.le hexp
      have hsquare := pow_le_pow_left₀ (apply_nonneg _ _) (hzero i) 2
      have hb := mul_le_mul (mul_le_mul hc hpower (Real.rpow_nonneg hz.le _)
        (mul_nonneg hA0 hcoeff)) hsquare (sq_nonneg _) (by positivity)
      exact hp.trans (hb.trans_eq (by dsimp only [H]; ring))
  have hsum : (∑ i : Index,
      childEnergy slotCap labels rows (childValue K S D (pieceFamily K S C hZ i) sectorUnit) γ) ≤
      24 * H := by
    calc
      _ ≤ ∑ _i : Index, H := Finset.sum_le_sum (fun i _ => hpiece i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Index,
        SchwartzTestPartition.Index, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hb := (raw_energy_le_pieces K S D sectorUnit C hZ γ slotCap labels rows
    hpool hlive hW).trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 24))
  exact hb.trans_eq (by dsimp only [E, H, exponent, N, Q]; ring)

/-- Restoring the normalization after the proved class conversion
uses one column and one label factor, with no extra counting cost. -/
theorem normalized_bound_of_raw (Z N V eps A : ℝ) (hZ : 0 < Z)
    (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K)
    (hraw : childEnergy slotCap labels rows F γ ≤ A * Z ^ (2 * (N + V) + eps)) :
    normalizedChildEnergy Z N V slotCap labels rows F γ ≤ A * Z ^ (N + V + eps) := by
  rw [normalizedChildEnergy_eq Z N V hZ]
  apply (mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hZ.le _)).trans_eq
  calc
    Z ^ (-(N + V)) * (A * Z ^ (2 * (N + V) + eps)) =
        A * (Z ^ (-(N + V)) * Z ^ (2 * (N + V) + eps)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ]
      congr 2
      ring

/-- The complete class conversion, including its true unit-scale
terminal allowance, fits inside the public physical loss. -/
theorem closed_physical_power_budget
    (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) :
    Z ^ (firstKappa M r ell V delta A B R + (9 / 2 : ℝ) * h) *
      Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * h + tau) *
      Z ^ (secondCount ell R j t g theta + (11 / 2 : ℝ) * h + pi) *
      Z ^ (2 * (max 0 Nactual + secondFormalLabel B theta v j + 4 * h) + 28 * h + eps) ≤
      Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hs := (CenteredChildGeometry.clipped_shift
    (secondFormalColumn r A B t g v) Nactual h hh hlo hhi hlive).2
  have hi := physical_prefactor_identity M r ell V delta A B R j t g theta v
  linarith

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildClosure

end
