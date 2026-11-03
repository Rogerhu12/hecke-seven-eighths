import HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorRowMass

/-!
# Actual terminal energies for smooth pieces below unit scale

The [1,2] test forces the original column to its unit summand. We count
its actual ideal rows and the original divisor-weighted labels. The
constant is selected before every scale, canonical family, row set and
label set. The resulting terminal bound requires no child induction
hypothesis and leaves the original prime marks in the column.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleEnergy

open NumberField IsDedekindDomain DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Counting sectors is literal: every ideal row is paired with one
member of the original fixed finite sector type. -/
theorem exists_row_count_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {Sector : Type*} [Fintype Sector]
      (rows : Finset (Ideal (𝓞 K) × Sector)) (X : ℝ),
      1 ≤ X → (∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ X) →
      (rows.card : ℝ) ≤ A * (Fintype.card Sector : ℝ) * X := by
  obtain ⟨A,hA,_hcount,hfinite⟩ := exists_ideal_count_bound_finset K
  refine ⟨A,hA,?_⟩
  intro Sector _ rows X hX hrows
  let ideals := rows.image (fun y => y.1)
  have hbound : (ideals.card : ℝ) ≤ A * X := by
    apply hfinite X hX ideals
    intro I hI
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hI
    exact hrows y hy
  have hincl : rows ⊆ ideals ×ˢ (Finset.univ : Finset Sector) := by
    intro y hy
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨y,hy,rfl⟩, Finset.mem_univ _⟩
  have hcard : rows.card ≤ ideals.card * Fintype.card Sector := by
    simpa only [Finset.card_product, Finset.card_univ] using Finset.card_le_card hincl
  have hcardReal : (rows.card : ℝ) ≤ (ideals.card : ℝ) * (Fintype.card Sector : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ (ideals.card : ℝ) * (Fintype.card Sector : ℝ) := hcardReal
    _ ≤ (A * X) * (Fintype.card Sector : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)
    _ = _ := by ring

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- A genuinely small canonical column is bounded using its actual
row and label norm windows. The sector factor is fixed and explicit. -/
theorem exists_raw_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {σ Sector : Type*} [Fintype Sector]
        {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (C : ColumnFamily K S σ Θ ψ) (G : HeckeCharacter K)
        (hcal : ThetaCalibrationInput K S D C.lambda G)
        (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
        (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
        (X Y : ℝ), 1 ≤ X → 1 ≤ Y →
      (∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ X) →
      (∀ f ∈ labels, (f.absNorm : ℝ) ≤ Y) →
      tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 →
      0 < C.base ^ C.columnLength γ → C.base ^ C.columnLength γ < 1 →
      (∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) →
      childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
        A * (Fintype.card Sector : ℝ) * X * Y ^ (1 + ε) *
          (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by
  obtain ⟨A,hA,hrows⟩ := exists_row_count_bound K
  obtain ⟨B,hB,hlabels⟩ := DivisorRowMass.exists_label_mass_bound
    (K := K) (9 + 4 * slotCap) (by omega) ε hε
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, ?_⟩
  intro σ Sector _ Θ ψ C G hcal sectorUnit γ labels rows X Y
    hX hY hr hf hW hU hsmall hprime
  have hr' := hrows rows X hX hr
  have hf' : (∑ f ∈ labels, labelDivisorWeight slotCap f) ≤ B * Y ^ (1 + ε) :=
    hlabels labels Y hY hf
  have hmass :
      (rows.card : ℝ) * (∑ f ∈ labels, labelDivisorWeight slotCap f) ≤
        (A * (Fintype.card Sector : ℝ) * X) * (B * Y ^ (1 + ε)) :=
    mul_le_mul hr' hf'
      (Finset.sum_nonneg fun f _ => labelDivisorWeight_nonneg slotCap f)
      (mul_nonneg (mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _))
        (zero_le_one.trans hX))
  calc
    _ ≤ ((rows.card : ℝ) * (∑ f ∈ labels, labelDivisorWeight slotCap f)) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 :=
      SmallScaleColumns.raw_energy_le_row_label_mass
        K S D C G hcal sectorUnit γ slotCap labels rows hW hU hsmall hprime
    _ ≤ ((A * (Fintype.card Sector : ℝ) * X) * (B * Y ^ (1 + ε))) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
    _ = _ := by ring

/-- The terminal raw energy has the same combined-length exponent as
a length-zero child. Only the actual geometric margin M ≤ V is used;
no estimate for a recursively smaller energy is assumed. -/
theorem exists_terminal_bound (slotCap : ℕ) (Vcap pi : ℝ)
    (hVcap : 0 ≤ Vcap) (hpi : 0 < pi) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {σ Sector : Type*} [Fintype Sector]
        {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (C : ColumnFamily K S σ Θ ψ) (G : HeckeCharacter K)
        (hcal : ThetaCalibrationInput K S D C.lambda G)
        (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
        (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
        (Z M V : ℝ), 1 ≤ Z → 0 ≤ M → M ≤ V → V ≤ Vcap →
      (∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ Z ^ M) →
      (∀ f ∈ labels, (f.absNorm : ℝ) ≤ Z ^ V) →
      tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 →
      0 < C.base ^ C.columnLength γ → C.base ^ C.columnLength γ < 1 →
      (∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) →
      childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
        A * (Fintype.card Sector : ℝ) * Z ^ (2 * V + pi) *
          (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by
  let ε := pi / (Vcap + 1)
  have hden : 0 < Vcap + 1 := by linarith
  have hε : 0 < ε := div_pos hpi hden
  obtain ⟨A,hA,hbound⟩ := exists_raw_bound K S D slotCap ε hε
  refine ⟨A,hA,?_⟩
  intro σ Sector _ Θ ψ C G hcal sectorUnit γ labels rows Z M V
    hZ hM hMV hVcap' hr hf hW hU hsmall hprime
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hV : 0 ≤ V := hM.trans hMV
  have hexp : M + V * (1 + ε) ≤ 2 * V + pi := by
    have hVe : V * ε ≤ pi := by
      calc
        _ ≤ (Vcap + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
        _ = pi := by dsimp only [ε]; field_simp [hden.ne']
    nlinarith
  have hp : Z ^ M * (Z ^ V) ^ (1 + ε) ≤ Z ^ (2 * V + pi) := by
    rw [← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hb := hbound C G hcal sectorUnit γ labels rows (Z ^ M) (Z ^ V)
    (Real.one_le_rpow hZ hM) (Real.one_le_rpow hZ hV)
    hr hf hW hU hsmall hprime
  calc
    _ ≤ A * (Fintype.card Sector : ℝ) * Z ^ M * (Z ^ V) ^ (1 + ε) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := hb
    _ = (A * (Fintype.card Sector : ℝ)) * (Z ^ M * (Z ^ V) ^ (1 + ε)) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by ring
    _ ≤ (A * (Fintype.card Sector : ℝ)) * Z ^ (2 * V + pi) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp
          (mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _))) (sq_nonneg _)

/-- A possibly negative row exponent is clipped for counting only. A
geometric row allowance is retained in the final exponent. This is the
form used for the finitely many smooth pieces of an actual child. -/
theorem exists_terminal_bound_with_allowance (slotCap : ℕ) (Vcap pi : ℝ)
    (hVcap : 0 ≤ Vcap) (hpi : 0 < pi) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ {σ Sector : Type*} [Fintype Sector]
        {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}
        (C : ColumnFamily K S σ Θ ψ) (G : HeckeCharacter K)
        (hcal : ThetaCalibrationInput K S D C.lambda G)
        (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
        (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
        (Z M V allowance : ℝ), 1 ≤ Z → 0 ≤ V → 0 ≤ allowance →
      M ≤ V + allowance → V ≤ Vcap →
      (∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ Z ^ M) →
      (∀ f ∈ labels, (f.absNorm : ℝ) ≤ Z ^ V) →
      tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 →
      0 < C.base ^ C.columnLength γ → C.base ^ C.columnLength γ < 1 →
      (∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) →
      childEnergy slotCap labels rows (childValue K S D C sectorUnit) γ ≤
        A * (Fintype.card Sector : ℝ) * Z ^ (2 * V + allowance + pi) *
          (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by
  let ε := pi / (Vcap + 1)
  have hden : 0 < Vcap + 1 := by linarith
  have hε : 0 < ε := div_pos hpi hden
  obtain ⟨A, hA, hb⟩ := exists_raw_bound K S D slotCap ε hε
  refine ⟨A, hA, ?_⟩
  intro σ Sector _ Θ ψ C G hcal sectorUnit γ labels rows Z M V allowance
    hZ hV ha hM hVc hr hf hW hU hsmall hprime
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hclip : max 0 M ≤ V + allowance := max_le (add_nonneg hV ha) hM
  have hVe : V * ε ≤ pi := by
    calc
      _ ≤ (Vcap + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
      _ = pi := by dsimp only [ε]; field_simp [hden.ne']
  have hexp : max 0 M + V * (1 + ε) ≤ 2 * V + allowance + pi := by
    nlinarith
  have hp : Z ^ max 0 M * (Z ^ V) ^ (1 + ε) ≤
      Z ^ (2 * V + allowance + pi) := by
    rw [← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  have hrows : ∀ y ∈ rows, (y.1.absNorm : ℝ) ≤ Z ^ max 0 M := by
    intro y hy
    exact (hr y hy).trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _))
  have he := hb C G hcal sectorUnit γ labels rows (Z ^ max 0 M) (Z ^ V)
    (Real.one_le_rpow hZ (le_max_left _ _)) (Real.one_le_rpow hZ hV)
    hrows hf hW hU hsmall hprime
  calc
    _ ≤ A * (Fintype.card Sector : ℝ) * Z ^ max 0 M * (Z ^ V) ^ (1 + ε) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := he
    _ = (A * (Fintype.card Sector : ℝ)) * (Z ^ max 0 M * (Z ^ V) ^ (1 + ε)) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by ring
    _ ≤ (A * (Fintype.card Sector : ℝ)) * Z ^ (2 * V + allowance + pi) *
        (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp
          (mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _))) (sq_nonneg _)

end HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleEnergy

end
