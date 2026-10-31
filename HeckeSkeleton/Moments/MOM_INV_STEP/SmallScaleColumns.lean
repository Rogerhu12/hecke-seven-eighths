import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Exact canonical columns below unit scale

A smooth [1,2] test at a positive scale strictly below one can see only
an ideal of absolute norm one.  This is the actual unit ideal, and the
finite source still decides whether that ideal is present.  A surviving
prime-divisor mark kills that unit contribution exactly.

These are identities of the original finite columns.  They do not
replace the physical scale by one or change the induction's test class.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

/-- The actual exterior unit ideal; no generator is chosen here. -/
def unitIdeal : Ext :=
  exteriorOf K S 1 ⟨one_ne_zero, by
    intro p hp
    rw [Ideal.one_eq_top] at hp
    exact (p.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hp))).elim⟩

@[simp] theorem unitIdeal_val : (unitIdeal K S).val.val = 1 := rfl

@[simp] theorem unitIdeal_height : height K S (unitIdeal K S) = 1 := by
  change ((1 : Ideal (𝓞 K)).absNorm : ℝ) = 1
  simp

/-- Positivity and integrality of the actual ideal norm leave only one. -/
theorem eq_unitIdeal_of_height_lt_two (n : Ext) (hn : height K S n < 2) :
    n = unitIdeal K S := by
  apply ideal_injective K S
  change n.val.val = 1
  rw [Ideal.one_eq_top]
  apply Ideal.absNorm_eq_one_iff.mp
  have hpos : 0 < n.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors n.val
  have hsmall : n.val.val.absNorm < 2 := by
    exact_mod_cast (show (n.val.val.absNorm : ℝ) < 2 from hn)
  omega

theorem test_eq_zero_of_ne_unitIdeal (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (U : ℝ) (hU : 0 < U) (hsmall : U < 1)
    (n : Ext) (hn : n ≠ unitIdeal K S) :
    W (height K S n / U) = 0 := by
  by_contra hne
  have hh := hW (subset_closure (Function.mem_support.mpr hne))
  have hnU : height K S n ≤ 2 * U := (div_le_iff₀ hU).mp hh.2
  have hn2 : height K S n < 2 := by linarith
  exact hn (eq_unitIdeal_of_height_lt_two K S n hn2)

/-- Exact reduction of any original finite source, including the
possibility that it does not contain the unit ideal. -/
theorem finite_source_eq_unit (T : Finset Ext) (A : Ext → ℂ)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (U : ℝ) (hU : 0 < U) (hsmall : U < 1) :
    (∑ n ∈ T, A n * W (height K S n / U)) =
      if unitIdeal K S ∈ T then A (unitIdeal K S) * W (1 / U) else 0 := by
  by_cases hu : unitIdeal K S ∈ T
  · rw [if_pos hu]
    calc
      _ = A (unitIdeal K S) * W (height K S (unitIdeal K S) / U) := by
        apply Finset.sum_eq_single_of_mem _ hu
        intro n hn hne
        rw [test_eq_zero_of_ne_unitIdeal K S W hW U hU hsmall n hne, mul_zero]
      _ = _ := by rw [unitIdeal_height]
  · rw [if_neg hu]
    apply Finset.sum_eq_zero
    intro n hn
    have hne : n ≠ unitIdeal K S := by
      intro he
      apply hu
      exact he ▸ hn
    rw [test_eq_zero_of_ne_unitIdeal K S W hW U hU hsmall n hne, mul_zero]

/-- A literal prime-divisor mark with a surviving slot vanishes at
the unit ideal, irrespective of its original individual coefficients. -/
theorem divisorMark_one_eq_zero {σ : Type*}
    (J : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hJ : J.Nonempty)
    (hprime : ∀ i ∈ J, ∀ P ∈ lists i, Prime P) :
    divisorMark J lists a (1 : Ideal (𝓞 K)) = 0 := by
  obtain ⟨i, hi⟩ := hJ
  unfold divisorMark
  apply Finset.prod_eq_zero hi
  apply Finset.sum_eq_zero
  intro P hP
  exact if_neg (hprime i hi P hP).not_dvd_one

variable (D : ThetaArithmeticData K S)
variable {σ Sector : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The actual canonical column has exactly its unit summand at a
small scale. Every original coefficient, puncture, mark and row stays
in that summand; there is no new residual coefficient on a variable n. -/
theorem column_eq_unit (C : ColumnFamily K S σ Θ ψ)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (hU : 0 < C.base ^ C.columnLength γ) (hsmall : C.base ^ C.columnLength γ < 1) :
    column K S D C sectorUnit γ f k =
      if unitIdeal K S ∈ C.columns γ then
        CoefficientCycle.canonicalCoefficient K S D C.lambda (unitIdeal K S) *
          heckeIdealCoefficient K (C.background γ) (unitIdeal K S).val *
          (if IsCoprime (1 : Ideal (𝓞 K)) (childPuncture C.originalPuncture γ)
            then 1 else 0) *
          sectorRow K S D sectorUnit (unitIdeal K S) k *
          labelRow K S D (unitIdeal K S) f ^ 4 *
          divisorMark (C.survivors γ) C.primeLists C.primeWeights (1 : Ideal (𝓞 K)) *
          C.cutoff γ (1 / C.base ^ C.columnLength γ)
      else 0 := by
  exact finite_source_eq_unit K S (C.columns γ)
    (fun n =>
      CoefficientCycle.canonicalCoefficient K S D C.lambda n *
        heckeIdealCoefficient K (C.background γ) n.val *
        (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
        sectorRow K S D sectorUnit n k * labelRow K S D n f ^ 4 *
        divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val)
    (C.cutoff γ) hW (C.base ^ C.columnLength γ) hU hsmall

theorem column_eq_zero_of_surviving_prime (C : ColumnFamily K S σ Θ ψ)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (hU : 0 < C.base ^ C.columnLength γ) (hsmall : C.base ^ C.columnLength γ < 1)
    (hslots : (C.survivors γ).Nonempty)
    (hprime : ∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) :
    column K S D C sectorUnit γ f k = 0 := by
  rw [column_eq_unit K S D C sectorUnit γ f k hW hU hsmall]
  split_ifs
  · rw [divisorMark_one_eq_zero K (C.survivors γ) C.primeLists C.primeWeights hslots hprime]
    simp only [mul_zero, zero_mul]
  · rfl


private theorem idealSymbol_norm_le_one (n : Ext) (x : Set.integer S K) :
    ‖idealSymbol K S D n x‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
    n.val.val (nonZeroDivisors.coe_ne_zero n.val) n.property
    (fun p hp => D.away_six p (n.property p hp)) x

private theorem labelRow_norm_le_one (n : Ext) (f : Ideal (𝓞 K)) :
    ‖labelRow K S D n f‖ ≤ 1 := by
  unfold labelRow
  split_ifs
  · exact idealSymbol_norm_le_one K S D n _
  · simp only [norm_zero, zero_le_one]

private theorem sectorRow_norm_le_one (sectorUnit : Sector → S.unit K)
    (n : Ext) (k : Ideal (𝓞 K) × Sector) :
    ‖sectorRow K S D sectorUnit n k‖ ≤ 1 := by
  unfold sectorRow
  split_ifs
  · exact idealSymbol_norm_le_one K S D n _
  · simp only [norm_zero, zero_le_one]

/-- The small-scale column has a uniform pointwise bound from the
original test alone. No size restriction on individual prime weights
is needed: every nonempty surviving prime mark is identically zero. -/
theorem column_norm_le_seminorm (C : ColumnFamily K S σ Θ ψ)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K S D C.lambda G)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (hU : 0 < C.base ^ C.columnLength γ) (hsmall : C.base ^ C.columnLength γ < 1)
    (hprime : ∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) :
    ‖column K S D C sectorUnit γ f k‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) := by
  by_cases hs : (C.survivors γ).Nonempty
  · rw [column_eq_zero_of_surviving_prime K S D C sectorUnit γ f k
      hW hU hsmall hs hprime, norm_zero]
    exact apply_nonneg _ _
  · have hempty : C.survivors γ = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => hs ⟨i, hi⟩)
    rw [column_eq_unit K S D C sectorUnit γ f k hW hU hsmall]
    split_ifs
    · have ha := CoefficientCycle.canonicalCoefficient_norm hcal (unitIdeal K S)
        (show Squarefree (unitIdeal K S).val.val from squarefree_one)
      have hν := norm_heckeIdealCoefficient_le_one K (C.background γ) (unitIdeal K S).val
      have hm : ‖(if IsCoprime (1 : Ideal (𝓞 K)) (childPuncture C.originalPuncture γ)
          then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
      have hr := sectorRow_norm_le_one K S D sectorUnit (unitIdeal K S) k
      have hf := labelRow_norm_le_one K S D (unitIdeal K S) f
      have ht := SchwartzMap.norm_le_seminorm ℝ (C.cutoff γ)
        (1 / C.base ^ C.columnLength γ)
      simp only [norm_mul, norm_pow, hempty, divisorMark, Finset.prod_empty, norm_one, ha]
      calc
        _ ≤ 1 * 1 * 1 * 1 * 1 ^ 4 * 1 *
            SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ) := by gcongr
        _ = _ := by ring
    · simpa only [norm_zero] using
        (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (C.cutoff γ))

/-- The literal positive child energy is bounded by its actual row
cardinality and actual weighted label mass. Subsequent norm counting
and terminal exponent choices are separate from this exact source bound. -/
theorem raw_energy_le_row_label_mass (C : ColumnFamily K S σ Θ ψ)
    (G : HeckeCharacter K) (hcal : ThetaCalibrationInput K S D C.lambda G)
    (sectorUnit : Sector → S.unit K) (γ : OuterTriple K)
    (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (hU : 0 < C.base ^ C.columnLength γ) (hsmall : C.base ^ C.columnLength γ < 1)
    (hprime : ∀ i ∈ C.survivors γ, ∀ P ∈ C.primeLists i, Prime P) :
    FixedTripleEnergy.childEnergy slotCap labels rows
      (childValue K S D C sectorUnit) γ ≤
      ((rows.card : ℝ) *
        ∑ f ∈ labels, FixedTripleEnergy.labelDivisorWeight slotCap f) *
          (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by
  unfold FixedTripleEnergy.childEnergy
  calc
    _ ≤ ∑ f ∈ labels, FixedTripleEnergy.labelDivisorWeight slotCap f *
        ∑ _k ∈ rows, (SchwartzMap.seminorm ℝ 0 0 (C.cutoff γ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro f hf
      apply mul_le_mul_of_nonneg_left _ (FixedTripleEnergy.labelDivisorWeight_nonneg slotCap f)
      apply Finset.sum_le_sum
      intro k hk
      exact pow_le_pow_left₀ (norm_nonneg _)
        (column_norm_le_seminorm K S D C G hcal sectorUnit γ f k hW hU hsmall hprime) 2
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SmallScaleColumns

end

