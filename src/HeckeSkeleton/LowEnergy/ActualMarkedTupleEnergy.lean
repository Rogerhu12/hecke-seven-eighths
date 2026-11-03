import HeckeSkeleton.LowEnergy.ActualFrozenAggregation
import HeckeSkeleton.LowEnergy.InactiveWindows
import HeckeSkeleton.LowEnergy.WindowTuples

/-!
# Actual marked tuples after the frozen-state and Gaussian estimates

The active marked ideal is aggregated exactly from its physical tuple and
split into at most `slots+1` ratio-two dyads.  Inactive tuples retain their
reciprocal-prime weights and the target Hecke phase.  Every active slot
subset is included.  The energy theorem below calls the derived two-sieve
frozen-state theorem directly; it introduces no energy hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open HeckeSkeleton.LowEnergy.ActualFrozenAggregation
open HeckeSkeleton.LowEnergy.WindowTuples HeckeSkeleton.LowEnergy.InactiveWindows
open scoped Classical BigOperators NumberField nonZeroDivisors ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def InactiveGood (frozen : ExteriorIdeal K S) {g : PrimeWindowGeometry}
    (I : Finset (Fin g.slots)) (b : I → ExteriorPrime K S) : Prop :=
  ∀ i : I, ¬(b i).val.asIdeal ∣ frozen.val.val

def InactiveRowGood {g : PrimeWindowGeometry}
    (I : Finset (Fin g.slots)) (b : I → ExteriorPrime K S) (k : Ideal (𝓞 K)) : Prop :=
  ∀ i : I, ¬(b i).val.asIdeal ∣ k

def ActiveGood (frozen P : ExteriorIdeal K S) : Prop :=
  ∀ p ∈ exteriorSupport K S P, ¬p.val.asIdeal ∣ frozen.val.val

def tupleDatum (frozen : ExteriorIdeal K S) (u : S.unit K) {g : PrimeWindowGeometry}
    (I : Finset (Fin g.slots)) (b : I → ExteriorPrime K S)
    (hb : InactiveGood K S frozen I b) : FixedData K S where
  frozen := frozen
  puncture := primeSetIdeal K S ∅
  puncture_squarefree := primeSetIdeal_squarefree K S ∅
  rowUnit := u
  inactive := Finset.univ.image b
  inactive_away := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨hb i, ?_⟩
    rw [emptyPrimeIdeal_val]
    exact (b i).val.prime.not_dvd_one

def markDyadIndices (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (A : Finset (Fin g.slots)) : Finset ℕ :=
  (activeIdeals K S g T Z A).image
    (DyadicReindex.index (fun P : ExteriorIdeal K S => P.val.val.absNorm))

def ordinaryMarkDyad (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (A : Finset (Fin g.slots)) (j : ℕ) : Finset (Ideal (𝓞 K)) :=
  (activeIdealDyad K S g T Z A j).image (fun P => P.val.val)

def ordinaryActiveWeight (frozen : ExteriorIdeal K S) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (A : Finset (Fin g.slots))
    (P : Ideal (𝓞 K)) : ℂ :=
  if hP : IsExterior K S P then
    if ActiveGood K S frozen (toExterior K S P hP) then
      idealCoefficient K S g T Z A (activeWeight K S ψ g Z A) (toExterior K S P hP)
    else 0
  else 0

theorem ordinaryActiveWeight_exterior (frozen : ExteriorIdeal K S)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (A : Finset (Fin g.slots))
    (P : ExteriorIdeal K S) :
    ordinaryActiveWeight K S frozen ψ g T Z A P.val.val =
      if ActiveGood K S frozen P then
        idealCoefficient K S g T Z A (activeWeight K S ψ g Z A) P else 0 := by
  rw [ordinaryActiveWeight, dif_pos (exterior_isExterior K S P)]
  rfl

theorem ordinaryActiveWeight_on_tuple (frozen : ExteriorIdeal K S)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (A : Finset (Fin g.slots))
    (a : A → ExteriorPrime K S) (ha : a ∈ activeTuples K S g T Z A) :
    ordinaryActiveWeight K S frozen ψ g T Z A (activeIdeal K S A a).val.val =
      if ActiveGood K S frozen (activeIdeal K S A a) then
        activeWeight K S ψ g Z A a else 0 := by
  rw [ordinaryActiveWeight_exterior]
  by_cases hgood : ActiveGood K S frozen (activeIdeal K S A a)
  · simp only [if_pos hgood]
    exact TupleCore.pushCoeff_apply _ _ (activeIdeal_injOn K S g T Z A) _ ha
  · simp only [if_neg hgood]

/-- The actual inactive tuple removes only a row-dependent guard.  The
squarefree row and its powerful complement are the original ideal parts. -/
theorem tupleDatum_row_admissible (x : ExteriorIdeal K S × SixthUnitClasses K S)
    {g : PrimeWindowGeometry} (I : Finset (Fin g.slots))
    (b : I → ExteriorPrime K S)
    (hb : InactiveGood K S (exteriorPowerfulPart K S x.1) I b)
    (hk : InactiveRowGood K S I b (exteriorResidualPart K S x.1).val.val) :
    RowAdmissible K S
      (tupleDatum K S (exteriorPowerfulPart K S x.1) (Quotient.out x.2) I b hb)
      (exteriorResidualPart K S x.1) where
  squarefree := IdealRows.residualPart_squarefree x.1.val
  frozen_coprime := (IdealRows.powerful_residual_coprime x.1.val).symm
  puncture_coprime := by
    dsimp only [tupleDatum]
    rw [emptyPrimeIdeal_val]
    exact isCoprime_one_right
  inactive_away := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hk i

theorem tupleDatum_mark_admissible (frozen : ExteriorIdeal K S) (u : S.unit K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
    (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
    (hb : b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A))
    (hgood : InactiveGood K S frozen ((Finset.univ \ J) \ A) b)
    (P : ExteriorIdeal K S) (hP : P ∈ activeIdeals K S g T Z A)
    (hPgood : ActiveGood K S frozen P) :
    MarkAdmissible K S (tupleDatum K S frozen u _ b hgood) P := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hP
  refine ⟨activeIdeal_squarefree K S A a, ?_, ?_⟩
  · intro p hp
    refine ⟨hPgood p hp, ?_⟩
    dsimp only [tupleDatum]
    rw [emptyPrimeIdeal_val]
    exact p.val.prime.not_dvd_one
  · change Disjoint (Finset.univ.image b)
      (exteriorSupport K S (primeSetIdeal K S (Finset.univ.image a)))
    rw [exteriorSupport_primeSetIdeal]
    apply Finset.disjoint_left.mpr
    intro p hpb hpa
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hpb
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpa
    have hne : i.val ≠ j.val := by
      intro hij
      exact (Finset.mem_sdiff.mp i.property).2 (hij.symm ▸ j.property)
    have hiw := Fintype.mem_piFinset.mp hb i
    have hjw := Fintype.mem_piFinset.mp ha j
    rw [hi] at hiw
    rw [hj] at hjw
    exact Finset.disjoint_left.mp (primeWindow_disjoint K S g T Z i j hne) hiw hjw

theorem ordinaryActiveWeight_admissible (frozen : ExteriorIdeal K S) (u : S.unit K)
    (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
    (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
    (hb : b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A))
    (hgood : InactiveGood K S frozen ((Finset.univ \ J) \ A) b)
    (P : ExteriorIdeal K S) (hP : P ∈ activeIdeals K S g T Z A)
    (ha : ordinaryActiveWeight K S frozen ψ g T Z A P.val.val ≠ 0) :
    MarkAdmissible K S (tupleDatum K S frozen u _ b hgood) P := by
  apply tupleDatum_mark_admissible K S frozen u g T Z J A hA b hb hgood P hP
  by_contra hbad
  exact ha (by rw [ordinaryActiveWeight_exterior, if_neg hbad])

theorem ordinaryActiveWeight_bound (g : PrimeWindowGeometry) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ (frozen : ExteriorIdeal K S)
      (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (Z : ℝ) (A : Finset (Fin g.slots)) (P : Ideal (𝓞 K)),
      ‖ordinaryActiveWeight K S frozen ψ g T Z A P‖ ≤ W := by
  obtain ⟨W, hW, hw⟩ := exists_activeIdealWeight_bound K S g
  refine ⟨W, hW, ?_⟩
  intro frozen ψ T Z A P
  by_cases hP : IsExterior K S P
  · by_cases hA : ActiveGood K S frozen (toExterior K S P hP)
    · simpa only [ordinaryActiveWeight, dif_pos hP, if_pos hA] using hw ψ T Z A (toExterior K S P hP)
    · simpa only [ordinaryActiveWeight, dif_pos hP, if_neg hA, norm_zero] using zero_le_one.trans hW
  · simpa only [ordinaryActiveWeight, dif_neg hP, norm_zero] using zero_le_one.trans hW

theorem ordinaryMarkDyad_support (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (A : Finset (Fin g.slots)) (j : ℕ) :
    ∀ P ∈ ordinaryMarkDyad K S g T Z A j,
      IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
  have h := activeIdealDyad_support K S g T hZ A j hQ
  exact ⟨exterior_isExterior K S Q, h.1, h.2.2.le⟩

theorem ordinaryMarkDyad_ratio (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (A : Finset (Fin g.slots)) (j : ℕ) :
    ∀ P ∈ ordinaryMarkDyad K S g T Z A j,
      1 ≤ safeNorm P / (2 : ℝ) ^ j ∧ safeNorm P / (2 : ℝ) ^ j ≤ 2 := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
  rw [safeNorm_exterior K S Q]
  have h := (activeIdealDyad_support K S g T hZ A j hQ).2
  exact ⟨(le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using h.1),
    (div_le_iff₀ (by positivity)).mpr h.2.le⟩

theorem markDyadIndices_card_le (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 1 ≤ Z)
    (A : Finset (Fin g.slots)) :
    (markDyadIndices K S g T Z A).card ≤ g.slots + 1 := by
  refine (activeIdeals_dyadic_count K S g T hZ A).trans (Nat.add_le_add_right ?_ 1)
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ A)

theorem markDyadIndices_nonempty (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (A : Finset (Fin g.slots)) {j : ℕ}
    (hj : j ∈ markDyadIndices K S g T Z A) :
    ∃ P ∈ activeIdeals K S g T Z A, P ∈ activeIdealDyad K S g T Z A j := by
  obtain ⟨P, hP, hj⟩ := Finset.mem_image.mp hj
  exact ⟨P, hP, Finset.mem_filter.mpr ⟨hP, hj⟩⟩

variable (D : ThetaArithmeticData K S)

def frozenTupleRow (frozen : ExteriorIdeal K S) (u : S.unit K)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots)) (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
    (k : Ideal (𝓞 K)) : ℂ :=
  if hb : InactiveGood K S frozen ((Finset.univ \ J) \ A) b then
    if InactiveRowGood K S ((Finset.univ \ J) \ A) b k then
      ∑ j ∈ markDyadIndices K S g T Z A,
        frozenReflectedRow K S D (tupleDatum K S frozen u _ b hb) F θ
          (ordinaryActiveWeight K S frozen ψ g T Z A) Z (ordinaryMarkDyad K S g T Z A j) k
    else 0
  else 0

def activeSubsetRow (frozen : ExteriorIdeal K S) (u : S.unit K)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J A : Finset (Fin g.slots)) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A),
    inactiveTwistedWeight K S ψ g Z ((Finset.univ \ J) \ A) b *
      frozenTupleRow K S D frozen u F θ ψ g T Z J A b k

def markedFrozenRow (frozen : ExteriorIdeal K S) (u : S.unit K)
    (F : FiniteMellinData K S) (θ ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (J : Finset (Fin g.slots)) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ A ∈ (Finset.univ \ J).powerset,
    activeSubsetRow K S D frozen u F θ ψ g T Z J A k

/-- The full actual active/inactive tuple assembly calls the derived
frozen-state estimate.  Its only analytic energy premises are the original
quadratic and cubic sieves, and all constants precede the physical scale,
row shell, selected slots, inactive tuples and powerful ideal. -/
theorem actual_marked_tuple_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (g : PrimeWindowGeometry) (delta eps C0 rho : ℝ)
    (hdelta : 0 < delta) (hdelta' : delta ≤ 1) (heps : 0 < eps)
    (hC0 : 0 ≤ C0) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (frozen : ExteriorIdeal K S) (u : S.unit K) (Z Klo q Ccut : ℝ),
      1 < Z → 1 ≤ Klo → 0 < q → 0 < Ccut →
      IdealRows.Powerful frozen.val → Real.log Ccut ≤ C0 →
      Real.log ((2 : ℝ) ^ g.slots) ≤ C0 →
      ∀ J : Finset (Fin g.slots),
      Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤ q →
      exteriorNorm K S frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      ∀ rows : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∑ k ∈ rows, ‖markedFrozenRow K S D frozen u F θ ψ g T Z J k‖ ^ 2) ≤
        C * exteriorNorm K S frozen ^ (-(1 / 2 : ℝ) + rho) *
          Z ^ ((5 / 6 : ℝ) - 2 * ((J.card : ℝ) / (6 * g.slots)) +
            23 * delta + 2 * eps) := by
  obtain ⟨Ce, hCe, he⟩ := actual_frozen_row_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta eps C0 rho hdelta hdelta' heps hC0 hrho
  obtain ⟨W, hW, hw⟩ := ordinaryActiveWeight_bound K S g
  obtain ⟨Ci, hCi, hi⟩ := exists_twisted_inactive_energy_constant K S g
  let L : ℝ := g.slots + 1
  let N : ℝ := (2 : ℝ) ^ g.slots
  refine ⟨N ^ 2 * Ci * L ^ 2 * Ce * W ^ 2, by dsimp [N, L]; positivity, ?_⟩
  intro ψ T frozen u Z Klo q Ccut hZ hK hq hCut hf hlogCut hlogWin J hselected hrow
    rows hrows hkr
  let d : ℝ := (J.card : ℝ) / (6 * g.slots)
  let E : ℝ := Ce * W ^ 2 * exteriorNorm K S frozen ^ (-(1 / 2 : ℝ) + rho) *
    Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps)
  have hE : 0 ≤ E :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hCe.le (sq_nonneg W))
        (Real.rpow_nonneg (exteriorNorm_pos K S frozen).le _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hL : 0 < L := by dsimp [L]; positivity
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hd := selected_exponent_bounds g J
  have htuple (A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
      (b : ↥((Finset.univ \ J) \ A) → ExteriorPrime K S)
      (hb : b ∈ activeTuples K S g T Z ((Finset.univ \ J) \ A)) :
      (∑ k ∈ rows, ‖frozenTupleRow K S D frozen u F θ ψ g T Z J A b k‖ ^ 2) ≤ L ^ 2 * E := by
    by_cases hgood : InactiveGood K S frozen ((Finset.univ \ J) \ A) b
    · let f := tupleDatum K S frozen u _ b hgood
      have hblock (j : ℕ) (hj : j ∈ markDyadIndices K S g T Z A) :
          (∑ k ∈ rows, ‖frozenReflectedRow K S D f F θ
            (ordinaryActiveWeight K S frozen ψ g T Z A) Z (ordinaryMarkDyad K S g T Z A j) k‖ ^ 2) ≤ E := by
        obtain ⟨P, hP, hPj⟩ := markDyadIndices_nonempty K S g T Z A hj
        have hpLower := (activeIdealDyad_support K S g T (zero_lt_one.trans hZ) A j hPj).2.1
        have hwindow := inactive_times_mark_lower_le K S g T hZ.le J A hA b hb P hP
          ((2 : ℝ) ^ j) hpLower
        have h := he f Z Klo ((2 : ℝ) ^ j) q d Ccut N hZ hK
          (one_le_pow₀ (by norm_num)) hq hCut (by dsimp [N]; positivity)
          hd.1 hd.2 hf rfl hselected hrow hwindow hlogCut hlogWin rows
          (ordinaryMarkDyad K S g T Z A j) hrows
          (ordinaryMarkDyad_support K S g T (zero_lt_one.trans hZ) A j) hkr
          (ordinaryMarkDyad_ratio K S g T (zero_lt_one.trans hZ) A j)
          (ordinaryActiveWeight K S frozen ψ g T Z A) W hW0 (fun P _ => hw frozen ψ T Z A P)
        exact h.2
      have hs := InactiveCore.finite_weighted_energy_le (markDyadIndices K S g T Z A) rows
        (fun _ => (1 : ℂ))
        (fun j k => frozenReflectedRow K S D f F θ
          (ordinaryActiveWeight K S frozen ψ g T Z A) Z (ordinaryMarkDyad K S g T Z A j) k) hblock
      have hcard : ((markDyadIndices K S g T Z A).card : ℝ) ≤ L := by
        dsimp only [L]
        exact_mod_cast markDyadIndices_card_le K S g T hZ.le A
      simp only [one_mul, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
      have hcontract :
          (∑ k ∈ rows, ‖frozenTupleRow K S D frozen u F θ ψ g T Z J A b k‖ ^ 2) ≤
            ∑ k ∈ rows, ‖∑ j ∈ markDyadIndices K S g T Z A,
              frozenReflectedRow K S D f F θ (ordinaryActiveWeight K S frozen ψ g T Z A)
                Z (ordinaryMarkDyad K S g T Z A j) k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [frozenTupleRow, dif_pos hgood]
        split_ifs
        · exact le_rfl
        · simpa only [norm_zero, pow_two, zero_mul] using sq_nonneg
            ‖∑ j ∈ markDyadIndices K S g T Z A,
              frozenReflectedRow K S D f F θ (ordinaryActiveWeight K S frozen ψ g T Z A)
                Z (ordinaryMarkDyad K S g T Z A j) k‖
      exact hcontract.trans (hs.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hE))
    · simpa only [frozenTupleRow, dif_neg hgood, norm_zero, pow_two, zero_mul,
        Finset.sum_const_zero]
        using mul_nonneg (sq_nonneg L) hE
  have hsubset (A : Finset (Fin g.slots)) (hA : A ∈ (Finset.univ \ J).powerset) :
      (∑ k ∈ rows, ‖activeSubsetRow K S D frozen u F θ ψ g T Z J A k‖ ^ 2) ≤ Ci * (L ^ 2 * E) := by
    exact hi ψ T Z hZ.le ((Finset.univ \ J) \ A)
      (activeTuples K S g T Z ((Finset.univ \ J) \ A)) rows
      (frozenTupleRow K S D frozen u F θ ψ g T Z J A) (L ^ 2 * E)
      (fun _ h => h) (mul_nonneg (sq_nonneg L) hE)
      (fun b hb => htuple A (Finset.mem_powerset.mp hA) b hb)
  have hs := InactiveCore.finite_weighted_energy_le ((Finset.univ \ J).powerset) rows
    (fun _ => (1 : ℂ))
    (fun A k => activeSubsetRow K S D frozen u F θ ψ g T Z J A k) hsubset
  have hcard : (((Finset.univ \ J).powerset).card : ℝ) ≤ N := by
    rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ \ J))
  simp only [one_mul, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hcomb := hs.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2)
    (mul_nonneg hCi.le (mul_nonneg (sq_nonneg L) hE)))
  convert hcomb using 1 <;> simp only [markedFrozenRow, E, d] <;> ring

#print axioms ordinaryActiveWeight_bound
#print axioms actual_marked_tuple_energy

end HeckeSkeleton.LowEnergy.ActualMarkedTupleEnergy
