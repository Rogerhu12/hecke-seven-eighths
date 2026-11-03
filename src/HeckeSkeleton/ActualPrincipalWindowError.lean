import HeckeGeneral.Analysis.PrincipalEulerFactor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The primitive principal window error follows from the actual local Euler
formulas, disjoint windows, and nonnegative weights. No reflection, prime
distribution, or nonzero-normalizer input is used. The only mathematical
premise is that the target is unramified at every exterior prime.
UNCOMPILED static candidate, 2026-10-12; native_runs=0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualPrincipalWindowDraft

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def windowRatio (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) : ℂ :=
  -localCompensatedEulerCorrection K S P ψ 1 p s 1 (1 / 6) /
    localPrincipalCorrection K S P ψ p s

/-- The local relative estimate is uniform on the whole requested half-plane.
Only large prime norm is required, with a target-independent cutoff. -/
theorem exists_windowRatio_bound :
    ∃ B C : ℝ, 1 ≤ B ∧ 1 ≤ C ∧
      ∀ (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S) (s : ℂ),
        UnramifiedAt K ψ p.val → B ≤ (p.val.asIdeal.absNorm : ℝ) → 7 / 8 < s.re →
        ‖windowRatio K S P ψ p s - 1‖ ≤ C * (p.val.asIdeal.absNorm : ℝ) ^ (-(7 / 8 : ℝ)) := by
  obtain ⟨A, hA, hH⟩ := norm_localPrincipalCorrection_sub_one_le K S
    (σ₀ := 7 / 8) (by norm_num)
  obtain ⟨D, hD, hG⟩ := norm_localCompensated_add_principal_le K S
  refine ⟨max 1 (6 * A), max 1 (2 * D), le_max_left _ _, le_max_left _ _, ?_⟩
  intro P ψ p s hψ hp hs
  let q : ℝ := p.val.asIdeal.absNorm
  have hq1 : 1 < q := by
    change (1 : ℝ) < (p.val.asIdeal.absNorm : ℝ)
    exact_mod_cast one_lt_primeIdeal_absNorm K p.val
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hAq : 6 * A ≤ q := (le_max_right _ _).trans hp
  have hdecay (a : ℝ) (ha : a ≤ -1) : q ^ a ≤ q⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hq1.le ha
  have hHsmall : ‖localPrincipalCorrection K S P ψ p s - 1‖ ≤ 1 / 2 := by
    have hb := hH P ψ p s hs.le
    have hsum : q ^ (-2 : ℝ) + q ^ (-1 - s.re) + q ^ (3 - 6 * s.re) ≤ 3 * q⁻¹ := by
      linarith [hdecay (-2) (by norm_num), hdecay (-1 - s.re) (by linarith),
        hdecay (3 - 6 * s.re) (by linarith)]
    calc
      _ ≤ A * (q ^ (-2 : ℝ) + q ^ (-1 - s.re) + q ^ (3 - 6 * s.re)) := hb
      _ ≤ A * (3 * q⁻¹) := mul_le_mul_of_nonneg_left hsum hA
      _ = (3 * A) / q := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hq0).mpr (by linarith)
  have hHlower : 1 / 2 ≤ ‖localPrincipalCorrection K S P ψ p s‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (localPrincipalCorrection K S P ψ p s)
    rw [norm_one, norm_sub_rev] at hh
    linarith
  have hHne := localPrincipalCorrection_ne_zero K S P ψ p (by linarith : 1 / 2 < s.re)
  have hid : windowRatio K S P ψ p s - 1 =
      -(localCompensatedEulerCorrection K S P ψ 1 p s 1 (1 / 6) +
        localPrincipalCorrection K S P ψ p s) / localPrincipalCorrection K S P ψ p s := by
    unfold windowRatio
    field_simp [hHne] <;> ring
  rw [hid, norm_div, norm_neg]
  calc
    _ ≤ (D * q ^ (-s.re)) / ‖localPrincipalCorrection K S P ψ p s‖ :=
      div_le_div_of_nonneg_right (hG P ψ p s hψ (by linarith)) (norm_nonneg _)
    _ ≤ 2 * D * q ^ (-s.re) := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hHlower)).mpr
      have hpos : 0 ≤ D * q ^ (-s.re) := mul_nonneg hD (Real.rpow_nonneg hq0.le _)
      nlinarith
    _ ≤ max 1 (2 * D) * q ^ (-(7 / 8 : ℝ)) :=
      mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith))
        (Real.rpow_nonneg hq0.le _) (le_trans zero_le_one (le_max_left _ _))

theorem primeWindow_weight_ne_zero (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (i : Fin g.slots) (p : ExteriorPrime K S)
    (hp : p ∈ primeWindow K S g T Z i) : windowWeight K S g Z i p ≠ 0 := by
  obtain ⟨q, _hq, he⟩ := Finset.mem_image.mp hp
  have hq := (Finset.mem_filter.mp q.property).2.2.2
  have hv : q.val = p.val := congrArg Subtype.val he
  simpa only [windowWeight, hv] using hq

theorem primeWindow_norm_gt_scale (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {Z : ℝ} (hZ : 0 < Z) (i : Fin g.slots) (p : ExteriorPrime K S)
    (hp : p ∈ primeWindow K S g T Z i) : primeScale g Z < (p.val.asIdeal.absNorm : ℝ) := by
  have hw := primeWindow_weight_ne_zero K S g T Z i p hp
  have hmem := g.support_annular i hw
  have hscale : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  simpa only [one_mul] using (lt_div_iff₀ hscale).mp hmem.1

theorem windowTuple_injective (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := primeWindow_weight_ne_zero K S g T Z i (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := primeWindow_weight_ne_zero K S g T Z j (p j) (Fintype.mem_piFinset.mp hp j)
  rw [← he] at hj
  exact Set.disjoint_left.mp (g.disjoint i j hij) hi hj

/-- A finite product estimate with an explicit degree-dependent constant. -/
theorem norm_finset_prod_sub_one_le {ι : Type*} (F : Finset ι) (f : ι → ℂ)
    {M d : ℝ} (hM : 1 ≤ M) (hd : 0 ≤ d)
    (hf : ∀ i ∈ F, ‖f i‖ ≤ M) (he : ∀ i ∈ F, ‖f i - 1‖ ≤ d) :
    ‖∏ i ∈ F, f i - 1‖ ≤ (F.card : ℝ) * M ^ F.card * d := by
  revert hf he
  induction F using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i F hi ih =>
    intro hf he
    have hfF : ∀ j ∈ F, ‖f j‖ ≤ M := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have heF : ∀ j ∈ F, ‖f j - 1‖ ≤ d := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hih := ih hfF heF
    have hid : f i * ∏ j ∈ F, f j - 1 =
        f i * (∏ j ∈ F, f j - 1) + (f i - 1) := by ring
    rw [Finset.prod_insert hi, hid]
    have hb :
        ‖f i * ((∏ j ∈ F, f j) - 1) + (f i - 1)‖ ≤
          ‖f i‖ * ‖(∏ j ∈ F, f j) - 1‖ + d :=
      (norm_add_le (f i * ((∏ j ∈ F, f j) - 1)) (f i - 1)).trans
        (add_le_add (le_of_eq (norm_mul (f i) ((∏ j ∈ F, f j) - 1)))
          (he i (Finset.mem_insert_self i F)))
    have hb' := mul_le_mul (hf i (Finset.mem_insert_self _ _)) hih (norm_nonneg _)
      (le_trans zero_le_one hM)
    have hp : 1 ≤ M ^ F.card := one_le_pow₀ hM
    have hMd : 0 ≤ M := le_trans zero_le_one hM
    simp only [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg hMd hd),
      mul_nonneg (sub_nonneg.mpr hM) hd]

def realWindowWeight (g : PrimeWindowGeometry) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) : ℝ :=
  (windowWeight K S g Z i p).re * (p.val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ))

theorem realWindowWeight_nonneg (g : PrimeWindowGeometry) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) : 0 ≤ realWindowWeight K S g Z i p :=
  mul_nonneg (g.nonnegative i _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem realWindowWeight_cast (g : PrimeWindowGeometry) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) :
    (realWindowWeight K S g Z i p : ℂ) =
      windowWeight K S g Z i p * (p.val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) := by
  have hw : ((windowWeight K S g Z i p).re : ℂ) = windowWeight K S g Z i p := by
    apply Complex.ext <;> simp [windowWeight, g.real_valued]
  rw [realWindowWeight, Complex.ofReal_mul, hw, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast <;> rfl

/-- Delete the actual selected local factors using finite modification of
a convergent complex product, which requires their proved non-vanishing. -/
theorem tuple_correction_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    {s : ℂ} (hs : 7 / 8 < s.re) (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) :
    (∏' q : ExteriorPrime K S,
      if q ∈ Finset.univ.image p then 1 else localPrincipalCorrection K S P ψ q s) *
      (∏ i : Fin g.slots, windowWeight K S g Z i (p i) *
        ((p i).val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) *
        localCompensatedEulerCorrection K S P ψ 1 (p i) s 1 (1 / 6)) =
    (principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) *
      ((∏ i : Fin g.slots, realWindowWeight K S g Z i (p i) : ℝ) : ℂ) *
      ∏ i : Fin g.slots, windowRatio K S P ψ (p i) s := by
  let F := Finset.univ.image p
  let H := fun q : ExteriorPrime K S => localPrincipalCorrection K S P ψ q s
  have hH : ∀ q, H q ≠ 0 := fun q => localPrincipalCorrection_ne_zero K S P ψ q (by linarith)
  have hmult := multipliable_localPrincipalCorrection K S P ψ (by linarith : 2 / 3 < s.re)
  have hFprod : (∏ q ∈ F, H q) = ∏ i : Fin g.slots, H (p i) := by
    exact Finset.prod_image (windowTuple_injective K S g T Z p hp).injOn
  have hprod1 : (∏ q ∈ F, if q ∈ F then (1 : ℂ) else H q) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    exact if_pos hq
  have hdel : (∏' q, if q ∈ F then (1 : ℂ) else H q) =
      principalCorrection K S P ψ s * (∏ i : Fin g.slots, H (p i))⁻¹ := by
    have hm := hmult.tsum_congr_cofinite₀ (s := F) (fun q _ => hH q)
      (g := fun q => if q ∈ F then 1 else H q) (fun q hq => by simp [hq, H])
    rw [hprod1, one_div, hFprod] at hm
    exact hm
  have hprodne : (∏ i : Fin g.slots, H (p i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hH _)
  have hG (i : Fin g.slots) :
      localCompensatedEulerCorrection K S P ψ 1 (p i) s 1 (1 / 6) =
        (-1 : ℂ) * H (p i) * windowRatio K S P ψ (p i) s := by
    have hHi : localPrincipalCorrection K S P ψ (p i) s ≠ 0 := hH (p i)
    unfold windowRatio
    dsimp only [H]
    field_simp [hHi] <;> ring
  have hprodG : (∏ i : Fin g.slots,
      localCompensatedEulerCorrection K S P ψ 1 (p i) s 1 (1 / 6)) =
      (-1 : ℂ) ^ g.slots * (∏ i : Fin g.slots, H (p i)) *
        ∏ i : Fin g.slots, windowRatio K S P ψ (p i) s := by
    simp only [hG, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (∏' q, if q ∈ F then (1 : ℂ) else H q) * _ = _
  rw [hdel]
  simp_rw [← realWindowWeight_cast]
  rw [Finset.prod_mul_distrib, hprodG, ← Complex.ofReal_prod]
  field_simp [hprodne] <;> ring

def tupleWeight (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) : ℝ :=
  ∏ i : Fin g.slots, realWindowWeight K S g Z i (p i)

theorem tupleWeight_nonneg (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) : 0 ≤ tupleWeight K S g Z p :=
  Finset.prod_nonneg (fun i _ => realWindowWeight_nonneg K S g Z i (p i))

theorem compensatedPrincipalCorrection_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    {s : ℂ} (hs : 7 / 8 < s.re) :
    compensatedPrincipalCorrection K S P ψ g T Z s =
      (principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) *
        ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          (tupleWeight K S g Z p : ℂ) * ∏ i : Fin g.slots, windowRatio K S P ψ (p i) s := by
  unfold compensatedPrincipalCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact (tuple_correction_eq K S P ψ g T Z hs p hp).trans (by simp only [tupleWeight, mul_assoc])

theorem principalMain_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z =
      (principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) *
        ((∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i), tupleWeight K S g Z p : ℝ) : ℂ) := by
  have hcancel : (Z : ℂ) ^ (1 / 36 : ℂ) * (Z : ℂ) ^ (-(1 / 36 : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hZ.ne')]
    norm_num
  have hslot (i : Fin g.slots) : normalizerSlot K S g T Z i =
      ((∑ p ∈ primeWindow K S g T Z i, realWindowWeight K S g Z i p : ℝ) : ℂ) := by
    unfold normalizerSlot
    simp_rw [← realWindowWeight_cast]
    exact (Complex.ofReal_sum _ _).symm
  have hprod : (∏ i : Fin g.slots, normalizerSlot K S g T Z i) =
      ((∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i), tupleWeight K S g Z p : ℝ) : ℂ) := by
    simp_rw [hslot]
    rewrite [← Complex.ofReal_prod, Finset.prod_univ_sum]
    rfl
  unfold primeNormalizer
  rw [hprod]
  calc
    _ = (principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) *
        ((Z : ℂ) ^ (1 / 36 : ℂ) * (Z : ℂ) ^ (-(1 / 36 : ℂ))) *
        ((∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i), tupleWeight K S g Z p : ℝ) : ℂ) := by ring
    _ = _ := by rw [hcancel]; ring

theorem norm_weighted_sum_sub_mass_le {ι : Type*} (F : Finset ι) (w : ι → ℝ) (f : ι → ℂ)
    {d : ℝ} (hd : 0 ≤ d) (hw : ∀ i ∈ F, 0 ≤ w i) (hf : ∀ i ∈ F, ‖f i - 1‖ ≤ d) :
    ‖(∑ i ∈ F, (w i : ℂ) * f i) - ((∑ i ∈ F, w i : ℝ) : ℂ)‖ ≤ d * ∑ i ∈ F, w i := by
  have hid : (∑ i ∈ F, (w i : ℂ) * f i) - ((∑ i ∈ F, w i : ℝ) : ℂ) =
      ∑ i ∈ F, (w i : ℂ) * (f i - 1) := by
    rw [Complex.ofReal_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  calc
    _ ≤ ∑ i ∈ F, ‖(w i : ℂ) * (f i - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, w i * d := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (hf i hi) (hw i hi)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem actual_principal_window_error (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (hψ : ∀ p : ExteriorPrime K S, UnramifiedAt K ψ p.val) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ (Z : ℝ) (s : ℂ), Z₀ ≤ Z → 7 / 8 < s.re →
      ‖compensatedPrincipalCorrection K S P ψ g T Z s -
        principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖ ≤
      C * Z ^ (-principalSlotSaving g) *
        ‖principalCorrection K S P ψ s * (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g T Z‖ := by
  obtain ⟨B, A, hB, hA, hratio⟩ := exists_windowRatio_bound K S
  have hJ : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hexp : 0 < (1 / 6 : ℝ) / g.slots := div_pos (by norm_num) hJ
  obtain ⟨Z₁, hZ₁⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hexp)) B
  let M : ℝ := 1 + A
  let C : ℝ := (g.slots : ℝ) * M ^ g.slots * A
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hC : 0 < C := mul_pos (mul_pos hJ (pow_pos hM0 _)) hA0
  refine ⟨C, max 1 Z₁, hC, le_max_left _ _, ?_⟩
  intro Z s hZ hs
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hscaleB : B ≤ primeScale g Z := hZ₁ Z ((le_max_right _ _).trans hZ)
  let d : ℝ := A * Z ^ (-principalSlotSaving g)
  have hd : 0 ≤ d := mul_nonneg (le_trans zero_le_one hA) (Real.rpow_nonneg hZ0.le _)
  have hdA : d ≤ A := by
    exact mul_le_of_le_one_right (le_trans zero_le_one hA)
      (Real.rpow_le_one_of_one_le_of_nonpos hZ1 (neg_nonpos.mpr (principalSlotSaving_pos g).le))
  have hri (p : Fin g.slots → ExteriorPrime K S)
      (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) (i : Fin g.slots) :
      ‖windowRatio K S P ψ (p i) s - 1‖ ≤ d := by
    have hpi := Fintype.mem_piFinset.mp hp i
    have hq := primeWindow_norm_gt_scale K S g T hZ0 i (p i) hpi
    have hscale0 : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
    have hb := hratio P ψ (p i) s (hψ _) (hscaleB.trans hq.le) hs
    have hrpow : (primeScale g Z) ^ (-(7 / 8 : ℝ)) =
        Z ^ (-(2 * principalSlotSaving g)) := by
      rw [primeScale, ← Real.rpow_mul hZ0.le]
      congr 1
      unfold principalSlotSaving
      field_simp [hJ.ne'] <;> ring
    calc
      _ ≤ A * ((p i).val.asIdeal.absNorm : ℝ) ^ (-(7 / 8 : ℝ)) := hb
      _ ≤ A * (primeScale g Z) ^ (-(7 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hscale0 hq.le (by norm_num))
          (le_trans zero_le_one hA)
      _ = A * Z ^ (-(2 * principalSlotSaving g)) := by rw [hrpow]
      _ ≤ d := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith [principalSlotSaving_pos g]))
        (le_trans zero_le_one hA)
  let F := Fintype.piFinset (fun i => primeWindow K S g T Z i)
  let w := tupleWeight K S g Z
  let f := fun p : Fin g.slots → ExteriorPrime K S => ∏ i : Fin g.slots, windowRatio K S P ψ (p i) s
  have hf : ∀ p ∈ F, ‖f p - 1‖ ≤ C * Z ^ (-principalSlotSaving g) := by
    intro p hp
    have hrnorm (i : Fin g.slots) : ‖windowRatio K S P ψ (p i) s‖ ≤ M := by
      have hh := norm_sub_norm_le (windowRatio K S P ψ (p i) s) (1 : ℂ)
      rw [norm_one] at hh
      have hh' := hri p hp i
      dsimp [M]
      linarith
    have hb := norm_finset_prod_sub_one_le Finset.univ (fun i => windowRatio K S P ψ (p i) s)
      hM hd (fun i _ => hrnorm i) (fun i _ => hri p hp i)
    simpa only [Finset.card_univ, Fintype.card_fin, C, d, mul_assoc] using hb
  have hmass : 0 ≤ ∑ p ∈ F, w p := Finset.sum_nonneg (fun p _ => tupleWeight_nonneg K S g Z p)
  have hsum := norm_weighted_sum_sub_mass_le F w f
    (mul_nonneg hC.le (Real.rpow_nonneg hZ0.le _)) (fun p _ => tupleWeight_nonneg K S g Z p) hf
  simp only [compensatedPrincipalCorrection_eq K S P ψ g T Z hs, principalMain_eq K S P ψ g T hZ0 s]
  change ‖(principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) * (∑ p ∈ F, (w p : ℂ) * f p) -
      (principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) * ((∑ p ∈ F, w p : ℝ) : ℂ)‖ ≤
    C * Z ^ (-principalSlotSaving g) *
      ‖(principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) * ((∑ p ∈ F, w p : ℝ) : ℂ)‖
  have hmainnorm : ‖(principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots) *
      ((∑ p ∈ F, w p : ℝ) : ℂ)‖ =
      ‖principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots‖ * ∑ p ∈ F, w p := by
    rw [norm_mul, Complex.norm_of_nonneg hmass]
  rw [← mul_sub, norm_mul, hmainnorm]
  calc
    _ ≤ ‖principalCorrection K S P ψ s * (-1 : ℂ) ^ g.slots‖ *
        (C * Z ^ (-principalSlotSaving g) * ∑ p ∈ F, w p) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = _ := by ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualPrincipalWindowDraft
