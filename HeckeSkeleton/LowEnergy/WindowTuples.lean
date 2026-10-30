import HeckeSkeleton.LowEnergy.TupleCore
import HeckeSkeleton.LowEnergy.DyadicReindex
import HeckeSkeleton.LowEnergy.SlotTuples
import HeckeSkeleton.LowCauchy.General
import HeckeGeneral.Analysis.IdealSquarefreeSupport

/-!
# Exact active-window aggregation into actual exterior ideals

The physical windows are disjoint. Therefore an active tuple is recovered
from its squarefree prime-product ideal: no arbitrary tuple-multiplicity
bound is introduced. The output coefficient remains a function of that
ideal alone and retains the same norm bound.

Project adapter, to be checked with the complete project dependencies.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.WindowTuples

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.LowEnergy.TupleCore
open scoped BigOperators Classical ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem primeSetIdeal_injective : Function.Injective (primeSetIdeal K S) := by
  intro A B h
  have h' := congrArg (fun I : ExteriorIdeal K S => I.val) h
  change squarefreeIdeal K (A.image Subtype.val) =
    squarefreeIdeal K (B.image Subtype.val) at h'
  exact Finset.image_injective Subtype.val_injective
    (SquarefreeAmplification.squarefreeIdeal_injective K h')

theorem primeWindow_disjoint (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (i j : Fin g.slots) (hij : i ≠ j) :
    Disjoint (primeWindow K S g T Z i) (primeWindow K S g T Z j) := by
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have hi' := HeckeSkeleton.LowCauchy.lc_weight_ne_zero_of_mem_window hi
  have hj' := HeckeSkeleton.LowCauchy.lc_weight_ne_zero_of_mem_window hj
  exact Set.disjoint_left.mp (g.disjoint i j hij)
    (Function.mem_support.mpr hi') (Function.mem_support.mpr hj')

def activeTuples (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (I : Finset (Fin g.slots)) : Finset (I → ExteriorPrime K S) :=
  Fintype.piFinset (fun i : I => primeWindow K S g T Z i)

def activeIdeal {g : PrimeWindowGeometry} (I : Finset (Fin g.slots))
    (p : I → ExteriorPrime K S) : ExteriorIdeal K S :=
  primeSetIdeal K S (Finset.univ.image p)

@[simp] theorem activeIdeal_restrict {g : PrimeWindowGeometry}
    (p : Fin g.slots → ExteriorPrime K S) (I : Finset (Fin g.slots)) :
    activeIdeal K S I (fun i => p i) = subsetPrimeIdeal K S p I := by
  apply congrArg (primeSetIdeal K S)
  ext q
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

/-- Different surviving slots still lie in disjoint physical windows. -/
theorem activeTuple_injective (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (I : Finset (Fin g.slots))
    {p : I → ExteriorPrime K S} (hp : p ∈ activeTuples K S g T Z I) :
    Function.Injective p := by
  intro i j hij
  by_contra hne
  have hi := Fintype.mem_piFinset.mp hp i
  have hj := Fintype.mem_piFinset.mp hp j
  rw [hij] at hi
  exact Finset.disjoint_left.mp
    (primeWindow_disjoint K S g T Z i j (fun h => hne (Subtype.ext h))) hi hj

/-- The encoded ideal is squarefree by its actual distinct-prime product
definition, including the empty active set. -/
theorem activeIdeal_squarefree {g : PrimeWindowGeometry}
    (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S) :
    Squarefree (activeIdeal K S I p).val.val :=
  HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _

/-- Exact norm, without an assumed tuple multiplicity or ideal norm bound. -/
theorem activeIdeal_norm_product {g : PrimeWindowGeometry}
    (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S)
    (hp : Function.Injective p) :
    exteriorNorm K S (activeIdeal K S I p) =
      ∏ i : I, ((p i).val.asIdeal.absNorm : ℝ) := by
  calc
    exteriorNorm K S (activeIdeal K S I p) =
        idealNorm K (squarefreeIdeal K ((Finset.univ.image p).image Subtype.val)) := rfl
    _ = ∏ q ∈ (Finset.univ.image p).image Subtype.val,
        (Ideal.absNorm q.asIdeal : ℝ) := idealNorm_squarefreeIdeal_eq_prod K _
    _ = ∏ q ∈ Finset.univ.image (Subtype.val ∘ p),
        (Ideal.absNorm q.asIdeal : ℝ) := by rw [Finset.image_image]
    _ = ∏ i : I, ((p i).val.asIdeal.absNorm : ℝ) :=
      Finset.prod_image (fun i _ j _ hij => hp (Subtype.ext hij))

/-- The actual active ideal lies in the window dictated by the active slot
count.  No power of Z is introduced by ideal aggregation. -/
theorem activeIdeal_norm_bounds (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (I : Finset (Fin g.slots)) {p : I → ExteriorPrime K S}
    (hp : p ∈ activeTuples K S g T Z I) :
    primeScale g Z ^ I.card ≤ exteriorNorm K S (activeIdeal K S I p) ∧
      exteriorNorm K S (activeIdeal K S I p) ≤ (2 * primeScale g Z) ^ I.card := by
  rw [activeIdeal_norm_product K S I p (activeTuple_injective K S g T Z I hp)]
  have hb (i : I) := HeckeSkeleton.LowCauchy.lc_norm_mem_window hZ
    (Fintype.mem_piFinset.mp hp i)
  have hps : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  constructor
  · calc
      primeScale g Z ^ I.card = ∏ _i : I, primeScale g Z := by simp
      _ ≤ ∏ i : I, ((p i).val.asIdeal.absNorm : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => hps.le) (fun i _ => (hb i).1.le)
  · calc
      (∏ i : I, ((p i).val.asIdeal.absNorm : ℝ)) ≤ ∏ _i : I, 2 * primeScale g Z :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => (hb i).2.le)
      _ = (2 * primeScale g Z) ^ I.card := by simp

theorem activeIdeal_injOn (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (I : Finset (Fin g.slots)) :
    Set.InjOn (activeIdeal K S I) (activeTuples K S g T Z I) := by
  intro p hp q hq heq
  have hset := primeSetIdeal_injective K S heq
  apply image_univ_injOn_piFinset
    (fun i : I => primeWindow K S g T Z i) ?_ hp hq hset
  intro i j hij
  apply primeWindow_disjoint K S g T Z i j
  intro h
  exact hij (Subtype.ext h)

def activeIdeals (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (I : Finset (Fin g.slots)) : Finset (ExteriorIdeal K S) :=
  (activeTuples K S g T Z I).image (activeIdeal K S I)

/-- Support interface for the two actual ideal sieve inputs.  Exteriority
is built into P's type, squarefreeness and both norm bounds are proved. -/
theorem activeIdeals_support (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (I : Finset (Fin g.slots)) {P : ExteriorIdeal K S}
    (hP : P ∈ activeIdeals K S g T Z I) :
    Squarefree P.val.val ∧ primeScale g Z ^ I.card ≤ exteriorNorm K S P ∧
      exteriorNorm K S P ≤ (2 * primeScale g Z) ^ I.card := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
  exact ⟨activeIdeal_squarefree K S I p, activeIdeal_norm_bounds K S g T hZ I hp⟩

theorem one_le_primeScale (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 1 ≤ Z) :
    1 ≤ primeScale g Z := Real.one_le_rpow hZ (by positivity)

/-- The nominal selected, active and inactive lengths exactly use the
original `1/6` mark budget. -/
theorem slot_exponent_partition (g : PrimeWindowGeometry)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J) :
    (J.card : ℝ) / (6 * g.slots) + (A.card : ℝ) / (6 * g.slots) +
      ((Finset.univ \ J \ A).card : ℝ) / (6 * g.slots) = (1 / 6 : ℝ) := by
  have hc : (J.card : ℝ) + A.card + (Finset.univ \ J \ A).card = g.slots := by
    exact_mod_cast (show J.card + A.card + (Finset.univ \ J \ A).card = g.slots by
      simpa only [Fintype.card_fin] using SlotTuples.card_partition J A hA)
  have hn : (g.slots : ℝ) ≠ 0 := by exact_mod_cast g.slots_pos.ne'
  rw [← add_div, ← add_div, hc]
  field_simp [hn]

theorem surviving_exponent_eq (g : PrimeWindowGeometry)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J) :
    ((A.card : ℝ) + (Finset.univ \ J \ A).card) / (6 * g.slots) =
      (1 / 6 : ℝ) - (J.card : ℝ) / (6 * g.slots) := by
  have h := slot_exponent_partition g J A hA
  rw [add_div]
  linarith

theorem selected_exponent_bounds (g : PrimeWindowGeometry)
    (J : Finset (Fin g.slots)) :
    0 ≤ (J.card : ℝ) / (6 * g.slots) ∧
      (J.card : ℝ) / (6 * g.slots) ≤ (1 / 6 : ℝ) := by
  have hs : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hcard : (J.card : ℝ) ≤ g.slots := by
    exact_mod_cast (show J.card ≤ g.slots by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ J))
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (show (0 : ℝ) < 6 * g.slots by positivity)).mpr
  nlinarith

theorem primeScale_pow_eq_rpow (g : PrimeWindowGeometry)
    {Z : ℝ} (hZ : 0 < Z) (r : ℕ) :
    primeScale g Z ^ r = Z ^ ((r : ℝ) / (6 * g.slots)) := by
  rw [primeScale, ← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The target selected norm is bracketed by its nominal power with one
fixed geometry factor, uniform in the selected subset and physical tuple. -/
theorem selected_norm_bounds (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) :
    Z ^ ((J.card : ℝ) / (6 * g.slots)) ≤
      exteriorNorm K S (subsetPrimeIdeal K S p J) ∧
    exteriorNorm K S (subsetPrimeIdeal K S p J) ≤
      (2 : ℝ) ^ g.slots * Z ^ ((J.card : ℝ) / (6 * g.slots)) := by
  have h := HeckeSkeleton.LowCauchy.lc_subsetNorm_bounds hZ hp J
  rw [primeScale_pow_eq_rpow g hZ J.card] at h
  refine ⟨h.1, h.2.trans ?_⟩
  rw [mul_pow, primeScale_pow_eq_rpow g hZ J.card]
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hZ.le _)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ J))

/-- The physical product of the inactive norm and an active dyad's lower
endpoint obeys the surviving `1/6-d` budget.  The sole slack is `2^slots`.
All norms are the original prime-product ideal norms. -/
theorem inactive_times_mark_lower_le (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 1 ≤ Z)
    (J A : Finset (Fin g.slots)) (hA : A ⊆ Finset.univ \ J)
    (b : (Finset.univ \ J \ A) → ExteriorPrime K S)
    (hb : b ∈ activeTuples K S g T Z (Finset.univ \ J \ A))
    (P : ExteriorIdeal K S) (hP : P ∈ activeIdeals K S g T Z A)
    (Plo : ℝ) (hPlo : Plo ≤ exteriorNorm K S P) :
    exteriorNorm K S (activeIdeal K S (Finset.univ \ J \ A) b) * Plo ≤
      (2 : ℝ) ^ g.slots * Z ^ ((1 / 6 : ℝ) - (J.card : ℝ) / (6 * g.slots)) := by
  let I := Finset.univ \ J \ A
  have hZ0 := zero_lt_one.trans_le hZ
  have hbn := activeIdeal_norm_bounds K S g T hZ0 I hb
  have hpn := (activeIdeals_support K S g T hZ0 A hP).2
  have hps : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
  have hcard : I.card + A.card ≤ g.slots := by
    have h := SlotTuples.card_partition J A hA
    rw [Fintype.card_fin] at h
    dsimp [I]
    omega
  have hexp : ((I.card + A.card : ℕ) : ℝ) / (6 * g.slots) =
      (1 / 6 : ℝ) - (J.card : ℝ) / (6 * g.slots) := by
    simpa only [Nat.cast_add, add_comm] using surviving_exponent_eq g J A hA
  calc
    _ ≤ exteriorNorm K S (activeIdeal K S I b) * exteriorNorm K S P :=
      mul_le_mul_of_nonneg_left hPlo (by
        change (0 : ℝ) ≤ ((activeIdeal K S I b).val.val.absNorm : ℝ)
        exact Nat.cast_nonneg _)
    _ ≤ (2 * primeScale g Z) ^ I.card * (2 * primeScale g Z) ^ A.card :=
      mul_le_mul hbn.2 hpn.2 (by
        change (0 : ℝ) ≤ (P.val.val.absNorm : ℝ)
        exact Nat.cast_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ (I.card + A.card) *
        Z ^ ((1 / 6 : ℝ) - (J.card : ℝ) / (6 * g.slots)) := by
      rw [← pow_add, mul_pow, primeScale_pow_eq_rpow g hZ0, hexp]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard)
      (Real.rpow_nonneg hZ0.le _)

/-- A product of `I.card` physical windows needs at most `I.card+1`
ratio-two mark dyads, independently of `Z`. -/
theorem activeIdeals_dyadic_count (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 1 ≤ Z)
    (I : Finset (Fin g.slots)) :
    ((activeIdeals K S g T Z I).image
      (DyadicReindex.index (fun P : ExteriorIdeal K S => P.val.val.absNorm))).card ≤
        I.card + 1 := by
  apply DyadicReindex.window_shell_image_card_le
    (fun P : ExteriorIdeal K S => P.val.val.absNorm) _
    (one_le_pow₀ (one_le_primeScale g hZ)) I.card
  intro P hP
  have h := activeIdeals_support K S g T (zero_lt_one.trans_le hZ) I hP
  exact ⟨h.2.1, by simpa only [mul_pow] using h.2.2⟩

def activeIdealDyad (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (I : Finset (Fin g.slots)) (j : ℕ) : Finset (ExteriorIdeal K S) :=
  (activeIdeals K S g T Z I).filter
    (fun P => DyadicReindex.index (fun Q : ExteriorIdeal K S => Q.val.val.absNorm) P = j)

/-- Actual squarefree active ideals in one dyad have exactly the ratio-two
norm bounds required by the common Mellin separation. -/
theorem activeIdealDyad_support (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 0 < Z)
    (I : Finset (Fin g.slots)) (j : ℕ) {P : ExteriorIdeal K S}
    (hP : P ∈ activeIdealDyad K S g T Z I j) :
    Squarefree P.val.val ∧ (2 : ℝ) ^ j ≤ exteriorNorm K S P ∧
      exteriorNorm K S P < 2 * (2 : ℝ) ^ j := by
  obtain ⟨hm, hj⟩ := Finset.mem_filter.mp hP
  have hp : 0 < P.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors P.val
  have hb := DyadicReindex.index_bounds_real
    (fun Q : ExteriorIdeal K S => Q.val.val.absNorm) hp
  exact ⟨(activeIdeals_support K S g T hZ I hm).1,
    by simpa only [hj] using hb.1,
    by simpa only [hj, pow_succ, mul_comm] using hb.2⟩

theorem active_ideal_sum_eq_dyads (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) {Z : ℝ} (hZ : 1 ≤ Z)
    (I : Finset (Fin g.slots)) (f : ExteriorIdeal K S → ℂ) :
    (∑ P ∈ activeIdeals K S g T Z I, f P) =
      ∑ j ∈ Finset.Ico (Nat.log 2 ⌊primeScale g Z ^ I.card⌋₊)
        (Nat.log 2 ⌊primeScale g Z ^ I.card⌋₊ + I.card + 1),
        ∑ P ∈ activeIdealDyad K S g T Z I j, f P := by
  apply DyadicReindex.finite_sum_eq_window_shells
    (fun P : ExteriorIdeal K S => P.val.val.absNorm) _
    (one_le_pow₀ (one_le_primeScale g hZ)) I.card
  intro P hP
  have h := activeIdeals_support K S g T (zero_lt_one.trans_le hZ) I hP
  exact ⟨h.2.1, by simpa only [mul_pow] using h.2.2⟩

def idealCoefficient (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (I : Finset (Fin g.slots))
    (a : (I → ExteriorPrime K S) → ℂ) : ExteriorIdeal K S → ℂ :=
  pushCoeff (activeTuples K S g T Z I) (activeIdeal K S I) a

theorem idealCoefficient_norm_le (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (I : Finset (Fin g.slots))
    (a : (I → ExteriorPrime K S) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ p ∈ activeTuples K S g T Z I, ‖a p‖ ≤ C)
    (P : ExteriorIdeal K S) :
    ‖idealCoefficient K S g T Z I a P‖ ≤ C :=
  pushCoeff_norm_le _ _ a hC ha P

/-- The active marks are summed in the linear row, and the resulting
coefficient depends only on P. This is precisely the hybrid sieve shape. -/
theorem active_tuple_sum_eq_ideal_sum (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (I : Finset (Fin g.slots))
    (a : (I → ExteriorPrime K S) → ℂ) (kernel : ExteriorIdeal K S → ℂ) :
    (∑ p ∈ activeTuples K S g T Z I, a p * kernel (activeIdeal K S I p)) =
      ∑ P ∈ activeIdeals K S g T Z I,
        idealCoefficient K S g T Z I a P * kernel P :=
  sum_pushCoeff _ _ (activeIdeal_injOn K S g T Z I) a kernel

/-- The exact selected-slot restriction in the target is a free sum over
the surviving slots. No cardinality factor or norm inequality is used. -/
theorem selected_tuple_sum (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) (f : (Fin g.slots → ExteriorPrime K S) → ℂ) :
    (∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      if ∀ i ∈ J, p' i = p i then f p' else 0) =
    ∑ q ∈ Fintype.piFinset (fun i : {i // i ∉ J} => primeWindow K S g T Z i),
      f (join (fun i => i ∈ J) (fun i => p i) q) :=
  sum_piFinset_fixed _ (fun i => i ∈ J) p
    (fun i _ => Fintype.mem_piFinset.mp hp i) f

/-- The literal active coefficient from the target marked row.  Its ideal
phase is retained when the active tuple is aggregated into a single ideal. -/
def activeWeight (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (Z : ℝ)
    (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S) : ℂ :=
  (∏ i : I, windowWeight K S g Z i (p i)) *
    conj (heckeIdealCoefficient K ψ (activeIdeal K S I p).val)

/-- Compact support bounds the original weights uniformly before every
scale, selected/active subset, ray filter, character and prime tuple. -/
theorem exists_activeWeight_bound (g : PrimeWindowGeometry) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ψ : HeckeCharacter K) (Z : ℝ)
      (I : Finset (Fin g.slots)) (p : I → ExteriorPrime K S),
      ‖activeWeight K S ψ g Z I p‖ ≤ A := by
  obtain ⟨W, hW, hw⟩ := HeckeSkeleton.LowCauchy.lc_exists_weight_bound g
  let B : ℝ := max 1 W
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B ^ g.slots, one_le_pow₀ hB, ?_⟩
  intro ψ Z I p
  have hprod : ‖∏ i : I, windowWeight K S g Z i (p i)‖ ≤ B ^ I.card := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : I, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
        (hw i _).trans (le_max_right 1 W))
      _ = B ^ I.card := by simp
  calc
    ‖activeWeight K S ψ g Z I p‖ ≤
        ‖∏ i : I, windowWeight K S g Z i (p i)‖ := by
      rw [activeWeight, norm_mul, Complex.norm_conj]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_heckeIdealCoefficient_le_one K ψ _)
    _ ≤ B ^ I.card := hprod
    _ ≤ B ^ g.slots := pow_le_pow_right₀ hB (by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ I))

/-- The fixed bound survives the exact tuple-to-ideal pushforward.  Hence
the actual target coefficient is an admissible mark array in the sieve. -/
theorem exists_activeIdealWeight_bound (g : PrimeWindowGeometry) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ψ : HeckeCharacter K) (T : Finset (HeckeCharacter K))
      (Z : ℝ) (I : Finset (Fin g.slots)) (P : ExteriorIdeal K S),
      ‖idealCoefficient K S g T Z I (activeWeight K S ψ g Z I) P‖ ≤ A := by
  obtain ⟨A, hA, ha⟩ := exists_activeWeight_bound K S g
  refine ⟨A, hA, ?_⟩
  intro ψ T Z I P
  exact idealCoefficient_norm_le K S g T Z I _ (zero_le_one.trans hA)
    (fun p _ => ha ψ Z I p) P

/-- No multiplicity factor is introduced even for the literal target
weight, and the entire active sum remains inside the linear row. -/
theorem active_weighted_sum_eq_ideal_sum (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (I : Finset (Fin g.slots)) (kernel : ExteriorIdeal K S → ℂ) :
    (∑ p ∈ activeTuples K S g T Z I,
      activeWeight K S ψ g Z I p * kernel (activeIdeal K S I p)) =
    ∑ P ∈ activeIdeals K S g T Z I,
      idealCoefficient K S g T Z I (activeWeight K S ψ g Z I) P * kernel P :=
  active_tuple_sum_eq_ideal_sum K S g T Z I _ kernel

#print axioms activeIdeal_injOn
#print axioms activeIdeals_support
#print axioms active_tuple_sum_eq_ideal_sum
#print axioms selected_tuple_sum
#print axioms exists_activeIdealWeight_bound
#print axioms active_weighted_sum_eq_ideal_sum

end HeckeSkeleton.LowEnergy.WindowTuples
