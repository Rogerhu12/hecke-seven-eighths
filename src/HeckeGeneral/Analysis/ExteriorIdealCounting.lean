import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification
import HeckeGeneral.Arithmetic.PrincipalOrbitCounting
import HeckeGeneral.Analysis.LocalThetaInput

/-!
Linear lower counting for actual nonzero integral ideals outside a fixed
finite set of primes. Multiplication by a prime gives the exact counting
recurrence; induction transfers the proved ordinary ideal-count asymptotic.
No lower-count hypothesis, principal generator, or allowed section is used.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification HeckeGeneral.ThetaSkeleton
open Filter
open scoped Classical BigOperators nonZeroDivisors Topology

variable (K : Type) [Field K] [NumberField K]

def avoidsIdealPrimes (T : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) : Prop :=
  ∀ p ∈ T, ¬p.asIdeal ∣ I.val

/-- The genuine finite norm cutoff, with only the specified primes deleted. -/
def idealAvoidanceFinset (T : Finset (HeightOneSpectrum (𝓞 K))) (X : ℝ) :
    Finset (NonzeroIdeal K) :=
  (dyadicIdealSupport K (X / 2)).filter (avoidsIdealPrimes K T)

theorem mem_idealAvoidanceFinset {T : Finset (HeightOneSpectrum (𝓞 K))}
    {X : ℝ} (hX : 0 ≤ X) (I : NonzeroIdeal K) :
    I ∈ idealAvoidanceFinset K T X ↔ idealNorm K I ≤ X ∧ avoidsIdealPrimes K T I := by
  rw [idealAvoidanceFinset, Finset.mem_filter,
    mem_dyadicIdealSupport_iff K (div_nonneg hX (by norm_num))]
  rw [show 2 * (X / 2) = X by ring]

def idealAvoidanceCount (T : Finset (HeightOneSpectrum (𝓞 K))) (X : ℝ) : ℝ :=
  (idealAvoidanceFinset K T X).card

def countingPrimeIdeal (p : HeightOneSpectrum (𝓞 K)) : NonzeroIdeal K :=
  ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩

theorem idealNorm_mul_counting (I J : NonzeroIdeal K) :
    idealNorm K (I * J) = idealNorm K I * idealNorm K J := by
  simp only [idealNorm, Submonoid.coe_mul, map_mul, Nat.cast_mul]

theorem one_lt_countingPrimeNorm (p : HeightOneSpectrum (𝓞 K)) :
    1 < idealNorm K (countingPrimeIdeal K p) := by
  have hn := Ideal.absNorm_pos_of_nonZeroDivisors (countingPrimeIdeal K p)
  have hne : p.asIdeal.absNorm ≠ 1 :=
    fun h => p.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  change (1 : ℝ) < (p.asIdeal.absNorm : ℝ)
  exact_mod_cast (by change 0 < p.asIdeal.absNorm at hn; omega : 1 < p.asIdeal.absNorm)

theorem countingPrime_mul_injective (p : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (fun I : NonzeroIdeal K => countingPrimeIdeal K p * I) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ p.ne_bot (congrArg Subtype.val h)

/-- The ideals divisible by p are exactly p times the smaller cutoff.
The old avoided primes remain avoided because p is a new prime. -/
theorem idealAvoidance_divisible_filter
    (T : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ T)
    {X : ℝ} (hX : 0 ≤ X) :
    (idealAvoidanceFinset K T X).filter (fun I => p.asIdeal ∣ I.val) =
      (idealAvoidanceFinset K T (X / idealNorm K (countingPrimeIdeal K p))).image
        (fun J => countingPrimeIdeal K p * J) := by
  have hNp := idealNorm_pos K (countingPrimeIdeal K p)
  ext I
  constructor
  · intro hI
    obtain ⟨hI, hdvd⟩ := Finset.mem_filter.mp hI
    obtain ⟨hNI, havoid⟩ := (mem_idealAvoidanceFinset K hX I).mp hI
    obtain ⟨J, hJ⟩ := hdvd
    have hJ0 : J ≠ 0 := by
      intro h
      apply nonZeroDivisors.coe_ne_zero I
      simpa [h] using hJ
    let J₀ : NonzeroIdeal K := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩
    have heq : countingPrimeIdeal K p * J₀ = I := Subtype.ext hJ.symm
    refine Finset.mem_image.mpr ⟨J₀, ?_, heq⟩
    apply (mem_idealAvoidanceFinset K (div_nonneg hX hNp.le) J₀).mpr
    constructor
    · apply (le_div_iff₀ hNp).mpr
      rw [mul_comm, ← idealNorm_mul_counting, heq]
      exact hNI
    · intro q hq hqJ
      apply havoid q hq
      rw [← heq]
      exact dvd_mul_of_dvd_right hqJ p.asIdeal
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hNJ, havoid⟩ :=
      (mem_idealAvoidanceFinset K (div_nonneg hX hNp.le) J).mp hJ
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_idealAvoidanceFinset K hX _).mpr
      constructor
      · rw [idealNorm_mul_counting, mul_comm]
        exact (le_div_iff₀ hNp).mp hNJ
      · intro q hq hdiv
        rcases q.prime.dvd_mul.mp hdiv with hqp | hqJ
        · have heq : p = q := HeightOneSpectrum.asIdeal_injective
            (p.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.dvd_iff_le.mp hqp))
          exact hp (heq ▸ hq)
        · exact havoid q hq hqJ
    · exact dvd_mul_right p.asIdeal J.val

theorem idealAvoidance_nondivisible_filter
    (T : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) (X : ℝ) :
    (idealAvoidanceFinset K T X).filter (fun I => ¬p.asIdeal ∣ I.val) =
      idealAvoidanceFinset K (insert p T) X := by
  ext I
  simp only [idealAvoidanceFinset, Finset.mem_filter, avoidsIdealPrimes,
    Finset.forall_mem_insert]
  tauto

/-- Exact deletion recurrence, proved using the actual multiplication image. -/
theorem idealAvoidanceCount_recurrence
    (T : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ T)
    {X : ℝ} (hX : 0 ≤ X) :
    idealAvoidanceCount K T X = idealAvoidanceCount K (insert p T) X +
      idealAvoidanceCount K T (X / idealNorm K (countingPrimeIdeal K p)) := by
  have hc := Finset.card_filter_add_card_filter_not (s := idealAvoidanceFinset K T X)
    (fun I => p.asIdeal ∣ I.val)
  rw [idealAvoidance_divisible_filter K T p hp hX,
    Finset.card_image_of_injective _ (countingPrime_mul_injective K p),
    idealAvoidance_nondivisible_filter K T p X] at hc
  unfold idealAvoidanceCount
  exact_mod_cast hc.symm.trans (Nat.add_comm _ _)

def idealAvoidanceDensity (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  dedekindZeta_residue K * ∏ p ∈ T, (1 - (idealNorm K (countingPrimeIdeal K p))⁻¹)

theorem idealAvoidanceDensity_pos (T : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < idealAvoidanceDensity K T := by
  apply mul_pos (dedekindZeta_residue_pos K)
  apply Finset.prod_pos
  intro p _
  exact sub_pos.mpr ((inv_lt_one₀ (idealNorm_pos K (countingPrimeIdeal K p))).mpr
    (one_lt_countingPrimeNorm K p))

theorem idealAvoidanceDensity_insert
    (T : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ T) :
    idealAvoidanceDensity K (insert p T) = idealAvoidanceDensity K T -
      idealAvoidanceDensity K T / idealNorm K (countingPrimeIdeal K p) := by
  simp only [idealAvoidanceDensity, Finset.prod_insert hp, div_eq_mul_inv]
  ring

theorem idealAvoidanceCount_empty_limit :
    Tendsto (fun X : ℝ => idealAvoidanceCount K ∅ X / X) atTop
      (𝓝 (idealAvoidanceDensity K ∅)) := by
  have hlim : Tendsto
      (fun X : ℝ => (Nat.card {I : NonzeroIdeal K // idealNorm K I ≤ X} : ℝ) / X)
      atTop (𝓝 (dedekindZeta_residue K)) :=
    NumberField.Ideal.tendsto_norm_le_div_atTop₀ K
  have hden : idealAvoidanceDensity K ∅ = dedekindZeta_residue K := by
    simp [idealAvoidanceDensity]
  rw [hden]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
  congr 1
  let e : {I : NonzeroIdeal K // I ∈ idealAvoidanceFinset K ∅ X} ≃
      {I : NonzeroIdeal K // idealNorm K I ≤ X} :=
    Equiv.subtypeEquivRight (fun I => by
      simp only [mem_idealAvoidanceFinset K hX I, avoidsIdealPrimes,
        Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true])
  have hc := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, idealAvoidanceCount] using
    congrArg Nat.cast hc.symm

/-- The positive fixed-S density is derived from the proved ordinary count. -/
theorem idealAvoidanceCount_limit (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun X : ℝ => idealAvoidanceCount K T X / X) atTop
      (𝓝 (idealAvoidanceDensity K T)) := by
  induction T using Finset.induction_on with
  | empty => exact idealAvoidanceCount_empty_limit K
  | @insert p T hp ih =>
    let q := idealNorm K (countingPrimeIdeal K p)
    have hq : 0 < q := idealNorm_pos K (countingPrimeIdeal K p)
    have hscale : Tendsto (fun X : ℝ => X / q) atTop atTop :=
      Tendsto.atTop_div_const hq tendsto_id
    have hs := (ih.comp hscale).div_const q
    rw [idealAvoidanceDensity_insert K T p hp]
    apply (ih.sub hs).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hr := idealAvoidanceCount_recurrence K T p hp hX.le
    change idealAvoidanceCount K T X / X -
        (idealAvoidanceCount K T (X / q) / (X / q)) / q =
      idealAvoidanceCount K (insert p T) X / X
    rw [hr]
    field_simp [ne_of_gt hX, ne_of_gt hq]
    ring

theorem exists_idealAvoidanceCount_linear_lower
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X ≤ idealAvoidanceCount K T X := by
  let c := idealAvoidanceDensity K T / 2
  have hc : 0 < c := half_pos (idealAvoidanceDensity_pos K T)
  have hclt : c < idealAvoidanceDensity K T := by
    dsimp [c]
    linarith [idealAvoidanceDensity_pos K T]
  have he : ∀ᶠ X : ℝ in atTop, c < idealAvoidanceCount K T X / X :=
    (tendsto_order.mp (idealAvoidanceCount_limit K T)).1 c hclt
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp he
  refine ⟨c, max 1 X₁, hc, le_max_left _ _, ?_⟩
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hX)
  exact ((lt_div_iff₀ hXpos).mp (hX₁ X ((le_max_right _ _).trans hX))).le

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A genuine finite set of exterior ideals, with no selected class or sector. -/
def exteriorAmplifierIdeals (P : ℝ) : Finset (ExteriorIdeal K S) :=
  (idealAvoidanceFinset K S.toFinset P).attach.map
    ⟨(fun I => ⟨I.val, by
      intro p hp hpin
      exact (Finset.mem_filter.mp I.property).2 p (Set.mem_toFinset.mpr hpin) hp⟩),
      (by
        intro I J h
        exact Subtype.ext (congrArg (fun A : ExteriorIdeal K S => A.val) h))⟩

@[simp] theorem card_exteriorAmplifierIdeals (P : ℝ) :
    (exteriorAmplifierIdeals K S P).card = (idealAvoidanceFinset K S.toFinset P).card := by
  simp [exteriorAmplifierIdeals]

theorem norm_le_of_mem_exteriorAmplifierIdeals {P : ℝ} (hP : 0 ≤ P)
    (A : ExteriorIdeal K S) (hA : A ∈ exteriorAmplifierIdeals K S P) :
    idealNorm K A.val ≤ P := by
  obtain ⟨I, _hI, hIA⟩ := Finset.mem_map.mp hA
  have hnorm := ((mem_idealAvoidanceFinset K hP I.val).mp I.property).1
  have hval : I.val = A.val := congrArg (fun J : ExteriorIdeal K S => J.val) hIA
  rw [← hval]
  exact hnorm

theorem mem_exteriorAmplifierIdeals_iff {P : ℝ} (hP : 0 ≤ P)
    (A : ExteriorIdeal K S) :
    A ∈ exteriorAmplifierIdeals K S P ↔ idealNorm K A.val ≤ P := by
  constructor
  · exact norm_le_of_mem_exteriorAmplifierIdeals K S hP A
  · intro hA
    have hmem : A.val ∈ idealAvoidanceFinset K S.toFinset P := by
      refine (mem_idealAvoidanceFinset K hP A.val).mpr ⟨hA, ?_⟩
      intro p hp hdiv
      exact A.property p hdiv (Set.mem_toFinset.mp hp)
    exact Finset.mem_map.mpr
      ⟨⟨A.val, hmem⟩, Finset.mem_attach _ _, rfl⟩

theorem exteriorAmplifierIdeals_count_limit :
    Tendsto (fun P : ℝ => ((exteriorAmplifierIdeals K S P).card : ℝ) / P) atTop
      (𝓝 (idealAvoidanceDensity K S.toFinset)) := by
  simpa only [card_exteriorAmplifierIdeals, idealAvoidanceCount] using
    idealAvoidanceCount_limit K S.toFinset

/-- The actual exterior finite set has a positive linear lower count. -/
theorem exists_exteriorAmplifierIdeals_linear_lower :
    ∃ c P₀ : ℝ, 0 < c ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      c * P ≤ ((exteriorAmplifierIdeals K S P).card : ℝ) := by
  simpa only [card_exteriorAmplifierIdeals, idealAvoidanceCount] using
    exists_idealAvoidanceCount_linear_lower K S.toFinset

end HeckeGeneral.Analysis.ActualSIntegerMoments
