import CubicSieve.CoprimeGramGeneral

/-! Coprime-column Gram bounds for an arbitrary actual cubic matrix.
The two finite support arguments are adapted from the generic vendor lemmas;
no quadratic-character estimate is applied to the cubic family.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.CoprimeGram
open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel
open scoped Classical BigOperators

def supportCost {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) : ℝ :=
  (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors I).toFinset.card
theorem supportCost_le_divisorCount {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    supportCost u ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) := by
  classical
  set m := UniqueFactorizationMonoid.normalizedFactors u with hm
  set S := m.toFinset with hS
  have hmem : ∀ p : Ideal (𝓞 F), p ∈ S ↔ p ∈ m := fun p => Multiset.mem_toFinset
  have hprime : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p ((hmem p).mp hp)
  have hnorm : ∀ p ∈ S, normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p ((hmem p).mp hp)
  have key : ∀ s : Finset (Ideal (𝓞 F)), s ⊆ S →
      UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val := by
    intro s hs
    have hirr : ∀ p ∈ s.val, Irreducible p := by
      intro p hp
      exact hprime p (hs (by simpa using hp))
    have h1 := UniqueFactorizationMonoid.normalizedFactors_prod_eq s.val hirr
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, h1]
    rw [Multiset.map_congr rfl (fun p hp => hnorm p (hs (by simpa using hp))),
      Multiset.map_id']
  have hinj : Set.InjOn (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F)))) := by
    intro s hs t ht hst
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have htsub : t ⊆ S := Finset.mem_powerset.mp ht
    have hsval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val :=
      key s hssub
    have htval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ t, p) = t.val :=
      key t htsub
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := hst
    rw [hst'] at hsval
    exact Finset.val_inj.mp (hsval.symm.trans htval)
  have hmaps : Set.MapsTo (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F))))
      (↑(DedekindZetaZeroFree.LargeSieve.idealDivisors u) : Set (Ideal (𝓞 F))) := by
    intro s hs
    change (∏ p ∈ s, p) ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors u
    rw [DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hu]
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have hle : s.val ≤ m := by
      rw [Multiset.le_iff_subset s.nodup]
      intro p hp
      exact (hmem p).mp (hssub (by simpa using hp))
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, ← Ideal.prod_normalizedFactors_eq_self hu]
    exact Multiset.prod_dvd_prod_of_le hle
  have hcard : S.powerset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisors u).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcost : supportCost u = (2 : ℝ) ^ S.card := by
    rw [supportCost, hS, ← hm]
  rw [hcost]
  have hpc : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]
    push_cast
    ring
  rw [← hpc]
  exact_mod_cast hcard

theorem sup_eq_top_iff_disjoint_normalizedFactors
    {F : Type} [Field F] [NumberField F] {u v : Ideal (𝓞 F)} (hu : u ≠ ⊥) (hv : v ≠ ⊥) :
    u ⊔ v = ⊤ ↔ Disjoint (UniqueFactorizationMonoid.normalizedFactors u).toFinset
      (UniqueFactorizationMonoid.normalizedFactors v).toFinset := by
  constructor
  · intro h
    have hprod : (UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v).prod = 1 := by
      have h1 := Ideal.sup_eq_prod_inf_factors hu hv
      rw [h, ← Ideal.one_eq_top] at h1
      exact h1.symm
    rw [Finset.disjoint_left]
    intro x hxu hxv
    rw [Multiset.mem_toFinset] at hxu hxv
    have hxmem : x ∈ UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v := Multiset.mem_inter.mpr ⟨hxu, hxv⟩
    have hdvd : x ∣ (UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v).prod := Multiset.dvd_prod hxmem
    rw [hprod] at hdvd
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor x hxu).not_isUnit
      (isUnit_of_dvd_one hdvd)
  · intro hd
    rw [Ideal.sup_eq_prod_inf_factors hu hv]
    have hinter : UniqueFactorizationMonoid.normalizedFactors u ∩
        UniqueFactorizationMonoid.normalizedFactors v = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx
      exact (Finset.disjoint_left.mp hd (Multiset.mem_toFinset.mpr (Multiset.mem_inter.mp hx).1))
        (Multiset.mem_toFinset.mpr (Multiset.mem_inter.mp hx).2)
    rw [hinter, Multiset.prod_zero, Ideal.one_eq_top]


theorem supportCost_epsilon (K : Type) [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      supportCost I ≤ C * (I.absNorm : ℝ) ^ ε := by
  obtain ⟨C, hC, hb⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow K ε hε
  exact ⟨C, hC, fun I hI => (supportCost_le_divisorCount I hI).trans (hb I)⟩

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def pairRow {m n : Type*} [Fintype n]
    (rows : m → ExteriorIdeal K S) (cols : n → ExteriorIdeal K S)
    (z : n → ℂ) (i : m) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j).val.val (cols k).val.val then
    (positiveKernel K S D (rows i) (cols j) * z j) *
      star (positiveKernel K S D (rows i) (cols k) * z k) else 0

/-- Removing intersecting column supports costs only a divisor epsilon factor.
The energy hypothesis is for the very same cubic matrix appearing on the left. -/
theorem pairRow_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n : Type*} [Fintype m] [Fintype n]
      (rows : m → ExteriorIdeal K S) (cols : n → ExteriorIdeal K S)
      (N U : ℝ), 1 ≤ N → 0 ≤ U →
      (∀ j, exteriorNorm K S (cols j) ≤ N) →
      (∀ x : n → ℂ, (∑ i, ‖∑ j, positiveKernel K S D (rows i) (cols j) * x j‖ ^ 2) ≤
        U * ∑ j, ‖x j‖ ^ 2) →
      ∀ z : n → ℂ,
        (∑ i, ‖pairRow K S D rows cols z i‖) ≤
          U * C * N ^ ε * ∑ j, ‖z j‖ ^ 2 := by
  obtain ⟨C, hC, hcost⟩ := supportCost_epsilon K ε hε
  have hC0 : 0 ≤ C := (by linarith : 0 < C).le
  refine ⟨C, by linarith, ?_⟩
  intro m n _ _ rows cols N U hN hU hcols hA z
  let s := fun j : n => (UniqueFactorizationMonoid.normalizedFactors (cols j).val.val).toFinset
  let E := ∑ j, supportCost (cols j).val.val * ‖z j‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg
    (fun j _ => mul_nonneg (by unfold supportCost; positivity) (sq_nonneg _))
  have hdisj (j k : n) :
      IsCoprime (cols j).val.val (cols k).val.val ↔ Disjoint (s j) (s k) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact sup_eq_top_iff_disjoint_normalizedFactors
      (by exact nonZeroDivisors.coe_ne_zero (cols j).val)
      (by exact nonZeroDivisors.coe_ne_zero (cols k).val)
  have hsq := General.coprime_bilinear_operator_bound s s
    (fun i j => positiveKernel K S D (rows i) (cols j))
    (fun i j => positiveKernel K S D (rows i) (cols j)) U U hU hU hA hA z z
  have heq : (∑ i, ‖pairRow K S D rows cols z i‖) ^ 2 ≤ U * U * E * E := by
    simpa only [pairRow, hdisj, s, E, supportCost] using hsq
  have hmass : (∑ i, ‖pairRow K S D rows cols z i‖) ≤ U * E := by
    have hm : 0 ≤ ∑ i, ‖pairRow K S D rows cols z i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    nlinarith [mul_nonneg hU hE]
  have hEbound : E ≤ C * N ^ ε * ∑ j, ‖z j‖ ^ 2 := by
    unfold E
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (hcost (cols j).val.val (nonZeroDivisors.coe_ne_zero (cols j).val)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols j) hε.le) hC0)
  calc
    _ ≤ U * E := hmass
    _ ≤ U * (C * N ^ ε * ∑ j, ‖z j‖ ^ 2) := mul_le_mul_of_nonneg_left hEbound hU
    _ = _ := by ring

end CubicSieve.CoprimeGram

