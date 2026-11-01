import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedAnnuli
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedCount
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedComplete

/-! Original prime windows and their actual residual canonical marks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedWindows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open CanonicalChildren ProviderNodes ProviderMarkedSlots ProviderMarkedReindex
  ProviderMarkedTupleSplit ProviderMarkedMellin
open scoped Classical BigOperators nonZeroDivisors Function

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

theorem prime_exterior (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ Sset) :
    IsExterior K Sset p.asIdeal := by
  refine ⟨p.ne_bot, ?_⟩
  intro q hq
  have he : q = p := by
    by_contra hne
    exact q.prime.not_unit ((q.isCoprime_of_ne p hne).isUnit_of_dvd hq)
  simpa only [he] using hp

theorem idealLists_disjoint {J : ℕ}
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (hdis : Pairwise (Disjoint on lists)) :
    Pairwise (Disjoint on fun i => (lists i).image HeightOneSpectrum.asIdeal) := by
  intro i k hik
  apply Finset.disjoint_left.mpr
  intro P hPi hPk
  obtain ⟨p, hp, hpP⟩ := Finset.mem_image.mp hPi
  obtain ⟨q, hq, hqP⟩ := Finset.mem_image.mp hPk
  have he : p = q := HeightOneSpectrum.ext (hpP.trans hqP.symm)
  exact Finset.disjoint_left.mp (hdis hik) hp (by simpa only [he] using hq)

/-- Original individual coefficients acquire only their Mobius sign
and a unit Mellin phase. The lists and exponents are unchanged. -/
theorem marks {J : ℕ} (slotCap : ℕ) (Z z : ℝ)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (lengths : Fin J → ℝ)
    (hJ : J ≤ slotCap) (hlen : ∀ i, 0 ≤ lengths i)
    (htotal : (∑ i, lengths i) ≤ z)
    (hext : ∀ i p, p ∈ lists i → p ∉ Sset)
    (hwindow : ∀ i p, p ∈ lists i →
      (1 / 2) * Z ^ lengths i ≤ ProviderMarkedPools.norm p.asIdeal ∧
      ProviderMarkedPools.norm p.asIdeal ≤ 2 * Z ^ lengths i)
    (ha : ∀ i p, p ∈ lists i → ‖a i p.asIdeal‖ ≤ 1)
    (hdis : Pairwise (Disjoint on lists)) (t : ℝ) :
    MarkConditions K S slotCap Z z (1 / 2) 2 Finset.univ
      (fun i => (lists i).image HeightOneSpectrum.asIdeal) (primeWeight a t) lengths where
  card_le := by simpa only [Finset.card_univ, Fintype.card_fin] using hJ
  length_nonneg := fun i hi => hlen i
  total_length := htotal
  prime := by
    intro i hi P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact p.prime
  exterior := by
    intro i hi P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact prime_exterior S p (hext i p hp)
  norm_window := by
    intro i hi P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact hwindow i p hp
  weights_le := by
    intro i hi P hP
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hP
    exact primeWeight_norm_le a t i p.asIdeal (ha i p hp)
  disjoint := fun i hi k hk hik => idealLists_disjoint lists hdis hik

theorem restriction_sum {d : ℕ} (J : Finset (Fin d)) (lengths : Fin d → ℝ) :
    (∑ i : Fin J.card, lengths (slot J i)) = ∑ i ∈ J, lengths i := by
  calc
    _ = ∑ i : J, lengths i.val := Fintype.sum_equiv J.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort J lengths

theorem remaining_sum {d : ℕ} (J : Finset (Fin d)) (lengths : Fin d → ℝ) :
    (∑ i : Fin (remaining J).card, lengths (slot (remaining J) i)) =
      (∑ i, lengths i) - ∑ i ∈ J, lengths i := by
  rw [restriction_sum, remaining, Finset.sum_sdiff (Finset.subset_univ J)]

/-- A common fixed multiplicative envelope for every selected product.
Only the original per-slot norm windows are used. -/
theorem product_window {J : ℕ} (slotCap : ℕ) (hJ : J ≤ slotCap)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (lengths : Fin J → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hwindow : ∀ i p, p ∈ lists i →
      (1 / 2) * Z ^ lengths i ≤ ProviderMarkedPools.norm p.asIdeal ∧
      ProviderMarkedPools.norm p.asIdeal ≤ 2 * Z ^ lengths i)
    (p : Fin J → HeightOneSpectrum (𝓞 K)) (hp : p ∈ tuples lists) :
    ((2 : ℝ) ^ slotCap)⁻¹ ≤ ProviderMarkedPools.norm (primeProduct Finset.univ p) /
      Z ^ (∑ i, lengths i) ∧
      ProviderMarkedPools.norm (primeProduct Finset.univ p) / Z ^ (∑ i, lengths i) ≤
        (2 : ℝ) ^ slotCap := by
  rw [ProviderMarkedScale.normalized_primeProduct Finset.univ p lengths Z hZ]
  have hlo (i : Fin J) : (1 / 2 : ℝ) ≤ ProviderMarkedPools.norm (p i).asIdeal / Z ^ lengths i :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr
      (hwindow i (p i) (Fintype.mem_piFinset.mp hp i)).1
  have hhi (i : Fin J) : ProviderMarkedPools.norm (p i).asIdeal / Z ^ lengths i ≤ 2 :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mpr
      (hwindow i (p i) (Fintype.mem_piFinset.mp hp i)).2
  constructor
  · calc
      ((2 : ℝ) ^ slotCap)⁻¹ ≤ ((2 : ℝ) ^ J)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).mpr
          (pow_le_pow_right₀ (by norm_num) hJ)
      _ = ∏ _i : Fin J, (1 / 2 : ℝ) := by simp only [Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, one_div, inv_pow]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i hi => hlo i)
  · calc
      _ ≤ ∏ _i : Fin J, (2 : ℝ) := Finset.prod_le_prod₀
        (fun i hi => (div_pos (ProviderMarkedPools.norm_pos (p i).ne_bot)
          (Real.rpow_pos_of_pos hZ _)).le) (fun i hi => hhi i)
      _ = (2 : ℝ) ^ J := by simp
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hJ

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedWindows

end
