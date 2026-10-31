import HeckePort.CenteredMoment.IdealMobius
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform Rankin bounds on a fixed prime-ideal support

The constants depend only on the number field and the positive Rankin
exponent, and are uniform over the chosen finite prime support.  Large
prime ideals have local mass at most one; the product over the finitely
many small prime ideals is bounded before the support is chosen.
Injective multiplicity coding then bounds every finite set of nonzero
ideals with that exact support.

This is the general-number-field version of openai/math
`Moments/Rankin.lean` and `Moments/RankinCount.lean`.  It uses the actual
absolute ideal norm and its finite bounded-norm sets.  No counting
hypothesis or parent recurrence is assumed.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open Filter UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum

namespace HeckeSkeleton.Moments.EngineStep.PrimeSupportMass

variable {K : Type*} [Field K] [NumberField K]

def primeMass (P : Ideal (𝓞 K)) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

theorem prime_norm_ge_two (P : Ideal (𝓞 K)) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal (𝓞 K)) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal (𝓞 K)) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (K : Type*) [Field K] [NumberField K] (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal (𝓞 K)), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal (𝓞 K)) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal (𝓞 K)) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod₀
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one₀ (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal (𝓞 K)) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (bound : ℕ) :
    (∑ n ∈ Finset.range bound,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)<Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range bound) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp


def powerCode (R : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal (𝓞 K))-1

theorem powerCode_reconstruct (R : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal (𝓞 K))^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal (𝓞 K)) := by
    have hp : (P:Ideal (𝓞 K)) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal (𝓞 K))^(normalizedFactors I).count (P:Ideal (𝓞 K)) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal (𝓞 K) => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal (𝓞 K))) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal (𝓞 K)):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

set_option maxHeartbeats 800000 in
theorem fixed_support_mass (K : Type*) [Field K] [NumberField K] (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal (𝓞 K))),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product K δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let bound : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal (𝓞 K)):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range bound) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range bound),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range bound,((Ideal.absNorm (P:Ideal (𝓞 K)):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range bound)
        (fun P n => ((Ideal.absNorm (P:Ideal (𝓞 K)):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ bound)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (K : Type*) [Field K] [NumberField K] (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal (𝓞 K))),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass K δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal (𝓞 K)) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)<Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _


end HeckeSkeleton.Moments.EngineStep.PrimeSupportMass

#print axioms HeckeSkeleton.Moments.EngineStep.PrimeSupportMass.fixed_support_mass
#print axioms HeckeSkeleton.Moments.EngineStep.PrimeSupportMass.fixed_support_count

