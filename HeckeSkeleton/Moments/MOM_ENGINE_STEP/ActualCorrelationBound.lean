import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalCRT
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool
import HeckePort.Moments.ProductCRT

/-!
# The actual complete correlation and its unit-frequency radical

The characters in this file come from the normalized sextic residue family.
Their prime-power and CRT descriptions are proved, including all nonunit
zeros.  The denominator in the final bound is the norm of the actual
product of equal-depth, nonprincipal, unit-frequency primes.  The complete
prime-power quotients, and hence their nonprimitive multiplicities, remain
in the correlation throughout.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckePort.Moments.ProductCRT

section FiniteCorrelation

variable {T X Y : Type*} [CommRing T] [Fintype X] [Fintype Y]

/-- An injective right-hand residue map leaves at most one summand for
each left-hand residue.  This estimate does not discard nonunit zeros. -/
theorem fullCorrelation_norm_le_card_left
    (left : X → T) (right : Y → T) (hright : Function.Injective right)
    (f : X → ℂ) (g : Y → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (h : T) : ‖fullCorrelation left right f g h‖ ≤ (Fintype.card X : ℝ) := by
  have hrow (x : X) :
      ‖∑ y : Y, if left x - right y = h then f x * star (g y) else 0‖ ≤ 1 := by
    by_cases hex : ∃ y, left x - right y = h
    · obtain ⟨y₀, hy₀⟩ := hex
      have hsum : (∑ y : Y, if left x - right y = h then f x * star (g y) else 0) =
          f x * star (g y₀) := by
        rw [Finset.sum_eq_single y₀]
        · simp only [hy₀, if_pos]
        · intro y _ hne
          apply if_neg
          intro hy
          apply hne
          apply hright
          linear_combination hy₀ - hy
        · simp
      rw [hsum, norm_mul, norm_star]
      exact (mul_le_mul (hf x) (hg y₀) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · have hz : ∀ y, left x - right y ≠ h := by simpa only [not_exists] using hex
      simp only [hz, if_false, Finset.sum_const_zero, norm_zero]
      exact zero_le_one
  calc
    _ ≤ ∑ x : X, ‖∑ y : Y,
        if left x - right y = h then f x * star (g y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : X, (1 : ℝ) := Finset.sum_le_sum fun x _ => hrow x
    _ = _ := by simp

theorem fullCorrelation_norm_le_card_right
    (left : X → T) (right : Y → T) (hleft : Function.Injective left)
    (f : X → ℂ) (g : Y → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ y, ‖g y‖ ≤ 1)
    (h : T) : ‖fullCorrelation left right f g h‖ ≤ (Fintype.card Y : ℝ) := by
  rw [fullCorrelation_swap, norm_star]
  exact fullCorrelation_norm_le_card_left right left hleft g f hg hf (-h)

end FiniteCorrelation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance boundPrimePowerFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFinite C p n

local instance boundPrimePowerFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFintype C p n

/-- The actual normalized residue family multiplies over every power,
including the zero values on the nonunit classes. -/
theorem actual_sextic_prime_power (p : ExteriorPrime A) (n : ℕ) (x : A.R) :
    σ (A.sexticResidue (powerIdeal p n) x) = σ (A.sexticResidue (primeIdeal p) x) ^ n := by
  induction n with
  | zero =>
    change σ (A.residueValue A.sexticResidueFamily (powerIdeal p 0) x) = _
    rw [A.residueValue_top A.sexticResidueFamily _ (by
      simp [powerIdeal, ExteriorIdealEuler.pow]), map_one, pow_zero]
  | succ n ih =>
    have hprod : (powerIdeal p (n + 1)).val =
        (powerIdeal p n).val * (primeIdeal p).val := by
      simp only [powerIdeal, ExteriorIdealEuler.pow, pow_succ]
    change σ (A.residueValue A.sexticResidueFamily _ x) = _
    rw [A.sexticResidueFamily_normalized.2.2
      (powerIdeal p n) (primeIdeal p) (powerIdeal p (n + 1)) hprod x, map_mul]
    change σ (A.sexticResidue (powerIdeal p n) x) *
      σ (A.sexticResidue (primeIdeal p) x) = _
    rw [ih, pow_succ]

/-- This calibrates the actual complete ideal character with the masked
local character; it is not a primitive-character replacement. -/
theorem generatedIdealCharacter_prime_power
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (hn : n ≠ 0) :
    generatedIdealCharacter (σ := σ) (powerIdeal p n) (generator C p ^ n)
      (generator_power_generates C p n) = localMaskedCharacter C p n hn := by
  apply MulChar.ext'
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [generatedIdealCharacter_mk, actual_sextic_prime_power,
    localMaskedCharacter_mk, MulChar.pow_apply' _ hn]
  congr 1
  have hb := generatedIdealCharacter_mk (σ := σ) (primeIdeal p)
    (generator C p) (generator_generates C p) x
  rw [generatedIdealCharacter, transportCharacter_mk] at hb
  exact hb.symm

/-- A convenient actual correlation with literal prime-power generators. -/
def actualPrimePowerCorrelation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (m n : ℕ) (h : A.R) : ℂ :=
  generatedIdealCorrelation (σ := σ) (powerIdeal p m) (powerIdeal p n)
    (generator C p ^ m) (generator C p ^ n)
    (generator_power_generates C p m) (generator_power_generates C p n) h

theorem actualPrimePowerCorrelation_norm_le
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) :
    ‖actualPrimePowerCorrelation C p m n h‖ ≤ Q p ^ min m n := by
  let χm := generatedIdealCharacter (σ := σ) (powerIdeal p m)
    (generator C p ^ m) (generator_power_generates C p m)
  let χn := generatedIdealCharacter (σ := σ) (powerIdeal p n)
    (generator C p ^ n) (generator_power_generates C p n)
  have hb₁ := fullCorrelation_norm_le_card_left
    (scaledResidue (generator C p ^ m) (generator C p ^ n) _ rfl)
    (scaledResidue (generator C p ^ n) (generator C p ^ m) _ (mul_comm _ _))
    (scaledResidue_injective _ _ _ _ (pow_ne_zero _ (generator_generates C p).1))
    χm χn (fun x => finiteCharacter_norm_le_one χm x)
    (fun x => finiteCharacter_norm_le_one χn x) (Ideal.Quotient.mk _ h)
  have hb₂ := fullCorrelation_norm_le_card_right
    (scaledResidue (generator C p ^ m) (generator C p ^ n) _ rfl)
    (scaledResidue (generator C p ^ n) (generator C p ^ m) _ (mul_comm _ _))
    (scaledResidue_injective _ _ _ _ (pow_ne_zero _ (generator_generates C p).1))
    χm χn (fun x => finiteCharacter_norm_le_one χm x)
    (fun x => finiteCharacter_norm_le_one χn x) (Ideal.Quotient.mk _ h)
  have hc (r : ℕ) : (Fintype.card (CommonSupport.Residue
      (generator C p ^ r)) : ℝ) = Q p ^ r := by
    change (Fintype.card (LocalFiniteSums.Residue C p r) : ℝ) = _
    exact_mod_cast localPrimePowerResidue_card C p r
  change ‖actualPrimePowerCorrelation C p m n h‖ ≤
    (Fintype.card (CommonSupport.Residue (generator C p ^ m)) : ℝ) at hb₁
  change ‖actualPrimePowerCorrelation C p m n h‖ ≤
    (Fintype.card (CommonSupport.Residue (generator C p ^ n)) : ℝ) at hb₂
  rcases le_total m n with hmn | hnm
  · rw [min_eq_left hmn]
    exact hb₁.trans (hc m).le
  · rw [min_eq_right hnm]
    exact hb₂.trans (hc n).le

theorem actualPrimePowerCorrelation_unit_norm
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (hn : 0 < n) (hsix : ¬6 ∣ n) (k : A.R)
    (hk : ¬generator C p ∣ k) :
    ‖actualPrimePowerCorrelation C p n n (generator C p ^ n * k)‖ = Q p ^ (n - 1) := by
  have hunit : reduction C p n hn.ne'
      (Ideal.Quotient.mk (Ideal.span {generator C p ^ n}) k) ≠ 0 := by
    change Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) k ≠ 0
    intro hz
    apply hk
    apply Ideal.mem_span_singleton.mp
    have hmem : k ∈ A.extendIdeal (primeIdeal p) := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [← (generator_generates C p).2] at hmem
    exact hmem
  unfold actualPrimePowerCorrelation generatedIdealCorrelation
  rw [generatedIdealCharacter_prime_power C p n hn.ne',
    HeckePort.Moments.Local.fullCorrelation_equal_divided _ _
      (pow_ne_zero _ (generator_generates C p).1)]
  change ‖fullCorrelation (fun x : LocalFiniteSums.Residue C p n => x)
    (fun y : LocalFiniteSums.Residue C p n => y)
    (fun x => localMaskedCharacter C p n hn.ne' x)
    (fun x => localMaskedCharacter C p n hn.ne' x) (Ideal.Quotient.mk _ k)‖ = _
  simp_rw [localMaskedCharacter_apply]
  simpa only [equalDepthCorrelation, Units.val_one, one_mul] using
    equalDepthCorrelation_nonprincipal_unit_norm C p n hn 1 1
      (Ideal.Quotient.mk _ k) (by simp) hunit hsix

/-- The exact local condition selecting a prime in the `t₂` radical. -/
def unitFrequencySaving (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (m n : ℕ) (h : A.R) : Prop :=
  m = n ∧ ¬6 ∣ m ∧ ∃ k : A.R, h = generator C p ^ m * k ∧ ¬generator C p ∣ k

theorem actualPrimePowerCorrelation_radical_bound
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (hm : 0 < m) (h : A.R) :
    ‖actualPrimePowerCorrelation C p m n h‖ ≤
      Q p ^ min m n / (if unitFrequencySaving C p m n h then Q p else 1) := by
  by_cases hs : unitFrequencySaving C p m n h
  · rw [if_pos hs]
    obtain ⟨heq, hsix, k, rfl, hk⟩ := hs
    subst n
    rw [actualPrimePowerCorrelation_unit_norm C p m hm hsix k hk, min_self]
    apply le_of_eq
    rw [eq_div_iff (primeNorm_pos p).ne', ← pow_succ, Nat.sub_add_cancel hm]
  · rw [if_neg hs, div_one]
    exact actualPrimePowerCorrelation_norm_le C p m n h

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Public product-generator identity for the actual exterior ideals. -/
theorem actual_product_generates (I : ι → A.Exterior) (a : ι → A.R)
    (ha : ∀ i, A.Generates (I i) (a i)) (S : Finset ι) :
    A.Generates (GaussProductCancellation.productExterior A I S) (∏ i ∈ S, a i) := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (ha i).1), ?_⟩
  rw [← Ideal.prod_span_singleton]
  simp_rw [(ha _).2]
  change (∏ i ∈ S, A.extendIdeal (I i)) = _
  simp only [SArithmeticData.extendIdeal, GaussProductCancellation.productExterior]
  exact (map_prod (Ideal.mapHom (algebraMap (𝓞 F) A.R)) _ _).symm

theorem actual_sextic_product (I : ι → A.Exterior) (S : Finset ι) (x : A.R) :
    σ (A.sexticResidue (GaussProductCancellation.productExterior A I S) x) =
      ∏ i ∈ S, σ (A.sexticResidue (I i) x) := by
  induction S using Finset.induction_on with
  | empty =>
    change σ (A.residueValue A.sexticResidueFamily _ x) = _
    rw [A.residueValue_top A.sexticResidueFamily _ (by
      simp [GaussProductCancellation.productExterior])]
    simp
  | @insert i S hi ih =>
    have hp : (GaussProductCancellation.productExterior A I (insert i S)).val =
        (I i).val * (GaussProductCancellation.productExterior A I S).val := by
      simp [GaussProductCancellation.productExterior, Finset.prod_insert, hi]
    change σ (A.residueValue A.sexticResidueFamily _ x) = _
    rw [A.sexticResidueFamily_normalized.2.2 (I i)
      (GaussProductCancellation.productExterior A I S) _ hp x, map_mul]
    change σ (A.sexticResidue (I i) x) *
      σ (A.sexticResidue (GaussProductCancellation.productExterior A I S) x) = _
    rw [ih, Finset.prod_insert hi]

theorem generatedIdealCharacter_product
    (I : ι → A.Exterior) (a : ι → A.R) (ha : ∀ i, A.Generates (I i) (a i))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    generatedIdealCharacter (σ := σ)
      (GaussProductCancellation.productExterior A I Finset.univ)
      (∏ i, a i) (actual_product_generates I a ha Finset.univ) =
      crtCharacter (productCRT a hcop)
        (fun i => generatedIdealCharacter (σ := σ) (I i) (a i) (ha i)) := by
  apply MulChar.ext'
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [generatedIdealCharacter_mk, crtCharacter_apply, productCRT_mk]
  exact actual_sextic_product I Finset.univ x

def primePowerProduct (p : ι → ExteriorPrime A) (n : ι → ℕ) : A.Exterior :=
  GaussProductCancellation.productExterior A (fun i => powerIdeal (p i) (n i)) Finset.univ

def primePowerProductGenerator (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (n : ι → ℕ) : A.R := ∏ i, generator C (p i) ^ n i

theorem primePowerProduct_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (n : ι → ℕ) :
    A.Generates (primePowerProduct p n) (primePowerProductGenerator C p n) :=
  actual_product_generates _ _ (fun i => generator_power_generates C (p i) (n i)) _

theorem primePowerProduct_norm (p : ι → ExteriorPrime A) (n : ι → ℕ) :
    A.exteriorNorm (primePowerProduct p n) = ∏ i, Q (p i) ^ n i := by
  simp [primePowerProduct, GaussProductCancellation.productExterior, powerIdeal,
    ExteriorIdealEuler.pow, Q, SArithmeticData.exteriorNorm, idealNorm, map_prod, map_pow]

theorem primePowerGenerator_pairwise (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (n : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {generator C (p i) ^ n i})) := by
  intro i j hij
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  apply generated_elements_coprime (powerIdeal (p i) (n i)) (powerIdeal (p j) (n j))
    _ _ (generator_power_generates C (p i) (n i)) (generator_power_generates C (p j) (n j))
  have hpij : (p i).val ≠ (p j).val := by
    intro he
    exact hij (hp (Subtype.ext he))
  exact ((p i).val.isCoprime_of_ne (p j).val hpij).pow

/-- CRT applied to the actual ideal characters.  Coprimality follows
from distinct actual prime labels; no character-factorization premise is
part of this statement. -/
theorem actual_prime_power_product_correlation_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R) :
    ‖generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h‖ =
      ∏ i, ‖actualPrimePowerCorrelation C (p i) (m i) (n i) h‖ := by
  let a : ι → A.R := fun i => generator C (p i) ^ m i
  let b : ι → A.R := fun i => generator C (p i) ^ n i
  have ha := primePowerGenerator_pairwise C p hp m
  have hb := primePowerGenerator_pairwise C p hp n
  have hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})) := by
    simpa only [a, b, ← pow_add] using
      primePowerGenerator_pairwise C p hp (fun i => m i + n i)
  letI : Finite (A.R ⧸ Ideal.span {∏ i, a i}) := by
    change Finite (A.R ⧸ Ideal.span {primePowerProductGenerator C p m})
    rw [(primePowerProduct_generates C p m).2]
    exact A.exteriorResidue_finite _
  letI : Finite (A.R ⧸ Ideal.span {∏ i, b i}) := by
    change Finite (A.R ⧸ Ideal.span {primePowerProductGenerator C p n})
    rw [(primePowerProduct_generates C p n).2]
    exact A.exteriorResidue_finite _
  letI : Fintype (A.R ⧸ Ideal.span {∏ i, a i}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {∏ i, b i}) := Fintype.ofFinite _
  have hcm : generatedIdealCharacter (σ := σ) (primePowerProduct p m)
      (primePowerProductGenerator C p m) (primePowerProduct_generates C p m) =
      crtCharacter (productCRT a ha)
        (fun i => generatedIdealCharacter (σ := σ) (powerIdeal (p i) (m i)) (a i)
          (generator_power_generates C (p i) (m i))) :=
    generatedIdealCharacter_product (fun i => powerIdeal (p i) (m i)) a
      (fun i => generator_power_generates C (p i) (m i)) ha
  have hcn : generatedIdealCharacter (σ := σ) (primePowerProduct p n)
      (primePowerProductGenerator C p n) (primePowerProduct_generates C p n) =
      crtCharacter (productCRT b hb)
        (fun i => generatedIdealCharacter (σ := σ) (powerIdeal (p i) (n i)) (b i)
          (generator_power_generates C (p i) (n i))) :=
    generatedIdealCharacter_product (fun i => powerIdeal (p i) (n i)) b
      (fun i => generator_power_generates C (p i) (n i)) hb
  unfold generatedIdealCorrelation
  rw [hcm, hcn]
  exact fullModulusCorrelation_product_norm a b ha hb hab
    (fun i => generatedIdealCharacter (σ := σ) (powerIdeal (p i) (m i)) (a i)
      (generator_power_generates C (p i) (m i)))
    (fun i => generatedIdealCharacter (σ := σ) (powerIdeal (p i) (n i)) (b i)
      (generator_power_generates C (p i) (n i))) h

/-- The actual squarefree ideal supplying the second unit-frequency
saving.  Membership is determined by the original frequency. -/
def unitFrequencyRadical (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) : A.Exterior :=
  primePowerProduct p (fun i => if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0)

theorem unitFrequencyRadical_norm (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (h : A.R) :
    A.exteriorNorm (unitFrequencyRadical C p m n h) =
      ∏ i, if unitFrequencySaving C (p i) (m i) (n i) h then Q (p i) else 1 := by
  rw [unitFrequencyRadical, primePowerProduct_norm]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem primePowerProduct_min_dvd_gcd (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    (primePowerProduct p (fun i => min (m i) (n i))).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  apply dvd_gcd
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow _ (min_le_left _ _))
  · exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow _ (min_le_right _ _))

theorem unitFrequencyRadical_squarefree (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (h : A.R) :
    Squarefree (unitFrequencyRadical C p m n h).val := by
  change Squarefree (∏ i, (p i).val.asIdeal ^
    (if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0))
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    have hpij : (p i).val ≠ (p j).val := fun he => hij (hp (Subtype.ext he))
    exact (((p i).val.isCoprime_of_ne (p j).val hpij).pow).isRelPrime
  · intro i _
    split_ifs
    · simpa only [pow_one] using (p i).val.irreducible.squarefree
    · simp

theorem unitFrequencyRadical_dvd_gcd (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (h : A.R) :
    (unitFrequencyRadical C p m n h).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  apply dvd_trans (b := (primePowerProduct p (fun i => min (m i) (n i))).val)
  · apply Finset.prod_dvd_prod_of_dvd
    intro i _
    apply pow_dvd_pow
    change (if unitFrequencySaving C (p i) (m i) (n i) h then 1 else 0) ≤ min (m i) (n i)
    split_ifs with hs
    · rw [hs.1, min_self]
      simpa only [hs.1] using hm i
    · exact Nat.zero_le _
  · exact primePowerProduct_min_dvd_gcd p m n

theorem unitFrequencyRadical_norm_le_gcd (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (h : A.R) :
    A.exteriorNorm (unitFrequencyRadical C p m n h) ≤
      (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) :=
  ideal_norm_le_of_dvd (gcd_ne_zero_of_left (primePowerProduct p m).property.1)
    (unitFrequencyRadical_dvd_gcd C p m n hm h)

/-- The complete actual global correlation is bounded by the genuine gcd
norm divided by the genuine unit-frequency radical norm. -/
theorem actual_complete_correlation_gcd_radical_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (h : A.R) :
    ‖generatedIdealCorrelation (σ := σ) (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h‖ ≤
      (Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) /
        A.exteriorNorm (unitFrequencyRadical C p m n h) := by
  rw [actual_prime_power_product_correlation_norm C p hp m n h]
  calc
    _ ≤ ∏ i, Q (p i) ^ min (m i) (n i) /
        (if unitFrequencySaving C (p i) (m i) (n i) h then Q (p i) else 1) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        (fun i _ => actualPrimePowerCorrelation_radical_bound C (p i) (m i) (n i) (hm i) h)
    _ = A.exteriorNorm (primePowerProduct p (fun i => min (m i) (n i))) /
        A.exteriorNorm (unitFrequencyRadical C p m n h) := by
      rw [Finset.prod_div_distrib, primePowerProduct_norm, unitFrequencyRadical_norm]
    _ ≤ _ := div_le_div_of_nonneg_right
      (ideal_norm_le_of_dvd
        (gcd_ne_zero_of_left (primePowerProduct p m).property.1)
        (primePowerProduct_min_dvd_gcd p m n))
      (A.exteriorNorm_pos _).le

end Product

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generatedIdealCharacter_prime_power
#print axioms HeckeSkeleton.Moments.EngineStep.actual_prime_power_product_correlation_norm
#print axioms HeckeSkeleton.Moments.EngineStep.actual_complete_correlation_gcd_radical_bound
