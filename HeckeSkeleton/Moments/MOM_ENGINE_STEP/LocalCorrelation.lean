import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LocalAmplifier
import DedekindZetaZeroFree.CharacterSums.Gauss.GeneratorInvariance
import HeckePort.Moments.FullCorrelation
import HeckePort.Moments.Unequal

/-!
# Complete nonprimitive local correlations

The characters below are the repository's actual `maskedPower` characters
on the entire prime-power quotient.  Reduction to the residue field retains
the full fibre multiplicity.  In particular a unit divided frequency at an
equal, non-six-divisible depth saves one prime norm; the zero-frequency
factor is the full Euler factor.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums LocalFiniteSumCompatibility
open CanonicalLocalGaussTable HeckePort.Moments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance localPrimeResidueField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _

local instance localPrimeResidueFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _

local instance localPrimeResidueFintype (p : ExteriorPrime A) :
    Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) := Fintype.ofFinite _

theorem sextic_character_nat (p : ExteriorPrime A) (n : ℕ) :
    chi (σ := σ) p ^ SArithmeticData.sexticExponent (n : ℤ) = chi (σ := σ) p ^ n := by
  have he : SArithmeticData.sexticExponent (n : ℤ) = n % 6 := by
    simp [SArithmeticData.sexticExponent,
      Int.toNat_emod (Int.natCast_nonneg n) (by decide : (0 : ℤ) ≤ 6)]
  rw [he]
  simpa only [chi_exact_order] using pow_mod_orderOf (chi (σ := σ) p) n

theorem maskedPower_eq_natural_character (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : Residue C p n) :
    maskedPower C p n (n : ℤ) x = (chi (σ := σ) p ^ n) (reduction C p n hn x) := by
  rw [maskedPower_eq_reduction C p n hn, sextic_character_nat]

/-- A genuine multiplicative character of the full prime-power quotient;
its zeros on every nonunit are retained. -/
def localMaskedCharacter (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) : MulChar (Residue C p n) ℂ where
  __ := (chi (σ := σ) p ^ n).toMonoidHom.comp (reduction C p n hn).toMonoidHom
  map_nonunit' := by
    intro x hx
    apply MulChar.map_nonunit
    intro hunit
    exact hx ((reduction_isUnit C p n hn x).mp hunit)

theorem localMaskedCharacter_apply (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : Residue C p n) :
    localMaskedCharacter C p n hn x = maskedPower C p n (n : ℤ) x :=
  (maskedPower_eq_natural_character C p n hn x).symm

theorem localPrimeResidue_card (p : ExteriorPrime A) :
    (Fintype.card (A.R ⧸ A.extendIdeal (primeIdeal p)) : ℂ) = (Q p : ℂ) := by
  rw [← Nat.card_eq_fintype_card, A.exteriorResidue_card]
  simp [Q, SArithmeticData.exteriorNorm, idealNorm]

theorem localPrimePowerResidue_card (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    (Fintype.card (Residue C p n) : ℂ) = (Q p : ℂ) ^ n := by
  have he : Nat.card (Residue C p n) = Ideal.absNorm (p.val.asIdeal ^ n) := by
    change Nat.card (A.R ⧸ Ideal.span {generator C p ^ n}) = _
    rw [(generator_power_generates C p n).2]
    exact A.exteriorResidue_card (powerIdeal p n)
  rw [Nat.card_eq_fintype_card] at he
  rw [he]
  simp [Q, SArithmeticData.exteriorNorm, idealNorm, primeIdeal, map_pow]

/-- The complete nonprimitive fibre contributes `Q^(n-1)`. -/
theorem localReduction_multiplicity (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n) :
    (reductionMultiplicity (reduction C p n hn.ne') : ℂ) = (Q p : ℂ) ^ (n - 1) := by
  have hc := reductionMultiplicity_mul_card (reduction C p n hn.ne')
    (Ideal.Quotient.factor_surjective _)
  have he : (reductionMultiplicity (reduction C p n hn.ne') : ℂ) *
      (Fintype.card (A.R ⧸ A.extendIdeal (primeIdeal p)) : ℂ) =
        (Fintype.card (Residue C p n) : ℂ) := by exact_mod_cast hc
  rw [localPrimeResidue_card, localPrimePowerResidue_card] at he
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (primeNorm_pos p).ne')
  rw [he, ← pow_succ, Nat.sub_add_cancel hn]

/-- The divided equal-depth correlation still sums over both full quotients. -/
def equalDepthCorrelation (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (u : (Residue C p n)ˣ) (v j : Residue C p n) : ℂ :=
  fullCorrelation (fun x : Residue C p n => v * x)
    (fun y : Residue C p n => (u : Residue C p n) * y)
    (maskedPower C p n (n : ℤ)) (maskedPower C p n (n : ℤ)) j

theorem equalDepthCorrelation_reduction (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n)
    (u : (Residue C p n)ˣ) (v j : Residue C p n) :
    equalDepthCorrelation C p n u v j =
      (Q p : ℂ) ^ (n - 1) * localCorrelation (chi (σ := σ) p ^ n)
        (reduction C p n hn.ne' u) (reduction C p n hn.ne' v)
        (reduction C p n hn.ne' j) := by
  have hmask : maskedPower C p n (n : ℤ) =
      fun x : Residue C p n => (chi (σ := σ) p ^ n) (reduction C p n hn.ne' x) := by
    funext x
    exact maskedPower_eq_natural_character C p n hn.ne' x
  unfold equalDepthCorrelation
  simp only [hmask]
  rw [fullCorrelation_reduction_unit_right (reduction C p n hn.ne')
    (Ideal.Quotient.factor_surjective _), localReduction_multiplicity C p n hn]
  rfl

/-- The exact equal-depth table includes both principal and nonprincipal
characters, and both zero and nonzero divided frequencies. -/
theorem equalDepthCorrelation_units (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n)
    (u : (Residue C p n)ˣ) (v j : Residue C p n)
    (hv : reduction C p n hn.ne' v ≠ 0) :
    equalDepthCorrelation C p n u v j =
      (Q p : ℂ) ^ (n - 1) *
        (chi (σ := σ) p ^ n)
          (reduction C p n hn.ne' u / reduction C p n hn.ne' v) *
        (if reduction C p n hn.ne' j = 0 then (Q p : ℂ) - 1
         else if 6 ∣ n then (Q p : ℂ) - 2 else -1) := by
  have hu : reduction C p n hn.ne' u ≠ 0 :=
    isUnit_iff_ne_zero.mp (u.isUnit.map (reduction C p n hn.ne'))
  have hpow : chi (σ := σ) p ^ n = 1 ↔ 6 ∣ n := by
    rw [← orderOf_dvd_iff_pow_eq_one, chi_exact_order]
  rw [equalDepthCorrelation_reduction C p n hn,
    localCorrelation_units _ hu hv, localPrimeResidue_card, hpow, mul_assoc]

/-- A nonunit divided side vanishes unless the depth is divisible by six. -/
theorem equalDepthCorrelation_nonunit (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n)
    (u : (Residue C p n)ˣ) (v j : Residue C p n)
    (hv : reduction C p n hn.ne' v = 0) :
    equalDepthCorrelation C p n u v j =
      (Q p : ℂ) ^ (n - 1) *
        (if 6 ∣ n ∧ reduction C p n hn.ne' j ≠ 0 then (Q p : ℂ) - 1 else 0) := by
  have hu : reduction C p n hn.ne' u ≠ 0 :=
    isUnit_iff_ne_zero.mp (u.isUnit.map (reduction C p n hn.ne'))
  have hpow : chi (σ := σ) p ^ n = 1 ↔ 6 ∣ n := by
    rw [← orderOf_dvd_iff_pow_eq_one, chi_exact_order]
  rw [equalDepthCorrelation_reduction C p n hn, hv,
    localCorrelation_second_zero _ hu, localPrimeResidue_card, hpow]

/-- The norm saving attached to the `t₂` unit-frequency radical is exactly one
prime norm; all `Q^(n-1)` nonprimitive lifts are still present. -/
theorem equalDepthCorrelation_nonprincipal_unit_norm
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (hn : 0 < n) (u : (Residue C p n)ˣ) (v j : Residue C p n)
    (hv : reduction C p n hn.ne' v ≠ 0)
    (hj : reduction C p n hn.ne' j ≠ 0) (hsix : ¬6 ∣ n) :
    ‖equalDepthCorrelation C p n u v j‖ = Q p ^ (n - 1) := by
  have hu : reduction C p n hn.ne' u ≠ 0 :=
    isUnit_iff_ne_zero.mp (u.isUnit.map (reduction C p n hn.ne'))
  have hr : IsUnit (reduction C p n hn.ne' u / reduction C p n hn.ne' v) :=
    isUnit_iff_ne_zero.mpr (div_ne_zero hu hv)
  have hphase : ‖(chi (σ := σ) p ^ n)
      (reduction C p n hn.ne' u / reduction C p n hn.ne' v)‖ = 1 := by
    rw [MulChar.pow_apply' _ hn.ne', norm_pow,
      Complex.norm_eq_one_of_pow_eq_one (chi_unit_sixth (σ := σ) p _ hr) (by decide),
      one_pow]
  rw [equalDepthCorrelation_units C p n hn u v j hv, if_neg hj, if_neg hsix]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (primeNorm_pos p).le,
    hphase, norm_neg, norm_one, mul_one]

/-- The diagonal retains the complete Euler factor at every positive depth. -/
theorem equalDepthCorrelation_diagonal (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n) :
    equalDepthCorrelation C p n 1 1 0 =
      (Q p : ℂ) ^ (n - 1) * ((Q p : ℂ) - 1) := by
  rw [equalDepthCorrelation_units C p n hn 1 1 0 (by simp)]
  simp

theorem equalDepthCorrelation_diagonal_card_units
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (n : ℕ) (hn : 0 < n) :
    equalDepthCorrelation C p n 1 1 0 = (Fintype.card (Residue C p n)ˣ : ℂ) := by
  have hmask : maskedPower C p n (n : ℤ) = localMaskedCharacter C p n hn.ne' := by
    funext x
    exact (localMaskedCharacter_apply C p n hn.ne' x).symm
  have hcond (x y : Residue C p n) : x - y = 0 ↔ y = x := sub_eq_zero.trans eq_comm
  unfold equalDepthCorrelation fullCorrelation
  simp only [hmask, Units.val_one, one_mul, hcond, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units

/-- The full Euler factor is computed from the original nonprimitive quotient. -/
theorem localPrimePower_euler_factor (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n) :
    (Fintype.card (Residue C p n)ˣ : ℂ) =
      (Q p : ℂ) ^ (n - 1) * ((Q p : ℂ) - 1) := by
  rw [← equalDepthCorrelation_diagonal_card_units C p n hn,
    equalDepthCorrelation_diagonal C p n hn]

/-- The full zero-frequency correlation, before dividing the common modulus,
is the cardinality of the units of that full quotient. -/
theorem localMaskedCharacter_full_diagonal (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) :
    fullModulusCorrelation (generator C p ^ n) (generator C p ^ n)
      (localMaskedCharacter C p n hn) (localMaskedCharacter C p n hn) 0 =
        (Fintype.card (Residue C p n)ˣ : ℂ) :=
  fullModulusCorrelation_zero_frequency_diagonal _
    (pow_ne_zero _ (generator_generates C p).1) _

section UnequalDepth

/-- Changing the presentation of the same quotient does not change a
character evaluated on an original ring element. -/
theorem transportCharacter_mk {T : Type*} [CommRing T] (I J : Ideal T)
    (h : I = J) (χ : MulChar (T ⧸ I) ℂ) (x : T) :
    GeneratorInvariance.transportCharacter I J h χ (Ideal.Quotient.mk J x) =
      χ (Ideal.Quotient.mk I x) := by
  subst J
  rfl

local instance productPowerResidueFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ j * generator C p ^ d}) := by
  rw [← pow_add]
  infer_instance

local instance productPowerResidueFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ j * generator C p ^ d}) := Fintype.ofFinite _

/-- The actual upper prime-power character in the product presentation
required by the complete unequal-modulus correlation. -/
def productPowerCharacter (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) (hn : j + d ≠ 0) :
    MulChar (A.R ⧸ Ideal.span {generator C p ^ j * generator C p ^ d}) ℂ :=
  GeneratorInvariance.transportCharacter
    (Ideal.span {generator C p ^ (j + d)})
    (Ideal.span {generator C p ^ j * generator C p ^ d})
    (by rw [pow_add]) (localMaskedCharacter C p (j + d) hn)

theorem localMaskedCharacter_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : n ≠ 0) (x : A.R) :
    localMaskedCharacter C p n hn (Ideal.Quotient.mk _ x) =
      (chi (σ := σ) p ^ n) (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x) := by
  rfl

theorem productPowerCharacter_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) (hn : j + d ≠ 0) (x : A.R) :
    productPowerCharacter C p j d hn (Ideal.Quotient.mk _ x) =
      (chi (σ := σ) p ^ (j + d)) (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x) := by
  rw [productPowerCharacter, transportCharacter_mk, localMaskedCharacter_mk]

theorem productPowerCharacter_lift_constant (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (k : A.R) :
    ∀ y : Residue C p j,
      productPowerCharacter C p j d (by omega)
          (scaledResidue (generator C p ^ j) (generator C p ^ d)
            (generator C p ^ j * generator C p ^ d) rfl y + Ideal.Quotient.mk _ k) =
        productPowerCharacter C p j d (by omega) (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hg : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) (generator C p) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [scaledResidue_mk, ← map_add, productPowerCharacter_mk, productPowerCharacter_mk,
    map_add, map_mul, map_pow, hg, zero_pow hd.ne', zero_mul, zero_add]

theorem localMaskedCharacter_sum_zero (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : ℕ) (hj : 0 < j) (hsix : ¬6 ∣ j) :
    (∑ y : Residue C p j, localMaskedCharacter C p j hj.ne' y) = 0 := by
  have hn : chi (σ := σ) p ^ j ≠ 1 := by
    intro h
    apply hsix
    have hh := orderOf_dvd_iff_pow_eq_one.mpr h
    simpa only [chi_exact_order] using hh
  change (∑ y : Residue C p j,
    (chi (σ := σ) p ^ j) (reduction C p j hj.ne' y)) = 0
  rw [sum_reduction (reduction C p j hj.ne') (Ideal.Quotient.factor_surjective _),
    MulChar.sum_eq_zero_of_ne_one hn, mul_zero]

/-- Unequal positive multiplicities vanish unless the smaller multiplicity
is divisible by six.  The original prime-power moduli are unchanged. -/
theorem actual_unequal_prime_power_zero_of_not_six
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (hsix : ¬6 ∣ j) (k : A.R) :
    fullModulusCorrelation (generator C p ^ j * generator C p ^ d)
      (generator C p ^ j) (productPowerCharacter C p j d (by omega))
      (localMaskedCharacter C p j hj.ne') (generator C p ^ j * k) = 0 := by
  rw [HeckePort.Moments.Unequal.fullCorrelation_divisor_constant
    (generator C p ^ j) (generator C p ^ d) k
    (pow_ne_zero _ (generator_generates C p).1) _ _
    (productPowerCharacter_lift_constant C p j d hj hd k),
    localMaskedCharacter_sum_zero C p j hj hsix, star_zero, mul_zero]

/-- A nonunit divided frequency also vanishes on the unequal-depth row. -/
theorem actual_unequal_prime_power_zero_of_nonunit
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (k : A.R)
    (hk : generator C p ∣ k) :
    fullModulusCorrelation (generator C p ^ j * generator C p ^ d)
      (generator C p ^ j) (productPowerCharacter C p j d (by omega))
      (localMaskedCharacter C p j hj.ne') (generator C p ^ j * k) = 0 := by
  rw [HeckePort.Moments.Unequal.fullCorrelation_divisor_constant
    (generator C p ^ j) (generator C p ^ d) k
    (pow_ne_zero _ (generator_generates C p).1) _ _
    (productPowerCharacter_lift_constant C p j d hj hd k), productPowerCharacter_mk]
  have hz : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) k = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton.mpr hk
  rw [hz, MulChar.map_zero, zero_mul]

theorem finiteCharacter_norm_le_one {T : Type*} [CommRing T] [Fintype T]
    (χ : MulChar T ℂ) (x : T) : ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have he := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity hx.unit)
    exact le_of_eq (by simpa only [hx.unit_spec] using he)
  · rw [χ.map_nonunit hx, norm_zero]
    exact zero_le_one

/-- The retained unequal-depth correlation has the full smaller-modulus
bound, including every nonprimitive lift. -/
theorem actual_unequal_prime_power_norm_le
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (k : A.R) :
    ‖fullModulusCorrelation (generator C p ^ j * generator C p ^ d)
      (generator C p ^ j) (productPowerCharacter C p j d (by omega))
      (localMaskedCharacter C p j hj.ne') (generator C p ^ j * k)‖ ≤ Q p ^ j := by
  have hb := HeckePort.Moments.Unequal.unequal_norm_le
    (generator C p ^ j) (generator C p ^ d) k
    (pow_ne_zero _ (generator_generates C p).1)
    (productPowerCharacter C p j d (by omega)) (localMaskedCharacter C p j hj.ne')
    (productPowerCharacter_lift_constant C p j d hj hd k)
    (finiteCharacter_norm_le_one _ _) (fun y => finiteCharacter_norm_le_one _ y)
  have hc : (Fintype.card (Residue C p j) : ℝ) = Q p ^ j := by
    exact_mod_cast localPrimePowerResidue_card C p j
  simpa only [hc] using hb

/-- The retained support of a complete unequal prime-power correlation:
the full smaller power divides the frequency, its multiplicity is a
multiple of six, and the divided frequency is a unit at the prime. -/
theorem actual_unequal_prime_power_support
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (h : A.R)
    (hne : fullModulusCorrelation (generator C p ^ j * generator C p ^ d)
      (generator C p ^ j) (productPowerCharacter C p j d (by omega))
      (localMaskedCharacter C p j hj.ne') h ≠ 0) :
    ∃ k : A.R, h = generator C p ^ j * k ∧ 6 ∣ j ∧ ¬generator C p ∣ k := by
  have hdiv : generator C p ^ j ∣ h := by
    by_contra hn
    apply hne
    exact fullModulusCorrelation_eq_zero_of_common_not_dvd
      (generator C p ^ j * generator C p ^ d) (generator C p ^ j)
      (generator C p ^ j) h _ _ (dvd_mul_right _ _) dvd_rfl hn
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k, hk, ?_, ?_⟩
  · by_contra hsix
    apply hne
    rw [hk]
    exact actual_unequal_prime_power_zero_of_not_six C p j d hj hd hsix k
  · intro hunit
    apply hne
    rw [hk]
    exact actual_unequal_prime_power_zero_of_nonunit C p j d hj hd k hunit

/-- The complete correlation is extended by its actual zero off the
retained frequency partition, before any absolute-value estimate. -/
theorem actual_unequal_prime_power_all_frequency_norm_le
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (h : A.R) :
    ‖fullModulusCorrelation (generator C p ^ j * generator C p ^ d)
      (generator C p ^ j) (productPowerCharacter C p j d (by omega))
      (localMaskedCharacter C p j hj.ne') h‖ ≤ Q p ^ j := by
  by_cases hdiv : generator C p ^ j ∣ h
  · obtain ⟨k, hk⟩ := hdiv
    rw [hk]
    exact actual_unequal_prime_power_norm_le C p j d hj hd k
  · rw [fullModulusCorrelation_eq_zero_of_common_not_dvd
      (generator C p ^ j * generator C p ^ d) (generator C p ^ j)
      (generator C p ^ j) h _ _ (dvd_mul_right _ _) dvd_rfl hdiv, norm_zero]
    exact pow_nonneg (primeNorm_pos p).le _

end UnequalDepth

end HeckeSkeleton.Moments.EngineStep
