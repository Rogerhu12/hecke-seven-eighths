import HeckeSkeleton.Base
import HeckeAxiom.GaussDictionary
import DedekindZetaZeroFree.CharacterSums.Gauss.PositiveDepthLocalSums
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Actual local prime-power Gauss sums

The quotient, zero-extended sextic character, primitive additive character,
and prime generator are those of the one arithmetic choice in `TargetContext`.
The sum includes every residue class.  Unit changes of frequency are proved
by reindexing that sum, and nonzero frequencies are decomposed in the actual
completed discrete valuation ring before being returned to the same quotient.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE.LocalGauss

open NumberField IsDedekindDomain
open DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums
open DedekindZetaZeroFree.LocalFiniteSumCompatibility
open DedekindZetaZeroFree.CanonicalLocalGaussTable
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The same exterior prime in the arithmetic-choice model. -/
def contextLocalPrime
    (p : HeckeGeneral.ThetaSkeleton.ExteriorPrime K (places K c)) :
    LocalFiniteSums.ExteriorPrime (axiomChoice K c).A :=
  ⟨p.val, (HeckeAxiom.primeExterior (axiomChoice K c).A p.val p.property).property.2⟩

variable (p : HeckeGeneral.ThetaSkeleton.ExteriorPrime K (places K c))

local notation "C" => HeckeAxiom.ArithmeticChoice.C (axiomChoice K c)
local notation "P" => contextLocalPrime K c p

local instance : Field ((axiomChoice K c).A.R ⧸ (axiomChoice K c).A.extendIdeal (primeIdeal P)) :=
  Ideal.Quotient.field _

local instance : Finite ((axiomChoice K c).A.R ⧸ (axiomChoice K c).A.extendIdeal (primeIdeal P)) :=
  (axiomChoice K c).A.exteriorResidue_finite _

local instance : Fintype ((axiomChoice K c).A.R ⧸ (axiomChoice K c).A.extendIdeal (primeIdeal P)) :=
  Fintype.ofFinite _

abbrev Quotient (n : ℕ) := Residue C P n

def primeNorm : ℝ := Q P

theorem primeNorm_eq : primeNorm K c p = (p.val.asIdeal.absNorm : ℝ) := rfl

theorem primeNorm_pos : 0 < primeNorm K c p := by
  rw [primeNorm_eq]
  exact_mod_cast (lt_trans Nat.zero_lt_one
    (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))

def generatorClass (n M : ℕ) : Quotient K c p n :=
  residueMap C P n (generator C P ^ M)

theorem generatorClass_eq_zero_of_le (n M : ℕ) (h : n ≤ M) :
    generatorClass K c p n M = 0 := by
  change Ideal.Quotient.mk (Ideal.span {generator C P ^ n}) (generator C P ^ M) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (pow_dvd_pow (generator C P) h))

@[simp] theorem generatorClass_self (n : ℕ) : generatorClass K c p n n = 0 :=
  generatorClass_eq_zero_of_le K c p n n le_rfl

private theorem generator_nonunit : ¬ IsUnit (generator C P) := by
  intro hu
  have hz : Ideal.Quotient.mk ((axiomChoice K c).A.extendIdeal (primeIdeal P))
      (generator C P) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C P).2]
    exact Ideal.mem_span_singleton_self _
  have hh := hu.map (Ideal.Quotient.mk ((axiomChoice K c).A.extendIdeal (primeIdeal P)))
  rw [hz] at hh
  exact not_isUnit_zero hh

theorem generatorClass_eq_zero_iff (n M : ℕ) :
    generatorClass K c p n M = 0 ↔ n ≤ M := by
  change Ideal.Quotient.mk (Ideal.span {generator C P ^ n}) (generator C P ^ M) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow_iff (generator_generates C P).1 (generator_nonunit K c p)

theorem generatorClass_mul (n M L : ℕ) :
    generatorClass K c p n M * generatorClass K c p n L = generatorClass K c p n (M + L) := by
  simp only [generatorClass, pow_add, map_mul]

/-- The quotient has the actual full prime-power cardinality. -/
theorem quotient_card (n : ℕ) :
    Nat.card (Quotient K c p n) = p.val.asIdeal.absNorm ^ n := by
  have he : Nat.card (Quotient K c p n) = Ideal.absNorm (p.val.asIdeal ^ n) := by
    change Nat.card ((axiomChoice K c).A.R ⧸ Ideal.span {generator C P ^ n}) = _
    rw [(generator_power_generates C P n).2]
    exact (axiomChoice K c).A.exteriorResidue_card (powerIdeal P n)
  rw [he, map_pow]

/-- The last prime-power layer, as an actual image in the original quotient. -/
def lastLayer (n : ℕ) (h : Quotient K c p n) : Prop :=
  ∃ z : Quotient K c p n, h = generatorClass K c p n (n - 1) * z

@[simp] theorem lastLayer_zero (n : ℕ) : lastLayer K c p n 0 := by
  exact ⟨0, (mul_zero _).symm⟩

/-- For an original S-integer frequency this layer is precisely divisibility
by the original ideal `p^(n-1)`, before any primitive reduction. -/
theorem lastLayer_mk_iff (n : ℕ) (h : (axiomChoice K c).A.R) :
    lastLayer K c p n (residueMap C P n h) ↔
      h ∈ (p.val.asIdeal ^ (n - 1)).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) := by
  change lastLayer K c p n (residueMap C P n h) ↔
    h ∈ (axiomChoice K c).A.extendIdeal (powerIdeal P (n - 1))
  rw [← (generator_power_generates C P (n - 1)).2]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk (Ideal.span {generator C P ^ n}) h =
      Ideal.Quotient.mk _ (generator C P ^ (n - 1)) * Ideal.Quotient.mk _ z at hz
    rw [← map_mul] at hz
    have hd := Ideal.Quotient.eq.mp hz
    have hle : Ideal.span {generator C P ^ n} ≤ Ideal.span {generator C P ^ (n - 1)} := by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = generator C P ^ n)
      exact Ideal.mem_span_singleton.mpr (pow_dvd_pow (generator C P) (Nat.sub_le n 1))
    have hp : generator C P ^ (n - 1) * z ∈ Ideal.span {generator C P ^ (n - 1)} :=
      Ideal.mul_mem_right z _ (Ideal.mem_span_singleton_self _)
    simpa only [sub_add_cancel] using (Ideal.add_mem _ (hle hd) hp)
  · intro hh
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hh
    refine ⟨residueMap C P n z, ?_⟩
    change residueMap C P n h = residueMap C P n (generator C P ^ (n - 1)) * residueMap C P n z
    rw [← map_mul, ← hz]

theorem frequency_mk_eq_zero_iff (n : ℕ) (h : (axiomChoice K c).A.R) :
    residueMap C P n h = 0 ↔
      h ∈ (p.val.asIdeal ^ n).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) := by
  change Ideal.Quotient.mk (Ideal.span {generator C P ^ n}) h = 0 ↔
    h ∈ (axiomChoice K c).A.extendIdeal (powerIdeal P n)
  rw [Ideal.Quotient.eq_zero_iff_mem, (generator_power_generates C P n).2]

/-- The unnormalized complete sum with its actual original nonunit zeros. -/
def raw (n : ℕ) (h : Quotient K c p n) : ℂ :=
  ∑ x : Quotient K c p n, maskedPower C P n (n : ℤ) x * psi C P n (h * x)

/-- Normalization by the square root of the full prime-power modulus norm. -/
def normalized (n : ℕ) (h : Quotient K c p n) : ℂ :=
  (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ * raw K c p n h

theorem raw_generatorClass (n M : ℕ) (hn : 0 < n) :
    raw K c p n (generatorClass K c p n M) =
      if n - 1 ≤ M then
        (primeNorm K c p : ℂ) ^ (n - 1) *
          T C P (n : ℤ) (generatorClass K c p 1 (M - (n - 1)))
      else 0 :=
  PrimePowerFourier.masked_fourier_prime_power C P n M hn (n : ℤ)

theorem maskedPower_mul_unit (n : ℕ) (hn : 0 < n)
    (u : (Quotient K c p n)ˣ) (x : Quotient K c p n) :
    maskedPower C P n (n : ℤ) ((u : Quotient K c p n) * x) =
      maskedPower C P n (n : ℤ) u * maskedPower C P n (n : ℤ) x := by
  simp only [maskedPower_eq_reduction C P n hn.ne', map_mul]

theorem maskedPower_unit_norm (n : ℕ) (hn : 0 < n)
    (u : (Quotient K c p n)ˣ) : ‖maskedPower C P n (n : ℤ) u‖ = 1 := by
  rw [maskedPower_eq_reduction C P n hn.ne']
  let v := Units.map (reduction C P n hn.ne').toMonoidHom u
  have h6 := chi_unit_sixth (σ := complexEmbedding K) P
    (v : (axiomChoice K c).A.R ⧸ (axiomChoice K c).A.extendIdeal (primeIdeal P)) v.isUnit
  have hnorm : ‖chi (σ := complexEmbedding K) P v‖ = 1 := by
    have h := congrArg norm h6
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6 : ℕ) ≠ 0)).mp h
  change ‖(chi (σ := complexEmbedding K) P ^
    SArithmeticData.sexticExponent (n : ℤ)) (v : _)‖ = 1
  rw [MulChar.pow_apply_coe, norm_pow, hnorm, one_pow]

theorem sexticExponent_eq_zero (n : ℕ) (hn : 6 ∣ n) :
    SArithmeticData.sexticExponent (n : ℤ) = 0 := by
  have hz : (6 : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
  simp only [SArithmeticData.sexticExponent, Int.emod_eq_zero_of_dvd hz, Int.toNat_zero]

theorem maskedPower_unit_of_six_dvd (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (u : (Quotient K c p n)ˣ) : maskedPower C P n (n : ℤ) u = 1 := by
  rw [maskedPower_eq_reduction C P n hn.ne', sexticExponent_eq_zero n h6, pow_zero]
  exact MulChar.one_apply (u.isUnit.map (reduction C P n hn.ne'))

/-- Unit scaling is an exact reindexing of the original complete sum. -/
theorem raw_mul_unit (n : ℕ) (hn : 0 < n) (u : (Quotient K c p n)ˣ)
    (h : Quotient K c p n) :
    maskedPower C P n (n : ℤ) u * raw K c p n ((u : Quotient K c p n) * h) =
      raw K c p n h := by
  unfold raw
  rw [Finset.mul_sum]
  calc
    _ = ∑ x : Quotient K c p n,
        maskedPower C P n (n : ℤ) ((u : Quotient K c p n) * x) *
          psi C P n (h * ((u : Quotient K c p n) * x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [maskedPower_mul_unit K c p n hn]
      have hh : ((u : Quotient K c p n) * h) * x = h * ((u : Quotient K c p n) * x) := by ring
      rw [hh]
      ring
    _ = _ := Equiv.sum_comp u.mulLeft
      (fun x => maskedPower C P n (n : ℤ) x * psi C P n (h * x))

theorem normalized_mul_unit (n : ℕ) (hn : 0 < n) (u : (Quotient K c p n)ˣ)
    (h : Quotient K c p n) :
    maskedPower C P n (n : ℤ) u * normalized K c p n ((u : Quotient K c p n) * h) =
      normalized K c p n h := by
  unfold normalized
  calc
    _ = (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ *
        (maskedPower C P n (n : ℤ) u * raw K c p n ((u : Quotient K c p n) * h)) := by ring
    _ = _ := by rw [raw_mul_unit K c p n hn]

theorem normalized_mul_unit_norm (n : ℕ) (hn : 0 < n)
    (u : (Quotient K c p n)ˣ) (h : Quotient K c p n) :
    ‖normalized K c p n ((u : Quotient K c p n) * h)‖ =
      ‖normalized K c p n h‖ := by
  have hh := congrArg norm (normalized_mul_unit K c p n hn u h)
  rw [norm_mul, maskedPower_unit_norm K c p n hn u, one_mul] at hh
  exact hh

theorem normalized_mul_unit_of_six_dvd (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (u : (Quotient K c p n)ˣ) (h : Quotient K c p n) :
    normalized K c p n ((u : Quotient K c p n) * h) = normalized K c p n h := by
  have hh := normalized_mul_unit K c p n hn u h
  rw [maskedPower_unit_of_six_dvd K c p n hn h6 u, one_mul] at hh
  exact hh

private theorem local_generator_irreducible : Irreducible (localUniformizer C P) := by
  have hπ : (Valued.v : Valuation (LocalField P) (WithZero (Multiplicative ℤ))).IsUniformizer
      (localUniformizer C P) := by
    change (Valued.v (uniformizer C P) : WithZero (Multiplicative ℤ)) = _
    rw [uniformizer_valuation]
    have hgen := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective K p.val)
    exact (congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => u.val)
      hgen).symm
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hπ.is_generator

/-- The actual completed integer ring maps back to the same finite quotient. -/
def localQuotientMap (n : ℕ) : LocalIntegers P →+* Quotient K c p n :=
  (residueEquiv C P n).symm.toRingHom.comp (Ideal.Quotient.mk _)

theorem localQuotientMap_generator (n : ℕ) :
    localQuotientMap K c p n (localUniformizer C P) = residueMap C P n (generator C P) := by
  apply (residueEquiv C P n).injective
  change residueEquiv C P n ((residueEquiv C P n).symm
    (Ideal.Quotient.mk _ (localUniformizer C P))) = _
  rw [RingEquiv.apply_symm_apply, residueEquiv_mk] <;> rfl

/-- Every nonzero frequency has a derived unit-times-prime-power
representative in its original quotient.  No valuation decomposition is
assumed as an extra input to the Gauss formula. -/
theorem nonzero_frequency_representation (n : ℕ) (h : Quotient K c p n) (hh : h ≠ 0) :
    ∃ M : ℕ, M < n ∧ ∃ u : (Quotient K c p n)ˣ,
      h = (u : Quotient K c p n) * generatorClass K c p n M := by
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (residueEquiv C P n h)
  have hz' : localQuotientMap K c p n z = h := by
    change (residueEquiv C P n).symm (Ideal.Quotient.mk _ z) = h
    rw [hz, RingEquiv.symm_apply_apply]
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hh
    rw [← hz', hzero, map_zero]
  obtain ⟨M, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (R := LocalIntegers P) hz0
    (local_generator_irreducible K c p)
  let v : (Quotient K c p n)ˣ := Units.map (localQuotientMap K c p n).toMonoidHom u
  have hrep : h = (v : Quotient K c p n) * generatorClass K c p n M := by
    calc
      h = localQuotientMap K c p n z := hz'.symm
      _ = localQuotientMap K c p n u.val *
          localQuotientMap K c p n (localUniformizer C P) ^ M := by
        rw [hu, map_mul, map_pow]
      _ = _ := by
        change localQuotientMap K c p n u.val *
            localQuotientMap K c p n (localUniformizer C P) ^ M =
          localQuotientMap K c p n u.val * residueMap C P n (generator C P ^ M)
        rw [map_pow, localQuotientMap_generator]
  have hM : M < n := by
    by_contra hnot
    have hzclass := generatorClass_eq_zero_of_le K c p n M (le_of_not_gt hnot)
    exact hh (by rw [hrep, hzclass, mul_zero])
  exact ⟨M, hM, v, hrep⟩

/-- The truncated prime order of an actual quotient frequency.  Zero has
order `n`; nonzero elements have the proved unit-times-prime-power order. -/
def frequencyOrder (n : ℕ) (h : Quotient K c p n) : ℕ :=
  if hh : h = 0 then n else Classical.choose (nonzero_frequency_representation K c p n h hh)

@[simp] theorem frequencyOrder_zero (n : ℕ) : frequencyOrder K c p n 0 = n := by
  simp [frequencyOrder]

theorem frequencyOrder_lt (n : ℕ) (h : Quotient K c p n) (hh : h ≠ 0) :
    frequencyOrder K c p n h < n := by
  simpa only [frequencyOrder, dif_neg hh] using
    (Classical.choose_spec (nonzero_frequency_representation K c p n h hh)).1

theorem frequencyOrder_representation (n : ℕ) (h : Quotient K c p n) (hh : h ≠ 0) :
    ∃ u : (Quotient K c p n)ˣ,
      h = (u : Quotient K c p n) * generatorClass K c p n (frequencyOrder K c p n h) := by
  simpa only [frequencyOrder, dif_neg hh] using
    (Classical.choose_spec (nonzero_frequency_representation K c p n h hh)).2

/-- The chosen order has the exact original last-layer support condition. -/
theorem frequencyOrder_eq_pred_iff (n : ℕ) (hn : 0 < n)
    (h : Quotient K c p n) (hh : h ≠ 0) :
    frequencyOrder K c p n h = n - 1 ↔ lastLayer K c p n h := by
  obtain ⟨u, hu⟩ := frequencyOrder_representation K c p n h hh
  constructor
  · intro he
    refine ⟨u, ?_⟩
    rw [he] at hu
    simpa only [mul_comm] using hu
  · rintro ⟨z, hz⟩
    have hkill : generatorClass K c p n 1 * h = 0 := by
      rw [hz, ← mul_assoc, generatorClass_mul]
      have he : 1 + (n - 1) = n := by omega
      rw [he, generatorClass_self, zero_mul]
    have hkill' : (u : Quotient K c p n) *
        generatorClass K c p n (1 + frequencyOrder K c p n h) = 0 := by
      rw [← generatorClass_mul]
      calc
        _ = generatorClass K c p n 1 *
          ((u : Quotient K c p n) * generatorClass K c p n (frequencyOrder K c p n h)) := by ring
        _ = 0 := by rw [← hu]; exact hkill
    have hzero := (u.mul_right_eq_zero).mp hkill'
    have hle := (generatorClass_eq_zero_iff K c p n _).mp hzero
    have hlt := frequencyOrder_lt K c p n h hh
    omega

theorem frequencyOrder_support (n : ℕ) (hn : 0 < n) (h : Quotient K c p n) :
    frequencyOrder K c p n h = n - 1 ↔ h ≠ 0 ∧ lastLayer K c p n h := by
  by_cases hz : h = 0
  · subst h
    have hne : n ≠ n - 1 := by omega
    simp [hne]
  · simpa only [ne_eq, hz, not_false_eq_true, true_and] using
      frequencyOrder_eq_pred_iff K c p n hn h hz

theorem frequencyOrder_lastLayer (n : ℕ) (hn : 0 < n) (h : Quotient K c p n) :
    n - 1 ≤ frequencyOrder K c p n h ↔ lastLayer K c p n h := by
  by_cases hz : h = 0
  · subst h
    simp
  · have hlt := frequencyOrder_lt K c p n h hz
    have he : n - 1 ≤ frequencyOrder K c p n h ↔ frequencyOrder K c p n h = n - 1 := by omega
    exact he.trans (frequencyOrder_eq_pred_iff K c p n hn h hz)

theorem prime_tau_of_six_dvd (n : ℕ) (h6 : 6 ∣ n) : tau C P (n : ℤ) = -1 := by
  rw [tau, T_eq_finiteField, map_one]
  change FiniteGaussTable.T (chi (σ := complexEmbedding K) P) (primeTrace C P)
    (SArithmeticData.sexticExponent (n : ℤ)) 1 = -1
  rw [sexticExponent_eq_zero n h6]
  simp only [FiniteGaussTable.T, pow_zero, one_mul]
  exact gaussSum_one_left (primeTrace_ne_one C P)

theorem raw_generatorClass_norm (n M : ℕ) (hn : 0 < n) (h6 : ¬ 6 ∣ n) :
    ‖raw K c p n (generatorClass K c p n M)‖ =
      if M = n - 1 then primeNorm K c p ^ (n - 1) * Real.sqrt (primeNorm K c p) else 0 := by
  have h6Z : ¬ (6 : ℤ) ∣ (n : ℤ) := by exact_mod_cast h6
  have ht := norm_tau_of_not_six_dvd C P (n : ℤ) h6Z
  change ‖tau C P (n : ℤ)‖ = Real.sqrt (primeNorm K c p) at ht
  rw [raw_generatorClass K c p n M hn]
  simp only [generatorClass, T_generator_power]
  by_cases hM : M = n - 1
  · subst M
    simp [norm_pow, ht, abs_of_pos (primeNorm_pos K c p)]
  · by_cases hle : n - 1 ≤ M
    · have hne : M - (n - 1) ≠ 0 := by omega
      simp [hle, hne, h6Z, hM]
    · simp [hle, hM]

private theorem normalized_sqrt_ratio (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) :
    (q ^ (n - 1) * Real.sqrt q) / Real.sqrt (q ^ n) = Real.sqrt (q ^ (n - 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change (q ^ r * Real.sqrt q) / Real.sqrt (q ^ (r + 1)) = Real.sqrt (q ^ r)
  rw [pow_succ, Real.sqrt_mul (pow_nonneg hq.le _)]
  apply (div_eq_iff (mul_ne_zero (Real.sqrt_pos.mpr (pow_pos hq _)).ne'
    (Real.sqrt_pos.mpr hq).ne')).2
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (pow_nonneg hq.le _)]

/-- The nonprincipal branch of (can-local-G), at every valuation representative. -/
theorem normalized_generatorClass_norm (n M : ℕ) (hn : 0 < n) (h6 : ¬ 6 ∣ n) :
    ‖normalized K c p n (generatorClass K c p n M)‖ =
      if M = n - 1 then Real.sqrt (primeNorm K c p ^ (n - 1)) else 0 := by
  rw [normalized, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), raw_generatorClass_norm K c p n M hn h6]
  by_cases hM : M = n - 1
  · simp only [if_pos hM]
    rw [mul_comm, ← div_eq_mul_inv]
    exact normalized_sqrt_ratio (primeNorm K c p) (primeNorm_pos K c p) n hn
  · simp [hM]

/-- The exact Ramanujan branch before normalization, with both divisibility
indicators retained.  In particular zero frequency is not discarded. -/
theorem raw_generatorClass_of_six_dvd (n M : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    raw K c p n (generatorClass K c p n M) =
      (if n ≤ M then (primeNorm K c p : ℂ) ^ n else 0) -
        (if n - 1 ≤ M then (primeNorm K c p : ℂ) ^ (n - 1) else 0) := by
  have h6Z : (6 : ℤ) ∣ (n : ℤ) := by exact_mod_cast h6
  rw [raw_generatorClass K c p n M hn]
  simp only [generatorClass, T_generator_power]
  by_cases hle : n - 1 ≤ M
  · by_cases hnM : n ≤ M
    · have hne : M - (n - 1) ≠ 0 := by omega
      simp only [hle, hnM, hne, h6Z, if_true, if_false]
      have he : n = (n - 1) + 1 := by omega
      conv_rhs => lhs; rw [he, pow_succ]
      simp only [primeNorm]
      ring
    · have he : M - (n - 1) = 0 := by omega
      simp [hle, hnM, he, prime_tau_of_six_dvd K c p n h6]
  · have hnM : ¬ n ≤ M := by omega
    simp [hle, hnM]

theorem normalized_generatorClass_of_six_dvd (n M : ℕ) (hn : 0 < n) (h6 : 6 ∣ n) :
    normalized K c p n (generatorClass K c p n M) =
      (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ *
        ((if n ≤ M then (primeNorm K c p : ℂ) ^ n else 0) -
          (if n - 1 ≤ M then (primeNorm K c p : ℂ) ^ (n - 1) else 0)) := by
  rw [normalized, raw_generatorClass_of_six_dvd K c p n M hn h6]

/-- The nonprincipal normalized formula for every actual quotient frequency,
including zero.  The frequency order was constructed from that frequency. -/
theorem normalized_norm (n : ℕ) (hn : 0 < n) (h6 : ¬ 6 ∣ n)
    (h : Quotient K c p n) :
    ‖normalized K c p n h‖ =
      if frequencyOrder K c p n h = n - 1 then
        Real.sqrt (primeNorm K c p ^ (n - 1)) else 0 := by
  by_cases hz : h = 0
  · subst h
    simpa only [generatorClass_self, frequencyOrder_zero] using
      normalized_generatorClass_norm K c p n n hn h6
  · obtain ⟨u, hu⟩ := frequencyOrder_representation K c p n h hz
    calc
      ‖normalized K c p n h‖ =
          ‖normalized K c p n (generatorClass K c p n (frequencyOrder K c p n h))‖ :=
        (congrArg (fun z => ‖normalized K c p n z‖) hu).trans
          (normalized_mul_unit_norm K c p n hn u _)
      _ = _ := normalized_generatorClass_norm K c p n (frequencyOrder K c p n h) hn h6

/-- The exact normalized Ramanujan formula for every actual frequency.
The first indicator is divisibility by the full modulus; the second keeps
the penultimate prime-power divisibility mask. -/
theorem normalized_of_six_dvd (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (h : Quotient K c p n) :
    normalized K c p n h = (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ *
      ((if h = 0 then (primeNorm K c p : ℂ) ^ n else 0) -
        (if n - 1 ≤ frequencyOrder K c p n h then (primeNorm K c p : ℂ) ^ (n - 1) else 0)) := by
  by_cases hz : h = 0
  · subst h
    simpa using normalized_generatorClass_of_six_dvd K c p n n hn h6
  · obtain ⟨u, hu⟩ := frequencyOrder_representation K c p n h hz
    have horder := frequencyOrder_lt K c p n h hz
    calc
      normalized K c p n h =
          normalized K c p n (generatorClass K c p n (frequencyOrder K c p n h)) :=
        (congrArg (normalized K c p n) hu).trans
          (normalized_mul_unit_of_six_dvd K c p n hn h6 u _)
      _ = _ := by
        rw [normalized_generatorClass_of_six_dvd K c p n (frequencyOrder K c p n h) hn h6]
        simp only [hz, not_le.mpr horder, if_false]

/-- The nonprincipal formula stated using the original quotient support mask. -/
theorem normalized_norm_original_mask (n : ℕ) (hn : 0 < n) (h6 : ¬ 6 ∣ n)
    (h : Quotient K c p n) :
    ‖normalized K c p n h‖ =
      if h ≠ 0 ∧ lastLayer K c p n h then Real.sqrt (primeNorm K c p ^ (n - 1)) else 0 := by
  simp only [normalized_norm K c p n hn h6, frequencyOrder_support K c p n hn h]

/-- The principal formula stated using the original quotient support masks. -/
theorem normalized_of_six_dvd_original_mask (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (h : Quotient K c p n) :
    normalized K c p n h = (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ *
      ((if h = 0 then (primeNorm K c p : ℂ) ^ n else 0) -
        (if lastLayer K c p n h then (primeNorm K c p : ℂ) ^ (n - 1) else 0)) := by
  simp only [normalized_of_six_dvd K c p n hn h6, frequencyOrder_lastLayer K c p n hn h]

/-- Equation (can-local-G), nonprincipal case, for an arbitrary original
S-integer frequency.  The two membership tests are exactly the consecutive
prime-power ideals, so their conjunction means valuation `n-1`. -/
theorem normalized_norm_mk (n : ℕ) (hn : 0 < n) (h6 : ¬ 6 ∣ n)
    (h : (axiomChoice K c).A.R) :
    ‖normalized K c p n (residueMap C P n h)‖ =
      if h ∉ (p.val.asIdeal ^ n).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) ∧
          h ∈ (p.val.asIdeal ^ (n - 1)).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) then
        Real.sqrt (primeNorm K c p ^ (n - 1)) else 0 := by
  simp only [normalized_norm_original_mask K c p n hn h6,
    ne_eq, frequency_mk_eq_zero_iff, lastLayer_mk_iff]

/-- Equation (can-local-G), principal case, with both original divisibility
indicators and the true complete-modulus normalization. -/
theorem normalized_of_six_dvd_mk (n : ℕ) (hn : 0 < n) (h6 : 6 ∣ n)
    (h : (axiomChoice K c).A.R) :
    normalized K c p n (residueMap C P n h) =
      (Real.sqrt (primeNorm K c p ^ n) : ℂ)⁻¹ *
        ((if h ∈ (p.val.asIdeal ^ n).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) then
            (primeNorm K c p : ℂ) ^ n else 0) -
          (if h ∈ (p.val.asIdeal ^ (n - 1)).map (algebraMap (𝓞 K) (axiomChoice K c).A.R) then
            (primeNorm K c p : ℂ) ^ (n - 1) else 0)) := by
  simp only [normalized_of_six_dvd_original_mask K c p n hn h6,
    frequency_mk_eq_zero_iff, lastLayer_mk_iff]

end HeckeSkeleton.Moments.MOM_BASE.LocalGauss
