import HeckePort.Moments.Canonical
import HeckeGeneral.Analysis.ThetaPrimeGaussNorm
import HeckeGeneral.Analysis.GlobalThetaData
import SIntegerSexticPrimePowerQuotient

/-!
# Actual finite coefficients for the canonical moment reductions

The local characters are the specified-root sextic characters from
`ThetaArithmeticData`. Their exact order, prime Gauss norm, prime-power
tables and CRT decomposition are proved here without character/order
hypotheses. The prime ideals need not be principal in the ring of integers.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem actualPrimeCharacter_order (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

theorem actualPrimeCharacter_pow_eq_one_iff (p : ExteriorPrime K S) (a : ℕ) :
    thetaPrimeCharacter K S D p ^ a = 1 ↔ 6 ∣ a := by
  rw [← orderOf_dvd_iff_pow_eq_one, actualPrimeCharacter_order]

theorem actualPrimeCharacter_norm (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) (hx : x ≠ 0) :
    ‖thetaPrimeCharacter K S D p x‖ = 1 :=
  sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property) x hx

theorem actualPrimeGaussNorm (p : ExteriorPrime K S) :
    ‖thetaGamma K S D (exteriorPrimeIdeal K S p) 2‖ = 1 :=
  thetaGamma_exteriorPrime_two_norm K S D p

/-- An arbitrary power of an actual exterior prime, including power zero. -/
def actualPrimePowerIdeal (p : ExteriorPrime K S) (a : ℕ) : ExteriorIdeal K S :=
  ⟨⟨p.val.asIdeal ^ a, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ p.val.ne_bot)⟩,
    primePower_exterior K S p.val p.property a⟩

@[simp] theorem actualPrimePowerIdeal_mul (p : ExteriorPrime K S) (a b : ℕ) :
    exteriorMul K S (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b) =
      actualPrimePowerIdeal K S p (a + b) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (pow_add p.val.asIdeal a b).symm

/-- The original zero-extended prime-power character. In particular a
positive exponent divisible by six gives the unit mask. -/
def actualPrimePowerCharacter (p : ExteriorPrime K S) {a : ℕ} (ha : 1 ≤ a) :
    MulChar (𝓞 K ⧸ p.val.asIdeal ^ a) ℂ :=
  primePowerCharacter p.val.asIdeal ha (thetaPrimeCharacter K S D p ^ a)

@[simp] theorem actualPrimePowerCharacter_apply (p : ExteriorPrime K S)
    {a : ℕ} (ha : 1 ≤ a) (x : 𝓞 K ⧸ p.val.asIdeal ^ a) :
    actualPrimePowerCharacter K S D p ha x =
      (thetaPrimeCharacter K S D p ^ a) (primePowerReduction p.val.asIdeal ha x) := rfl

@[simp] theorem actualPrimePowerCharacter_mk (p : ExteriorPrime K S)
    {a : ℕ} (ha : 1 ≤ a) (x : 𝓞 K) :
    actualPrimePowerCharacter K S D p ha (Ideal.Quotient.mk _ x) =
      thetaPrimeCharacter K S D p (Ideal.Quotient.mk _ x) ^ a := by
  rw [actualPrimePowerCharacter_apply, MulChar.pow_apply' _ (by omega)] <;> rfl

/-- Localization identifies the ordinary prime-power quotient with the
actual S-integer quotient, without a principal prime in the integers. -/
def actualPrimePowerResidueEquiv (p : ExteriorPrime K S) (a : ℕ) :
    (𝓞 K ⧸ p.val.asIdeal ^ a) ≃+* sIntegerPrimePowerQuotient K S p.val a :=
  sIntegerResidueEquiv K S (p.val.asIdeal ^ a)
    (sexticIdeal_coprime_S K S (p.val.asIdeal ^ a)
      (primePower_exterior K S p.val p.property a))

@[simp] theorem actualPrimePowerResidueEquiv_reduction (p : ExteriorPrime K S)
    {a : ℕ} (ha : 1 ≤ a) (x : 𝓞 K ⧸ p.val.asIdeal ^ a) :
    sIntegerPrimePowerReduction K S p.val p.property a ha
      (actualPrimePowerResidueEquiv K S p a x) =
      primePowerReduction p.val.asIdeal ha x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [actualPrimePowerResidueEquiv, sIntegerResidueEquiv_mk,
    sIntegerPrimePowerReduction_mk, sIntegerSexticResidueMap_algebraMap] <;> rfl

/-- The port's prime-power character is the actual ideal quotient
function after the proved localization equivalence. This equality
includes every zero and all positive exponents divisible by six. -/
theorem actualPrimePowerCharacter_eq_quotientFunction (p : ExteriorPrime K S)
    {a : ℕ} (ha : 1 ≤ a) (x : 𝓞 K ⧸ p.val.asIdeal ^ a) :
    actualPrimePowerCharacter K S D p ha x =
      sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
        (p.val.asIdeal ^ a) (pow_ne_zero _ p.val.ne_bot)
        (primePower_exterior K S p.val p.property a)
        (primePower_away_six K p.val a (D.away_six p.val p.property))
        (actualPrimePowerResidueEquiv K S p a x) := by
  rw [sIntegerSexticPrimePowerQuotientFunction_eq_pullback K S p.val p.property
    a ha D.root6 D.primitive6 D.embedding (D.away_six p.val p.property),
    actualPrimePowerResidueEquiv_reduction] <;> rfl

section PrimePower

variable (p : ExteriorPrime K S) {a : ℕ} (ha : 1 ≤ a)
variable [Fintype (𝓞 K ⧸ p.val.asIdeal ^ a)] [Fintype (𝓞 K ⧸ p.val.asIdeal)]
local instance : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

theorem actualPrimePowerCharacter_zero_of_reduction_zero
    (x : 𝓞 K ⧸ p.val.asIdeal ^ a)
    (hx : primePowerReduction p.val.asIdeal ha x = 0) :
    actualPrimePowerCharacter K S D p ha x = 0 := by
  rw [actualPrimePowerCharacter_apply, hx, MulChar.map_zero]

/-- Exponents divisible by six preserve the original unit mask, including
its zero at the prime. -/
theorem actualPrimePowerCharacter_trivial_exponent_mask (ha6 : 6 ∣ a)
    (x : 𝓞 K ⧸ p.val.asIdeal ^ a) :
    actualPrimePowerCharacter K S D p ha x =
      if primePowerReduction p.val.asIdeal ha x = 0 then 0 else 1 := by
  rw [actualPrimePowerCharacter_apply,
    (actualPrimeCharacter_pow_eq_one_iff K S D p a).mpr ha6]
  by_cases hx : primePowerReduction p.val.asIdeal ha x = 0
  · simp [hx, MulChar.map_zero]
  · rw [if_neg hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

/-- The equal-prime-power unit table with the actual sextic phase. -/
theorem actualPrimePowerCorrelation_units
    (u : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ) (v k : 𝓞 K ⧸ p.val.asIdeal ^ a)
    (hv : primePowerReduction p.val.asIdeal ha v ≠ 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.val.asIdeal ^ a) * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k =
      (p.val.asIdeal.absNorm : ℂ) ^ (a - 1) *
        thetaPrimeCharacter K S D p
          (primePowerReduction p.val.asIdeal ha u / primePowerReduction p.val.asIdeal ha v) ^ a *
        (if primePowerReduction p.val.asIdeal ha k = 0 then (p.val.asIdeal.absNorm : ℂ) - 1
         else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units p.val.asIdeal ha (thetaPrimeCharacter K S D p)
    (actualPrimeCharacter_order K S D p) u v k hv

/-- The branch where the second residual column is zero; its mask survives. -/
theorem actualPrimePowerCorrelation_second_zero
    (u : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ) (v k : 𝓞 K ⧸ p.val.asIdeal ^ a)
    (hv : primePowerReduction p.val.asIdeal ha v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.val.asIdeal ^ a) * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k =
      (p.val.asIdeal.absNorm : ℂ) ^ (a - 1) *
        (if 6 ∣ a ∧ primePowerReduction p.val.asIdeal ha k ≠ 0
         then (p.val.asIdeal.absNorm : ℂ) - 1 else 0) :=
  primePower_localCorrelation_second_zero p.val.asIdeal ha (thetaPrimeCharacter K S D p)
    (actualPrimeCharacter_order K S D p) u v k hv

/-- The symmetric zero branch; this statement uses the original column. -/
theorem actualPrimePowerCorrelation_first_zero
    (u : 𝓞 K ⧸ p.val.asIdeal ^ a) (v : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ)
    (k : 𝓞 K ⧸ p.val.asIdeal ^ a) (hu : primePowerReduction p.val.asIdeal ha u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ p.val.asIdeal ^ a) * x) (fun y => u * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k =
      (p.val.asIdeal.absNorm : ℂ) ^ (a - 1) *
        (if 6 ∣ a ∧ primePowerReduction p.val.asIdeal ha k ≠ 0
         then (p.val.asIdeal.absNorm : ℂ) - 1 else 0) :=
  primePower_localCorrelation_first_zero p.val.asIdeal ha (thetaPrimeCharacter K S D p)
    (actualPrimeCharacter_order K S D p) u v k hu

theorem actualPrimePowerCorrelation_units_norm
    (u : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ) (v k : 𝓞 K ⧸ p.val.asIdeal ^ a)
    (hv : primePowerReduction p.val.asIdeal ha v ≠ 0) :
    ‖fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.val.asIdeal ^ a) * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k‖ =
      (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) *
        ‖(if primePowerReduction p.val.asIdeal ha k = 0 then (p.val.asIdeal.absNorm : ℂ) - 1
          else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1)‖ := by
  have hu : primePowerReduction p.val.asIdeal ha u ≠ 0 :=
    isUnit_iff_ne_zero.mp (u.isUnit.map (primePowerReduction p.val.asIdeal ha))
  have hphase := actualPrimeCharacter_norm K S D p _ (div_ne_zero hu hv)
  rw [actualPrimePowerCorrelation_units K S D p ha u v k hv,
    norm_mul, norm_mul, norm_pow, norm_pow, hphase]
  simp

/-- The improved bound for a unit frequency and nontrivial exponent. -/
theorem actualPrimePowerCorrelation_unit_frequency_norm
    (u : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ) (v k : 𝓞 K ⧸ p.val.asIdeal ^ a)
    (hv : primePowerReduction p.val.asIdeal ha v ≠ 0)
    (hk : primePowerReduction p.val.asIdeal ha k ≠ 0) (ha6 : ¬ 6 ∣ a) :
    ‖fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.val.asIdeal ^ a) * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k‖ =
      (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) := by
  rw [actualPrimePowerCorrelation_units_norm K S D p ha u v k hv]
  simp [hk, ha6]

private theorem actualPrime_norm_sub_le (r : ℝ) (hr : 0 ≤ r)
    (hrP : r ≤ (p.val.asIdeal.absNorm : ℝ)) :
    ‖(p.val.asIdeal.absNorm : ℂ) - (r : ℂ)‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
  have he : (p.val.asIdeal.absNorm : ℂ) - (r : ℂ) =
      (((p.val.asIdeal.absNorm : ℝ) - r : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hrP)]
  linarith

/-- Uniform size `P^a` for every frequency and every residual second column. -/
theorem actualPrimePowerCorrelation_norm_le
    (u : (𝓞 K ⧸ p.val.asIdeal ^ a)ˣ) (v k : 𝓞 K ⧸ p.val.asIdeal ^ a) :
    ‖fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.val.asIdeal ^ a) * y)
      (actualPrimePowerCharacter K S D p ha) (actualPrimePowerCharacter K S D p ha) k‖ ≤
      (p.val.asIdeal.absNorm : ℝ) ^ a := by
  have hP : (2 : ℝ) ≤ p.val.asIdeal.absNorm := by
    exact_mod_cast (show 2 ≤ p.val.asIdeal.absNorm from
      NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  have hnormP : ‖(p.val.asIdeal.absNorm : ℂ)‖ = (p.val.asIdeal.absNorm : ℝ) := by simp
  have hsub1 : ‖(p.val.asIdeal.absNorm : ℂ) - 1‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
    simpa using actualPrime_norm_sub_le K S p 1 (by norm_num) (by linarith)
  have hsub2 : ‖(p.val.asIdeal.absNorm : ℂ) - 2‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
    simpa using actualPrime_norm_sub_le K S p 2 (by norm_num) hP
  have hfactor : (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) * p.val.asIdeal.absNorm =
      (p.val.asIdeal.absNorm : ℝ) ^ a := by
    rw [← pow_succ, Nat.sub_add_cancel ha]
  by_cases hv : primePowerReduction p.val.asIdeal ha v = 0
  · rw [actualPrimePowerCorrelation_second_zero K S D p ha u v k hv,
      norm_mul, norm_pow, hnormP]
    have hb : ‖(if 6 ∣ a ∧ primePowerReduction p.val.asIdeal ha k ≠ 0
        then (p.val.asIdeal.absNorm : ℂ) - 1 else 0)‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
      split_ifs
      · exact hsub1
      · simp
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq hfactor
  · rw [actualPrimePowerCorrelation_units_norm K S D p ha u v k hv]
    have hb : ‖(if primePowerReduction p.val.asIdeal ha k = 0
        then (p.val.asIdeal.absNorm : ℂ) - 1
        else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1)‖ ≤
        (p.val.asIdeal.absNorm : ℝ) := by
      split_ifs
      · exact hsub1
      · exact hsub2
      · simpa using (show (1 : ℝ) ≤ p.val.asIdeal.absNorm by linarith)
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq hfactor

end PrimePower

section CRT

variable {ι : Type*} [Fintype ι]
variable (p : ι → ExteriorPrime K S) (hp : Function.Injective p)
variable (a : ι → ℕ) (ha : ∀ i, 1 ≤ a i)

include hp in
theorem actualPrimeList_coprime :
    Pairwise (Function.onFun IsCoprime (fun i => (p i).val.asIdeal)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  intro he
  apply hij
  apply hp
  apply Subtype.ext
  exact HeightOneSpectrum.asIdeal_injective he

include hp in
theorem actualPrimePowerList_coprime :
    Pairwise (Function.onFun IsCoprime (fun i => (p i).val.asIdeal ^ a i)) := by
  intro i j hij
  exact (actualPrimeList_coprime K S p hp hij).pow

def actualPrimeCRTEquiv :
    (𝓞 K ⧸ ∏ i, (p i).val.asIdeal ^ a i) ≃+*
      ∀ i, 𝓞 K ⧸ (p i).val.asIdeal ^ a i :=
  quotientProdEquivPi (fun i => (p i).val.asIdeal ^ a i)
    (actualPrimePowerList_coprime K S p hp a)

def actualCRTCharacter : MulChar (𝓞 K ⧸ ∏ i, (p i).val.asIdeal ^ a i) ℂ :=
  crtCharacter (actualPrimeCRTEquiv K S p hp a)
    (fun i => actualPrimePowerCharacter K S D (p i) (ha i))

@[simp] theorem actualCRTCharacter_mk (x : 𝓞 K) :
    actualCRTCharacter K S D p hp a ha (Ideal.Quotient.mk _ x) =
      ∏ i, thetaPrimeCharacter K S D (p i) (Ideal.Quotient.mk _ x) ^ a i := by
  unfold actualCRTCharacter
  simp only [crtCharacter_apply, actualPrimeCRTEquiv, quotientProdEquivPi_mk,
    actualPrimePowerCharacter_mk]

variable [Fintype (𝓞 K ⧸ ∏ i, (p i).val.asIdeal ^ a i)]
variable [∀ i, Fintype (𝓞 K ⧸ (p i).val.asIdeal ^ a i)]

/-- Actual finite-support CRT factorization. Distinctness of the displayed
prime list proves the coprimality required by the generic port. -/
theorem actualCRTCorrelation (u v k : 𝓞 K ⧸ ∏ i, (p i).val.asIdeal ^ a i) :
    let e := actualPrimeCRTEquiv K S p hp a
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (actualCRTCharacter K S D p hp a ha) (actualCRTCharacter K S D p hp a ha) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (actualPrimePowerCharacter K S D (p i) (ha i))
        (actualPrimePowerCharacter K S D (p i) (ha i)) (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, actualPrimePowerCharacter K S D (p i) (ha i)
      (actualPrimeCRTEquiv K S p hp a x i))
    (fun x => ∏ i, actualPrimePowerCharacter K S D (p i) (ha i)
      (actualPrimeCRTEquiv K S p hp a x i)) k = _
  rw [fullCorrelation_ringEquiv (actualPrimeCRTEquiv K S p hp a) u v k
    (fun x => ∏ i, actualPrimePowerCharacter K S D (p i) (ha i) (x i))
    (fun x => ∏ i, actualPrimePowerCharacter K S D (p i) (ha i) (x i)),
    fullCorrelation_pi]

end CRT

end HeckeSkeleton.Moments.MOM_BASE
