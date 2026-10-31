import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SIntegerFirstFourier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PowerfulProducts

/-!
# Genuine powerful support at the first zero frequency

The zero-frequency Gauss sum of an actual residual ideal splits by CRT
into the complete prime-power character sums.  A positive exponent not
divisible by six makes its local sum zero.  Thus the two exclusive
residual ideals in a nonzero first mixed transform are powerful.  Every
common prime already occurs on both sides, so the complete original
product is powerful as well.  The result includes the empty prime sets.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.ProductCRT

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance zeroPrimePowerFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFinite C p n

local instance zeroPrimePowerFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFintype C p n

local instance zeroProductFinite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A) (n : ι → ℕ) :
    Finite (A.R ⧸ Ideal.span {primePowerProductGenerator C p n}) := by
  rw [(primePowerProduct_generates C p n).2]
  exact A.exteriorResidue_finite _

local instance zeroProductFintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A) (n : ι → ℕ) :
    Fintype (A.R ⧸ Ideal.span {primePowerProductGenerator C p n}) := Fintype.ofFinite _

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complete zero-frequency sum keeps all prime-power fibers; it is
not replaced by a primitive Gauss sum. -/
theorem actual_prime_power_product_zero_gauss
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) :
    completeResidueGauss T (primePowerProductGenerator C p n)
      (generatedIdealCharacter (σ := σ) (primePowerProduct p n)
        (primePowerProductGenerator C p n) (primePowerProduct_generates C p n)) 0 =
      ∏ i, ∑ x : Residue C (p i) (n i),
        localMaskedCharacter C (p i) (n i) (hn i).ne' x := by
  let a : ι → A.R := fun i => generator C (p i) ^ n i
  let hc := primePowerGenerator_pairwise C p hp n
  let e := productCRT a hc
  have hchar : generatedIdealCharacter (σ := σ) (primePowerProduct p n)
      (primePowerProductGenerator C p n) (primePowerProduct_generates C p n) =
      crtCharacter e (fun i => localMaskedCharacter C (p i) (n i) (hn i).ne') := by
    have he := generatedIdealCharacter_product
      (fun i => powerIdeal (p i) (n i)) a
      (fun i => generator_power_generates C (p i) (n i)) hc
    change generatedIdealCharacter (σ := σ) (primePowerProduct p n)
      (primePowerProductGenerator C p n) (primePowerProduct_generates C p n) = _ at he
    rw [he]
    congr 1
    funext i
    exact generatedIdealCharacter_prime_power C (p i) (n i) (hn i).ne'
  simp only [completeResidueGauss, zero_mul, AddChar.map_zero_eq_one, mul_one, hchar,
    crtCharacter_apply]
  rw [Fintype.prod_sum]
  exact e.toEquiv.sum_comp (fun x => ∏ i, localMaskedCharacter C (p i) (n i) (hn i).ne' (x i))

theorem actual_zero_gauss_nonzero_exponents
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i)
    (hzero : completeResidueGauss T (primePowerProductGenerator C p n)
      (generatedIdealCharacter (σ := σ) (primePowerProduct p n)
        (primePowerProductGenerator C p n) (primePowerProduct_generates C p n)) 0 ≠ 0) :
    ∀ i, 6 ∣ n i := by
  rw [actual_prime_power_product_zero_gauss C T p hp n hn] at hzero
  intro i
  by_contra hsix
  apply hzero
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact localMaskedCharacter_sum_zero C (p i) (n i) (hn i) hsix

theorem actual_zero_gauss_nonzero_powerful
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (n : ι → ℕ)
    (hn : ∀ i, 0 < n i)
    (hzero : completeResidueGauss T (primePowerProductGenerator C p n)
      (generatedIdealCharacter (σ := σ) (primePowerProduct p n)
        (primePowerProductGenerator C p n) (primePowerProduct_generates C p n)) 0 ≠ 0) :
    Powerful (primePowerProduct p n).val := by
  have hsix := actual_zero_gauss_nonzero_exponents C T p hp n hn hzero
  change Powerful (∏ i, (p i).val.asIdeal ^ n i)
  apply powerful_finset_prime_powers Finset.univ
    (fun i => (p i).val.asIdeal) n (fun i _ => (p i).val.ne_bot)
  intro i _
  right
  exact (by norm_num : 2 ≤ 6).trans (Nat.le_of_dvd (hn i) (hsix i))

/-- A common prime occurs in both original indices, hence at least
twice in their product, with no cancellation of either multiplicity. -/
theorem actual_common_product_powerful (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) :
    Powerful ((primePowerProduct p m).val * (primePowerProduct p n).val) := by
  change Powerful ((∏ i, (p i).val.asIdeal ^ m i) * ∏ i, (p i).val.asIdeal ^ n i)
  rw [← Finset.prod_mul_distrib]
  simp_rw [← pow_add]
  apply powerful_finset_prime_powers Finset.univ (fun i => (p i).val.asIdeal)
    (fun i => m i + n i) (fun i _ => (p i).val.ne_bot)
  intro i _
  right
  have hi := hm i
  have hj := hn i
  omega

end Product

section FirstTransform

variable {ι κ λ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype λ] [DecidableEq λ]

/-- The first mixed Fourier coefficient at zero can be nonzero only on
the powerful product diagonal of the complete original two indices.
The common function is arbitrary, so every moving-mask divisor and
every bounded common phase can be retained inside it. -/
theorem actual_first_zero_powerful_original
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (q : κ → ExteriorPrime A) (hq : Function.Injective q) (u : κ → ℕ) (hu : ∀ i, 0 < u i)
    (r : λ → ExteriorPrime A) (hr : Function.Injective r) (v : λ → ℕ) (hv : ∀ i, 0 < v i)
    (c : A.R) (hc : c ≠ 0)
    (habc : IsCoprime (primePowerProductGenerator C q u)
      (primePowerProductGenerator C r v * c))
    (hbc : IsCoprime (primePowerProductGenerator C r v) c)
    [Fintype (CommonSupport.Residue c)]
    [Fintype (CommonSupport.Residue (primePowerProductGenerator C r v * c))]
    [Fintype (CommonSupport.Residue
      (primePowerProductGenerator C q u * (primePowerProductGenerator C r v * c)))]
    (G : CommonSupport.Residue c → ℂ)
    (hzero : (∑ x : CommonSupport.Residue
      (primePowerProductGenerator C q u * (primePowerProductGenerator C r v * c)),
      generatedIdealCharacter (σ := σ) (primePowerProduct q u)
        (primePowerProductGenerator C q u) (primePowerProduct_generates C q u)
        (completeFrequencyReduction _ _ (dvd_mul_right _ _) x) *
      (generatedIdealCharacter (σ := σ) (primePowerProduct r v)
        (primePowerProductGenerator C r v) (primePowerProduct_generates C r v))⁻¹
        (completeFrequencyReduction _ _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x) *
      G (completeFrequencyReduction _ _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) *
      T.ψ _ (0 * x)) ≠ 0) :
    Powerful (((primePowerProduct p m).val * (primePowerProduct q u).val) *
      ((primePowerProduct p n).val * (primePowerProduct r v).val)) := by
  let a := primePowerProductGenerator C q u
  let b := primePowerProductGenerator C r v
  let χa := generatedIdealCharacter (σ := σ) (primePowerProduct q u) a
    (primePowerProduct_generates C q u)
  let χb := generatedIdealCharacter (σ := σ) (primePowerProduct r v) b
    (primePowerProduct_generates C r v)
  have he := complete_three_factor_mixed_fourier T a b c
    (primePowerProduct_generates C q u).1 (primePowerProduct_generates C r v).1
    hc habc hbc χa χb⁻¹ G 0
  simp only [map_zero] at he
  have hGa : completeResidueGauss T a χa 0 ≠ 0 := by
    intro hz
    apply hzero
    rw [he]
    simp only [hz, mul_zero, zero_mul]
  have hGb : completeResidueGauss T b χb 0 ≠ 0 := by
    intro hz
    have hz' : completeResidueGauss T b χb⁻¹ 0 = 0 := by
      rw [completeResidueGauss_inverse, neg_zero, hz, star_zero]
    apply hzero
    rw [he]
    simp only [hz', mul_zero, zero_mul]
  have hpa := actual_zero_gauss_nonzero_powerful C T q hq u hu hGa
  have hpb := actual_zero_gauss_nonzero_powerful C T r hr v hv hGb
  have hcommon := actual_common_product_powerful p m n hm hn
  have hprod := powerful_mul
    (mul_ne_zero (primePowerProduct p m).property.1 (primePowerProduct p n).property.1)
    (mul_ne_zero (primePowerProduct q u).property.1 (primePowerProduct r v).property.1)
    hcommon (powerful_mul (primePowerProduct q u).property.1
      (primePowerProduct r v).property.1 hpa hpb)
  convert hprod using 1 <;> ring

end FirstTransform

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_zero_gauss_nonzero_exponents
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_zero_powerful_original
