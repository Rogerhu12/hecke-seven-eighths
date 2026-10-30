import CubicSieve.Gauss
import CubicSieve.ExteriorKernel
import HeckeGeneral.Analysis.IdealSquarefreeSupport

/-!
The actual squarefree S-integer residue quotient, its literal sextic row,
and its cubic Gauss transforms. Mixed local powers 2 and 4 are allowed;
all frequencies, including zero and nonunits, remain in the identity.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussSquarefree

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Arithmetic.PeriodicFourier
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

abbrev PrimeSupport (I : ExteriorIdeal K S) := ↥(idealPrimeSupport K I.val)

def residueEquiv (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ThetaQuotient K S I ≃+* ∀ p : PrimeSupport K S I, Residue p.val :=
  (sIntegerResidueEquiv K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)).symm.trans
    ((Ideal.quotEquivOfEq
      (congrArg Subtype.val (squarefreeIdeal_primeSupport K I.val hI)).symm).trans
        (squarefreeCRT (idealPrimeSupport K I.val)))

@[simp] theorem residueEquiv_mk (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (a : 𝓞 K) (p : PrimeSupport K S I) :
    residueEquiv K S I hI (Ideal.Quotient.mk _
      (algebraMap (𝓞 K) (S.integer K) a)) p = Ideal.Quotient.mk p.val.asIdeal a := by
  let T := idealPrimeSupport K I.val
  have hprod : primeProduct T = I.val.val :=
    congrArg Subtype.val (squarefreeIdeal_primeSupport K I.val hI)
  change ((Ideal.quotEquivOfEq hprod.symm).trans (squarefreeCRT T))
    ((sIntegerResidueEquiv K S I.val.val
      (sexticIdeal_coprime_S K S I.val.val I.property)).symm
      (Ideal.Quotient.mk _ (algebraMap (𝓞 K) (S.integer K) a))) p = _
  rw [sIntegerResidueEquiv_symm_mk]
  change squarefreeCRT T ((Ideal.quotEquivOfEq hprod.symm)
    (Ideal.Quotient.mk _ a)) p = _
  rw [Ideal.quotEquivOfEq_mk]
  have hpair : Pairwise (Function.onFun IsCoprime (fun q : T => q.val.asIdeal)) := by
    intro q r hqr
    exact Ideal.isCoprime_of_isMaximal (fun h => hqr
      (Subtype.ext (HeightOneSpectrum.asIdeal_injective h)))
  change (Ideal.quotientInfRingEquivPiQuotient (fun q : T => q.val.asIdeal) hpair)
    ((Ideal.quotEquivOfEq (squarefree_quotient_eq T)) (Ideal.Quotient.mk _ a)) p = _
  rw [Ideal.quotEquivOfEq_mk]
  exact Ideal.quotientInfRingEquivPiQuotient_mk_apply hpair a p

def localCharacter (I : ExteriorIdeal K S) (p : PrimeSupport K S I) :
    MulChar (Residue p.val) ℂ :=
  sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val (I.property p.val
      ((mem_idealPrimeSupport_iff K I.val p.val).mp p.property)))

theorem localCharacter_order (I : ExteriorIdeal K S) (p : PrimeSupport K S I) :
    orderOf (localCharacter K S D I p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val _

theorem localCharacter_power_ne_one (I : ExteriorIdeal K S)
    (p : PrimeSupport K S I) (j : ℕ) (hj : j = 2 ∨ j = 4) :
    localCharacter K S D I p ^ j ≠ 1 := by
  intro h
  have hh := orderOf_dvd_of_pow_eq_one h
  rw [localCharacter_order K S D I p] at hh
  rcases hj with rfl | rfl <;> norm_num at hh

def quotientFunction (I : ExteriorIdeal K S) : ThetaQuotient K S I → ℂ :=
  sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

private theorem squarefree_multiplicity (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (p : idealPrimeDivisors K I.val.val) :
    idealPrimeMultiplicity K p.val I.val.val = 1 := by
  have hle : primeExponents I.val p.val ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors
        (nonZeroDivisors.coe_ne_zero I.val)).mp hI) p.val.asIdeal
  have hne : primeExponents I.val p.val ≠ 0 := by
    exact Finsupp.mem_support_iff.mp
      ((mem_idealPrimeSupport_iff K I.val p.val).mpr p.property)
  have hm : primeExponents I.val p.val =
      idealPrimeMultiplicity K p.val I.val.val := by
    rw [primeExponents_apply]
    exact (Ideal.count_associates_factors_eq
      (nonZeroDivisors.coe_ne_zero I.val) p.val.isPrime p.val.ne_bot).symm
  omega

theorem quotientFunction_eq_product (I : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (q : ThetaQuotient K S I) :
    quotientFunction K S D I q =
      ∏ p : PrimeSupport K S I, localCharacter K S D I p
        (residueEquiv K S I hI q p) := by
  let e := sIntegerResidueEquiv K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)
  obtain ⟨x, rfl⟩ := e.surjective q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientFunction K S D I
      (sIntegerResidueEquiv K S I.val.val _ (Ideal.Quotient.mk _ a)) = _
  rw [sIntegerResidueEquiv_mk]
  simp only [quotientFunction, sIntegerSexticIdealQuotientFunction_mk,
    residueEquiv_mk]
  letI : Fintype (idealPrimeDivisors K I.val.val) :=
    (idealPrimeDivisors_finite K _ (nonZeroDivisors.coe_ne_zero I.val)).fintype
  unfold sIntegerSexticIdealEvaluation
  apply Finset.prod_bij (fun p _ =>
    (⟨p.val, (mem_idealPrimeSupport_iff K I.val p.val).mpr p.property⟩ :
      PrimeSupport K S I))
  · intro p _; exact Finset.mem_univ _
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun t : PrimeSupport K S I => t.val) hpq)
  · intro p _
    exact ⟨⟨p.val, (mem_idealPrimeSupport_iff K I.val p.val).mp p.property⟩,
      Finset.mem_univ _, rfl⟩
  · intro p _
    rw [squarefree_multiplicity K S I hI p, pow_one,
      sIntegerSexticEvaluation_algebraMap]
    rfl

/-- A mixed cubic row on the actual quotient, with the same specified root. -/
def mixedRow (I : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (j : PrimeSupport K S I → ℕ) (q : ThetaQuotient K S I) : ℂ :=
  Gauss.productCoefficient (fun p => localCharacter K S D I p ^ j p)
    (residueEquiv K S I hI q)

theorem mixedRow_constant (I : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (j : ℕ) (hj : j ≠ 0) (q : ThetaQuotient K S I) :
    mixedRow K S D I hI (fun _ => j) q = quotientFunction K S D I q ^ j := by
  rw [quotientFunction_eq_product K S D I hI, ← Finset.prod_pow]
  unfold mixedRow Gauss.productCoefficient
  apply Finset.prod_congr rfl
  intro p _
  exact MulChar.pow_apply' _ hj _

section Finite
variable (I : ExteriorIdeal K S)
local instance quotientFinite : Finite (ThetaQuotient K S I) :=
  finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
local instance quotientFintype : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _

theorem mixedRow_fourier (hI : Squarefree I.val.val)
    (j : PrimeSupport K S I → ℕ) (hj : ∀ p, j p = 2 ∨ j p = 4)
    (ψ : AddChar (ThetaQuotient K S I) ℂ) (h : ThetaQuotient K S I) :
    fourier ψ (mixedRow K S D I hI j) h =
      star (mixedRow K S D I hI j h) *
        fourier ψ (mixedRow K S D I hI j) 1 :=
  Gauss.crt_fourier_conj (residueEquiv K S I hI)
    (fun p => localCharacter K S D I p ^ j p)
    (fun p => localCharacter_power_ne_one K S D I p (j p) (hj p)) ψ h

theorem mixedRow_gauss_norm_sq (hI : Squarefree I.val.val)
    (j : PrimeSupport K S I → ℕ) (hj : ∀ p, j p = 2 ∨ j p = 4)
    (ψ : AddChar (ThetaQuotient K S I) ℂ) (hψ : ψ.IsPrimitive) :
    ‖fourier ψ (mixedRow K S D I hI j) 1‖ ^ 2 = (I.val.val.absNorm : ℝ) := by
  unfold mixedRow
  rw [Gauss.crt_gauss_norm_sq (residueEquiv K S I hI)
    (fun p => localCharacter K S D I p ^ j p)
    (fun p => localCharacter_power_ne_one K S D I p (j p) (hj p)) ψ hψ]
  rw [← Nat.card_eq_fintype_card, natCard_sIntegerResidue K S I.val.val
    (sexticIdeal_coprime_S K S I.val.val I.property)]

theorem quotientFunction_power_fourier (hI : Squarefree I.val.val)
    (j : ℕ) (hj : j = 2 ∨ j = 4)
    (ψ : AddChar (ThetaQuotient K S I) ℂ) (h : ThetaQuotient K S I) :
    fourier ψ (fun q => quotientFunction K S D I q ^ j) h =
      star (quotientFunction K S D I h ^ j) *
        fourier ψ (fun q => quotientFunction K S D I q ^ j) 1 := by
  have hne : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
  have heq : mixedRow K S D I hI (fun _ => j) =
      fun q => quotientFunction K S D I q ^ j :=
    funext (mixedRow_constant K S D I hI j hne)
  simpa only [heq] using mixedRow_fourier K S D I hI (fun _ => j) (fun _ => hj) ψ h

set_option maxHeartbeats 1000000 in
theorem thetaGamma_norm (hI : Squarefree I.val.val)
    (j : ℕ) (hj : j = 2 ∨ j = 4) : ‖thetaGamma K S D I j‖ = 1 := by
  have hne : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
  have hn : 0 < (I.val.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors (I.val : (Ideal (𝓞 K))⁰)
  have hsqrt : 0 < Real.sqrt (I.val.val.absNorm : ℝ) := Real.sqrt_pos.mpr hn
  have hsum : ‖∑ x : ThetaQuotient K S I,
      quotientFunction K S D I x ^ j * thetaPrincipalAddCharacter K S D I x‖ ^ 2 =
        (I.val.val.absNorm : ℝ) := by
    have h := mixedRow_gauss_norm_sq K S D I hI (fun _ => j) (fun _ => hj)
      (thetaPrincipalAddCharacter K S D I) (thetaPrincipalAddCharacter_isPrimitive K S D I)
    simpa only [PeriodicFourier.fourier, one_mul,
      mixedRow_constant K S D I hI j hne] using h
  have hsumNorm : ‖∑ x : ThetaQuotient K S I,
      quotientFunction K S D I x ^ j * thetaPrincipalAddCharacter K S D I x‖ =
        Real.sqrt (I.val.val.absNorm : ℝ) := by
    nlinarith [norm_nonneg (∑ x : ThetaQuotient K S I,
      quotientFunction K S D I x ^ j * thetaPrincipalAddCharacter K S D I x),
      Real.sq_sqrt hn.le]
  change ‖(Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
    ∑ x : ThetaQuotient K S I,
      quotientFunction K S D I x ^ j * thetaPrincipalAddCharacter K S D I x‖ = 1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt, hsumNorm, inv_mul_cancel₀ hsqrt.ne']

end Finite
end CubicSieve.GaussSquarefree
