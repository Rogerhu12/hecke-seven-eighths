import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteProductGauss
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SIntegerFirstFourier

/-!
# The genuine active common Gauss factor

The active character has the actual nonzero net exponent at each prime.
Its complete squarefree quotient is identified with the product of the
actual residue fields, and the primitive trace character is transported
along that equivalence.  The square-root bound is derived from finite
Gauss sums, for all frequencies and all divisor dilations.
-/

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree LocalFiniteSums LocalFiniteSumCompatibility
open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckePort.Moments.ProductCRT HeckePort.Moments.Active

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

local instance commonPrimeField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _

local instance commonPrimeFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _

local instance commonPrimeFintype (p : ExteriorPrime A) :
    Fintype (A.R ⧸ A.extendIdeal (primeIdeal p)) := Fintype.ofFinite _

def actualFirstPrimeEquiv (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) :
    CommonSupport.Residue (generator C p ^ 1) ≃+*
      (A.R ⧸ A.extendIdeal (primeIdeal p)) :=
  Ideal.quotEquivOfEq (by simpa only [pow_one] using (generator_generates C p).2)

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance activeResidueFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    Finite (A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) := by
  rw [(firstActiveGenerator_generates C p m n).2]
  exact A.exteriorResidue_finite _

local instance activeResidueFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    Fintype (A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) := Fintype.ofFinite _

def actualFirstFieldCRT (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) :
    (A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) ≃+*
      ∀ i : activeSupport Finset.univ m n, A.R ⧸ A.extendIdeal (primeIdeal (p i.val)) := by
  change (A.R ⧸ Ideal.span
    {∏ i : activeSupport Finset.univ m n, generator C (firstActivePrimes p m n i) ^ 1}) ≃+* _
  exact (productCRT
    (fun i : activeSupport Finset.univ m n => generator C (firstActivePrimes p m n i) ^ 1)
    (primePowerGenerator_pairwise C (firstActivePrimes p m n)
      (firstActivePrimes_injective p hp m n) (fun _ => 1))).trans
    (RingEquiv.piCongrRight (fun i => actualFirstPrimeEquiv C (p i.val)))

theorem actualFirstFieldCRT_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (x : A.R) (i : activeSupport Finset.univ m n) :
    actualFirstFieldCRT C p hp m n (Ideal.Quotient.mk _ x) i =
      Ideal.Quotient.mk (A.extendIdeal (primeIdeal (p i.val))) x := by
  change actualFirstPrimeEquiv C (p i.val)
    (productCRT
      (fun i : activeSupport Finset.univ m n => generator C (firstActivePrimes p m n i) ^ 1)
      (primePowerGenerator_pairwise C (firstActivePrimes p m n)
        (firstActivePrimes_injective p hp m n) (fun _ => 1)) (Ideal.Quotient.mk _ x) i) = _
  rw [productCRT_mk]
  exact Ideal.quotEquivOfEq_mk _ x

theorem actualFirstActiveCharacter_fieldCRT (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (x : A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) :
    actualFirstActiveCharacter C p hp m n x =
      ∏ i : activeSupport Finset.univ m n,
        (chi (σ := σ) (p i.val) ^ netExponent (m i.val) (n i.val))
          (actualFirstFieldCRT C p hp m n x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [actualFirstActiveCharacter_mk]
  apply Finset.prod_congr rfl
  intro i _
  rw [actualFirstFieldCRT_mk]

theorem actual_first_local_active_nonprincipal
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (i : activeSupport Finset.univ m n) :
    chi (σ := σ) (p i.val) ^ netExponent (m i.val) (n i.val) ≠ 1 := by
  intro hh
  have hd : 6 ∣ netExponent (m i.val) (n i.val) := by
    rwa [← orderOf_dvd_iff_pow_eq_one, chi_exact_order] at hh
  have hn := netExponent_ne_zero Finset.univ m n i
  have hl := netExponent_lt_six (m i.val) (n i.val)
  have hg := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  omega

theorem actual_active_gauss_norm_le_sqrt
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (h : A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) :
    ‖completeResidueGauss T (firstActiveGenerator C p m n)
      (actualFirstActiveCharacter C p hp m n) h‖ ≤
        Real.sqrt (A.exteriorNorm (firstActiveIdeal p m n)) := by
  let e := actualFirstFieldCRT C p hp m n
  let χ := fun i : activeSupport Finset.univ m n =>
    chi (σ := σ) (p i.val) ^ netExponent (m i.val) (n i.val)
  have hb := FiniteProductGauss.crt_gauss_norm_le_sqrt e
    (T.ψ (firstActiveGenerator C p m n))
    (T.primitive _ (firstActiveGenerator_generates C p m n).1)
    χ (actual_first_local_active_nonprincipal (σ := σ) p m n) h
  have hc : (Fintype.card (A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) : ℝ) =
      A.exteriorNorm (firstActiveIdeal p m n) := by
    rw [← Nat.card_eq_fintype_card, (firstActiveGenerator_generates C p m n).2,
      A.exteriorResidue_card]
    simp [SArithmeticData.exteriorNorm, idealNorm]
  rw [hc] at hb
  simpa only [completeResidueGauss, actualFirstActiveCharacter_fieldCRT, e, χ] using hb

theorem actual_active_divisor_gauss_norm_le_sqrt
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (δ : A.R) (h : A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) :
    ‖actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ δ) *
      completeResidueGauss T (firstActiveGenerator C p m n)
        (actualFirstActiveCharacter C p hp m n) h‖ ≤
      Real.sqrt (A.exteriorNorm (firstActiveIdeal p m n)) := by
  rw [norm_mul]
  by_cases hδ : IsUnit (Ideal.Quotient.mk (Ideal.span {firstActiveGenerator C p m n}) δ)
  · obtain ⟨u, hu⟩ := hδ
    rw [← hu, norm_char_unit, one_mul]
    exact actual_active_gauss_norm_le_sqrt C T p hp m n h
  · rw [MulChar.map_nonunit _ hδ, norm_zero, zero_mul]
    exact Real.sqrt_nonneg _

end Product
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_active_gauss_norm_le_sqrt
#print axioms HeckeSkeleton.Moments.EngineStep.actual_active_divisor_gauss_norm_le_sqrt
