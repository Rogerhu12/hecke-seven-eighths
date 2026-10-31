import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationBound
import HeckePort.Moments.Active

/-!
# Actual active and principal factors in the first transform

The common prime-power factors of the original two characters are
reduced using the repository's genuine order-six residue characters.
Principal local factors remain literal coprimality zeros.  The active
factor is a character of the genuine squarefree active quotient, so it
can be substituted directly into the mixed S-integer Fourier transform.
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

local instance firstPrimeResidueField (p : ExteriorPrime A) :
    Field (A.R ⧸ A.extendIdeal (primeIdeal p)) := Ideal.Quotient.field _

local instance firstPrimeResidueFinite (p : ExteriorPrime A) :
    Finite (A.R ⧸ A.extendIdeal (primeIdeal p)) := A.exteriorResidue_finite _

theorem actual_prime_character_value (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (x : A.R) :
    chi (σ := σ) p (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x) =
      σ (A.sexticResidue (primeIdeal p) x) := by
  have hb := generatedIdealCharacter_mk (σ := σ) (primeIdeal p)
    (generator C p) (generator_generates C p) x
  rw [generatedIdealCharacter, transportCharacter_mk] at hb
  exact hb

theorem actual_prime_power_character_value (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) (hn : 0 < n) (x : A.R) :
    σ (A.sexticResidue (powerIdeal p n) x) =
      (chi (σ := σ) p ^ n) (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x) := by
  rw [actual_sextic_prime_power, MulChar.pow_apply' _ hn.ne', actual_prime_character_value C p x]

theorem actual_prime_residue_zero_iff (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (x : A.R) :
    Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) x = 0 ↔ generator C p ∣ x := by
  constructor
  · intro hx
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [← (generator_generates C p).2] at hm
    exact Ideal.mem_span_singleton.mp hm
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← (generator_generates C p).2]
    exact Ideal.mem_span_singleton.mpr hx

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def firstPrincipalMask (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (x : A.R) : ℂ :=
  if ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x then 0 else 1

def firstActivePrimes (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    activeSupport Finset.univ m n → ExteriorPrime A := fun i => p i.val

theorem firstActivePrimes_injective (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) : Function.Injective (firstActivePrimes p m n) := by
  intro i j hij
  exact Subtype.ext (hp hij)

def firstActiveIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ) : A.Exterior :=
  primePowerProduct (firstActivePrimes p m n) (fun _ => 1)

def firstActiveGenerator (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) : A.R :=
  primePowerProductGenerator C (firstActivePrimes p m n) (fun _ => 1)

theorem firstActiveGenerator_generates (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    A.Generates (firstActiveIdeal p m n) (firstActiveGenerator C p m n) :=
  primePowerProduct_generates C (firstActivePrimes p m n) _

/-- The nonprincipal factor on its actual squarefree active modulus. -/
def actualFirstActiveCharacter (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) :
    MulChar (A.R ⧸ Ideal.span {firstActiveGenerator C p m n}) ℂ :=
  crtCharacter (productCRT
    (fun i : activeSupport Finset.univ m n => generator C (p i.val) ^ 1)
    (primePowerGenerator_pairwise C (firstActivePrimes p m n)
      (firstActivePrimes_injective p hp m n) (fun _ => 1)))
    (fun i => localMaskedCharacter C (p i.val) 1 one_ne_zero ^ netExponent (m i.val) (n i.val))

theorem actualFirstActiveCharacter_mk (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) (x : A.R) :
    actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ x) =
      ∏ i : activeSupport Finset.univ m n,
        (chi (σ := σ) (p i.val) ^ netExponent (m i.val) (n i.val))
          (Ideal.Quotient.mk (A.extendIdeal (primeIdeal (p i.val))) x) := by
  rw [actualFirstActiveCharacter, crtCharacter_apply]
  simp only [productCRT_mk]
  apply Finset.prod_congr rfl
  intro i _
  have hn := netExponent_ne_zero Finset.univ m n i
  rw [MulChar.pow_apply' _ hn, MulChar.pow_apply' _ hn]
  have hl : localMaskedCharacter C (p i.val) 1 one_ne_zero (Ideal.Quotient.mk _ x) =
      chi (σ := σ) (p i.val) (Ideal.Quotient.mk (A.extendIdeal (primeIdeal (p i.val))) x) := by
    simpa only [pow_one] using localMaskedCharacter_mk C (p i.val) 1 one_ne_zero x
  exact congrArg (fun z : ℂ => z ^ netExponent (m i.val) (n i.val)) hl

theorem actual_principal_product_mask (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (x : A.R) :
    (∏ i ∈ principalSupport Finset.univ m n,
      (1 : MulChar (A.R ⧸ A.extendIdeal (primeIdeal (p i))) ℂ)
        (Ideal.Quotient.mk _ x)) = firstPrincipalMask C p m n x := by
  by_cases hz : ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x
  · rw [firstPrincipalMask, if_pos hz]
    obtain ⟨i, hi, hx⟩ := hz
    apply Finset.prod_eq_zero hi
    rw [(actual_prime_residue_zero_iff C (p i) x).mpr hx, MulChar.map_zero]
  · rw [firstPrincipalMask, if_neg hz]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    apply isUnit_iff_ne_zero.mpr
    exact fun hx => hz ⟨i, hi, (actual_prime_residue_zero_iff C (p i) x).mp hx⟩

/-- This is the source-specific active/principal dictionary.  It assumes
neither a factorization of the actual characters nor an active-table
formula; both follow from their normalized residue family. -/
theorem actual_common_pair_active (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (x : A.R) :
    σ (A.sexticResidue (primePowerProduct p m) x) *
      star (σ (A.sexticResidue (primePowerProduct p n) x)) =
      firstPrincipalMask C p m n x *
        actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ x) := by
  let f : ι → ℂ := fun i =>
    (chi (σ := σ) (p i) ^ netExponent (m i) (n i))
      (Ideal.Quotient.mk (A.extendIdeal (primeIdeal (p i))) x)
  have hrow (r : ι → ℕ) (hr : ∀ i, 0 < r i) :
      σ (A.sexticResidue (primePowerProduct p r) x) =
        ∏ i, (chi (σ := σ) (p i) ^ r i) (Ideal.Quotient.mk _ x) := by
    rw [primePowerProduct, actual_sextic_product]
    apply Finset.prod_congr rfl
    intro i _
    exact actual_prime_power_character_value C (p i) (r i) (hr i) x
  have hlocal : σ (A.sexticResidue (primePowerProduct p m) x) *
      star (σ (A.sexticResidue (primePowerProduct p n) x)) = ∏ i, f i := by
    rw [hrow m hm, hrow n hn, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have h6 : chi (σ := σ) (p i) ^ 6 = 1 := by
      simpa only [chi_exact_order] using pow_orderOf_eq_one (chi (σ := σ) (p i))
    exact local_pair_reduction (chi (σ := σ) (p i)) h6 (m i) (n i) _
  have hprincipal : (∏ i ∈ Finset.univ.filter (fun i => netExponent (m i) (n i) = 0), f i) =
      firstPrincipalMask C p m n x := by
    rw [← actual_principal_product_mask C p m n x]
    apply Finset.prod_congr rfl
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2
    simp only [f, hi0, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i => netExponent (m i) (n i) = 0) f, hprincipal,
    actualFirstActiveCharacter_mk]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport Finset.univ m n) (f := f)).symm

/-- The full original pair becomes two genuine residual characters, one
literal principal mask, and the active common character.  This is the
pointwise input for the first mixed Fourier transform. -/
theorem actual_full_pair_active (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (IA IB IFull JFull : A.Exterior)
    (hI : IFull.val = (primePowerProduct p m).val * IA.val)
    (hJ : JFull.val = (primePowerProduct p n).val * IB.val) (x : A.R) :
    σ (A.sexticResidue IFull x) * star (σ (A.sexticResidue JFull x)) =
      σ (A.sexticResidue IA x) * star (σ (A.sexticResidue IB x)) *
        firstPrincipalMask C p m n x *
          actualFirstActiveCharacter C p hp m n (Ideal.Quotient.mk _ x) := by
  have hleft : σ (A.sexticResidue IFull x) =
      σ (A.sexticResidue (primePowerProduct p m) x) * σ (A.sexticResidue IA x) := by
    change σ (A.residueValue A.sexticResidueFamily IFull x) = _
    rw [A.sexticResidueFamily_normalized.2.2 (primePowerProduct p m) IA IFull hI x, map_mul]
  have hright : σ (A.sexticResidue JFull x) =
      σ (A.sexticResidue (primePowerProduct p n) x) * σ (A.sexticResidue IB x) := by
    change σ (A.residueValue A.sexticResidueFamily JFull x) = _
    rw [A.sexticResidueFamily_normalized.2.2 (primePowerProduct p n) IB JFull hJ x, map_mul]
  rw [hleft, hright, star_mul]
  calc
    _ = (σ (A.sexticResidue IA x) * star (σ (A.sexticResidue IB x))) *
        (σ (A.sexticResidue (primePowerProduct p m) x) *
          star (σ (A.sexticResidue (primePowerProduct p n) x))) := by ring
    _ = _ := by rw [actual_common_pair_active C p hp m n hm hn x]; ring

end Product

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_pair_active
#print axioms HeckeSkeleton.Moments.EngineStep.actual_full_pair_active
