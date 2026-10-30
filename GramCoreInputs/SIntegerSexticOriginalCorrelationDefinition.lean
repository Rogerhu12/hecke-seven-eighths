import FiniteCommonFactorFibre
import HeckeGeneral.Characters.SIntegerSexticSymbol

/-! SOURCE ONLY, UNRUN. CFT-free extraction of the original full
correlation definition and principal quotient-fibre transport. Copied
from SIntegerSexticOriginalFullCorrelation through its original sum
definition; originalColumnEquiv is exported for later transports. -/

noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical
variable {R : Type*} [CommRing R]

theorem commonFactorFullFibre_relation_mk_iff
    (C : Ideal R) (n₁ n₂ k x y : R) :
    commonFactorFirstMultiplier C n₁ n₂ (Ideal.Quotient.mk _ x) -
        commonFactorSecondMultiplier C n₁ n₂ (Ideal.Quotient.mk _ y) =
          Ideal.Quotient.mk _ k ↔
      n₂ * x - n₁ * y - k ∈ commonFactorTotalIdeal C n₁ n₂ := by
  change Ideal.Quotient.mk _ (n₂ * x) - Ideal.Quotient.mk _ (n₁ * y) =
    Ideal.Quotient.mk _ k ↔ _
  rw [← map_sub]
  exact Ideal.Quotient.eq

theorem principalCommonFactor_column_eq (c n : R) :
    commonFactorColumnIdeal (⊤ : Ideal R) (c * n) =
      commonFactorColumnIdeal (Ideal.span ({c} : Set R)) n := by
  simp only [commonFactorColumnIdeal, Ideal.top_mul,
    Ideal.span_singleton_mul_span_singleton]

/-- Actual pair-quotient transport; the original and reduced congruence
predicates are proved equivalent by domain cancellation. -/
def originalToReducedPrincipalFibreEquiv [IsDomain R]
    (c n₁ n₂ k : R) (hc : c ≠ 0) :
    commonFactorFullFibre (⊤ : Ideal R) (c * n₁) (c * n₂) (c * k) ≃
      commonFactorFullFibre (Ideal.span ({c} : Set R)) n₁ n₂ k :=
  Equiv.subtypeEquiv
    ((Ideal.quotEquivOfEq (principalCommonFactor_column_eq c n₁)).toEquiv.prodCongr
      (Ideal.quotEquivOfEq (principalCommonFactor_column_eq c n₂)).toEquiv)
    (by
      rintro ⟨x, y⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change (_ = _) ↔ (_ = _)
      change
        commonFactorFirstMultiplier ⊤ (c * n₁) (c * n₂) (Ideal.Quotient.mk _ x) -
          commonFactorSecondMultiplier ⊤ (c * n₁) (c * n₂) (Ideal.Quotient.mk _ y) =
            Ideal.Quotient.mk _ (c * k) ↔
        commonFactorFirstMultiplier (Ideal.span ({c} : Set R)) n₁ n₂
            (Ideal.Quotient.mk _ x) -
          commonFactorSecondMultiplier (Ideal.span ({c} : Set R)) n₁ n₂
            (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ k
      rw [commonFactorFullFibre_relation_mk_iff, commonFactorFullFibre_relation_mk_iff]
      simpa only [commonFactorTotalIdeal, Ideal.top_mul,
        Ideal.span_singleton_mul_span_singleton, mul_assoc] using
        (commonFactor_original_congruence_iff c n₁ n₂ k x y hc))

@[simp] theorem originalToReducedPrincipalFibreEquiv_fst [IsDomain R]
    (c n₁ n₂ k : R) (hc : c ≠ 0)
    (p : commonFactorFullFibre (⊤ : Ideal R) (c * n₁) (c * n₂) (c * k)) :
    (originalToReducedPrincipalFibreEquiv c n₁ n₂ k hc p).val.1 =
      Ideal.quotEquivOfEq (principalCommonFactor_column_eq c n₁) p.val.1 := rfl

@[simp] theorem originalToReducedPrincipalFibreEquiv_snd [IsDomain R]
    (c n₁ n₂ k : R) (hc : c ≠ 0)
    (p : commonFactorFullFibre (⊤ : Ideal R) (c * n₁) (c * n₂) (c * k)) :
    (originalToReducedPrincipalFibreEquiv c n₁ n₂ k hc p).val.2 =
      Ideal.quotEquivOfEq (principalCommonFactor_column_eq c n₂) p.val.2 := rfl
end HeckeGeneral.Arithmetic.PeriodicFourier

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "R" => S.integer K
local notation "N" => NonzeroRingElements R
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6

/-- Literal symbol descended to its principal residue quotient. The
choice of lift is removed by the proved numerator periodicity. -/
def sIntegerSexticPrincipalQuotientSymbol (u : N)
    (q : R ⧸ Ideal.span ({u.val} : Set R)) : ℂ :=
  χ (Classical.choose (Ideal.Quotient.mk_surjective q)) u

@[simp] theorem sIntegerSexticPrincipalQuotientSymbol_mk (u : N) (x : R) :
    sIntegerSexticPrincipalQuotientSymbol K S ζ hζ σ hS6 u
        (Ideal.Quotient.mk _ x) = χ x u := by
  apply sIntegerSexticSymbol_periodic K S ζ hζ σ hS6 _ x u
  apply Ideal.Quotient.eq.mp
  exact Classical.choose_spec (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _ x))

def originalColumnEquiv (u : N) :
    (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) ≃+*
      (R ⧸ Ideal.span ({u.val} : Set R)) :=
  Ideal.quotEquivOfEq (Ideal.top_mul _)

def originalColumnWeight (u : N)
    (q : R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) : ℂ :=
  sIntegerSexticPrincipalQuotientSymbol K S ζ hζ σ hS6 u (originalColumnEquiv K S u q)

@[simp] theorem originalColumnWeight_mk (u : N) (x : R) :
    originalColumnWeight K S ζ hζ σ hS6 u (Ideal.Quotient.mk _ x) = χ x u := by
  change sIntegerSexticPrincipalQuotientSymbol K S ζ hζ σ hS6 u
    (Ideal.Quotient.mk _ x) = χ x u
  exact sIntegerSexticPrincipalQuotientSymbol_mk K S ζ hζ σ hS6 u x

/-- Original genuine full sum: two actual principal residue columns,
literal relation v*x-u*y=j modulo (u*v), and actual symbol weights. -/
def sIntegerSexticOriginalFullCorrelation (u v : N) (j : R) : ℂ := by
  letI originalFull_firstFinite : Finite (R ⧸ Ideal.span ({u.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S u.val u.property
  letI originalFull_secondFinite : Finite (R ⧸ Ideal.span ({v.val} : Set R)) :=
    finite_sIntegerPrincipalResidue K S v.val v.property
  letI originalFull_firstColumnFinite : Finite (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) :=
    Finite.of_equiv _ (originalColumnEquiv K S u).symm.toEquiv
  letI originalFull_secondColumnFinite : Finite (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) v.val) :=
    Finite.of_equiv _ (originalColumnEquiv K S v).symm.toEquiv
  letI originalFull_firstFintype : Fintype (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) u.val) :=
    Fintype.ofFinite _
  letI originalFull_secondFintype : Fintype (R ⧸ commonFactorColumnIdeal (⊤ : Ideal R) v.val) :=
    Fintype.ofFinite _
  letI : Fintype (commonFactorFullFibre (⊤ : Ideal R) u.val v.val j) := by
    classical
    unfold commonFactorFullFibre
    infer_instance
  exact ∑ p : commonFactorFullFibre (⊤ : Ideal R) u.val v.val j,
    originalColumnWeight K S ζ hζ σ hS6 u p.val.1 *
      starRingEnd ℂ (originalColumnWeight K S ζ hζ σ hS6 v p.val.2)
theorem sIntegerSexticCommonFactor_exterior (c : N)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val) : p ∉ S := by
  intro hpS
  have hc := sIntegerModulusContraction_coprime K S c.val c.property p hpS
  rw [sup_eq_right.mpr (Ideal.dvd_iff_le.mp hp)] at hc
  exact p.isPrime.ne_top hc

end HeckeGeneral.Characters
