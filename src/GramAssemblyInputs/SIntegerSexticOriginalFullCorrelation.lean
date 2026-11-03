import SIntegerSexticReducedFullCorrelation
import SIntegerSexticOriginalCorrelationDefinition

/-! SOURCE ONLY, UNRUN. Original full coefficient and the concrete
principal common-factor congruence transport. The original relation is
v*x-u*y=j modulo (u*v), prior to cancelling any common factor. -/
noncomputable section
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

/-- Transport of a full fibre along an equality of ideals. -/
def fibreCongr {I I' : Ideal R} (h : I = I') (n₁ n₂ k : R) :
    commonFactorFullFibre I n₁ n₂ k ≃ commonFactorFullFibre I' n₁ n₂ k := by
  subst h
  exact Equiv.refl _

theorem fibreCongr_fst {I I' : Ideal R} (h : I = I') (n₁ n₂ k : R)
    (p : commonFactorFullFibre I n₁ n₂ k) :
    (fibreCongr K S h n₁ n₂ k p).val.1 =
      Ideal.quotEquivOfEq (congrArg (fun J => commonFactorColumnIdeal J n₁) h) p.val.1 := by
  subst h
  change p.val.1 = _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective p.val.1
  rw [← ha, Ideal.quotEquivOfEq_mk]

theorem fibreCongr_snd {I I' : Ideal R} (h : I = I') (n₁ n₂ k : R)
    (p : commonFactorFullFibre I n₁ n₂ k) :
    (fibreCongr K S h n₁ n₂ k p).val.2 =
      Ideal.quotEquivOfEq (congrArg (fun J => commonFactorColumnIdeal J n₂) h) p.val.2 := by
  subst h
  change p.val.2 = _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective p.val.2
  rw [← ha, Ideal.quotEquivOfEq_mk]

/-- The original fibre is transported to the actual extended contraction,
not just to an ideal named as if it were the contraction. -/
def sIntegerSexticOriginalToReducedFibreEquiv (c n₁ n₂ : N) (k : R) :
    commonFactorFullFibre (⊤ : Ideal R) (c.val * n₁.val) (c.val * n₂.val) (c.val * k) ≃
      commonFactorFullFibre
        ((sIntegerModulusContraction K S c.val).map (algebraMap (𝓞 K) R))
        n₁.val n₂.val k :=
  (originalToReducedPrincipalFibreEquiv c.val n₁.val n₂.val k c.property).trans
    (fibreCongr K S (map_sIntegerModulusContraction K S c.val).symm n₁.val n₂.val k)

/-- On every representative, the original symbol weight equals the actual
product-denominator quotient weight at C=I_c. Shared factors are retained. -/
theorem sIntegerSexticOriginalColumnWeight_common_factor (c n : N) (x : R) :
    originalColumnWeight K S ζ hζ σ hS6
        ⟨c.val * n.val, mul_ne_zero c.property n.property⟩ (Ideal.Quotient.mk _ x) =
      sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6
        (sIntegerModulusContraction K S c.val)
        (sIntegerModulusContraction_ne_bot K S c.val c.property)
        (sIntegerSexticCommonFactor_exterior K S c) n (Ideal.Quotient.mk _ x) := by
  rw [originalColumnWeight_mk, sIntegerSexticReducedFullColumnFunction_mk]
  rw [sIntegerSexticCommonColumnEvaluation_eq K S ζ hζ σ hS6
    (sIntegerModulusContraction K S c.val)
    (sIntegerModulusContraction_ne_bot K S c.val c.property)
    (sIntegerSexticCommonFactor_exterior K S c)
    (fun p hp h => sIntegerSexticCommonFactor_exterior K S c p hp (hS6 h)) n x]
  rw [sIntegerSexticSymbol_mul_denominator K S ζ hζ σ hS6 x c n]
  rfl

/-- Explicit original-to-reduced equality of genuine sums. No common
factor is cancelled in the character: denominator multiplicativity
transports the full actual symbol, including every shared-prime zero. -/
theorem sIntegerSexticOriginalFullCorrelation_common_factor
    (c n₁ n₂ : N) (a b k : R) (hbezout : a * n₂.val - b * n₁.val = 1) :
    sIntegerSexticOriginalFullCorrelation K S ζ hζ σ hS6
        ⟨c.val * n₁.val, mul_ne_zero c.property n₁.property⟩
        ⟨c.val * n₂.val, mul_ne_zero c.property n₂.property⟩ (c.val * k) =
      sIntegerSexticReducedFullCorrelation K S ζ hζ σ hS6
        (sIntegerModulusContraction K S c.val)
        (sIntegerModulusContraction_ne_bot K S c.val c.property)
        (sIntegerSexticCommonFactor_exterior K S c) n₁ n₂ a b k hbezout := by
  let u : N := ⟨c.val * n₁.val, mul_ne_zero c.property n₁.property⟩
  let v : N := ⟨c.val * n₂.val, mul_ne_zero c.property n₂.property⟩
  let C := sIntegerModulusContraction K S c.val
  let hC := sIntegerModulusContraction_ne_bot K S c.val c.property
  let hCS := sIntegerSexticCommonFactor_exterior K S c
  let J := C.map (algebraMap (𝓞 K) R)
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
  letI reducedFullCorrelation_finite : Finite (R ⧸ J) :=
    finite_sIntegerSexticIdealQuotient K S C hC hCS
  letI reducedFullCorrelation_fintype : Fintype (R ⧸ J) := Fintype.ofFinite _
  letI reducedFullCorrelation_fibreFintype : Fintype (commonFactorFullFibre J n₁.val n₂.val k) :=
    Fintype.ofEquiv (R ⧸ J) (commonFactorFullFibreEquiv J n₁.val n₂.val a b k hbezout)
  let e := sIntegerSexticOriginalToReducedFibreEquiv K S c n₁ n₂ k
  letI originalFull_sourceFibreFintype :
      Fintype (commonFactorFullFibre (⊤ : Ideal R) u.val v.val (c.val * k)) :=
    Fintype.ofEquiv _ e.symm
  have key : ∀ p : commonFactorFullFibre (⊤ : Ideal R) u.val v.val (c.val * k),
      originalColumnWeight K S ζ hζ σ hS6 u p.val.1 *
        starRingEnd ℂ (originalColumnWeight K S ζ hζ σ hS6 v p.val.2) =
      sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₁ (e p).val.1 *
        starRingEnd ℂ (sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₂
          (e p).val.2) := by
    intro p
    rcases p with ⟨⟨x, y⟩, hp⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := sIntegerSexticOriginalColumnWeight_common_factor K S ζ hζ σ hS6 c n₁ x
    have hy := sIntegerSexticOriginalColumnWeight_common_factor K S ζ hζ σ hS6 c n₂ y
    have he := congrArg₂ (fun z w : ℂ => z * starRingEnd ℂ w) hx hy
    have hfst : (e ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩).val.1 =
        Ideal.Quotient.mk _ x := by
      have h1 := fibreCongr_fst K S (map_sIntegerModulusContraction K S c.val).symm n₁.val
        n₂.val k (originalToReducedPrincipalFibreEquiv c.val n₁.val n₂.val k c.property
          ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩)
      have h2 := originalToReducedPrincipalFibreEquiv_fst c.val n₁.val n₂.val k c.property
        ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩
      rw [h2, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk] at h1
      exact h1
    have hsnd : (e ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩).val.2 =
        Ideal.Quotient.mk _ y := by
      have h1 := fibreCongr_snd K S (map_sIntegerModulusContraction K S c.val).symm n₁.val
        n₂.val k (originalToReducedPrincipalFibreEquiv c.val n₁.val n₂.val k c.property
          ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩)
      have h2 := originalToReducedPrincipalFibreEquiv_snd c.val n₁.val n₂.val k c.property
        ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩
      rw [h2, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk] at h1
      exact h1
    exact he.trans (congrArg₂ (fun z w =>
      sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₁ z *
        starRingEnd ℂ (sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₂ w))
      hfst.symm hsnd.symm)
  unfold sIntegerSexticOriginalFullCorrelation sIntegerSexticReducedFullCorrelation
  dsimp only
  convert Fintype.sum_equiv e
    (fun p : commonFactorFullFibre (⊤ : Ideal R) u.val v.val (c.val * k) =>
      originalColumnWeight K S ζ hζ σ hS6 u p.val.1 *
        starRingEnd ℂ (originalColumnWeight K S ζ hζ σ hS6 v p.val.2))
    (fun q : commonFactorFullFibre J n₁.val n₂.val k =>
      sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₁ q.val.1 *
        starRingEnd ℂ (sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₂ q.val.2))
    key
end HeckeGeneral.Characters
