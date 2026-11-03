import FiniteCommonFactorFibre
import SIntegerSexticCorrelationWeight
import SIntegerSexticFiniteCorrelation

/-! SOURCE ONLY, UNRUN. Genuine sum over the reduced full-congruence
fibre, with actual product-denominator quotient characters. The relation
is n2*x-n1*y=k modulo C*(n1)*(n2). This is not yet named the original
F(c*n1,c*n2;c*k): that requires the separate nonzero-c cancellation
transport from its original modulus (c^2*n1*n2). Frequency zero is allowed. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
variable (C : Ideal (𝓞 K)) (hC : C ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hC6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → (6 : 𝓞 K) ∉ p.asIdeal)
local notation "R" => S.integer K
local notation "J" => C.map (algebraMap (𝓞 K) R)
local notation "Q" => R ⧸ J
local notation "N" => NonzeroRingElements R
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ C hC hCS hC6
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6

private theorem reducedFullColumn_exterior (n : N)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal ∣ sIntegerModulusContraction K S n.val) : p ∉ S := by
  intro hpS
  have hc := sIntegerModulusContraction_coprime K S n.val n.property p hpS
  rw [sup_eq_right.mpr (Ideal.dvd_iff_le.mp hp)] at hc
  exact p.isPrime.ne_top hc

/-- Actual quotient character for C*I_n, transported along the proved
equality of its extended ideal with J*(n). -/
def sIntegerSexticReducedFullColumnFunction (n : N)
    (q : R ⧸ commonFactorColumnIdeal J n.val) : ℂ := by
  let I := C * sIntegerModulusContraction K S n.val
  have hI : I ≠ 0 := mul_ne_zero hC
    (sIntegerModulusContraction_ne_bot K S n.val n.property)
  have hS (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) : p ∉ S :=
    (p.prime.dvd_mul.mp hp).elim (hCS p) (reducedFullColumn_exterior K S n p)
  have h6 (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) :
      (6 : 𝓞 K) ∉ p.asIdeal := fun h => hS p hp (hS6 h)
  have he : I.map (algebraMap (𝓞 K) R) = commonFactorColumnIdeal J n.val := by
    dsimp [I, commonFactorColumnIdeal]
    rw [Ideal.map_mul, map_sIntegerModulusContraction]
  exact sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6
    (Ideal.quotEquivOfEq he.symm q)

@[simp] theorem sIntegerSexticReducedFullColumnFunction_mk (n : N) (x : R) :
    sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n
        (Ideal.Quotient.mk _ x) =
      sIntegerSexticCommonColumnEvaluation K S ζ hζ σ hS6 C hC hCS n x := by
  simp only [sIntegerSexticReducedFullColumnFunction, Ideal.quotEquivOfEq_mk,
    sIntegerSexticIdealQuotientFunction_mk]
  rfl

/-- This is a sum over the actual reduced full fibre, rather than a
definition as a product of a proposed raw factor and L_C. -/
def sIntegerSexticReducedFullCorrelation (n₁ n₂ : N) (a b k : R)
    (hbezout : a * n₂.val - b * n₁.val = 1) : ℂ := by
  letI reducedFullCorrelation_finite : Finite Q :=
    finite_sIntegerSexticIdealQuotient K S C hC hCS
  letI reducedFullCorrelation_fintype : Fintype Q := Fintype.ofFinite Q
  letI reducedFullCorrelation_fibreFintype :
      Fintype (commonFactorFullFibre J n₁.val n₂.val k) :=
    Fintype.ofEquiv Q (commonFactorFullFibreEquiv J n₁.val n₂.val a b k hbezout)
  exact ∑ p : commonFactorFullFibre J n₁.val n₂.val k,
    sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₁ p.val.1 *
      starRingEnd ℂ (sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₂ p.val.2)

/-- Exact reduced full-correlation lift, including k=0 and all frequency
zero masks, with the genuine affine congruence sum as the final factor. -/
theorem sIntegerSexticReducedFullCorrelation_eq
    (n₁ n₂ : N) (a b k : R) (hbezout : a * n₂.val - b * n₁.val = 1)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S n₁.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S n₂.val)) :
    sIntegerSexticReducedFullCorrelation K S ζ hζ σ hS6 C hC hCS n₁ n₂ a b k hbezout =
      (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ *
        sIntegerSexticFiniteCorrelation K S ζ hζ σ C hC hCS hC6
          (Ideal.Quotient.mk J n₁.val) (Ideal.Quotient.mk J n₂.val) (Ideal.Quotient.mk J k) := by
  letI reducedFullCorrelation_finite : Finite Q :=
    finite_sIntegerSexticIdealQuotient K S C hC hCS
  letI reducedFullCorrelation_fintype : Fintype Q := Fintype.ofFinite Q
  letI reducedFullCorrelation_fibreFintype :
      Fintype (commonFactorFullFibre J n₁.val n₂.val k) :=
    Fintype.ofEquiv Q (commonFactorFullFibreEquiv J n₁.val n₂.val a b k hbezout)
  let e := commonFactorFullToAffineFibreEquiv J n₁.val n₂.val a b k hbezout
  let A := (χ k n₁ * starRingEnd ℂ (χ (-k) n₂)) *
    sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂
  let f := fun p : {p : Q × Q //
      Ideal.Quotient.mk J n₂.val * p.1 - Ideal.Quotient.mk J n₁.val * p.2 =
        Ideal.Quotient.mk J k} => Φ p.val.1 * starRingEnd ℂ (Φ p.val.2)
  have hw (p : commonFactorFullFibre J n₁.val n₂.val k) :
      sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₁ p.val.1 *
          starRingEnd ℂ (sIntegerSexticReducedFullColumnFunction K S ζ hζ σ hS6 C hC hCS n₂ p.val.2) =
        A * f (e p) := by
    rcases p with ⟨⟨x, y⟩, hp⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hc := commonFactorFullFibre_residual_congruences J n₁.val n₂.val k x y hp
    have hw := sIntegerSexticCorrelation_product_denominator_weight K S ζ hζ σ hS6
      C hC hCS hC6 n₁ n₂ k x y hab hc.1 hc.2
    have h1 := commonFactorFullToAffineFibreEquiv_fst J n₁.val n₂.val a b k hbezout
      ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩
    have h2 := commonFactorFullToAffineFibreEquiv_snd J n₁.val n₂.val a b k hbezout
      ⟨(Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y), hp⟩
    simp only [commonFactorReduce_mk] at h1 h2
    simp only [A, f, e, sIntegerSexticReducedFullColumnFunction_mk, h1, h2,
      sIntegerSexticIdealQuotientFunction_mk]
    exact hw
  change (∑ p : commonFactorFullFibre J n₁.val n₂.val k, _) = A * _
  calc
    _ = ∑ p : commonFactorFullFibre J n₁.val n₂.val k, A * f (e p) :=
      Finset.sum_congr rfl (fun p _ => hw p)
    _ = A * ∑ p : commonFactorFullFibre J n₁.val n₂.val k, f (e p) :=
      (Finset.mul_sum _ _ _).symm
    _ = A * ∑ p, f p := congrArg (fun z => A * z)
      (Fintype.sum_equiv e _ _ (fun _ => rfl))
    _ = _ := by
      rw [sIntegerSexticFiniteCorrelation, affineCorrelation_eq_sum_fibre]
end HeckeGeneral.Characters
