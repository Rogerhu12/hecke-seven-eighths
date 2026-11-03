import HeckePort.Moments.PrimePower
import HeckePort.Moments.CRT
import HeckeGeneral.Characters.SexticResidueCharacter

/-!
# Canonical prime-power and CRT rows

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Canonical.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai fixes the sextic residue character `actualSextic P hg` of `ℤ[ω]` at a prime `P` prime to
`λ = goodLambda`.  Over a general number field the corresponding object is the sextic residue
character of the skeleton (`HeckeGeneral.Characters.sexticResidueCharacter`, for a height-one
prime `p` with `6 ∉ p`).  The statements are proved for an *arbitrary* family of characters
`χ P : MulChar (𝓞 K ⧸ P) ℂ` of order six (the order hypothesis replaces
`actualSextic_order_six`, which is `HeckeGeneral.Characters.sexticResidueCharacter_order` for
the skeleton's character; see `sexticResidue_primePower_units`).

Not ported: `canonicalPrimePowerCharacter_mk` and `canonicalCRTCharacter_mk`.  They identify the
character with `CanonicalRowCompletion.idealRowHom`, the ideal-level row hom of
`RowCompletion/ThetaNonvanishing.lean`, which is not part of S0.  `IdealGaussCRT.quotientProdEquivPi`
(`Poisson/EisensteinLattice.lean`) is re-proved here (it is Mathlib's CRT equivalence).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open HeckeGeneral.Characters IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The Chinese remainder equivalence for a finite product of pairwise coprime ideals. -/
theorem finite_prod_eq_iInf {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (∏ i, P i) = ⨅ i, P i := by
  simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime
    (s := Finset.univ) (J := P) (by
      intro i _ j _ hij
      exact hc hij))

noncomputable def quotientProdEquivPi {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P)) :
    (A ⧸ ∏ i, P i) ≃+* ∀ i, A ⧸ P i :=
  (Ideal.quotEquivOfEq (finite_prod_eq_iInf P hc)).trans
    (Ideal.quotientInfRingEquivPiQuotient P hc)

@[simp] theorem quotientProdEquivPi_mk {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    (a : A) (i : ι) :
    quotientProdEquivPi P hc (Ideal.Quotient.mk (∏ j, P j) a) i =
      Ideal.Quotient.mk (P i) a := by
  simp only [quotientProdEquivPi, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

section Row

variable (χ : ∀ P : Ideal (𝓞 K), MulChar (𝓞 K ⧸ P) ℂ)

/-- openai `primePowerRow`: the character `χ P ^ c` pulled back to `𝓞 K ⧸ P ^ c`. -/
def primePowerRow (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
    (x : 𝓞 K ⧸ P ^ c) : ℂ :=
  (χ P ^ c) (primePowerReduction P hc x)

variable (P : Ideal (𝓞 K)) [P.IsMaximal]

theorem canonical_primePower_units (hχ : orderOf (χ P) = 6)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (primePowerRow χ P hc) (primePowerRow χ P hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      χ P (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units P hc (χ P) hχ u v k hv

theorem canonical_primePower_second_zero (hχ : orderOf (χ P) = 6)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (primePowerRow χ P hc) (primePowerRow χ P hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_second_zero P hc (χ P) hχ u v k hv

theorem canonical_primePower_first_zero (hχ : orderOf (χ P) = 6)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
    (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ) (k : 𝓞 K ⧸ P ^ c)
    (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (primePowerRow χ P hc) (primePowerRow χ P hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_first_zero P hc (χ P) hχ u v k hu

/-- openai `canonicalPrimePowerCharacter`. -/
def canonicalPrimePowerCharacter {c : ℕ} (hc : 1 ≤ c) : MulChar (𝓞 K ⧸ P ^ c) ℂ :=
  primePowerCharacter P hc (χ P ^ c)

end Row

private theorem pairwise_isCoprime_pow {ι : Type*}
    (P : ι → Ideal (𝓞 K)) (c : ι → ℕ)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
  intro i j hij
  exact (hcop hij).pow

/-- openai `canonicalCRTCharacter`. -/
def canonicalCRTCharacter (χ : ∀ P : Ideal (𝓞 K), MulChar (𝓞 K ⧸ P) ℂ) {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) [∀ i, (P i).IsMaximal]
    (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (𝓞 K ⧸ ∏ i, P i ^ c i) ℂ :=
  crtCharacter (quotientProdEquivPi (fun i => P i ^ c i)
    (pairwise_isCoprime_pow P c hcop))
    (fun i => canonicalPrimePowerCharacter χ (P i) (hc i))

theorem canonicalCRTCorrelation (χ : ∀ P : Ideal (𝓞 K), MulChar (𝓞 K ⧸ P) ℂ)
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal (𝓞 K)) [∀ i, (P i).IsMaximal]
    (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (𝓞 K ⧸ ∏ i, P i ^ c i)] [∀ i, Fintype (𝓞 K ⧸ P i ^ c i)]
    (u v k : 𝓞 K ⧸ ∏ i, P i ^ c i) :
    let e := quotientProdEquivPi (fun i => P i ^ c i)
      (pairwise_isCoprime_pow P c hcop)
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (canonicalCRTCharacter χ P c hc hcop) (canonicalCRTCharacter χ P c hc hcop) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (primePowerRow χ (P i) (hc i)) (primePowerRow χ (P i) (hc i))
        (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, primePowerRow χ (P i) (hc i)
      (quotientProdEquivPi _ _ x i))
    (fun x => ∏ i, primePowerRow χ (P i) (hc i)
      (quotientProdEquivPi _ _ x i)) k = _
  rw [fullCorrelation_ringEquiv (quotientProdEquivPi _ _) u v k
    (fun x => ∏ i, primePowerRow χ (P i) (hc i) (x i))
    (fun x => ∏ i, primePowerRow χ (P i) (hc i) (x i)), fullCorrelation_pi]

/-- The skeleton's sextic residue character satisfies the hypotheses of the canonical
correlation formulas: this is the instance of `canonical_primePower_units` that replaces
openai's `actualSextic`. -/
theorem sexticResidue_primePower_units (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
    (p : HeightOneSpectrum (𝓞 K)) (hp : (6 : 𝓞 K) ∉ p.asIdeal)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (𝓞 K ⧸ p.asIdeal ^ c)] [Fintype (𝓞 K ⧸ p.asIdeal)]
    (u : (𝓞 K ⧸ p.asIdeal ^ c)ˣ) (v k : 𝓞 K ⧸ p.asIdeal ^ c)
    (hv : primePowerReduction p.asIdeal hc v ≠ 0) :
    letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ p.asIdeal ^ c) * y)
      (fun x => (sexticResidueCharacter K ζ hζ σ p hp ^ c) (primePowerReduction p.asIdeal hc x))
      (fun x => (sexticResidueCharacter K ζ hζ σ p hp ^ c) (primePowerReduction p.asIdeal hc x))
      k =
    (Ideal.absNorm p.asIdeal : ℂ) ^ (c - 1) *
      sexticResidueCharacter K ζ hζ σ p hp
        (primePowerReduction p.asIdeal hc u / primePowerReduction p.asIdeal hc v) ^ c *
      (if primePowerReduction p.asIdeal hc k = 0 then (Ideal.absNorm p.asIdeal : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm p.asIdeal : ℂ) - 2 else -1) := by
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  exact primePower_localCorrelation_units p.asIdeal hc _
    (sexticResidueCharacter_order K ζ hζ σ p hp) u v k hv

end HeckePort.Moments

end
