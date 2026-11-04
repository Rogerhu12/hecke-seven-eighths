module

public import Mathlib

/-!
# Challenge: unitary Hecke L-functions have no zeros in Re(s) > 7/8

The statement of Theorem 1.2 ("Hecke analytic core") of the paper
`paper/weil_seven_eighths_revised.tex`, written with Mathlib notions only.

* A unitary Hecke character of a number field `K` is a continuous homomorphism from
  Mathlib's idèle class group `IdeleClassGroup (𝓞 K) K` to the unit circle. Characters
  of infinite order are included.
* At a finite place `v` where `χ` is unramified (trivial on the local integral units),
  `χ(𝔭_v)` is the value of `χ` on a uniformizer of the completion `K_v`; at ramified
  places it is `0`. The coefficient of a nonzero integral ideal is the product of these
  values over its prime factorization, and the coefficient of the zero ideal is `0`.
* The theorem asserts that the Dirichlet series `∑ χ(I) N(I)^(-s)` over integral ideals
  has an analytic continuation to `ℂ`, except for at most one pole, which is simple and lies
  on the line `Re(s) = 1`, and that the continuation has no zeros in `Re(s) > 7/8`.

Requiring the pole to be genuine (a nonzero residue) keeps a zero from being hidden
behind the exceptional point. The paper's further statement that a pole occurs only for
the norm characters `‖·‖^{it}`, and its form for unitary Weil representations
(Theorem 1.1), are not part of this challenge.
-/

@[expose] public section

namespace HeckeSevenEighths

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open scoped Classical

/-- A unitary Hecke character of `K`: a continuous homomorphism from the idèle class group
to the unit circle. -/
abbrev HeckeCharacter (K : Type) [Field K] [NumberField K] :=
  IdeleClassGroup (𝓞 K) K →ₜ* Circle

variable {K : Type} [Field K] [NumberField K]

/-- `χ` is unramified at the finite place `v`: it is trivial on the units of the ring of
integers of the completion `K_v`. -/
def IsUnramifiedAt (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ u ∈ (v.adicCompletionIntegers K).units,
    χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) = 1

/-- `χ(𝔭_v)`: the value of `χ` on a uniformizer of `K_v` if `χ` is unramified at `v`,
and `0` otherwise. When `χ` is unramified the value does not depend on the uniformizer. -/
def primeValue (χ : HeckeCharacter K) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if h : IsUnramifiedAt χ v ∧
      ∃ ϖ : (v.adicCompletion K)ˣ, Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) then
    (χ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v (Classical.choose h.2)) : ℂ)
  else 0

/-- The coefficient `χ(I)` of an integral ideal: the product of `χ(𝔭)` over the prime
factorization of `I`, and `0` for the zero ideal. -/
def coeff (χ : HeckeCharacter K) (I : Ideal (𝓞 K)) : ℂ :=
  if I = ⊥ then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
      if h : P.IsPrime ∧ P ≠ ⊥ then primeValue χ ⟨P, h.1, h.2⟩ else 0).prod

/-- **Theorem 1.2.** The Hecke L-function of every unitary Hecke character of every number
field continues to `ℂ` with at most one pole, which is simple and lies on `Re(s) = 1`,
and it has no zeros in `Re(s) > 7/8`. -/
theorem heckeL_zeroFree (K : Type) [Field K] [NumberField K] (χ : HeckeCharacter K) :
    ∃ f : ℂ → ℂ, ∃ P : Set ℂ, P.Subsingleton ∧
      DifferentiableOn ℂ f Pᶜ ∧
      (∀ p ∈ P, p.re = 1 ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ g p ≠ 0 ∧
        ∀ᶠ s in 𝓝[≠] p, f s = g s / (s - p)) ∧
      (∀ s : ℂ, 1 < s.re →
        HasSum (fun I : Ideal (𝓞 K) => coeff χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s : ℂ, 7 / 8 < s.re → s ∉ P → f s ≠ 0 := by
  sorry

end

end HeckeSevenEighths
