import Mathlib
import HeckeGeneral.Bridge.ChallengeCoefficients
import HeckeGeneral.Analysis.ChallengeContinuation
import HeckeSkeleton.Main

/-!
# Solution: unitary Hecke L-functions have no zeros in Re(s) > 7/8

The four definitions below are copied verbatim from the independent Challenge.
The coefficient and analytic bridges live in HeckeGeneral. This module does not
import the Challenge; the comparator checks their declarations independently.
-/

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
  classical
  have hp (v : HeightOneSpectrum (𝓞 K)) :
      primeValue χ v = HeckeGeneral.Characters.primeCoefficient K χ v := by
    unfold primeValue
    exact HeckeGeneral.Bridge.primeValue_eq_primeCoefficient
      K χ v (IsUnramifiedAt χ v)
      (HeckeGeneral.Bridge.unramifiedAt_iff_integral_units_ofAdicCompletion K χ v)
  have hc (I : Ideal (𝓞 K)) :
      coeff χ I = HeckeGeneral.Arithmetic.idealCoefficient
        (HeckeGeneral.Characters.primeCoefficient K χ) I := by
    unfold coeff
    simp_rw [hp]
    exact HeckeGeneral.Bridge.normalizedFactors_coefficient_eq
      K (HeckeGeneral.Characters.primeCoefficient K χ) I
  obtain ⟨f, P, hP, hf, hpole, hseries, hzero⟩ :=
    HeckeGeneral.Analysis.exists_challengeContinuation K χ
      (HeckeSkeleton.generalHeckeSevenEighths_skeleton K χ)
  refine ⟨f, P, hP, hf, hpole, ?_, hzero⟩
  intro s hs
  rw [hseries s hs]
  simp_rw [hc]
  exact HeckeGeneral.Bridge.hasSum_heckeIdealCoefficient_all K χ hs

end

end HeckeSevenEighths
