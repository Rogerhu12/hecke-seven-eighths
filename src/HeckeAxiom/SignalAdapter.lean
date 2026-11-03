import HeckeAxiom.ArithmeticChoice
import HeckeGeneral.Characters.Unramified
import HeckeGeneral.Characters.Packet

/-!
# The Gauss correction characters as the skeleton's signal characters

Axiom's idele class group of `SArithmeticData` is Mathlib's
`NumberField.IdeleClassGroup`, the same group on which the skeleton's Hecke
characters live. So the continuous correction characters `Λ` and `G` of an
arithmetic choice are actual unitary Hecke characters, and the context's own
finite-order and unramifiedness statements become the skeleton's
`FiniteOrder` and `UnramifiedAt` outside the chosen finite set.

The local components agree definitionally: both libraries embed a local unit
at `v` into the ideles with Mathlib's `ofAdicCompletion` and then pass to the
class group. Norm one and valuation one agree on the completion.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

/-- A continuous Axiom idele class character, as a unitary Hecke character. -/
def toHeckeCharacter (Φ : A.ArithmeticIdeleClasses →* Circle) (hΦ : Continuous Φ) :
    HeckeCharacter F :=
  { toMonoidHom := Φ, continuous_toFun := hΦ }

@[simp] theorem toHeckeCharacter_apply (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hΦ : Continuous Φ) (x : NumberField.IdeleClassGroup (𝓞 F) F) :
    toHeckeCharacter A Φ hΦ x = Φ x := rfl

theorem finiteOrder_toHeckeCharacter (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hΦ : Continuous Φ) (h : A.IdeleCharacterHasFiniteOrder Φ) :
    FiniteOrder (toHeckeCharacter A Φ hΦ) := by
  obtain ⟨n, hn, hpow⟩ := h
  refine (finiteOrder_iff _).mpr ⟨n, hn, ?_⟩
  ext x
  simpa using congrArg (fun z : Circle => (z : ℂ)) (hpow x)

theorem unramifiedAt_toHeckeCharacter (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hΦ : Continuous Φ) (h : A.IdeleCharacterUnramifiedOutside Φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    UnramifiedAt F (toHeckeCharacter A Φ hΦ) v := by
  intro u hu
  have hval : Valued.v (u : v.adicCompletion F) = 1 :=
    (Valued.toNormedField.norm_eq_one_iff (L := v.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mp hu
  exact h v (fun hmem => hv (Finset.mem_coe.mpr hmem)) u hval

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {σ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 σ)

/-- The correction character `Λ` of the choice. -/
def Lambda : HeckeCharacter F :=
  toHeckeCharacter X.A X.C.correction.Λ X.C.correction.Λ_continuous

/-- The finite-order correction character `G` of the choice. -/
def G : HeckeCharacter F :=
  toHeckeCharacter X.A X.C.correction.G X.C.correction.G_continuous

theorem G_finiteOrder : FiniteOrder X.G :=
  finiteOrder_toHeckeCharacter X.A _ _ X.C.correction.G_finiteOrder

theorem Lambda_unramified (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ (X.places : Set (HeightOneSpectrum (𝓞 F)))) : UnramifiedAt F X.Lambda p :=
  unramifiedAt_toHeckeCharacter X.A _ _ X.C.correction.Λ_unramified p hp

theorem G_unramified (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ (X.places : Set (HeightOneSpectrum (𝓞 F)))) : UnramifiedAt F X.G p :=
  unramifiedAt_toHeckeCharacter X.A _ _ X.C.correction.G_unramified p hp

end ArithmeticChoice

end HeckeAxiom
