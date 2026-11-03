import HeckePort.Moments.CommonSupport
import HeckePort.CenteredMoment.Mask

/-!
# Correlations of supported modulus characters

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/SupportedCorrelation.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to a commutative ring `A` (and `𝓞 K` for the Möbius form).

In openai the characters are `supportedModulusCharacter d hd : MulChar (A ⧸ span {d}) ℂ`,
`x ↦ idealRowHom x (span {d})` (the sextic residue symbol of `x` modulo the supported `d`), and
the reciprocity phase is `sexticReciprocityPhase a b`.  The facts about them used by the file are
the following, which become hypotheses on an abstract family `χ d : MulChar (A ⧸ span {d}) ℂ`
and an abstract phase `φ : A → A → ℂ`:

* `hmul`: `χ (d * a)` restricted to residues is the product `χ d * χ a`
  (openai `supportedModulusCharacter_mul`);
* `hrecip`: for coprime `a b`, `χ b a * star (χ a b) = φ a b` (openai `supported_opposite_phase`,
  from `idealRowHom_primary_reciprocity`; the sextic reciprocity law);
* `hsymm`, `hreal`: `φ a b = φ b a` and `star (φ a b) = φ a b`
  (`sexticReciprocityPhase_symm`, `star_sexticReciprocityPhase`).

Ported from there: `supportedCorrelation`, `supported_complete_common_support` and the
Möbius form `complete_support_mobius` (for `A = 𝓞 K`, where the supported ideals are principal
ideals).  Not ported: the construction of `supportedModulusCharacter` itself,
`supported_mul_elements`, `actualCorrelation` (finite quotients of `ℤ[ω]`).
-/

noncomputable section

namespace HeckePort.Moments.SupportedCorrelation

open scoped BigOperators Classical
open HeckePort.Moments HeckePort.Moments.CommonSupport

section Abstract

variable {A : Type*} [CommRing A]

/-- A family of residue characters with reciprocity phase. -/
structure CharFamily (A : Type*) [CommRing A] where
  χ : ∀ d : A, MulChar (A ⧸ Ideal.span {d}) ℂ
  φ : A → A → ℂ
  hmul : ∀ d a x : A, χ (d * a) (Ideal.Quotient.mk _ x) =
    χ d (Ideal.Quotient.mk _ x) * χ a (Ideal.Quotient.mk _ x)
  hrecip : ∀ a b : A, IsCoprime a b →
    χ b (Ideal.Quotient.mk _ a) * star (χ a (Ideal.Quotient.mk _ b)) = φ a b
  hsymm : ∀ a b, φ a b = φ b a
  hreal : ∀ a b, star (φ a b) = φ a b

def supportedCorrelation (F : CharFamily A) (u v : A)
    [Fintype (Residue u)] [Fintype (Residue v)] (j : A) : ℂ :=
  fullModulusCorrelation u v (F.χ u) (F.χ v) j

theorem supported_complete_common_support (F : CharFamily A) (D E a b : A)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))] (j : A) :
    supportedCorrelation F (D * a) (E * b) j =
      supportedCorrelation F D E j * F.φ a E *
        star (F.φ b D) * F.φ a b *
        F.χ a (Ideal.Quotient.mk _ j) * star (F.χ b (Ideal.Quotient.mk _ (-j))) := by
  unfold supportedCorrelation
  rw [fullModulusCorrelation_complete_support D E a b hcopA hcopB hab
    (F.χ D) (F.χ E) (F.χ a) (F.χ b) (F.χ (D * a)) (F.χ (E * b))
    (F.hmul D a) (F.hmul E b) j]
  have h1 := F.hrecip a E (IsCoprime.mul_left_iff.mp hcopA).2.symm
  have h2 := F.hrecip D b (IsCoprime.mul_left_iff.mp hcopB).1
  have h3 := F.hrecip a b hab
  rw [h1, h2, h3, F.hsymm D b, F.hreal]

end Abstract

section Mobius

open scoped NumberField
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve

variable {K : Type*} [Field K] [NumberField K]

/-- openai `actual_complete_support_mobius`, for a character family on `𝓞 K` (hypothesis
`hext`: the common-support formula for the coprime case). -/
theorem complete_support_mobius (a b : 𝓞 K) (hb : Ideal.span {b} ≠ ⊥)
    (Corr Ext : ℂ) (hext : IsCoprime a b → Corr = Ext) :
    (if IsCoprime a b then Corr else 0) =
      Ext * ∑ T ∈ idealDivisors (Ideal.span {b}),
        if T ∣ Ideal.span {a} then (moebius T : ℂ) else 0 := by
  rw [← HeckePort.CenteredMomentMask.ideal_coprime_mobius (Ideal.span {a}) (Ideal.span {b}) hb,
    Ideal.isCoprime_span_singleton_iff]
  by_cases hab : IsCoprime a b
  · simp only [hab, if_true, mul_one]
    exact hext hab
  · simp only [hab, if_false, mul_zero]

end Mobius

end HeckePort.Moments.SupportedCorrelation

end
