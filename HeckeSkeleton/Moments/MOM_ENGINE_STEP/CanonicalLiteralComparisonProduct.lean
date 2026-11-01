import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralNormFactorTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveOriginalScale

/-!
# Original comparison products through the actual atom operations

The comparison product is required only for a centered original source.
The two plain divisors act on both rectangles with the same denominators,
and the atlas and deletion operations leave their scales unchanged.
These lemmas let the six actual constructors supply the redistribution
identity directly from the original engine domain.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : Atoms (K := K) k)

theorem comparison_product_extract
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (h : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false) :
    (d.extract b).centered = true →
      (d.extract b).scale₁ true * (d.extract b).scale₂ true =
        (d.extract b).scale₁ false * (d.extract b).scale₂ false := by
  intro hc
  change (d.scale₁ true / idealNorm K b.plainDivisor₁) *
      (d.scale₂ true / idealNorm K b.plainDivisor₂) =
    (d.scale₁ false / idealNorm K b.plainDivisor₁) *
      (d.scale₂ false / idealNorm K b.plainDivisor₂)
  rw [div_mul_div_comm, div_mul_div_comm, h hc]

theorem comparison_product_onAtlas {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (h : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false) :
    (d.onAtlas T count).centered = true →
      (d.onAtlas T count).scale₁ true * (d.onAtlas T count).scale₂ true =
        (d.onAtlas T count).scale₁ false * (d.onAtlas T count).scale₂ false := by
  cases count
  exact h

theorem comparison_product_deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (h : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false) :
    (d.deleteMask M).centered = true →
      (d.deleteMask M).scale₁ true * (d.deleteMask M).scale₂ true =
        (d.deleteMask M).scale₁ false * (d.deleteMask M).scale₂ false := h

section SecondInput

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem comparison_product_secondInput
    (h : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).centered = true →
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale₁ true *
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale₂ true =
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale₁ false *
      (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale₂ false :=
  d.comparison_product_extract b h

end SecondInput
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.comparison_product_extract
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
