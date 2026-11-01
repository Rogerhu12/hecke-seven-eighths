import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralInactiveRectangle
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScaleProduct
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCentralCoefficientBound

/-!
# Original scale products on the actual active rectangle

The centered product identity follows from the original engine domain.
The ordinary comparison scales need not satisfy it: their literal
rectangle is absent. These lemmas expose the exact original scale
identities needed after that same source activity test, without
changing the source or imposing a condition on an unused comparison.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)

include domain

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

/-- This is the conditional original comparison identity consumed by
the actual-family active coefficient theorem. -/
theorem literalOriginalAtoms_comparison_product
    (hc : (seed).centered = true) :
    (seed).scale₁ true * (seed).scale₂ true = (seed).scale₁ false * (seed).scale₂ false := by
  change Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂
  rw [domain.comparison_product_eq_power hc, Real.rpow_add (zero_lt_one.trans hZ)]

/-- The activity predicate of the unchanged source supplies precisely
this alternative. Both valid cases retain the same original product. -/
theorem literalOriginalAtoms_plain_product_of_domain (r : Bool)
    (hr : r = false ∨ centered = true) :
    (seed).scale₁ r * (seed).scale₂ r = (seed).scale₁ false * (seed).scale₂ false := by
  rcases hr with hr | hc
  · rw [hr]
  · cases r with
    | false => rfl
    | true => exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
        centered hZ hY₁ hY₂ domain hc

/-- The sharp original degree is used only for a present rectangle.
No relation between ordinary unused comparison scales is required. -/
theorem literalOriginalAtoms_scaleProduct_of_domain (r : Bool)
    (hr : r = false ∨ centered = true) :
    (seed).scaleProduct r = Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  have hp := Q.literalOriginalAtoms_plain_product_of_domain ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ domain r hr
  change (seed).scale₁ r * (seed).scale₂ r * ∏ i, (seed).base ^ (seed).length i = _
  rw [hp]
  simp only [literalOriginalAtoms, Bool.false_eq_true, if_false,
    SlotGeometry.totalLength, Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]

/-- The first extraction's original norm window for the same present
rectangle. The ideal is the literal product of every frozen occurrence;
the direct/main/pool atlas identities identify it with their displayed
first common ideal, including the original pool prime power. -/
theorem literalOriginalAtoms_firstScale_of_domain
    {support : Finset (Ideal (𝓞 K))}
    (branch : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {bound : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) bound)
    (annulus : ℝ) (hannulus : 1 ≤ annulus) (ht : t ∈ heightDomain)
    (hwindow : ∀ x ∈ window, x ≤ annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap) (r : Bool)
    (hr : r = false ∨ centered = true) :
    ((seed).extract branch).scaleProduct r *
        (Ideal.absNorm (frozenSourceIdeal branch.plainDivisor₁ branch.plainDivisor₂
          branch.keep branch.witness.2) : ℝ) ≤
      annulus ^ cap * Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  have hp := Q.literalOriginalAtoms_primeNormWindow ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ profiles annulus ht hwindow
  have he := (seed).extract_scaleProduct_mul_frozenNorm_le hp hannulus cap hcap branch r
  rw [Q.literalOriginalAtoms_scaleProduct_of_domain ξ W a Z t Y₁ Y₂
    centered hZ hY₁ hY₂ domain r hr] at he
  exact he

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_comparison_product
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_scaleProduct_of_domain
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_firstScale_of_domain
