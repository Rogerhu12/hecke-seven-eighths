import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileFactorExtraction

set_option linter.unusedSectionVars false

/-!
# Frozen prime costs after extracting the complete profile factor

Dividing a transformed occurrence by its original positive scale
factor leaves `φ(y) * y^(-1 + δ₁ + δ₂)`, where `y` is the same original
prime-norm ratio.  Its actual annulus-weighted square is therefore
`y^(-1 + 2*(δ₁+δ₂)) * ‖φ(y)‖²`.  The original open prime window gives
`1 < y` whenever that occurrence is nonzero.

The bound remains the original squared profile bound.  The complete
residual factor is paid in the row scalar, not inserted into an atom
budget or lost when the actual source table is redistributed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFactorFreeAtomCosts

/-- Cancellation uses the original occurrence scale, before any
second common or allocation divisor is extracted. -/
theorem transform_divide_factor (N np δ₁ δ₂ : ℝ)
    (hN : 0 < N) (hp : 0 < np) (z : ℂ) :
    ((((z * (Real.sqrt N : ℂ)) * (np ^ (-1 : ℝ) : ℂ)) *
        (np ^ δ₁ : ℂ)) * (np ^ δ₂ : ℂ)) *
        (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ)⁻¹ =
      z * ((np / N) ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ) := by
  sorry

theorem weighted_power_norm_sq (y δ₁ δ₂ : ℝ) (hy : 0 < y) (z : ℂ) :
    y * ‖z * (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)‖ ^ 2 =
      y ^ (-1 + 2 * (δ₁ + δ₂)) * ‖z‖ ^ 2 := by
  sorry

end CanonicalLiteralFactorFreeAtomCosts

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem redistributedSecondInput_primeAtomCost_eq
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p =
      ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length (SlotRestriction.index b.keep i)) ^
          (-1 + 2 * (δ₁ + δ₂)) * ‖d.slotWeight (SlotRestriction.index b.keep i) p‖ ^ 2 := by
  sorry

/-- Only the original occurrence being nonzero is needed for its
scale lower bound.  The zero branch is handled exactly. -/
theorem redistributedSecondInput_primeAtomCost_le
    (hδ : δ₁ + δ₂ ≤ 1 / 2) (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K))
    (hscale : d.slotWeight (SlotRestriction.index b.keep i) p ≠ 0 →
      d.base ^ d.length (SlotRestriction.index b.keep i) ≤ (Ideal.absNorm p.asIdeal : ℝ)) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤
      ‖d.slotWeight (SlotRestriction.index b.keep i) p‖ ^ 2 := by
  sorry

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

/-- Every actual frozen or common prime in the redistributed table
is paid from the original parent window, with no completed-table
estimate supplied by the caller. -/
theorem literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    ((seed).redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤ B ^ 2 := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFactorFreeAtomCosts.transform_divide_factor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFactorFreeAtomCosts.weighted_power_norm_sq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributedSecondInput_primeAtomCost_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le
