import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstTerminalWindows

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Original ideal windows for the actual first normalization

The two common ideals, their active radical and the selected physical
mask divisor are bounded by the original full Cartesian columns. These
bounds apply before second-stage rows or coefficients are inspected.
The pool frozen ideal includes its full original valuation power.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => (atoms).raw Y₁ Y₂

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

/-- Every first arithmetic length is derived from a norm window on
the same original columns. The physical mask divisor is not discarded. -/
theorem literalPrimitiveFirstIdealLengths
    (normBound : ℝ)
    (hN : ∀ i ∈ (source).columns, (Ideal.absNorm ((source).ideal i).val : ℝ) ≤ Z ^ normBound)
    (DE : (source).CommonLabel) (D : (((source).block DE).mask (source).mask).powerset) :
    idealLogLength Z DE.val.1 ≤ normBound ∧
      idealLogLength Z DE.val.2 ≤ normBound ∧
      idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) ≤ normBound ∧
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val ≤ normBound := by
  sorry

end CompleteMovingRowRecipe

namespace PowerScaleExteriorPool

variable {A : SArithmeticData K} {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable {Z ell eps : ℝ} (pool : PowerScaleExteriorPool A bad Z ell eps)

/-- The original frozen ideal includes all of the actual prime
valuation. Its fixed box pays at most seven original pool lengths. -/
theorem original_frozen_length_le
    (D : Ideal (𝓞 K)) (hD : D ≠ 0) (bound : ℝ)
    (hDN : (Ideal.absNorm D : ℝ) ≤ Z ^ bound)
    (valuation : AmplifierValuation) (p : pool.primes) :
    idealLogLength Z (D * p.val.val.asIdeal ^ valuation.multiplicity) ≤ bound + 7 * ell := by
  sorry

end PowerScaleExteriorPool
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstIdealLengths
#print axioms HeckeSkeleton.Moments.EngineStep.PowerScaleExteriorPool.original_frozen_length_le
