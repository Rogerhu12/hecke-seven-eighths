import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstProfilePower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedDirectSourceTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalDualTerminal

/-!
# Original first windows for the complete second terminal sum

The actual first source has an empty physical mask. The original
full-support deletion remains in its coefficients and original row
budget. Its common-label counting uses the unit compulsory divisor.
All first Fourier costs are fixed values of the same row-ball kernel.
The original raw profile window supplies the full column norm bound.
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
local notation "raw" => atoms.raw Y₁ Y₂

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

local notation "firstTotal" => Q.literalPrimitiveFirstTotal μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
local notation "firstShift" => fun DE D =>
  Q.literalPrimitiveFirstProfileShift μv ν C hroot hemb W ξ a Z t Y₁ Y₂
    hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half DE D (firstTotal DE D)
local notation "firstKernel" => ActualGaussStage.canonicalRowBallKernel
  (A := A) (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv ν δ₁ hδ₁ hδ₁half
local notation "kernelBound" => (firstTerminalFourierControl (W := ℝ)).seminorms.sup
  (schwartzSeminormFamily ℝ ℝ ℂ) firstKernel

variable (cap : ℕ) (annulus loss leftExponent rightExponent normBound : ℝ)
variable (hannulus : 1 ≤ annulus) (hcap : (data ξ).geometry.slotCount ≤ cap)
variable (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss) (hbound : 0 ≤ normBound)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
variable (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent)
variable (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
variable (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
variable (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ normBound)

include hannulus hcap hannulusZ hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le
  profiles hrows ht hwindow hcolumn in
/-- This bounds the same full Cartesian union, including columns with
zero actual coefficients. No active-source replacement is made. -/
theorem literalPrimitiveFirstSource_column_norm :
    ∀ i ∈ source.columns, (Ideal.absNorm (source.ideal i).val : ℝ) ≤ Z ^ normBound := by
  have hrows' : ∀ u ∈ pairedRows (data ξ) internal Z, u ∈ rowDomain := by
    simpa only [Q.literalPrimitiveFirstSource_pairedRows] using hrows
  intro i hi
  have h := raw.original_union_column_norm_le_power profiles cap annulus loss
    leftExponent rightExponent hannulus hcap hannulusZ (zero_lt_one.trans hZ) hY₁ hY₂
    hleftPower hrightPower hY₁le hY₂le hrows' ht hwindow i hi
  exact h.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hcolumn)

/-- Every field required for the original direct terminal summation
is constructed here from individual original profiles and lengths. -/
def literalPrimitiveFirstTerminalWindows :
    source.CombinedTerminalOriginalWindows normBound (a.m + a.q)
      (orbitalFieldFactor K) kernelBound firstTotal firstShift where
  oldMask := 1
  old_squarefree := squarefree_one
  old_ne_zero := one_ne_zero
  old_divides := fun _ _ => one_dvd _
  column_norm := Q.literalPrimitiveFirstSource_column_norm μv ν C hroot hemb W ξ
    a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
    cap annulus loss leftExponent rightExponent normBound hannulus hcap hannulusZ
    hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le profiles hrows ht hwindow hcolumn
  maskIdeal := 1
  mask_ne_zero := one_ne_zero
  mask_norm := by
    simpa only [map_one, Nat.cast_one] using Real.one_le_rpow hZ.le hbound
  original_mask := emptyOriginalSIntegerMask
  first_profile := by
    intro DE D
    exact (Q.literalPrimitiveFirstSource_weightBound μv ν C hroot hemb W ξ
      a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half
      DE D (firstTotal DE D)).le
  first_kernel := by
    intro DE D
    exact le_rfl

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstSource_column_norm
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstTerminalWindows
