import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalIndexMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectNormalizedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalPoolAllowanceTransport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolMonotonicity

set_option linter.unusedSectionVars false

/-!
# Sum the proved exceptional estimates over the actual source labels

The arithmetic carrier, its source map, admissibility and finite
fibres are supplied by the existing actual-source index-mass theorems.
Their constants precede the scale, profiles, source and divisor dyads.

The leaf inequalities below are internal conclusions consumed after
the actual exceptional factory and its original Fourier integration.
They are not new primitives of the engine theorem. No index, finite
family, total arithmetic mass or profile catalogue is supplied anew.
The amplified scalar transport retains the original pool, actual
valuation tag and its moving-prime length exactly once.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}

section OriginalTag

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- Internal transport of the already proved original scalar. The
local density windows may vary with the actual source label, while
the same amplified arithmetic index uses one fixed upper window. -/
theorem original_tag_to_uniform_dyad
    (pool : PowerScaleExteriorPool A bad Z ell eps)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    {localM localB M B : ℝ}
    (hlocalM : 0 ≤ localM) (hM : localM ≤ M) (hB : localB ≤ B)
    (hdensity : 0 < pool.rowDensity M B)
    (i : AmplifiedCommonIndex pool main error)
    (actual coefficient control remaining loss lower : ℝ)
    (hcoefficient : 0 ≤ coefficient) (hcontrol : 0 ≤ control)
    (hremaining : remaining ≤ loss + AmplifiedCommonIndex.movingLength pool main error i)
    (hraw : actual ≤ coefficient * control *
      AmplifiedCommonIndex.originalTagWeight pool localM localB main error i *
        Z ^ remaining * AmplifiedCommonIndex.dyadWeight pool main error lower i) :
    actual ≤ coefficient * control * Z ^ loss *
      amplifiedExceptionalDyadWeight pool M B main error lower i := by
  sorry

end OriginalTag

variable {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ]

/-- Sum the integrated literal direct leaves using their actual
arithmetic image and original fibre. The fixed coefficient includes
the already paid theta, atom, common-profile and Fourier constants. -/
theorem direct
    (cap dimension width degree : ℕ) (normBox δ₁ δ₂ δ₃ coefficient : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hcoefficient : 0 ≤ coefficient) :
    ∃ Cex : ℝ, 0 < Cex ∧ ∀ Z : ℝ, 1 < Z → ∀ P : ℝ, 1 ≤ P → ∀ loss : ℝ,
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := U) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ rows : R.prepared.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBox) →
    ∀ (lower : R.prepared.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.prepared.innerDivisor L i.val) : ℝ) ≤ Z ^ (lower i + mesh)) →
      (∀ i : R.prepared.liveLeaves L exceptional N,
        (R.prepared.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
          coefficient * P ^ degree * Z ^ loss *
            (R.prepared.arithmeticLabels L hcap exceptional N).carrier.exceptionalDyadWeight
              Z (lower i) (R.prepared.originalIndex L hcap exceptional N i)) →
      R.prepared.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ degree * Z ^ (loss + δ₁ + δ₂ + δ₃ + mesh) /
          (Ideal.absNorm oldMask : ℝ) := by
  sorry

/-- The amplified entrance sums the same actual supported, gated
leaves and their original arithmetic tags. The moving length has
already been absorbed by `original_tag_to_uniform_dyad`; the index
mass pays only its proved three small losses, pool loss and dyad mesh. -/
theorem amplified
    (cap dimension width degree : ℕ)
    (normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax coefficient : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) (hcoefficient : 0 ≤ coefficient) :
    ∃ Cex Z₀ : ℝ, 0 < Cex ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B P : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax → 1 ≤ P → ∀ loss : ℝ,
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := U) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
      (B₀ : ℝ), B₀ + 7 * ell ≤ normBox →
    ∀ rows : R.supported.gated.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
    ∀ (lower : R.supported.gated.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.supported.gated.innerDivisor L i.val) : ℝ) ≤
        Z ^ (lower i + mesh)) →
      (∀ i : R.supported.gated.liveLeaves L exceptional N,
        (R.supported.gated.parentLeaf L exceptional N i.val).exceptionalCost / Z ^ (a.m + a.q) ≤
          coefficient * P ^ degree * Z ^ loss *
            amplifiedExceptionalDyadWeight pool M B
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              (lower i) (R.supported.gated.arithmeticIndex L hcap exceptional N i)) →
      R.supported.gated.exceptionalBudget L exceptional N / Z ^ (a.m + a.q) ≤
        Cex * P ^ degree * Z ^ (loss + δ₁ + δ₂ + δ₃ + eps + mesh) /
          (Ideal.absNorm oldMask : ℝ) := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.original_tag_to_uniform_dyad
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.direct
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalUniformIndexBudget.amplified
