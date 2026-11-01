import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalMovingFactorAppend
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingFactorAppend

/-!
# Exact raw deletion budgets after exterior normalization

The original recipe can first use `exteriorRemaining`, which retains
the same parent data and complete Boolean mask. Every later actual
common ideal is exterior. For these remaining ideals, normalization
removes repeated prime powers only; their complete radical supports
are equal, including after the complete second sixth root is inserted.

The actual physical second-row bound is therefore transported to the
literal remaining ideal used by the arithmetic child constructor. No
child-row norm bound, support equality or completed calibration is an
input to the final producer in this file.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExteriorChildBudget

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- For an actual exterior remaining ideal, no prime is removed by the
normalization. Multiplicities need not be one. -/
theorem remaining_primes (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hcop : IsCoprime remaining.val A.cS) :
    primeSupport (remainingMaskIdeal A remaining).val = primeSupport remaining.val := by
  rw [remainingMaskIdeal_val, remainingMaskRadical_primes]
  have hd := (primeSupport_disjoint_iff
    (nonZeroDivisors.ne_zero remaining.property) A.cS_ne_zero).mpr hcop
  exact Finset.sdiff_eq_self_of_disjoint hd

private theorem support_mul (I J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    primeSupport (I * J).val = primeSupport I.val ∪ primeSupport J.val := by
  change primeSupport (I.val * J.val) = _
  simp only [primeSupport, normalizedFactors_mul
    (nonZeroDivisors.ne_zero I.property) (nonZeroDivisors.ne_zero J.property),
    Multiset.toFinset_add]

/-- The complete radical support depends on the literal remaining
prime support, without any assumption on cancellation of characters. -/
theorem fullMaskSupport_congr (D : OriginalMovingFactors A P Rchar)
    (I J : HeckeGeneral.Analysis.NonzeroIdeal K) (h : primeSupport I.val = primeSupport J.val) :
    D.fullMaskSupport I = D.fullMaskSupport J := by
  apply Subtype.ext
  rw [← squarefree_support_product_self (D.fullMaskSupport_squarefree I),
    ← squarefree_support_product_self (D.fullMaskSupport_squarefree J)]
  simp only [D.fullMaskSupport_primes, h]

/-- The sixth-root or any other literal later deletion stays present on
both sides. This is equality of full ideals and hence of their norms. -/
theorem fullMaskSupport_normalized_mul (D : OriginalMovingFactors A P Rchar)
    (remaining later : HeckeGeneral.Analysis.NonzeroIdeal K) (hcop : IsCoprime remaining.val A.cS) :
    D.fullMaskSupport (remainingMaskIdeal A remaining * later) =
      D.fullMaskSupport (remaining * later) := by
  apply fullMaskSupport_congr D
  rw [support_mul, support_mul, remaining_primes remaining hcop]

/-- An original exterior-normalized recipe followed by an actual common
ideal provides the required coprimality internally. This also applies
to the pool's full common ideal including its actual prime power. -/
theorem original_remaining_common_exterior {ω ψ : HeckeCharacter K}
    {X : Type*} {data : X → MomentData K ω ψ}
    (Q : CompleteMovingRowRecipe A P Rchar data) (common : A.Exterior) :
    IsCoprime (Q.exteriorRemaining.remaining * exteriorMomentIdeal common).val A.cS := by
  change IsCoprime ((remainingMaskRadical A Q.remaining).val * common.val) A.cS
  exact (Ideal.isCoprime_iff_sup_eq.mpr (remainingMaskRadical A Q.remaining).property.2).
    mul_left (Ideal.isCoprime_iff_sup_eq.mpr common.property.2)

section ActualPatternWindows

open MeasureTheory

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)

/-- The original physical chart, original old-support window and actual
nonunit pattern produce the bound for the arithmetic child's literal
unreduced remaining ideal. The complete sixth-root support is charged. -/
theorem actualRows_raw_remaining_joint_window
    (hclass : chart.NonunitLabelStable)
    (oldMoving : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (hremaining : IsCoprime remaining.val A.cS)
    (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
    (retainedScale Z g a₀ q wo cutoffExponent : ℝ)
    (hscale : 0 < retainedScale) (hZ : 1 < Z)
    (hradius : radius = CanonicalRowBall.gaussRadius retainedScale Z g hscale
      (zero_lt_one.trans hZ))
    (hcutoff : X ≤ Z ^ cutoffExponent)
    (hleft : ∀ i ∈ left, A.exteriorNorm (fullI i) ≤ Z ^ a₀)
    (hright : ∀ j ∈ right, A.exteriorNorm (fullJ j) ≤ Z ^ a₀)
    (hold : A.exteriorNorm (oldMoving.effectiveFullSupport remaining) ≤ Z ^ (q + wo))
    (h : (chart.actualRows ∅ X hX label).live) :
    let pattern := chart.originalNonunitPattern ∅ X hX label
    idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
        idealNorm K
          ((oldMoving.append (secondOriginalMovingFactors P Rchar C b.primes
            b.leftMultiplicity b.rightMultiplicity pattern)).fullMaskSupport
              (remaining * exteriorMomentIdeal
                (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))) ≤
      Z ^ (secondCommonChildWidth Z a₀ q wo (Real.log retainedScale / Real.log Z) g
        (primePowerProduct b.primes b.leftMultiplicity).val
        (primePowerProduct b.primes b.rightMultiplicity).val
        (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity pattern).val
        (secondPatternNonunitIdeal b.primes pattern).val +
        idealLogLength Z (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
        cutoffExponent) := by
  have hw := chart.actualRows_appended_pattern_fullDeletion_joint_window hclass
    oldMoving remaining X hX label retainedScale Z g a₀ q wo cutoffExponent
    hscale hZ hradius hcutoff hleft hright hold h
  dsimp only at hw ⊢
  change idealNorm K ((chart.actualRows ∅ X hX label).extractedRow C h).momentIdeal *
    idealNorm K
      ((oldMoving.append (secondOriginalMovingFactors P Rchar C b.primes
        b.leftMultiplicity b.rightMultiplicity (chart.originalNonunitPattern ∅ X hX label))).
          fullMaskSupport (remainingMaskIdeal A remaining * exteriorMomentIdeal
            (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity))) ≤ _ at hw
  rw [fullMaskSupport_normalized_mul _ remaining _ hremaining] at hw
  exact hw

end ActualPatternWindows

end HeckeSkeleton.Moments.EngineStep.CanonicalExteriorChildBudget

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExteriorChildBudget.fullMaskSupport_normalized_mul
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExteriorChildBudget.original_remaining_common_exterior
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExteriorChildBudget.actualRows_raw_remaining_joint_window
