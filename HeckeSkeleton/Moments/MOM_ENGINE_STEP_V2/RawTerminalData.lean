import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TargetArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ChoiceBox
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedDirectFirstSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDualZeroSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussDualRawTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFamilyIntegrability

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual analytic data for the two original physical transforms

Every seminorm and numerical constant below is selected directly from
a proved base theorem. The first order is an explicit integer larger
than the lattice dimension and field degree times the chosen decay.
The second theorem already makes that order choice internally. The
fixed logarithmic kernel is the same row-ball kernel used by the source.
No terminal estimate or engine output is used to manufacture these data.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

/-- Only fixed analytic data. The actual source estimates are stated
separately for these same selected fields. -/
structure RawTerminalData where
  firstOrder : ℕ
  firstTailOrders : Finset (ℕ × ℕ)
  firstZeroOrders : Finset (ℕ × ℕ)
  firstTail : ℝ
  firstZero : ℝ
  firstTail_nonneg : 0 ≤ firstTail
  firstZero_pos : 0 < firstZero
  secondTailOrders : Finset (ℕ × ℕ)
  secondZeroOrders : Finset (ℕ × ℕ)
  secondTail : ℝ
  secondZero : ℝ
  secondTail_nonneg : 0 ≤ secondTail
  secondZero_pos : 0 < secondZero
  fourierOrders : Finset (ℕ × ℕ)
  fourierConstant : ℝ
  fourierConstant_pos : 0 < fourierConstant
  kernel : SchwartzMap ℝ ℂ

private theorem sixthUnits_power
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    ∀ u : sixthPowerSUnitSubgroup K S, ∃ v : S.unit K, u.val = v ^ 6 := by
  intro u
  obtain ⟨v, hv⟩ := u.property
  exact ⟨v, hv.symm⟩

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

/-- Direct projections of the existing analytic existence theorems,
at Base's unchanged arithmetic, self-dual local measures and actual
row-ball test. All choices precede every moving scale and parent. -/
def rawTerminalData (c : TargetContext K)
    (b : CanonicalPrimitiveEngineChoices.Box) : RawTerminalData := by
  let A := TargetArithmetic.arithmetic c
  let σ := TargetArithmetic.embedding c
  let C := TargetArithmetic.context c
  letI : IsPrincipalIdealRing A.R := TargetArithmetic.principalRing c
  letI : IsTotallyComplex K := TargetArithmetic.totallyComplex c
  letI : MeasurableSpace
      (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := borel _
  letI : BorelSpace
      (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := ⟨rfl⟩
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  let μv := TargetArithmetic.localMeasures (K := K)
  let ν := TargetArithmetic.finiteMeasure (K := K)
  let μ := TargetArithmetic.fullMeasure (K := K)
  let hΓ := sixthUnits_power (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
  let latticeDimension : ℝ := Module.finrank ℤ
    (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  let order : ℕ := ⌈max latticeDimension
    ((Module.finrank ℚ K : ℝ) * b.firstDecay)⌉₊ + 1
  have horder : Module.finrank ℤ
      (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < order := by
    have hd : latticeDimension ≤
        (⌈max latticeDimension ((Module.finrank ℚ K : ℝ) * b.firstDecay)⌉₊ : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    have hn : Module.finrank ℤ
        (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) ≤
        ⌈max latticeDimension ((Module.finrank ℚ K : ℝ) * b.firstDecay)⌉₊ := by
      dsimp only [latticeDimension] at hd
      exact_mod_cast hd
    exact Nat.lt_succ_of_le hn
  have hdegree : (Module.finrank ℚ K : ℝ) * b.firstDecay ≤ order := by
    have hd : (Module.finrank ℚ K : ℝ) * b.firstDecay ≤
        (⌈max latticeDimension ((Module.finrank ℚ K : ℝ) * b.firstDecay)⌉₊ : ℝ) :=
      (le_max_right _ _).trans (Nat.le_ceil _)
    apply hd.trans
    exact_mod_cast Nat.le_succ
      ⌈max latticeDimension ((Module.finrank ℚ K : ℝ) * b.firstDecay)⌉₊
  let firstTail := actual_parent_first_direct_dual (E := ℝ)
    (hΓ := hΓ) (μv := μv) (ν := ν) (μ := μ) C
    (TargetArithmetic.different c) 1 b.firstDecay b.firstDecay_gt_one
    order horder hdegree
  let zeroLoss : ℝ := (b.ε / 8) / (4 * (b.columnBound + 1))
  have hzeroLoss : 0 < zeroLoss := by
    have hB := b.columnBound_nonneg
    have hε := b.ε_pos
    dsimp [zeroLoss]
    positivity
  let firstZero := first_dual_zero_diagonal_supported.{0, 0}
    (σ := σ) (η := (TargetArithmetic.choice c).η)
    (hS := (TargetArithmetic.choice c).hS) (hΓ := hΓ) (μv := μv)
    (rowBallFiniteFamily K A.Sf 1) (2 * (b.cap + 2)) zeroLoss hzeroLoss
  let second := actual_gauss_raw_dual_terminal_bound.{0, 0} (E := ℝ)
    (ν := ν) (μ := μ) hΓ μv (TargetArithmetic.different c) C
    (TargetArithmetic.coefficients c) (TargetArithmetic.coefficients_recipe c)
    (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    (2 * (b.cap + 2)) b.tilt b.tilt_pos b.secondDegree b.saving b.loss b.loss_pos
  let secondConstants := second.choose_spec.choose_spec.2.2
  let fourier := actualFourierMeasure_uniform_mass (V := ℝ)
  exact {
    firstOrder := order
    firstTailOrders := firstTail.choose
    firstZeroOrders := firstZero.choose
    firstTail := firstTail.choose_spec.choose
    firstZero := firstZero.choose_spec.choose
    firstTail_nonneg := firstTail.choose_spec.choose_spec.1
    firstZero_pos := firstZero.choose_spec.choose_spec.1
    secondTailOrders := secondConstants.choose
    secondZeroOrders := secondConstants.choose_spec.choose
    secondTail := secondConstants.choose_spec.choose_spec.choose
    secondZero := secondConstants.choose_spec.choose_spec.choose_spec.choose
    secondTail_nonneg := secondConstants.choose_spec.choose_spec.choose_spec.choose_spec.1
    secondZero_pos := secondConstants.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    fourierOrders := fourier.choose
    fourierConstant := fourier.choose_spec.choose
    fourierConstant_pos := fourier.choose_spec.choose_spec.1
    kernel := CanonicalSecondLogChart.kernel
      (Γ := sixthPowerSUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
      μv ν (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      b.tilt b.tilt_pos b.tilt_le_half (CanonicalRowBall.archTest K A.Sf 1) }

end HeckeSkeleton.Moments.EngineStepV2
