import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullSupportFirstWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

set_option linter.unusedSectionVars false

/-!
# Numerical first terminals for the actual full-support source

The powerful-counting loss and the first mask loss are fixed before the
moving recipe, its original profiles and its real parameters. The
actual constructor supplies the sharp negative coefficient exponent,
the product window on nonzero Gram profiles and the full-support
inverse radius. Their length contributions cancel internally.

The tail seminorm and its analytic constant may be chosen by the
existing uniform first-stage theorem before applying this result.
This theorem then computes the numerical tail constant from the same
original physical windows. Neither a terminal estimate nor a final
exponent ledger is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical MeasureTheory
open HeckePort.Moments HeckePort.CenteredMomentCounting

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

/-- The same fixed constants bound the literal first dual-zero sum,
the original physical-tail budget and their sum.
The tail seminorm and constant are fixed analytic data, before every
source variable. The zero seminorm and all numerical constants are
selected here, also before those source variables. -/
theorem exists_canonical_full_support_first_terminal_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (cap degree : ℕ) (bound ε : ℝ) (hbound : 0 ≤ bound) (hε : 0 < ε)
    (orders sTail : Finset (ℕ × ℕ)) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (Nsave decay : ℝ) (hNsave : 0 ≤ Nsave) (hdecay : 1 < decay) :
    ∃ (sZero : Finset (ℕ × ℕ)) (Czero Cerror Cterminal : ℝ),
      0 < Czero ∧ 0 ≤ Cerror ∧
      Cerror = Ctail * (2 * firstTailFieldConstant K *
        idealCountConstant K ^ (2 * (cap + 2))) ∧ 0 < Cterminal ∧
    ∀ {ω ψ : HeckeCharacter K}
      {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
      {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
      {Index : Type*} {data : Index → MomentData K ω ψ}
      (Q : CompleteMovingRowRecipe A P R data) (W : NormProfileRecipe data) (ξ : Index)
      (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
      (C : A.GeneralArithmeticContext σ η hS)
      (B control annulus loss leftExponent rightExponent : ℝ),
      1 ≤ B → 1 ≤ control → B ≤ control ^ degree →
      1 ≤ annulus → 0 ≤ loss → loss ≤ 1 → loss ≤ ε / 4 →
      (data ξ).geometry.slotCount ≤ cap →
      annulus ^ (cap + 2) ≤ Z ^ loss →
    ∀ (centered : Bool) {floor padding : ℝ}
      (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding),
      0 < Y₁ → 0 < Y₂ →
      a.n₁ ≤ leftExponent → a.n₂ ≤ rightExponent →
      Y₁ ≤ Z ^ leftExponent → Y₂ ≤ Z ^ rightExponent →
    ∀ {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
      (profiles : RawProfileWindow rowDomain heightDomain window
        (OriginalProfileAtomBounds.profileOrders orders) (data ξ) B),
      (∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic annulus →
    ∀ (hcolumn : leftExponent + rightExponent + (data ξ).geometry.totalLength + loss ≤ bound)
      (hwidth : a.m + a.q ≤ bound)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0),
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t;
    let raw := atoms.raw Y₁ Y₂;
    let gram := fun i j => ((atoms.values Y₁ Y₂).coefficient centered i *
      star ((atoms.values Y₁ Y₂).coefficient centered j)) • CanonicalRowBall.archTest K A.Sf 1;
    let radius := Q.fullSupportRadius Z (a.m + a.q) (zero_lt_one.trans domain.scale);
    let cutoff := Z ^ firstTailCutoffExponent (originalFirstPhysicalDegree cap bound) Nsave decay;
    let hcutoff : 1 ≤ cutoff := Real.one_le_rpow domain.scale.le
      (firstTailCutoffExponent_nonneg (originalFirstPhysicalDegree cap bound) Nsave decay hdecay);
    let zeroCost := ∑ DE : FirstZeroLabel raw.exteriorColumns raw.exteriorColumns
          raw.columnExterior raw.columnExterior,
        ‖((raw.originalFirstBlocks C DE).finiteSource
          (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
          raw.exteriorColumns raw.exteriorColumns gram ∅ radius cutoff hcutoff).dualZeroTerm
            μv hDiff finiteTest‖;
    let tailCost := Ctail * cutoff ^ (1 - decay) *
        firstBlockTailMass
          (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) C
          raw.exteriorColumns raw.exteriorColumns raw.columnExterior raw.columnExterior
          (raw.originalFirstBlocks C) sTail gram radius ∅;
    zeroCost / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε ∧
    tailCost / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ (-Nsave) ∧
    (zeroCost + tailCost) / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree cap degree * Z ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_canonical_full_support_first_terminal_bound
