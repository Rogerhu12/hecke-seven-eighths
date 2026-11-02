import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimitiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectFirstDualTerminal

set_option linter.unusedSectionVars false

/-!
# First zero, tail and parent bounds on the literal dispatcher's source

The source here is the original recipe's own
`Q.literalPrimitiveFirstSource` at `Q.fullSupportParameters a Z`.
The primitive first-source wrapper only fixes the original box cutoff
and canonical unused ordinary comparison scales. All constants precede
that same source and every moving parameter.

The complete first zero, tail and parent estimates are applied directly
to this source. Neither an exterior-normalized recipe nor an
energy-equivalent replacement source enters the proof.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

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
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include μ in
/-- Uniform first-source production from the original data.  The zero
and tail quantities are those of the actual source in the parent bound;
neither is replaced by an unrelated positive majorant source. -/
theorem exists_original_primitive_first_bound
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (box : FixedBox) (degree : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hloss : box.loss ≤ ε / 4) (orders : Finset (ℕ × ℕ)) :
    ∃ (sTail sZero : Finset (ℕ × ℕ)) (Ctail Cterminal : ℝ),
      0 ≤ Ctail ∧ 0 < Cterminal ∧
    ∀ {ω ψ : HeckeCharacter K}
      {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
      {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
      {Index : Type*} {data : Index → MomentData K ω ψ}
      (Q : CompleteMovingRowRecipe A P R data) (W : NormProfileRecipe data) (index : Index)
      (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
      (a : RealParameters) (Z t Y₁ Y₂ amplitude control : ℝ),
      1 ≤ amplitude → 1 ≤ control → amplitude ≤ control ^ degree →
    ∀ (centered : Bool) {floor padding : ℝ}
      (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
      (hfull : Q.FullJointBudget Z (a.m + a.q)),
      a.m + a.q ≤ box.widthMax → padding ≤ box.paddingMax →
      (data index).geometry.slotCount ≤ box.cap → box.threshold ≤ Z →
    ∀ {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
      (profiles : RawProfileWindow rowDomain heightDomain window
        (OriginalProfileAtomBounds.profileOrders orders) (data index) amplitude),
      (∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic box.annulus →
    ∀ (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2),
    let s := primitiveSource μv ν box Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
      hfull centered δ hδ hδhalf;
    s.fiber = 1 ∧
    s.dualZeroCost hDiff / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε ∧
    (Ctail * (box.cutoff Z) ^ (1 - box.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree *
        Z ^ (-box.tailSaving) ∧
    pairedStageEnergy centered (data index) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      Cterminal * control ^ firstDualOriginalProfileDegree box.cap degree * Z ^ ε +
        s.rawRowCost hDiff / Z ^ (a.m + a.q) := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalOriginalParentFactory.exists_original_primitive_first_bound
