import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveFirstTerminalBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices

/-!
# First terminal choices before the moving parent

The original first zero and tail constants come from one application of
the proved raw source theorem. Its complete source, original comparison
scales and two separate terminal quantities are preserved verbatim.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveFirstTerminalConstants

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open CanonicalOriginalParentFactory CanonicalPrimitiveEngineChoices

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

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (orders : Finset (ℕ × ℕ))

/-- Internal fixed output of the original first Poisson theorem. The
public engine constructs this record before its moving data are given. -/
structure Fixed where
  sTail : Finset (ℕ × ℕ)
  sZero : Finset (ℕ × ℕ)
  Ctail : ℝ
  Cfirst : ℝ
  Ctail_nonneg : 0 ≤ Ctail
  Cfirst_pos : 0 < Cfirst
  bound :
      ∀ {ω ψ : HeckeCharacter K}
      {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
      {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
      {Index : Type*} {data : Index → MomentData K ω ψ}
      (Q : CompleteMovingRowRecipe A P R data) (W : NormProfileRecipe data) (index : Index)
      (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
      (a : RealParameters) (Z t Y₁ Y₂ amplitude control : ℝ),
      1 ≤ amplitude → 1 ≤ control → amplitude ≤ control ^ (1 : ℕ) →
    ∀ (centered : Bool) {floor padding : ℝ}
      (domain : PairedEngineDomain centered (data index) a Z Y₁ Y₂ floor padding)
      (hfull : Q.FullJointBudget Z (a.m + a.q)),
      a.m + a.q ≤ b.firstBox.widthMax → padding ≤ b.firstBox.paddingMax →
      (data index).geometry.slotCount ≤ b.firstBox.cap → b.firstBox.threshold ≤ Z →
    ∀ {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
      (profiles : RawProfileWindow rowDomain heightDomain window
        (OriginalProfileAtomBounds.profileOrders orders) (data index) amplitude),
      (∀ u ∈ pairedRows (data index) a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic b.firstBox.annulus →
    ∀ (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2),
    let s := primitiveSource μv ν b.firstBox Q W index C hroot hemb a Z t Y₁ Y₂ domain.scale
      hfull centered δ hδ hδhalf;
    s.fiber = 1 ∧
    s.dualZeroCost hDiff / Z ^ (a.m + a.q) ≤
      Cfirst * control ^ firstDualOriginalProfileDegree b.firstBox.cap 1 * Z ^ (b.ε / 8) ∧
    (Ctail * (b.firstBox.cutoff Z) ^ (1 - b.firstBox.decay) * s.tailCost sTail) /
        Z ^ (a.m + a.q) ≤
      Cfirst * control ^ firstDualOriginalProfileDegree b.firstBox.cap 1 *
        Z ^ (-b.firstBox.tailSaving) ∧
    pairedStageEnergy centered (data index) a Z t Y₁ Y₂ / Z ^ (a.m + a.q) ≤
      s.dualZeroCost hDiff / Z ^ (a.m + a.q) +
        (Ctail * (b.firstBox.cutoff Z) ^ (1 - b.firstBox.decay) * s.tailCost sTail) /
          Z ^ (a.m + a.q) + s.rawRowCost hDiff / Z ^ (a.m + a.q)

include μ in
/-- Choose the two first terminals once, from the original source
mother theorem and the same requested finite profile orders. -/
theorem exists_fixed : Nonempty (Fixed μv ν C hDiff b orders) := by
  have hε : 0 < b.ε / 8 := div_pos b.ε_pos (by norm_num)
  have hloss : b.firstBox.loss ≤ (b.ε / 8) / 4 := by
    have h := b.loss_le_ε
    change b.loss ≤ (b.ε / 8) / 4
    linarith [b.ε_pos]
  obtain ⟨sTail, sZero, Ctail, Cfirst, hCtail, hCfirst, hbound⟩ :=
    CanonicalOriginalParentFactory.exists_original_primitive_exact_first_bound
      (μv := μv) (ν := ν) (μ := μ) C hDiff b.firstBox 1 (b.ε / 8) hε hloss orders
  exact ⟨⟨sTail, sZero, Ctail, Cfirst, hCtail, hCfirst, hbound⟩⟩

def choose : Fixed μv ν C hDiff b orders :=
  Classical.choice (exists_fixed (μv := μv) (ν := ν) (μ := μ)
    (C := C) (hDiff := hDiff) (b := b) (orders := orders))

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveFirstTerminalConstants

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveFirstTerminalConstants.choose
