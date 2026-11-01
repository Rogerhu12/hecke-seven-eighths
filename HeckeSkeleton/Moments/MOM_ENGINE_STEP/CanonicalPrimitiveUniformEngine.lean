import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledEngine
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEnginePool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineFinalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyParentEngineOutput

/-!
# The uniform internal engine on the original parent

The fixed numerical choices precede the original scale and profiles.
An empty original row set produces the exact empty conclusion. A
nonempty parent supplies its own reference row; zero slots use the
direct engine, and positive slots select one pool shared by both sides
and all tags. The selected pool is never replaced after its sources
have been constructed.

Only the two exact exceptional source estimates remain parameters of
this internal assembly. The primitive public entrance supplies them
from its original volume input. Every other source estimate, analytic
input, normalized child and terminal bound is constructed by the two
actual engines below.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass HeckeGeneral.Bridge
open CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]

/-- All scale thresholds are fixed before any parent or pool is read. -/
def threshold (A : SArithmeticData K) (b : Box) (Zexceptional : ℝ) : ℝ :=
  max b.fullThreshold (max (CanonicalPrimitiveEnginePool.threshold A b)
    (max (CanonicalPrimitiveEngineMassChoices.pooledThreshold (A := A) b) Zexceptional))

theorem threshold_gt_one (A : SArithmeticData K) (b : Box) (Zexceptional : ℝ) :
    1 < threshold A b Zexceptional :=
  (CanonicalPrimitiveEnginePool.threshold_gt_one A b).trans_le
    ((le_max_left _ _).trans (le_max_right _ _))

theorem threshold_spec (A : SArithmeticData K) (b : Box) (Zexceptional Z : ℝ)
    (hlarge : threshold A b Zexceptional ≤ Z) :
    b.fullThreshold ≤ Z ∧ CanonicalPrimitiveEnginePool.threshold A b ≤ Z ∧
      CanonicalPrimitiveEngineMassChoices.pooledThreshold (A := A) b ≤ Z ∧
      Zexceptional ≤ Z := by
  simpa only [threshold, max_le_iff] using hlarge

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ω ψ : HeckeCharacter K}
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

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (b : Box) (mesh : ℝ) (hmesh : 0 ≤ mesh) (orders : Finset (ℕ × ℕ))
variable (first : CanonicalPrimitiveFirstTerminalConstants.Fixed μv ν C hDiff b orders)
variable (second : CanonicalPrimitiveSecondTerminalConstants.Fixed
  (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv hDiff C (rowBallFiniteFamily K A.Sf 1) b)
variable (heightC exceptionalConstant : ℝ)

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => CanonicalPrimitiveEngineMassChoices.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC

/-- One common constant pays two first terminals, two second terminals,
the actual exceptional term and the complete normalized family mass. -/
def constant : ℝ :=
  CanonicalPrimitiveEngineFinalBudget.constant
    first.Cfirst secondConstant exceptionalConstant massConstant

local notation "finalConstant" => constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ)
  μv ν C hDiff b mesh orders first second heightC exceptionalConstant

theorem constant_pos (hexceptionalConstant : 0 ≤ exceptionalConstant) :
    0 < finalConstant :=
  CanonicalPrimitiveEngineFinalBudget.constant_pos first.Cfirst_pos.le
    (CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second).le
    hexceptionalConstant
    (CanonicalPrimitiveEngineMassChoices.constant_pos
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le

variable (exceptionalDegree : ℕ) (Zexceptional : ℝ)
variable (hexceptionalConstant : 0 ≤ exceptionalConstant)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (hwidth : a.m + a.q ≤ b.widthMax) (hpadding : padding ≤ b.paddingMax)
variable (hcap : (data ξ).geometry.slotCount ≤ b.cap)
variable (hlarge : threshold A b Zexceptional ≤ Z)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi)
  (OriginalProfileAtomBounds.profileOrders orders ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := R) (data ξ).theta b.rawNormBound heightC)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
variable (hslotInverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

local notation "thresholds" => threshold_spec A b Zexceptional Z hlarge
local notation "hfull" => (thresholds).1
local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t
local notation "finalDegree" => CanonicalPrimitiveEngineFinalBudget.degree b exceptionalDegree
local notation "terminalExponent" => CanonicalPrimitiveEngineFinalBudget.terminalExponent b

local notation "directCost" => Q.literalPrimitiveDirectEngineExceptionalCost
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hcap := hcap) (hlarge := hfull)
  (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)

local notation "poolCost" => fun
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z)
    (selection : CanonicalPrimitiveEnginePool.Selection A b Z) =>
  Q.literalPrimitivePooledEngineExceptionalCost
    (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
    (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
    (hcap := hcap) (hlarge := hfull) (reference := reference) (href := href)
    (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)
    (pool := selection.pool) (hdensity := selection.density_pos)

/-- Internal assembly of all original slot cases. The two source
estimates refer to the actual costs; the public primitive theorem
constructs them from the original volume estimate. No source, pool,
reference row, analytic input or normalized family is an output premise. -/
def produce
    (hdirect : Zexceptional ≤ Z → (data ξ).geometry.slotCount = 0 →
      directCost ≤ exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent)
    (hpool : Zexceptional ≤ Z →
      ∀ (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
        (href : reference ∈ pairedRows (data ξ) a Z)
        (selection : CanonicalPrimitiveEnginePool.Selection A b Z),
      poolCost reference href selection ≤
        exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent) :
    PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ)) centered (data ξ) a Z t Y₁ Y₂
      b.step (b.ε + mesh) terminalExponent finalConstant (control ^ finalDegree)
      (MovingEngineChildAdmissible A P R
        (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
        Set.univ (Set.Icc (0 : ℝ) b.hi) orders Z) := by
  have hsecond : 0 ≤ secondConstant :=
    (CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second).le
  have hmass : 0 ≤ massConstant :=
    (CanonicalPrimitiveEngineMassChoices.constant_pos
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le
  have hfinal : 0 ≤ finalConstant :=
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      μv ν C hDiff b mesh orders first second heightC exceptionalConstant hexceptionalConstant).le
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · exact PairedEngineConclusion.ofEmptyParent centered (data ξ) a Z t Y₁ Y₂
      b.step (b.ε + mesh) terminalExponent finalConstant (control ^ finalDegree)
      (MovingEngineChildAdmissible A P R
        (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
        Set.univ (Set.Icc (0 : ℝ) b.hi) orders Z)
      (zero_lt_one.trans domain.scale).le hfinal
      (pow_nonneg (zero_le_one.trans
        (CanonicalPrimitiveEngineControl.one_le amplitude t hamplitude)) _) hempty
  · have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let reference := hnonempty.choose
    have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
    by_cases hzero : (data ξ).geometry.slotCount = 0
    · exact Q.literalPrimitiveDirectEngine
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (mesh := mesh) (hmesh := hmesh) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (hfit := hfit) (hslotsZero := hzero)
        (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
        (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
        (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
        (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
        (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
        (terminalExponent := terminalExponent) (exceptionalExponent := terminalExponent)
        (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
        (hfinalConstant := hfinal) (hexceptionalConstant := hexceptionalConstant)
        (hfirstDegree := CanonicalPrimitiveEngineFinalBudget.first_degree_le b exceptionalDegree)
        (hsecondDegree := CanonicalPrimitiveEngineFinalBudget.second_degree_le b exceptionalDegree)
        (hexceptionalDegree := CanonicalPrimitiveEngineFinalBudget.exceptional_degree_le b exceptionalDegree)
        (hmassDegree := CanonicalPrimitiveEngineFinalBudget.mass_degree_le b exceptionalDegree)
        (hterminalExponent := le_rfl) (hexceptionalExponent := le_rfl)
        (hterminalConstant := CanonicalPrimitiveEngineFinalBudget.terminals_le hmass)
        (hmassConstant := CanonicalPrimitiveEngineFinalBudget.mass_le
          first.Cfirst_pos.le hsecond hexceptionalConstant)
        (hexceptional := hdirect (thresholds).2.2.2 hzero)
    · let selection := CanonicalPrimitiveEnginePool.selected A b Z (thresholds).2.1
      exact Q.literalPrimitivePooledEngine
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (mesh := mesh) (hmesh := hmesh) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (hfit := hfit)
        (reference := reference) (href := href) (amplitude := amplitude) (hamplitude := hamplitude)
        (profiles := profiles) (hrows := hrows) (htime := htime) (hprime := hprime)
        (heightC := heightC) (analyticWindow := analyticWindow) (boundary := boundary)
        (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
        (Drecipe := Drecipe) (hD := hD) (pool := selection.pool) (hdensity := selection.density_pos)
        (hmassLarge := (thresholds).2.2.1)
        (finalConstant := finalConstant) (exceptionalConstant := exceptionalConstant)
        (terminalExponent := terminalExponent) (exceptionalExponent := terminalExponent)
        (finalDegree := finalDegree) (exceptionalDegree := exceptionalDegree)
        (hfinalConstant := hfinal) (hexceptionalConstant := hexceptionalConstant)
        (hfirstDegree := CanonicalPrimitiveEngineFinalBudget.first_degree_le b exceptionalDegree)
        (hsecondDegree := CanonicalPrimitiveEngineFinalBudget.second_degree_le b exceptionalDegree)
        (hexceptionalDegree := CanonicalPrimitiveEngineFinalBudget.exceptional_degree_le b exceptionalDegree)
        (hmassDegree := CanonicalPrimitiveEngineFinalBudget.mass_degree_le b exceptionalDegree)
        (hterminalExponent := le_rfl) (hexceptionalExponent := le_rfl)
        (hterminalConstant := CanonicalPrimitiveEngineFinalBudget.terminals_le hmass)
        (hmassConstant := CanonicalPrimitiveEngineFinalBudget.mass_le
          first.Cfirst_pos.le hsecond hexceptionalConstant)
        (hexceptional := hpool (thresholds).2.2.2 reference href selection)

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.threshold_gt_one
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveUniformEngine.produce
