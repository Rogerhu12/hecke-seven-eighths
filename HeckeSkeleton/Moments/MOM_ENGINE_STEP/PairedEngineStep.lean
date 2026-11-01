import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineSetup
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineInheritance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveDirectExceptionalBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitivePooledExceptionalBudget

/-!
# The paired engine step from the original data

All finite orders, constants, polynomial degrees and thresholds are
chosen from the fixed box, arithmetic data, original character catalogue,
single-character volume primitive and original prime analytic provider.
These choices precede the moving parent, its scale, profiles and pool.

The original profile annulus is enlarged internally without changing
any Schwartz representative. The direct and pooled exceptional budgets
are proved from the same original data. The uniform engine constructs
the actual sources, both Fourier kernels, normalized children and all
four terminal estimates. Positive-slot branches share its one selected
pool; zero slots require no pool. The full kappa interval is retained.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open CanonicalOriginalParentFactory CanonicalPrimitiveEngineChoices
open HeckeGeneral.Bridge HeckePort.Moments

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
variable (Drecipe : ComparisonPoissonCoefficientData K A)
variable (hD : GlobalPairCancel.HasArithmeticRecipes A σ hS C.correction.B Drecipe)
variable {ω ψ : HeckeCharacter K}
variable (b : Box) (theta : Finset (HeckeCharacter K))
variable (outputOrders : Finset (ℕ × ℕ))
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  ψ theta (Set.Icc b.lo b.hi))
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (provider : CanonicalOriginalPrimeAnalyticProvider.Provider
  (A := A) (P := P) (R := R) theta)

namespace CanonicalPairedEngineStep

local notation "box" => CanonicalPrimitiveEngineAnnulus.annularBox b
local notation "volume" => CanonicalPrimitiveEngineAnnulus.volumePrimitive b primitive

/-- The finite output orders are fixed before the moving parent. -/
def orders : Finset (ℕ × ℕ) :=
  CanonicalPrimitiveEngineSetup.orders (A := A) (σ := σ) (η := η) (hS := hS)
    box theta outputOrders volume

/-- One original profile window supplies every later restriction. -/
def profileOrders : Finset (ℕ × ℕ) :=
  CanonicalPrimitiveEngineSetup.originalOrders (A := A) (σ := σ) (η := η) (hS := hS)
    box theta outputOrders volume

local notation "allOrders" => orders (A := A) (σ := σ) (η := η) (hS := hS)
  b theta outputOrders primitive
local notation "first" => CanonicalPrimitiveEngineSetup.first
  (μv := μv) (ν := ν) (μ := μ) (C := C) (hDiff := hDiff)
  (b := box) (theta := theta) (outputOrders := outputOrders) (primitive := volume)
local notation "second" => CanonicalPrimitiveEngineSetup.second
  (μv := μv) (ν := ν) (μ := μ) (C := C) (hDiff := hDiff)
  (b := box) (Drecipe := Drecipe) (hD := hD)
local notation "heightC" => CanonicalPrimitiveEngineSetup.heightConstant
  (A := A) (P := P) (R := R) box theta provider
local notation "exceptionalC" => CanonicalPrimitiveExceptionalChoices.constant
  μv ν C hDiff box volume
local notation "exceptionalZ" => CanonicalPrimitiveExceptionalChoices.threshold
  μv ν C hDiff box volume

/-- The degree depends only on the original fixed numerical box. -/
def degree (b : Box) : ℕ :=
  CanonicalPrimitiveEngineFinalBudget.degree (CanonicalPrimitiveEngineAnnulus.annularBox b)
    (CanonicalPrimitiveExceptionalChoices.degree (CanonicalPrimitiveEngineAnnulus.annularBox b))

/-- One fixed constant pays every terminal term and the actual family mass. -/
def constant : ℝ :=
  CanonicalPrimitiveUniformEngine.constant
    (A := A) (σ := σ) (ω := ω) (ψ := ψ)
    μv ν C hDiff box allOrders first second heightC exceptionalC

/-- A fixed lower threshold for the original scale. -/
def threshold : ℝ := CanonicalPrimitiveUniformEngine.threshold A box exceptionalZ

theorem outputOrders_subset : outputOrders ⊆ allOrders :=
  CanonicalPrimitiveEngineSetup.outputOrders_subset
    (A := A) (σ := σ) (η := η) (hS := hS) box theta outputOrders volume

theorem constant_pos :
    0 < constant (ω := ω) μv ν μ C hDiff Drecipe hD
      b theta outputOrders primitive provider :=
  CanonicalPrimitiveUniformEngine.constant_pos
    (A := A) (σ := σ) (ω := ω) (ψ := ψ)
    μv ν C hDiff box allOrders first second heightC exceptionalC
    (CanonicalPrimitiveExceptionalChoices.constant_pos μv ν C hDiff box volume).le

theorem threshold_gt_one : 1 < threshold μv ν C hDiff b theta primitive :=
  CanonicalPrimitiveUniformEngine.threshold_gt_one A box exceptionalZ

end CanonicalPairedEngineStep

local notation "box" => CanonicalPrimitiveEngineAnnulus.annularBox b
local notation "volume" => CanonicalPrimitiveEngineAnnulus.volumePrimitive b primitive
local notation "allOrders" => CanonicalPairedEngineStep.orders
  (A := A) (σ := σ) (η := η) (hS := hS) b theta outputOrders primitive
local notation "inputOrders" => CanonicalPairedEngineStep.profileOrders
  (A := A) (σ := σ) (η := η) (hS := hS) b theta outputOrders primitive
local notation "first" => CanonicalPrimitiveEngineSetup.first
  (μv := μv) (ν := ν) (μ := μ) (C := C) (hDiff := hDiff)
  (b := box) (theta := theta) (outputOrders := outputOrders) (primitive := volume)
local notation "second" => CanonicalPrimitiveEngineSetup.second
  (μv := μv) (ν := ν) (μ := μ) (C := C) (hDiff := hDiff)
  (b := box) (Drecipe := Drecipe) (hD := hD)
local notation "heightC" => CanonicalPrimitiveEngineSetup.heightConstant
  (A := A) (P := P) (R := R) box theta provider
local notation "exceptionalC" => CanonicalPrimitiveExceptionalChoices.constant
  μv ν C hDiff box volume
local notation "exceptionalZ" => CanonicalPrimitiveExceptionalChoices.threshold
  μv ν C hDiff box volume
local notation "finalConstant" => CanonicalPairedEngineStep.constant
  (ω := ω) μv ν μ C hDiff Drecipe hD b theta outputOrders primitive provider
local notation "finalDegree" => CanonicalPairedEngineStep.degree b
local notation "scaleThreshold" => CanonicalPairedEngineStep.threshold
  μv ν C hDiff b theta primitive

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
variable (hlarge : scaleThreshold ≤ Z)
variable (hfit : (data ξ).geometry.fitsMesh b.loss)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi)
  inputOrders (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (htheta : (data ξ).theta = theta)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes theta ⊆ A.Sf)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
variable (hslotInverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t

include Q W hroot hemb domain hbudget hwidth hpadding hcap hlarge hfit hamplitude
  hrows htime hprime htheta hplaces boundary hone hbackground hslot hslotInverse in
/-- The complete paired engine step. Every parent, terminal and mass bound
is produced from the original inputs. The output has the same selected
children throughout and includes the slot-inverse condition needed by
another step. No finished source, leaf, child or numerical estimate is
an input to this public producer. -/
def paired_engine_step :
    PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ)) centered (data ξ) a Z t Y₁ Y₂
      b.step b.ε (b.paddingMax + 3 * b.step + b.ε)
      finalConstant (control ^ finalDegree)
      (fun child parameters =>
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
          Set.univ (Set.Icc (0 : ℝ) box.hi) allOrders Z child parameters ∧
        ∀ i, (child.slotCoefficient i)⁻¹ ∈ child.theta) := by
  subst theta
  let theta : Finset (HeckeCharacter K) := (data ξ).theta
  have hc : 0 < finalConstant := CanonicalPairedEngineStep.constant_pos
    (ω := ω) μv ν μ C hDiff Drecipe hD b (data ξ).theta outputOrders primitive provider
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · exact PairedEngineConclusion.ofEmptyParent centered (data ξ) a Z t Y₁ Y₂
      b.step b.ε (b.paddingMax + 3 * b.step + b.ε) finalConstant (control ^ finalDegree)
      (fun child parameters =>
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
          Set.univ (Set.Icc (0 : ℝ) box.hi) allOrders Z child parameters ∧
        ∀ i, (child.slotCoefficient i)⁻¹ ∈ child.theta)
      (zero_lt_one.trans domain.scale).le hc.le
      (pow_nonneg (zero_le_one.trans
        (CanonicalPrimitiveEngineControl.one_le amplitude t hamplitude)) _) hempty
  · have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let reference := hnonempty.choose
    have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
    let rawWindow := CanonicalPrimitiveEngineAnnulus.rawWindow b profiles
    have hrawPrime : ∀ i,
        Function.support (rawWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2 := hprime
    have hvolOrders : CanonicalPrimitiveExceptionalChoices.orders
        (A := A) (σ := σ) (η := η) (hS := hS) box volume ⊆ allOrders :=
      CanonicalPrimitiveEngineSetup.volumeOrders_subset
        (A := A) (σ := σ) (η := η) (hS := hS)
        box (data ξ).theta outputOrders volume
    have hprimeOrders : CanonicalFullKappaPrime.orders ⊆ allOrders :=
      CanonicalPrimitiveEngineSetup.primeOrders_subset
        (A := A) (σ := σ) (η := η) (hS := hS)
        box (data ξ).theta outputOrders volume
    exact CanonicalPrimitiveUniformEngine.produceWithInheritedSlots
      (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := box) (orders := allOrders)
      (first := first) (second := second) (heightC := heightC)
      (exceptionalConstant := exceptionalC)
      (exceptionalDegree := CanonicalPrimitiveExceptionalChoices.degree box)
      (Zexceptional := exceptionalZ)
      (hexceptionalConstant :=
        (CanonicalPrimitiveExceptionalChoices.constant_pos μv ν C hDiff box volume).le)
      (hprimeOrders := hprimeOrders) (Drecipe := Drecipe) (hD := hD)
      (Q := Q) (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
      (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
      (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
      (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
      (amplitude := amplitude) (hamplitude := hamplitude) (profiles := rawWindow)
      (hrows := hrows) (htime := htime) (hprime := hrawPrime)
      (analyticWindow := CanonicalPrimitiveEngineSetup.primeWindow
        (A := A) (P := P) (R := R) box (data ξ).theta provider)
      (boundary := boundary) (hone := hone) (hbackground := hbackground)
      (hslot := hslot) (hslotInverse := hslotInverse)
      (hdirect := fun hexceptionalLarge _ =>
        Q.literalPrimitiveDirectEngineExceptionalCost_le
          (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := box) (orders := allOrders)
          (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
          (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
          (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
          (hcap := hcap) (reference := reference) (href := href)
          (amplitude := amplitude) (hamplitude := hamplitude) (profiles := rawWindow)
          (hrows := hrows) (htime := htime) (hprime := hrawPrime)
          (hone := hone) (hplaces := hplaces) (primitive := volume)
          (hlower := CanonicalPrimitiveEngineAnnulus.inverse_hi_le_lo b)
          (hvolumeOrders := hvolOrders) (hlarge := hexceptionalLarge))
      (hpool := fun hexceptionalLarge selectedReference hselectedReference selection =>
        Q.literalPrimitivePooledEngineExceptionalCost_le
          (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := box) (orders := allOrders)
          (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
          (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
          (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
          (hcap := hcap) (reference := selectedReference) (href := hselectedReference)
          (amplitude := amplitude) (hamplitude := hamplitude) (profiles := rawWindow)
          (hrows := hrows) (htime := htime) (hprime := hrawPrime)
          (hone := hone) (hplaces := hplaces) (primitive := volume)
          (hlower := CanonicalPrimitiveEngineAnnulus.inverse_hi_le_lo b)
          (horders := hvolOrders) (hexceptionalLarge := hexceptionalLarge)
          (pool := selection.pool) (hdensity := selection.density_pos))

include Q W hroot hemb domain hbudget hwidth hpadding hcap hlarge hfit hamplitude
  hrows htime hprime htheta hplaces boundary hone hbackground hslot hslotInverse in
/-- The proposition-valued form of the same complete producer. -/
theorem paired_engine_step_exists :
    Nonempty (PairedEngineConclusion (Ω := WithLp 2 (ℝ × ℝ))
      centered (data ξ) a Z t Y₁ Y₂ b.step b.ε (b.paddingMax + 3 * b.step + b.ε)
      finalConstant (control ^ finalDegree)
      (fun child parameters =>
        MovingEngineChildAdmissible A P R
          (ActualSIntegerOrbit K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) (data ξ)
          Set.univ (Set.Icc (0 : ℝ) box.hi) allOrders Z child parameters ∧
        ∀ i, (child.slotCoefficient i)⁻¹ ∈ child.theta)) :=
  ⟨paired_engine_step
    (μv := μv) (ν := ν) (μ := μ) (C := C) (hDiff := hDiff)
    (Drecipe := Drecipe) (hD := hD) (b := b) (theta := theta)
    (outputOrders := outputOrders) (primitive := primitive) (provider := provider)
    (Q := Q) (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
    (hcap := hcap) (hlarge := hlarge) (hfit := hfit)
    (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles)
    (hrows := hrows) (htime := htime) (hprime := hprime) (htheta := htheta)
    (hplaces := hplaces) (boundary := boundary) (hone := hone)
    (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)⟩

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPairedEngineStep.constant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPairedEngineStep.threshold_gt_one
#print axioms HeckeSkeleton.Moments.EngineStep.paired_engine_step
#print axioms HeckeSkeleton.Moments.EngineStep.paired_engine_step_exists
