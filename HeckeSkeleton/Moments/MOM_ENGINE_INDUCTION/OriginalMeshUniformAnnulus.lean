import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshDirectAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshPooledAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshUniformEngine

/-!
# The uniform original-mesh engine preserves positive profile supports

The proof follows the producer's same empty, direct and pooled cases,
including its original reference row and selected pool. Thus every
public child already chosen by the numerical producer has the positive
annulus and strict prime support proved by its literal source family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformSupport

open OriginalMeshUniformEngine

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass HeckeGeneral.Bridge
open CanonicalPrimitiveEngineChoices

variable {K : Type} [Field K] [NumberField K]

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
variable (b : Box) (mesh : ℝ) (orders : Finset (ℕ × ℕ))
variable (first : CanonicalPrimitiveFirstTerminalConstants.Fixed μv ν C hDiff b orders)
variable (second : CanonicalPrimitiveSecondTerminalConstants.Fixed
  (actualSixthUnits_are_sixth (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
  μv hDiff C (rowBallFiniteFamily K A.Sf 1) b)
variable (heightC exceptionalConstant : ℝ)

local notation "secondConstant" =>
  CanonicalPrimitiveSecondTerminalUniform.Csecond μv ν C hDiff b second
local notation "massConstant" => OriginalMeshEngineMass.constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC

local notation "finalConstant" => constant
  (A := A) (σ := σ) (ω := ω) (ψ := ψ)
  μv ν C hDiff b mesh orders first second heightC exceptionalConstant

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
variable (hmesh : 0 ≤ mesh)
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

local notation "directCost" => Q.literalOriginalMeshDirectEngineExceptionalCost
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
  (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
  (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hcap := hcap) (hlarge := hfull)
  (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)

local notation "poolCost" => fun
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z)
    (selection : CanonicalPrimitiveEnginePool.Selection A b Z) =>
  Q.literalOriginalMeshPooledEngineExceptionalCost
    (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
    (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
    (hcap := hcap) (hlarge := hfull) (reference := reference) (href := href)
    (amplitude := amplitude) (profiles := profiles) (hrows := hrows) (htime := htime)
    (pool := selection.pool) (hdensity := selection.density_pos)

variable
    (hdirect : Zexceptional ≤ Z → (data ξ).geometry.slotCount = 0 →
      directCost ≤ exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent)
    (hpool : Zexceptional ≤ Z →
      ∀ (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
        (href : reference ∈ pairedRows (data ξ) a Z)
        (selection : CanonicalPrimitiveEnginePool.Selection A b Z),
      poolCost reference href selection ≤
        exceptionalConstant * control ^ exceptionalDegree * Z ^ terminalExponent)

local notation "produced" => OriginalMeshUniformEngine.produce
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff)
  (b := b) (mesh := mesh) (orders := orders) (first := first)
  (second := second) (heightC := heightC) (exceptionalConstant := exceptionalConstant) (exceptionalDegree := exceptionalDegree)
  (Zexceptional := Zexceptional) (hexceptionalConstant := hexceptionalConstant) (hprimeOrders := hprimeOrders) (Drecipe := Drecipe)
  (hD := hD) (Q := Q) (W := W) (ξ := ξ)
  (hroot := hroot) (hemb := hemb) (a := a) (Z := Z)
  (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hmesh := hmesh) (hfit := hfit)
  (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles) (hrows := hrows)
  (htime := htime) (hprime := hprime) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (hdirect := hdirect) (hpool := hpool)

/-- The actual uniform dispatcher has the stronger supports on all
of its same output branches. No support property is an output premise. -/
theorem annulusSupport : EngineAnnulusSupport produced b.lo b.hi orders := by
  have hsecond : 0 ≤ secondConstant :=
    (CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second).le
  have hmass : 0 ≤ massConstant :=
    (OriginalMeshEngineMass.constant_pos
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le
  have hfinal : 0 ≤ finalConstant :=
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      μv ν C hDiff b mesh orders first second heightC exceptionalConstant hexceptionalConstant).le
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · apply EngineAnnulusSupport.of_zero_branches
    simp only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_pos hempty,
      PairedEngineConclusion.ofEmptyParent_branches]
  · have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let reference := hnonempty.choose
    have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
    by_cases hzero : (data ξ).geometry.slotCount = 0
    · have h := OriginalMeshDirectSupport.annulusSupport (Q := Q)
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (mesh := mesh) (hmesh := hmesh) (hfit := hfit) (hslotsZero := hzero)
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
      simpa only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_neg hempty, dif_pos hzero] using h
    · let selection := CanonicalPrimitiveEnginePool.selected A b Z (thresholds).2.1
      have h := OriginalMeshPooledSupport.annulusSupport (Q := Q)
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
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
      simpa only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_neg hempty, dif_neg hzero] using h

local notation "supports" => annulusSupport
  (μv := μv) (ν := ν) (C := C) (hDiff := hDiff)
  (b := b) (mesh := mesh) (orders := orders) (first := first)
  (second := second) (heightC := heightC) (exceptionalConstant := exceptionalConstant) (exceptionalDegree := exceptionalDegree)
  (Zexceptional := Zexceptional) (hexceptionalConstant := hexceptionalConstant) (hprimeOrders := hprimeOrders) (Drecipe := Drecipe)
  (hD := hD) (Q := Q) (W := W) (ξ := ξ)
  (hroot := hroot) (hemb := hemb) (a := a) (Z := Z)
  (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hmesh := hmesh) (hfit := hfit)
  (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles) (hrows := hrows)
  (htime := htime) (hprime := hprime) (analyticWindow := analyticWindow) (boundary := boundary)
  (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  (hdirect := hdirect) (hpool := hpool)

/-- Strengthen only the admissibility proofs on the actual uniformly
selected output. All child data and numerical fields are retained. -/
def produceWithProfileSupports :=
  EngineAnnulusSupport.withProfileSupports produced supports

variable (narrowLo narrowHi : ℝ) (hnarrowLo : 0 < narrowLo) (hnarrowHi : 1 ≤ narrowHi)
variable (hnarrowHiLe : narrowHi ≤ b.hi)
variable (narrowProfiles : RawProfileWindow rowDomain heightDomain (Set.Icc narrowLo narrowHi)
  (OriginalProfileAtomBounds.profileOrders orders ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) amplitude)

/-- The normalization and exceptional estimates may use the larger
engine box, while support is read from the independent original window.
The actual output remains exactly the original uniform producer. -/
theorem narrowAnnulusSupport : EngineAnnulusSupport produced narrowLo narrowHi orders := by
  have hsecond : 0 ≤ secondConstant :=
    (CanonicalPrimitiveSecondTerminalUniform.Csecond_pos μv ν C hDiff b second).le
  have hmass : 0 ≤ massConstant :=
    (OriginalMeshEngineMass.constant_pos
      (A := A) (σ := σ) (ω := ω) (ψ := ψ) μv ν b mesh orders heightC).le
  have hfinal : 0 ≤ finalConstant :=
    (constant_pos (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      μv ν C hDiff b mesh orders first second heightC exceptionalConstant hexceptionalConstant).le
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · apply EngineAnnulusSupport.of_zero_branches
    simp only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_pos hempty,
      PairedEngineConclusion.ofEmptyParent_branches]
  · have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let reference := hnonempty.choose
    have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
    by_cases hzero : (data ξ).geometry.slotCount = 0
    · have h := OriginalMeshDirectSupport.narrowAnnulusSupport (Q := Q)
        (narrowLo := narrowLo) (narrowHi := narrowHi)
        (hnarrowLo := hnarrowLo) (hnarrowHi := hnarrowHi)
        (hnarrowHiLe := hnarrowHiLe) (narrowProfiles := narrowProfiles)
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (mesh := mesh) (hmesh := hmesh) (hfit := hfit) (hslotsZero := hzero)
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
      simpa only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_neg hempty, dif_pos hzero] using h
    · let selection := CanonicalPrimitiveEnginePool.selected A b Z (thresholds).2.1
      have h := OriginalMeshPooledSupport.narrowAnnulusSupport (Q := Q)
        (narrowLo := narrowLo) (narrowHi := narrowHi)
        (hnarrowLo := hnarrowLo) (hnarrowHi := hnarrowHi)
        (hnarrowHiLe := hnarrowHiLe) (narrowProfiles := narrowProfiles)
        (μv := μv) (ν := ν) (C := C) (hDiff := hDiff) (b := b) (orders := orders)
        (hprimeOrders := hprimeOrders) (first := first) (second := second)
        (W := W) (ξ := ξ) (hroot := hroot) (hemb := hemb)
        (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
        (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
        (hcap := hcap) (hlarge := hfull) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
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
      simpa only [OriginalMeshUniformEngine.produce,
        EngineStep.CanonicalPrimitiveUniformEngine.produce, dif_neg hempty, dif_neg hzero] using h

end HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformSupport

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformSupport.annulusSupport
#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformSupport.produceWithProfileSupports

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshUniformSupport.narrowAnnulusSupport
