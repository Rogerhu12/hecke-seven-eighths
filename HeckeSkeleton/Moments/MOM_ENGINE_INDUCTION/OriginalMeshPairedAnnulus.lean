import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshUniformAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OriginalMeshPairedEngineStep

/-!
# The complete original-mesh producer retains the independent narrow support

The public numerical producer pays the actual exceptional estimates in
its larger analytic box. The support theorem follows the same empty
case and exact uniform producer, using a separate original narrow raw
window. No exceptional bound, normalized child, or support conclusion
is assumed. The output data, kernel and energy estimate are unchanged.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineInduction.OriginalMeshPairedSupport

open EngineStep

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
variable (b : Box) (mesh : ℝ) (theta : Finset (HeckeCharacter K))
variable (outputOrders : Finset (ℕ × ℕ))
variable (primitive : CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  ψ theta (Set.Icc b.lo b.hi))
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (provider : CanonicalOriginalPrimeAnalyticProvider.Provider
  (A := A) (P := P) (R := R) theta)



local notation "box" => b
local notation "volume" => primitive
local notation "allOrders" => OriginalMeshPairedStep.orders
  (A := A) (σ := σ) (η := η) (hS := hS) b theta outputOrders primitive
local notation "inputOrders" => OriginalMeshPairedStep.profileOrders
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
local notation "finalConstant" => OriginalMeshPairedStep.constant
  (ω := ω) μv ν μ C hDiff Drecipe hD b mesh theta outputOrders primitive provider
local notation "finalDegree" => OriginalMeshPairedStep.degree b
local notation "scaleThreshold" => OriginalMeshPairedStep.threshold
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
variable (hmesh : 0 ≤ mesh)
variable (hfit : (data ξ).geometry.fitsMesh mesh)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
variable (amplitude : ℝ) (hamplitude : 1 ≤ amplitude)
variable (profiles : RawProfileWindow rowDomain heightDomain (Set.Icc b.lo b.hi)
  inputOrders (data ξ) amplitude)
variable (hrows : ∀ u ∈ pairedRows (data ξ) a Z, u ∈ rowDomain)
variable (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable (htheta : (data ξ).theta = theta)
variable (hlower : b.hi⁻¹ ≤ b.lo)
variable (hplaces : CanonicalLiteralExceptionalArithmetic.thetaBadPrimes theta ⊆ A.Sf)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hone : (1 : HeckeCharacter K) ∈ (data ξ).theta)
variable (hbackground : (data ξ).plainBackground⁻¹ ∈ (data ξ).theta ∨
  ¬ FiniteOrder (data ξ).plainBackground)
variable (hslot : ∀ i, (data ξ).slotCoefficient i ∈ (data ξ).theta)
variable (hslotInverse : ∀ i, ((data ξ).slotCoefficient i)⁻¹ ∈ (data ξ).theta)

local notation "control" => CanonicalPrimitiveEngineControl.value amplitude t

local notation "produced" => originalMeshPairedEngineStep
  (μv := μv) (ν := ν) (μ := μ) (C := C)
  (hDiff := hDiff) (Drecipe := Drecipe) (hD := hD) (b := b)
  (mesh := mesh) (theta := theta) (outputOrders := outputOrders) (primitive := primitive)
  (provider := provider) (Q := Q) (W := W) (ξ := ξ)
  (hroot := hroot) (hemb := hemb) (a := a) (Z := Z)
  (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
  (domain := domain) (hbudget := hbudget) (hwidth := hwidth) (hpadding := hpadding)
  (hcap := hcap) (hlarge := hlarge) (hmesh := hmesh) (hfit := hfit)
  (amplitude := amplitude) (hamplitude := hamplitude) (profiles := profiles) (hrows := hrows)
  (htime := htime) (hprime := hprime) (htheta := htheta) (hlower := hlower)
  (hplaces := hplaces) (boundary := boundary) (hone := hone) (hbackground := hbackground)
  (hslot := hslot) (hslotInverse := hslotInverse)

variable (narrowLo narrowHi : ℝ) (hnarrowLo : 0 < narrowLo) (hnarrowHi : 1 ≤ narrowHi)
variable (hnarrowHiLe : narrowHi ≤ b.hi)
variable (narrowProfiles : RawProfileWindow rowDomain heightDomain (Set.Icc narrowLo narrowHi)
  inputOrders (data ξ) amplitude)

/-- The full analytic producer's same children retain the original
positive annulus, independently of the exceptional analytic box. -/
theorem narrowAnnulusSupport : EngineAnnulusSupport produced narrowLo narrowHi allOrders := by
  subst theta
  let theta : Finset (HeckeCharacter K) := (data ξ).theta
  have hc : 0 < finalConstant := OriginalMeshPairedStep.constant_pos
    (ω := ω) μv ν μ C hDiff Drecipe hD b mesh (data ξ).theta outputOrders primitive provider
  by_cases hempty : pairedRows (data ξ) a Z = ∅
  · apply EngineAnnulusSupport.of_zero_branches
    simp only [originalMeshPairedEngineStep, dif_pos hempty,
      PairedEngineConclusion.ofEmptyParent_branches]
  · have hnonempty : (pairedRows (data ξ) a Z).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let reference := hnonempty.choose
    have href : reference ∈ pairedRows (data ξ) a Z := hnonempty.choose_spec
    let rawWindow := profiles
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
    have h := OriginalMeshUniformSupport.narrowAnnulusSupport
      (narrowLo := narrowLo) (narrowHi := narrowHi)
      (hnarrowLo := hnarrowLo) (hnarrowHi := hnarrowHi)
      (hnarrowHiLe := hnarrowHiLe) (narrowProfiles := narrowProfiles)
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
      (hcap := hcap) (hlarge := hlarge) (mesh := mesh) (hmesh := hmesh) (hfit := hfit)
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
          (hlower := hlower)
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
          (hlower := hlower)
          (horders := hvolOrders) (hexceptionalLarge := hexceptionalLarge)
          (pool := selection.pool) (hdensity := selection.density_pos))
    simpa only [originalMeshPairedEngineStep, dif_neg hempty] using h

end HeckeSkeleton.Moments.EngineInduction.OriginalMeshPairedSupport

#print axioms HeckeSkeleton.Moments.EngineInduction.OriginalMeshPairedSupport.narrowAnnulusSupport
