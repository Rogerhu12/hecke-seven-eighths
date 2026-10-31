import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileScaleBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedIndexedKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogOrbitalKernel

/-!
# Fourier control of the same canonical capacity children

The original data below contain only the literal base data and the
individual logarithmic profile multipliers.  Their moving realization
is the actual profile record update.  No atom control, transformed
profile window, admissibility, or moment bound is stored in the data.

Finite atom control is constructed for the already selected children.
The kernel estimates come from continuous linear operators on the
original Schwartz space.  The canonical first and second charts supply
exactly `CanonicalLogOrbital.fourierCLM`; no kernel estimate is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLogProfiles

inductive ProfileAtomIndex (n : ℕ) where
  | left
  | right
  | prime (i : Fin n)

/-- Original data, fixed before the Fourier variable.  The three
positivity fields concern the original profiles alone. -/
structure OriginalLogProfiles (K : Type) [Field K] [NumberField K]
    (ω ψ : HeckeCharacter K) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  original : MomentData K ω ψ
  left : Atom V
  right : Atom V
  slot : Fin original.geometry.slotCount → Atom V
  left_positive : PositivePlainProfile original.plainTest₁
  right_positive : PositivePlainProfile original.plainTest₂
  slot_positive : ∀ i, PositivePrimeProfile (original.geometry.slots i)

namespace OriginalLogProfiles

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (D : OriginalLogProfiles K ω ψ V)

def moving (ξ : V) : MomentData K ω ψ :=
  data D.original D.left D.right D.slot D.left_positive D.right_positive D.slot_positive ξ

def atom : ProfileAtomIndex D.original.geometry.slotCount → Atom V
  | .left => D.left
  | .right => D.right
  | .prime i => D.slot i

def amplitude (a B : ℝ) (ha : 0 < a) (orders : Finset (ℕ × ℕ)) (P : ℝ) : ℝ :=
  clippingCoefficient B orders * profileAmplitude D.original D.left D.right D.slot
    (Set.Icc a B) isCompact_Icc (positiveAnnulus a B ha) orders P

theorem amplitude_nonneg (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (orders : Finset (ℕ × ℕ)) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ D.amplitude a B ha orders P :=
  mul_nonneg (zero_le_one.trans (clippingCoefficient_one_le B hB orders))
    (profileAmplitude_nonneg D.original D.left D.right D.slot (Set.Icc a B)
      isCompact_Icc (positiveAnnulus a B ha) orders hP)

theorem amplitude_bound (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (orders : Finset (ℕ × ℕ)) (δ : ℝ) (hδ : 0 ≤ δ) (R cap : ℕ)
    (directionBound L Z P : ℝ) (hD : 0 ≤ directionBound) (hL : 0 ≤ L)
    (hZ : 1 ≤ Z) (hP : 0 ≤ P) (hcount : D.original.geometry.slotCount ≤ cap)
    (hexponent : ∀ i, (D.atom i).exponent ∈ exponentPalette δ R)
    (hdirection : ∀ i, ‖(D.atom i).direction‖ ≤ directionBound)
    (hscale : ∀ i, (D.atom i).scale ≤ Z ^ L) :
    D.amplitude a B ha orders P ≤
      clippedAmplitudeConstant a B ha orders δ R cap directionBound * P * Z ^ (L * R * δ) := by
  have hraw := profileAmplitude_le_original_scale (Set.Icc a B) isCompact_Icc
    (positiveAnnulus a B ha) orders δ hδ R cap directionBound L Z P hD hL hZ hP
    D.original D.left D.right D.slot hcount
    (hexponent .left) (hexponent .right) (fun i => hexponent (.prime i))
    (hdirection .left) (hdirection .right) (fun i => hdirection (.prime i))
    (hscale .left) (hscale .right) (fun i => hscale (.prime i))
  unfold amplitude
  apply (mul_le_mul_of_nonneg_left hraw
    (zero_le_one.trans (clippingCoefficient_one_le B hB orders))).trans_eq
  unfold clippedAmplitudeConstant
  ring

theorem source_count {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}
    {source : ActualAllocatedSource A V H k}
    (cal : source.Calibration (σ := σ) ω ψ)
    (hdata : ∀ ξ, cal.data ξ = D.moving ξ) :
    source.allocation.keep.card = D.original.geometry.slotCount := by
  have h := cal.count 0
  rw [hdata 0] at h
  exact h.symm

def childControl {A : SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}
    {source : ActualAllocatedSource A V H k}
    (cal : source.Calibration (σ := σ) ω ψ) {G : cal.NormalizedCapacityData}
    (out : G.Child) (hdata : ∀ ξ, cal.data ξ = D.moving ξ)
    (t : ℝ) (ht : ∀ ξ, cal.height ξ = t)
    {X : Type*} [NormedAddCommGroup X] [MeasureSpace X] [BorelSpace X]
    (parameter : X → V) (hparameter : Continuous parameter) :
    ActualFiniteFamilyControl
      (fun x => out.rawData (parameter x)) out.retainedCount
      (fun x => out.raw_count (parameter x)) out.parameters source.base
      (fun x => cal.height (parameter x)) :=
  childFiniteControl cal out D.original D.left D.right D.slot
    D.left_positive D.right_positive D.slot_positive hdata t ht parameter hparameter

end OriginalLogProfiles

section KernelOperators

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem fixedKernel_source_bound
    (T : 𝓢(W, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (target : Finset (ℕ × ℕ)) :
    ∃ source : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : 𝓢(W, ℂ),
      target.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T φ) ≤
        C * source.sup (schwartzSeminormFamily ℝ W ℂ) φ := by
  let q : Seminorm ℝ 𝓢(W, ℂ) :=
    (target.sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (Seminorm.continuous_finsetSup (fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i)).comp T.continuous
  obtain ⟨source, C, _hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ W ℂ) q hq
  exact ⟨source, (C : ℝ), C.coe_nonneg, fun φ => Seminorm.le_def.mp hbound φ⟩

/-- Both original source seminorm sets and one coefficient are selected
before either archimedean test or any finite label.  Canonical orbital
Fourier kernels are obtained by taking their already constructed CLMs. -/
theorem fixedKernelPair_source_bounds
    (T₁ T₂ : 𝓢(W, ℂ) →L[ℝ] 𝓢(ℝ, ℂ))
    (target₁ target₂ : Finset (ℕ × ℕ)) :
    ∃ source : Finset (ℕ × ℕ), ∃ C : ℝ, 1 ≤ C ∧ ∀ φ : 𝓢(W, ℂ),
      target₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₁ φ) ≤
          C * source.sup (schwartzSeminormFamily ℝ W ℂ) φ ∧
      target₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₂ φ) ≤
          C * source.sup (schwartzSeminormFamily ℝ W ℂ) φ := by
  obtain ⟨source₁, C₁, hC₁, h₁⟩ := fixedKernel_source_bound T₁ target₁
  obtain ⟨source₂, C₂, hC₂, h₂⟩ := fixedKernel_source_bound T₂ target₂
  let source := source₁ ∪ source₂
  let C := 1 + C₁ + C₂
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have h₁C : C₁ ≤ C := by dsimp only [C]; linarith
  have h₂C : C₂ ≤ C := by dsimp only [C]; linarith
  refine ⟨source, C, hC, fun φ => ?_⟩
  have hs₁ : source₁.sup (schwartzSeminormFamily ℝ W ℂ) φ ≤
      source.sup (schwartzSeminormFamily ℝ W ℂ) φ :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) φ
  have hs₂ : source₂.sup (schwartzSeminormFamily ℝ W ℂ) φ ≤
      source.sup (schwartzSeminormFamily ℝ W ℂ) φ :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) φ
  exact ⟨(h₁ φ).trans (mul_le_mul h₁C hs₁ (apply_nonneg _ _) (zero_le_one.trans hC)),
    (h₂ φ).trans (mul_le_mul h₂C hs₂ (apply_nonneg _ _) (zero_le_one.trans hC))⟩

end KernelOperators

section FamilyAtoms

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {Z : ℝ}

/-- The selected children are read from the existing family.  All
their finite atom fields are produced by `childFiniteControl`, with no
second invocation of the capacity producer. -/
def familyFourierControl
    (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
    (labels : Finset Λ)
    (left right : Λ → OriginalLogProfiles K ω ψ (WithLp 2 (U × E)))
    (leftTime rightTime : Λ → ℝ)
    (hleftData : ∀ b ξ, (family.leftCalibration b).data ξ = (left b).moving ξ)
    (hrightData : ∀ b ξ, (family.rightCalibration b).data ξ = (right b).moving ξ)
    (hleftTime : ∀ b ξ, (family.leftCalibration b).height ξ = leftTime b)
    (hrightTime : ∀ b ξ, (family.rightCalibration b).height ξ = rightTime b)
    (B₁ B₂ : Λ → ℝ) (hB₁ : ∀ b ∈ labels, 0 ≤ B₁ b) (hB₂ : ∀ b ∈ labels, 0 ≤ B₂ b)
    (J₁₁ J₁₂ J₂₁ J₂₂ : ℕ)
    (hleftRadius : ∀ b ∈ labels, ∀ z, (family.leftCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₁ b) J₁₁ J₁₂ z)
    (hrightRadius : ∀ b ∈ labels, ∀ z, (family.rightCapacity b).radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (B₂ b) J₂₁ J₂₂ z) :
    family.FourierAtomControl labels J₁₁ J₁₂ J₂₁ J₂₂ := by
  refine
    { left := ?_
      right := ?_
      leftAmplitude := B₁
      rightAmplitude := B₂
      left_nonneg := hB₁
      right_nonneg := hB₂
      left_radius := hleftRadius
      right_radius := hrightRadius }
  · intro b
    have h := (left b.val).childControl (family.leftCalibration b.val)
      (family.leftChild labels b) (hleftData b.val) (leftTime b.val) (hleftTime b.val)
      (WithLp.toLp 2) (WithLp.prod_continuous_toLp 2 U E)
    simpa only [family.left_base b.val, ActualNormalizedPairFamily.leftParameters] using h
  · intro b
    have h := (right b.val).childControl (family.rightCalibration b.val)
      (family.rightChild labels b) (hrightData b.val) (rightTime b.val) (hrightTime b.val)
      (WithLp.toLp 2) (WithLp.prod_continuous_toLp 2 U E)
    simpa only [family.right_base b.val, ActualNormalizedPairFamily.rightParameters] using h

end FamilyAtoms

section CompleteWindows

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [MeasurableSpace (WithLp 2 (ℝ × ℝ))] [BorelSpace (WithLp 2 (ℝ × ℝ))]

/-- Complete original-profile control for one and the same family.

`orders` fixes the child-radius Fourier degree before the mass theorem
requests its separate `target₁` and `target₂` kernel seminorms.  The
returned `source` enlarges only the original archimedean control; it
does not change the radius degree.  All four mass-profile degrees are
one.  The sole family identities below are the literal data, frozen
height, kernel and radius definitions.
-/
theorem exists_family_profile_controls
    (orders : Finset (ℕ × ℕ)) (R cap : ℕ)
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B)
    (δ directionBound L τ : ℝ) (hδ : 0 ≤ δ)
    (hD : 0 ≤ directionBound) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hbudget : L * R * δ ≤ τ)
    (T₁ T₂ : 𝓢(W, ℂ) →L[ℝ] 𝓢(ℝ, ℂ))
    (target₁ target₂ : Finset (ℕ × ℕ)) :
    ∃ source : Finset (ℕ × ℕ), ∃ Cprofile : ℝ, 1 ≤ Cprofile ∧
      ∀ {Λ : Type*} (Z P : ℝ), 1 ≤ Z → 1 ≤ P →
      ∀ (family : ActualNormalizedPairFamily A σ (WithLp 2 (ℝ × ℝ)) Λ ω ψ Z)
        (labels : Finset Λ)
        (left right : Λ → OriginalLogProfiles K ω ψ (WithLp 2 (ℝ × ℝ)))
        (leftTime rightTime : Λ → ℝ),
      (∀ b ξ, (family.leftCalibration b).data ξ = (left b).moving ξ) →
      (∀ b ξ, (family.rightCalibration b).data ξ = (right b).moving ξ) →
      (∀ b ξ, (family.leftCalibration b).height ξ = leftTime b) →
      (∀ b ξ, (family.rightCalibration b).height ξ = rightTime b) →
      ∀ (φ₁ φ₂ : Λ → 𝓢(W, ℂ)) (F₁ F₂ : Λ → 𝓢(ℝ, ℂ)) (outer : Λ → ℝ),
      (∀ b ∈ labels, F₁ b = T₁ (φ₁ b)) →
      (∀ b ∈ labels, F₂ b = T₂ (φ₂ b)) →
      (∀ b ∈ labels, source.sup (schwartzSeminormFamily ℝ W ℂ) (φ₁ b) ≤ P) →
      (∀ b ∈ labels, source.sup (schwartzSeminormFamily ℝ W ℂ) (φ₂ b) ≤ P) →
      (∀ b ∈ labels, 0 ≤ outer b) →
      (∀ b ∈ labels, (left b).original.geometry.slotCount ≤ cap) →
      (∀ b ∈ labels, (right b).original.geometry.slotCount ≤ cap) →
      (∀ b ∈ labels, ∀ i, ((left b).atom i).exponent ∈ exponentPalette δ R) →
      (∀ b ∈ labels, ∀ i, ((right b).atom i).exponent ∈ exponentPalette δ R) →
      (∀ b ∈ labels, ∀ i, ‖((left b).atom i).direction‖ ≤ directionBound) →
      (∀ b ∈ labels, ∀ i, ‖((right b).atom i).direction‖ ≤ directionBound) →
      (∀ b ∈ labels, ∀ i, ((left b).atom i).scale ≤ Z ^ L) →
      (∀ b ∈ labels, ∀ i, ((right b).atom i).scale ≤ Z ^ L) →
      (∀ b ∈ labels, ∀ z, (family.leftCapacity b).radius (WithLp.toLp 2 z) =
        polynomialProfileRadius ((left b).amplitude a B ha orders P)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z) →
      (∀ b ∈ labels, ∀ z, (family.rightCapacity b).radius (WithLp.toLp 2 z) =
        polynomialProfileRadius ((right b).amplitude a B ha orders P)
          (orders.sup Prod.snd) (orders.sup Prod.snd) z) →
      ∃ atoms : family.FourierAtomControl labels
        (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd),
        InternalMassAssembly.ProfileWindows family labels F₁ F₂ outer
          (fun b => (left b).amplitude a B ha orders P)
          (fun b => (right b).amplitude a B ha orders P) (Cprofile * P * Z ^ τ)
          cap (orders.sup Prod.snd) (orders.sup Prod.snd)
          (orders.sup Prod.snd) (orders.sup Prod.snd) 1 1 1 1 target₁ target₂ := by
  obtain ⟨source, Ckernel, hCkernel, hkernel⟩ :=
    fixedKernelPair_source_bounds T₁ T₂ target₁ target₂
  let Cclip := clippedAmplitudeConstant a B ha orders δ R cap directionBound
  let Cprofile := Cclip + Ckernel
  have hCclip : 1 ≤ Cclip := clippedAmplitudeConstant_one_le a B ha hB orders δ R cap directionBound hD
  have hCprofile : 1 ≤ Cprofile := by dsimp only [Cprofile]; linarith
  have hclip_le : Cclip ≤ Cprofile := by dsimp only [Cprofile]; linarith
  have hkernel_le : Ckernel ≤ Cprofile := by dsimp only [Cprofile]; linarith
  refine ⟨source, Cprofile, hCprofile, ?_⟩
  intro Λ Z P hZ hP family labels left right leftTime rightTime
    hleftData hrightData hleftTime hrightTime φ₁ φ₂ F₁ F₂ outer
    hF₁ hF₂ hφ₁ hφ₂ houter hleftCount hrightCount hleftExp hrightExp
    hleftDirection hrightDirection hleftScale hrightScale hleftRadius hrightRadius
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hprofile0 : 0 ≤ Cprofile := zero_le_one.trans hCprofile
  have hpower : 1 ≤ Z ^ τ := Real.one_le_rpow hZ hτ.le
  have hleftNonneg (b : Λ) : 0 ≤ (left b).amplitude a B ha orders P :=
    (left b).amplitude_nonneg a B ha hB orders hP0
  have hrightNonneg (b : Λ) : 0 ≤ (right b).amplitude a B ha orders P :=
    (right b).amplitude_nonneg a B ha hB orders hP0
  let atoms := familyFourierControl family labels left right leftTime rightTime
    hleftData hrightData hleftTime hrightTime
    (fun b => (left b).amplitude a B ha orders P)
    (fun b => (right b).amplitude a B ha orders P)
    (fun b _ => hleftNonneg b) (fun b _ => hrightNonneg b)
    (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd) (orders.sup Prod.snd)
    hleftRadius hrightRadius
  have hbudgetComparison : Cclip * P * Z ^ (L * R * δ) ≤ Cprofile * P * Z ^ τ :=
    mul_le_mul (mul_le_mul_of_nonneg_right hclip_le hP0)
      (Real.rpow_le_rpow_of_exponent_le hZ hbudget)
      (Real.rpow_nonneg hZ0 _) (mul_nonneg hprofile0 hP0)
  have hkernelComparison : Ckernel * P ≤ Cprofile * P * Z ^ τ :=
    (mul_le_mul_of_nonneg_right hkernel_le hP0).trans
      (le_mul_of_one_le_right (mul_nonneg hprofile0 hP0) hpower)
  refine ⟨atoms,
    { outer_nonneg := houter
      left_radius_nonneg := fun b _ => hleftNonneg b
      right_radius_nonneg := fun b _ => hrightNonneg b
      left_slots := ?_
      right_slots := ?_
      left_radius := hleftRadius
      right_radius := hrightRadius
      left_radius_power := ?_
      right_radius_power := ?_
      first_kernel_power := ?_
      second_kernel_power := ?_ }⟩
  · intro b hb
    rw [(left b).source_count (family.leftCalibration b) (hleftData b)]
    exact hleftCount b hb
  · intro b hb
    rw [(right b).source_count (family.rightCalibration b) (hrightData b)]
    exact hrightCount b hb
  · intro b hb
    rw [pow_one]
    exact ((left b).amplitude_bound a B ha hB orders δ hδ R cap directionBound L Z P
      hD hL hZ hP0 (hleftCount b hb) (hleftExp b hb)
      (hleftDirection b hb) (hleftScale b hb)).trans hbudgetComparison
  · intro b hb
    rw [pow_one]
    exact ((right b).amplitude_bound a B ha hB orders δ hδ R cap directionBound L Z P
      hD hL hZ hP0 (hrightCount b hb) (hrightExp b hb)
      (hrightDirection b hb) (hrightScale b hb)).trans hbudgetComparison
  · intro b hb
    rw [pow_one, hF₁ b hb]
    exact ((hkernel (φ₁ b)).1.trans
      (mul_le_mul_of_nonneg_left (hφ₁ b hb) (zero_le_one.trans hCkernel))).trans hkernelComparison
  · intro b hb
    rw [pow_one, hF₂ b hb]
    exact ((hkernel (φ₂ b)).2.trans
      (mul_le_mul_of_nonneg_left (hφ₂ b hb) (zero_le_one.trans hCkernel))).trans hkernelComparison

end CompleteWindows
end CanonicalLogProfiles
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.fixedKernelPair_source_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.familyFourierControl
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.exists_family_profile_controls
