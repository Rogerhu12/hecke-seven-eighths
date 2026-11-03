import ThetaGlobal.GlobalProjectSheetProfiles
import ThetaGlobal.GlobalProjectForwardCoefficients
import ThetaGlobal.GlobalProjectOrbitAbsolute
import DedekindZetaZeroFree.Theta.Unfolding.RationalOrbitFrequencyEquivalence
import DedekindZetaZeroFree.Theta.Profiles.ReflectedOrbitSmoothing

/-!
# Absolute actual orbit evaluation for the high K-type source

The compact-domain Fourier mass estimates supply the integrability
needed to unfold each whole S-unit orbit.  No profile-integrability
input is introduced.  The resulting terms use the normalized actual
direct and reflected Mellin sheets and the same source scalar.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 6000
noncomputable section

namespace ThetaGlobal.GlobalProjectOrbitEvaluation

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators Pointwise

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
  (C : FiniteFixedSource.Source R θ) (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization
local notation "Q" => C.projected.base.sources
local notation "T" => C.projected.base.realization
local notation "k" => QuotientGroup.mk' R.A.sixthPowers
local notation "B" => R.probe.correction.B
local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

local instance : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
local instance : Countable Fˣ :=
  Function.Injective.countable (f := ((↑) : Fˣ → F)) fun _ _ h => Units.ext h
local instance : Countable R.A.Gamma1 :=
  Countable.of_equiv (ThetaReflectionData.rationalGamma R.A) (gammaEquiv R).toEquiv
local instance : C.transport.groupHaar.IsHaarMeasure := C.transport.groupHaar_isHaar

def gammaFrequency (a : Fˣ) (γ : R.A.Gamma1) : Fˣ :=
  ((gammaEquiv R).symm γ).val * a

theorem gammaFrequency_injective (a : Fˣ) : Function.Injective (gammaFrequency R a) := by
  intro γ δ h
  apply (gammaEquiv R).symm.injective
  apply Subtype.ext
  exact mul_right_cancel h

theorem gammaFrequency_diagonal (a : Fˣ) (γ : R.A.Gamma1) :
    R.A.diagonal (gammaFrequency R a γ) = γ.val.val * R.A.diagonal a := by
  rw [gammaFrequency, map_mul]
  have h := gammaEquiv_val R ((gammaEquiv R).symm γ)
  simp only [MulEquiv.apply_symm_apply] at h
  rw [← h]

theorem gammaFrequency_class (a : Fˣ) (γ : R.A.Gamma1) :
    k (R.A.diagonal (gammaFrequency R a γ)) = k (R.A.diagonal a) := by
  rw [gammaFrequency_diagonal, map_mul, GlobalProjectUnfolding.gamma_class]
  exact one_mul (k (R.A.diagonal a))

variable (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
  (c : GlobalProjectWeightedDigits.Digits R m → ℂ)

def term (b : Bool) (a : Fˣ) (y : R.A.G) : ℂ :=
  GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) B y *
    ∑ d, c d * GlobalCoreSource.rationalPeriod T
      (GlobalProjectHighKReflection.vector R D u L.vector) (a : F)
      (signedArgument R m b y d)

def integralTerm (w : InfinitePlace F) (l : PositiveAxis)
    (Ω : Set (Sheet R.A l)) (b : Bool) (a : Fˣ) : ℂ :=
  ∫ y in Ω, term R θ C L u m c b a y.val ∂sheetHaar R.A w C.transport.groupHaar l

theorem forward_term (hR : RootAligned R) (a : Fˣ) (y : R.A.G) :
    term R θ C L u m c true a y =
      GlobalProjectForwardCoefficients.scalar R D m c a *
        GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) B y *
          GlobalProjectHighKExtraction.directProfile R D u L.vector (R.A.diagonal a * y) := by
  rw [term, GlobalProjectHighKExtraction.forward_average R D hR]
  have hphase := GlobalProjectForwardExtraction.hilbert_mul_of_class_support R
    (GlobalProjectHighKExtraction.directProfile R D u L.vector)
    (FiniteHighKDirect.global_diagonal_class_support R θ C L u) (R.A.diagonal a) y
  change _ = GlobalProjectForwardCoefficients.scalar R D m c a * _ * _
  unfold GlobalProjectForwardCoefficients.scalar
  calc
    _ = (GlobalProjectDigitProduct.forwardCoefficient R m c a *
        ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, (D).exteriorValue R p a) *
        GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) B y *
        (GlobalProjectConvention.paperHilbert R (k (R.A.diagonal a)) (k y) ^ 2 *
          GlobalProjectHighKExtraction.directProfile R D u L.vector (R.A.diagonal a * y)) := by ring
    _ = _ := by rw [hphase]

theorem reverse_term (hR : RootAligned R) (a : Fˣ) (y : R.A.G) :
    term R θ C L u m c false a y =
      GlobalProjectSignedExtraction.reverseCoefficient R D m c a *
        GlobalProjectUnfolding.reverseWeight R (GlobalTargetPeriod.period R θ u) B
          (k (R.A.diagonal a)) y *
          GlobalProjectHighKExtraction.reflectedProfile R D u L.vector (R.A.diagonal a / y) := by
  rw [term, GlobalProjectHighKExtraction.reverse_average R D hR]
  unfold GlobalProjectUnfolding.reverseWeight
  ring

def directTerm (w : InfinitePlace F) (l : PositiveAxis) (a : Fˣ) : ℂ :=
  GlobalProjectForwardCoefficients.scalar R D m c a *
    GlobalTargetPeriod.period R θ u (R.A.diagonal a) *
    (if k (R.A.diagonal a) ∈ B then 1 else 0) *
      FiniteNormalizedMellin.direct R θ C L w (q R.A a * l)

def reflectedTerm (w : InfinitePlace F) (l : PositiveAxis) (a : Fˣ) : ℂ :=
  GlobalProjectSignedExtraction.reverseCoefficient R D m c a *
    (GlobalTargetPeriod.period R θ u (R.A.diagonal a))⁻¹ *
      FiniteNormalizedMellin.reflected R θ C L u
        (GlobalProjectSheetProfiles.skeletonClass R (k (R.A.diagonal a))) w (q R.A a / l)

theorem integralTerm_norm_summable (w : InfinitePlace F) (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩm : NullMeasurableSet Ω (sheetHaar R.A w C.transport.groupHaar l))
    (hΩc : IsCompact (closure Ω)) (b : Bool) :
    Summable (fun a : Fˣ => ‖integralTerm R θ C L u m c w l Ω b a‖) := by
  have hs := GlobalProjectWeightedSheet.coefficient_abs_summable R m c w
    C.transport.groupHaar l Ω hΩm hΩc θ u
    (GlobalProjectHighKReflection.vector R D u L.vector) b
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro a
  exact norm_integral_le_integral_norm _

theorem reverse_orbit_term (hR : RootAligned R)
    (hc : GlobalProjectWeightedDigits.ReindexInvariant R m c)
    (a : Fˣ) (l : PositiveAxis) (γ : R.A.Gamma1) (y : Sheet R.A l) :
    term R θ C L u m c false (gammaFrequency R a γ⁻¹) y.val =
      GlobalProjectUnfolding.reverseWeight R (GlobalTargetPeriod.period R θ u) B
        (k (R.A.diagonal a)) y.val *
        (GlobalProjectSignedExtraction.reverseCoefficient R D m c a *
          GlobalProjectHighKExtraction.reflectedProfile R D u L.vector
            (sheetDiv R.A a l (γ • y)).val) := by
  have hr := GlobalProjectOrbitCoefficients.reverseCoefficient_gamma R D m c hc a
    ((gammaEquiv R).symm γ⁻¹)
  change GlobalProjectSignedExtraction.reverseCoefficient R D m c
    (gammaFrequency R a γ⁻¹) = _ at hr
  rw [reverse_term R θ C L u m c hR, hr, gammaFrequency_class, gammaFrequency_diagonal]
  have hy : (sheetDiv R.A a l (γ • y)).val =
      γ.val.val⁻¹ * R.A.diagonal a / y.val := by
    change R.A.diagonal a / (γ.val.val * y.val) = _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  rw [hy]
  change _ = _ * (_ * GlobalProjectHighKExtraction.reflectedProfile R D u L.vector
    (γ.val.val⁻¹ * R.A.diagonal a / y.val))
  have hinv : ((γ⁻¹ : R.A.Gamma1).val.val) = (γ.val.val)⁻¹ := rfl
  rw [hinv]
  ring

/-- Reflected orbit unfolding, with every integrability and absolute
summability condition supplied by the actual compact Fourier source. -/
theorem reverse_orbit (hR : RootAligned R)
    (hc : GlobalProjectWeightedDigits.ReindexInvariant R m c)
    (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (w : InfinitePlace F) (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w C.transport.groupHaar l))
    (hΩc : IsCompact (closure Ω)) (a : Fˣ) :
    Summable (fun γ : R.A.Gamma1 => integralTerm R θ C L u m c w l Ω false
      (gammaFrequency R a γ)) ∧
    (∑' γ : R.A.Gamma1, integralTerm R θ C L u m c w l Ω false (gammaFrequency R a γ)) =
      GlobalProjectSheetProfiles.commonScalar R θ C L u * reflectedTerm R θ C L u m c w l a := by
  let μ := sheetHaar R.A w C.transport.groupHaar l
  let χ := GlobalTargetPeriod.period R θ u
  let κ := k (R.A.diagonal a)
  let r := GlobalProjectSignedExtraction.reverseCoefficient R D m c a
  let f := fun z : Sheet R.A (q R.A a / l) =>
    r * GlobalProjectHighKExtraction.reflectedProfile R D u L.vector z.val
  have hi (γ : R.A.Gamma1) : IntegrableOn (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.reverseWeight R χ B κ y.val * f (sheetDiv R.A a l (γ • y))) Ω μ := by
    have h := GlobalProjectWeightedSheet.coefficient_integrable R m c w C.transport.groupHaar
      l Ω hΩc θ u (GlobalProjectHighKReflection.vector R D u L.vector) false
      (gammaFrequency R a γ⁻¹ : F)
    exact h.congr (Filter.Eventually.of_forall fun y => reverse_orbit_term R θ C L u m c hR hc a l γ y)
  have hs : Summable (fun γ : R.A.Gamma1 => ∫ y in Ω,
      ‖GlobalProjectUnfolding.reverseWeight R χ B κ y.val * f (sheetDiv R.A a l (γ • y))‖ ∂μ) := by
    have h := (GlobalProjectWeightedSheet.coefficient_abs_summable R m c w
      C.transport.groupHaar l Ω hΩ.nullMeasurableSet hΩc θ u
      (GlobalProjectHighKReflection.vector R D u L.vector) false).comp_injective
        ((gammaFrequency_injective R a).comp (Equiv.inv R.A.Gamma1).injective)
    apply h.congr
    intro γ
    apply integral_congr_ae
    filter_upwards [] with y
    exact congrArg norm (reverse_orbit_term R θ C L u m c hR hc a l γ y)
  have h := GlobalProjectOrbitAbsolute.weighted_unfold_of_pieces hΩ
    (sheetDiv R.A a l).toMeasurableEquiv
    (sheetDiv_measurePreserving R.A w C.transport.groupHaar a l)
    (fun y : Sheet R.A l => GlobalProjectUnfolding.reverseWeight R χ B κ y.val)
    (fun z : Sheet R.A (q R.A a / l) => GlobalProjectUnfolding.reflectedWeight R χ B κ z.val)
    f (χ (R.A.diagonal a))⁻¹
    (fun γ y => GlobalProjectUnfolding.reverseWeight_gamma R χ B
      (GlobalTargetPeriod.period_gamma R θ hS u) κ γ y.val)
    (fun y => GlobalProjectUnfolding.reverseWeight_div_transport R χ B (R.A.diagonal a) y.val)
    hi hs
  have hp (γ : R.A.Gamma1) : integralTerm R θ C L u m c w l Ω false
      (gammaFrequency R a γ⁻¹) =
      ∫ y in Ω, GlobalProjectUnfolding.reverseWeight R χ B κ y.val *
        f (sheetDiv R.A a l (γ • y)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact reverse_orbit_term R θ C L u m c hR hc a l γ y
  have hs' := h.1.congr (fun γ => (hp γ).symm)
  have he' := (tsum_congr hp).trans h.2
  have htarget : (∫ z : Sheet R.A (q R.A a / l),
      GlobalProjectUnfolding.reflectedWeight R χ B κ z.val * f z
      ∂sheetHaar R.A w C.transport.groupHaar (q R.A a / l)) =
      r * (GlobalProjectSheetProfiles.commonScalar R θ C L u *
        FiniteNormalizedMellin.reflected R θ C L u
          (GlobalProjectSheetProfiles.skeletonClass R κ) w (q R.A a / l)) := by
    calc
      _ = r * ∫ z : Sheet R.A (q R.A a / l),
          GlobalProjectUnfolding.reflectedWeight R χ B κ z.val *
            GlobalProjectHighKExtraction.reflectedProfile R D u L.vector z.val
          ∂sheetHaar R.A w C.transport.groupHaar (q R.A a / l) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [f]
        ring
      _ = _ := by rw [GlobalProjectSheetProfiles.reflected_sheet R θ C L]
  rw [htarget] at he'
  have hinv := (Equiv.inv R.A.Gamma1).tsum_eq
    (fun γ => integralTerm R θ C L u m c w l Ω false (gammaFrequency R a γ))
  simp only [Equiv.inv_apply] at hinv
  refine ⟨?_, ?_⟩
  · have hh := hs'.comp_injective (Equiv.inv R.A.Gamma1).injective
    simpa only [Function.comp_def, Equiv.inv_apply, inv_inv] using hh
  · rw [← hinv, he']
    dsimp only [reflectedTerm, r, χ, κ]
    ring

theorem forward_orbit_term (hR : RootAligned R)
    (hc : ∀ (a : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A),
      GlobalProjectForwardCoefficients.scalar R D m c (γ.val * a) =
        GlobalProjectForwardCoefficients.scalar R D m c a)
    (a : Fˣ) (l : PositiveAxis) (γ : R.A.Gamma1) (y : Sheet R.A l) :
    term R θ C L u m c true (gammaFrequency R a γ) y.val =
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) B y.val *
        (GlobalProjectForwardCoefficients.scalar R D m c a *
          GlobalProjectHighKExtraction.directProfile R D u L.vector
            (sheetMul R.A a l (γ • y)).val) := by
  have hr := hc a ((gammaEquiv R).symm γ)
  change GlobalProjectForwardCoefficients.scalar R D m c (gammaFrequency R a γ) = _ at hr
  rw [forward_term R θ C L u m c hR, hr, gammaFrequency_diagonal]
  have hy : (sheetMul R.A a l (γ • y)).val =
      γ.val.val * R.A.diagonal a * y.val := by
    change R.A.diagonal a * (γ.val.val * y.val) = _
    ac_rfl
  rw [hy]
  ring

/-- Direct orbit unfolding.  The invariant scalar is later supplied by
the literal finite forward-mask table and the actual exterior model. -/
theorem forward_orbit (hR : RootAligned R)
    (hc : ∀ (a : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A),
      GlobalProjectForwardCoefficients.scalar R D m c (γ.val * a) =
        GlobalProjectForwardCoefficients.scalar R D m c a)
    (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (w : InfinitePlace F) (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w C.transport.groupHaar l))
    (hΩc : IsCompact (closure Ω)) (a : Fˣ) :
    Summable (fun γ : R.A.Gamma1 => integralTerm R θ C L u m c w l Ω true
      (gammaFrequency R a γ)) ∧
    (∑' γ : R.A.Gamma1, integralTerm R θ C L u m c w l Ω true (gammaFrequency R a γ)) =
      GlobalProjectSheetProfiles.commonScalar R θ C L u * directTerm R θ C L u m c w l a := by
  let μ := sheetHaar R.A w C.transport.groupHaar l
  let χ := GlobalTargetPeriod.period R θ u
  let κ := k (R.A.diagonal a)
  let r := GlobalProjectForwardCoefficients.scalar R D m c a
  let f := fun z : Sheet R.A (q R.A a * l) =>
    r * GlobalProjectHighKExtraction.directProfile R D u L.vector z.val
  have hi (γ : R.A.Gamma1) : IntegrableOn (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.weight R χ B y.val * f (sheetMul R.A a l (γ • y))) Ω μ := by
    have h := GlobalProjectWeightedSheet.coefficient_integrable R m c w C.transport.groupHaar
      l Ω hΩc θ u (GlobalProjectHighKReflection.vector R D u L.vector) true
      (gammaFrequency R a γ : F)
    exact h.congr (Filter.Eventually.of_forall fun y => forward_orbit_term R θ C L u m c hR hc a l γ y)
  have hs : Summable (fun γ : R.A.Gamma1 => ∫ y in Ω,
      ‖GlobalProjectUnfolding.weight R χ B y.val * f (sheetMul R.A a l (γ • y))‖ ∂μ) := by
    have h := (GlobalProjectWeightedSheet.coefficient_abs_summable R m c w
      C.transport.groupHaar l Ω hΩ.nullMeasurableSet hΩc θ u
      (GlobalProjectHighKReflection.vector R D u L.vector) true).comp_injective
        (gammaFrequency_injective R a)
    apply h.congr
    intro γ
    apply integral_congr_ae
    filter_upwards [] with y
    exact congrArg norm (forward_orbit_term R θ C L u m c hR hc a l γ y)
  have h := GlobalProjectOrbitAbsolute.weighted_unfold_of_pieces hΩ
    (sheetMul R.A a l).toMeasurableEquiv
    (sheetMul_measurePreserving R.A w C.transport.groupHaar a l)
    (fun y : Sheet R.A l => GlobalProjectUnfolding.weight R χ B y.val)
    (fun z : Sheet R.A (q R.A a * l) => GlobalProjectUnfolding.directWeight R χ B κ z.val)
    f (χ (R.A.diagonal a))
    (fun γ y => GlobalProjectUnfolding.weight_gamma R χ B
      (GlobalTargetPeriod.period_gamma R θ hS u) γ y.val)
    (fun y => GlobalProjectUnfolding.weight_mul_transport R χ B (R.A.diagonal a) y.val)
    hi hs
  have hp (γ : R.A.Gamma1) : integralTerm R θ C L u m c w l Ω true
      (gammaFrequency R a γ) =
      ∫ y in Ω, GlobalProjectUnfolding.weight R χ B y.val *
        f (sheetMul R.A a l (γ • y)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact forward_orbit_term R θ C L u m c hR hc a l γ y
  have htarget : (∫ z : Sheet R.A (q R.A a * l),
      GlobalProjectUnfolding.directWeight R χ B κ z.val * f z
      ∂sheetHaar R.A w C.transport.groupHaar (q R.A a * l)) =
      r * ((if κ ∈ B then 1 else 0) * GlobalProjectSheetProfiles.commonScalar R θ C L u *
        FiniteNormalizedMellin.direct R θ C L w (q R.A a * l)) := by
    calc
      _ = r * ∫ z : Sheet R.A (q R.A a * l),
          GlobalProjectUnfolding.directWeight R χ B κ z.val *
            GlobalProjectHighKExtraction.directProfile R D u L.vector z.val
          ∂sheetHaar R.A w C.transport.groupHaar (q R.A a * l) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [f]
        ring
      _ = _ := by rw [GlobalProjectSheetProfiles.direct_sheet R θ C L]
  have he := (tsum_congr hp).trans h.2
  rw [htarget] at he
  refine ⟨h.1.congr (fun γ => (hp γ).symm), he.trans ?_⟩
  dsimp only [directTerm, r, χ, κ]
  ring

end ThetaGlobal.GlobalProjectOrbitEvaluation
