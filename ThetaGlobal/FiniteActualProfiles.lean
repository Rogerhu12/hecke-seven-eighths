import ThetaGlobal.FiniteHighKDirect
import ThetaGlobal.GammaDeconvolverProject

/-!
# The normalized Mellin profiles are measured coefficients of one source

The direct and reflected functions are both computed from the same
actual high K-type tensor.  Their common nonzero scalar is displayed
before cancellation.  Weighted L1 of both sheet functions is deduced
from their local integrability and the stored norm-sheet disintegration.
The direct Mellin transform is the concrete Gamma deconvolver profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.FiniteActualProfiles

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteLocalHighK ThetaGlobal.FiniteSheetMellin
open scoped NumberField Classical BigOperators

section SheetL1

variable {T X G : Type*} [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace G]
  {ν : Measure T} {μ : Measure X} {ξ : Measure G} [SigmaFinite ν] [SigmaFinite μ]

theorem weighted_sheet_integrable
    (e : T × X ≃ᵐ G) (he : MeasurePreserving e (ν.prod μ) ξ)
    (normCoordinate : G → T) (hnorm : ∀ z, normCoordinate (e z) = z.1)
    (weight : T → ℂ) (W : G → ℂ)
    (hW : Integrable (fun g => weight (normCoordinate g) * W g) ξ) :
    Integrable (fun t => weight t * SheetMellin.sheetProfile (μ := μ) e W t) ν := by
  have hi : Integrable (fun z : T × X => weight z.1 * W (e z)) (ν.prod μ) := by
    apply (he.integrable_comp_of_integrable hW).congr
    exact Filter.Eventually.of_forall fun z => by simp only [Function.comp_apply, hnorm]
  apply hi.integral_prod_left.congr
  exact Filter.Eventually.of_forall fun t => integral_const_mul (weight t) _

end SheetL1

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
variable (C : FiniteFixedSource.Source R θ) (L : Input R θ C)

local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local notation "D" => C.projected.base.factorization
local notation "Q" => C.projected.base.sources
local notation "M" => FiniteLocalHighK.finiteMellinData R θ C L

local instance : MeasurableSpace R.A.G1 := borel _
local instance : BorelSpace R.A.G1 := ⟨rfl⟩

def normalizingScalar (u : R.A.UnitQuotient) : ℂ :=
  fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1 *
    reflectedConstant R θ C L

theorem normalizingScalar_ne_zero (u : R.A.UnitQuotient) :
    normalizingScalar R θ C L u ≠ 0 :=
  mul_ne_zero
    (FiniteHighKTensor.source_scalar_nonzero R D
      (FiniteFixedSource.Source.period_nonzero R θ C) u L.vector L.source_nonzero)
    (reflectedConstant_nonzero R θ C L)

def directPoint (u : R.A.UnitQuotient) (z : R.A.G) : ℂ :=
  (GlobalTargetPeriod.period R θ u z)⁻¹ *
    fourier R Q.dq (FiniteHighKTensor.source R D u L.vector)
      (MomentSources.diagonal R z)

def reflectedPoint (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (z : R.A.G) : ℂ :=
  ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
    (ProjectFiniteClass.assemble R.A (fun p => QuotientGroup.mk (z.2 p))) *
    GlobalTargetPeriod.period R θ u z *
    fourier R Q.dq (FiniteHighKTensor.source R D u L.vector)
      (MomentSources.diagonal R z *
        KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)

theorem directPoint_eq (u : R.A.UnitQuotient) (z : R.A.G) :
    directPoint R θ C L u z =
      FiniteDirectMellin.directTensor R C.projected.cutoffs
        (fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1)
        (FiniteNormalizedMellin.archProfile R θ C L false) z :=
  FiniteHighKDirect.directTensor_eq R θ C L u z

theorem reflectedPoint_eq (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (z : R.A.G) :
    reflectedPoint R θ C L u κ z =
      reflectedTensor R D θ
        (fourier R Q.dq (FiniteHighKTensor.source R D u L.vector) 1)
        (FiniteNormalizedMellin.archProfile R θ C L true) u κ z := by
  have h := FiniteHighKWeyl.reflectedTensor_eq R D C.fullArchProduct
    (FiniteFixedSource.Source.period_nonzero R θ C) θ u L.vector L.source_nonzero κ z
  have ha : FiniteHighKWeyl.archLocal R D θ u L.vector =
      FiniteNormalizedMellin.archProfile R θ C L true := by
    funext w z
    exact FiniteLocalHighK.reflected_archLocal R θ C L u w z
  rw [ha] at h
  exact h

def directSheet (u : R.A.UnitQuotient) (v₀ : InfinitePlace F) (t : PositiveAxis) : ℂ :=
  ∫ z : R.A.G1, directPoint R θ C L u (sheetEquiv R v₀ (t, z))
    ∂R.probe.domain.measure

def reflectedSheet (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (v₀ : InfinitePlace F) (t : PositiveAxis) : ℂ :=
  ∫ z : R.A.G1, reflectedPoint R θ C L u κ (sheetEquiv R v₀ (t, z))
    ∂R.probe.domain.measure

theorem directSheet_normalization (u : R.A.UnitQuotient)
    (v₀ : InfinitePlace F) (t : PositiveAxis) :
    directSheet R θ C L u v₀ t =
      normalizingScalar R θ C L u * FiniteNormalizedMellin.direct R θ C L v₀ t := by
  unfold directSheet
  simp_rw [directPoint_eq R θ C L]
  exact FiniteNormalizedMellin.direct_common_normalization R θ C L _ v₀ t

theorem reflectedSheet_normalization (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) (v₀ : InfinitePlace F) (t : PositiveAxis) :
    reflectedSheet R θ C L u κ v₀ t =
      normalizingScalar R θ C L u *
        FiniteNormalizedMellin.reflected R θ C L u κ v₀ t := by
  unfold reflectedSheet
  simp_rw [reflectedPoint_eq R θ C L]
  exact FiniteNormalizedMellin.reflected_common_normalization R θ C L _ u κ v₀ t

theorem direct_weighted_integrable (v₀ : InfinitePlace F) (s : ℂ)
    (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (fun t : PositiveAxis => (t.val : ℂ) ^ s *
      FiniteNormalizedMellin.direct R θ C L v₀ t) positiveHaar := by
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  letI := R.probe.domain.haar
  have h := FiniteDirectMellin.direct_global_mellin R C.transport C.projected.cutoffs
    (reflectedConstant R θ C L)⁻¹ (FiniteNormalizedMellin.archProfile R θ C L false) s
    (fun w => L.direct_integrable w s hs)
  exact weighted_sheet_integrable (sheetEquiv R v₀)
    (sheetEquiv_measurePreserving R C.transport v₀) (normCoordinate R)
    (sheetEquiv_norm R v₀) (fun t : PositiveAxis => (t.val : ℂ) ^ s)
    (FiniteDirectMellin.directTensor R C.projected.cutoffs
      (reflectedConstant R θ C L)⁻¹ (FiniteNormalizedMellin.archProfile R θ C L false)) h.1

theorem reflected_weighted_integrable (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) (v₀ : InfinitePlace F) (s : ℂ)
    (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (fun t : PositiveAxis => (t.val : ℂ) ^ s *
      FiniteNormalizedMellin.reflected R θ C L u κ v₀ t) positiveHaar := by
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  letI := R.probe.domain.haar
  have h := reflected_global_mellin R D C.transport θ C.projected.cutoffs
    (C₀ R θ C L) (C₀_ne_zero R θ C L) (A₀ R θ C L) (A₀_pos R θ C L)
    (reflectedConstant R θ C L)⁻¹ (FiniteNormalizedMellin.archProfile R θ C L true)
    u κ s hs (fun w => L.reflected_integrable w s hs)
  exact weighted_sheet_integrable (sheetEquiv R v₀)
    (sheetEquiv_measurePreserving R C.transport v₀) (normCoordinate R)
    (sheetEquiv_norm R v₀) (fun t : PositiveAxis => (t.val : ℂ) ^ s)
    (reflectedTensor R D θ (reflectedConstant R θ C L)⁻¹
      (FiniteNormalizedMellin.archProfile R θ C L true) u κ) h.1

/-- Exact bridge to the deconvolver's actual finite Gamma profile. -/
theorem direct_mellin_eq_gamma (v₀ : InfinitePlace F) (s : ℂ)
    (hs : -(1 / 3 : ℝ) < s.re) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s *
      FiniteNormalizedMellin.direct R θ C L v₀ t ∂positiveHaar) =
    GammaDeconvolver.directGamma (GammaDeconvolverProject.actualProfile F Sf M θ) s := by
  rw [FiniteNormalizedMellin.direct_mellin R θ C L v₀ s hs,
    GammaDeconvolverProject.directGamma_actual F Sf M θ s] <;> rfl

end ThetaGlobal.FiniteActualProfiles

#print axioms ThetaGlobal.FiniteActualProfiles.directSheet_normalization
#print axioms ThetaGlobal.FiniteActualProfiles.reflectedSheet_normalization
#print axioms ThetaGlobal.FiniteActualProfiles.direct_weighted_integrable
#print axioms ThetaGlobal.FiniteActualProfiles.reflected_weighted_integrable
#print axioms ThetaGlobal.FiniteActualProfiles.direct_mellin_eq_gamma
