import ThetaGlobal.FiniteProjectedIntegral
import ThetaGlobal.FiniteMellinRatio
import ThetaGlobal.SheetMellin
import DedekindZetaZeroFree.Nonvanishing.Mellin.PositiveProfileTransform

/-!
# Actual norm-sheet and polar-Haar Mellin transport

The finite function is the literal projected Weyl coefficient table.
The measures are `N.finiteMultHaar`, `N.angularHaar`, `N.groupHaar`, and the
probe's original norm-one Haar.  Disintegration and polar transport are
applied exactly as stored in the same `TraceHaarTransport`.

The only analytic hypotheses in the main theorem are integrability of
the individual archimedean functions.  Finite integrability, valuation
summation, tensor separation and all global Fubini steps are proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteSheetMellin

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaPositiveSheetMellin
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ProjectedFiniteIntegral ThetaGlobal.ProjectedFiniteMellin
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (N : TraceHaarTransport R)

local instance : MeasurableSpace R.A.G1 := borel _
local instance : BorelSpace R.A.G1 := ⟨rfl⟩

def normCoordinate (y : R.A.G) : PositiveAxis :=
  ⟨R.A.norm y, norm_positive R.A y⟩

def sheetEquiv (v₀ : InfinitePlace F) : PositiveAxis × R.A.G1 ≃ᵐ R.A.G :=
  (normSplit R.A v₀).toHomeomorph.toMeasurableEquiv

theorem sheetEquiv_norm (v₀ : InfinitePlace F) (z : PositiveAxis × R.A.G1) :
    normCoordinate R (sheetEquiv R v₀ z) = z.1 := by
  exact congrArg Prod.fst ((normSplit R.A v₀).symm_apply_apply z)

theorem sheetEquiv_measurePreserving (v₀ : InfinitePlace F) :
    MeasurePreserving (sheetEquiv R v₀)
      (positiveHaar.prod R.probe.domain.measure) N.groupHaar :=
  ⟨(sheetEquiv R v₀).measurable, N.disintegration v₀⟩

theorem norm_cpow (y : R.A.G) (s : ℂ) :
    (R.A.norm y : ℂ) ^ s =
      (∏ w : InfinitePlace F, ((‖(y.1 w).val‖ ^ 2 : ℝ) : ℂ) ^ s) *
      ∏ p : R.A.Sf, (‖(y.2 p).val‖ : ℂ) ^ s := by
  unfold SArithmeticData.norm
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg
      (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)),
    FiniteMellinRatio.ofReal_prod_cpow _ _ (fun _ => sq_nonneg _),
    FiniteMellinRatio.ofReal_prod_cpow _ _ (fun _ => norm_nonneg _)]

def archWeighted (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (s : ℂ) (w : InfinitePlace F) (z : w.Completionˣ) : ℂ :=
  a w z * ((‖z.val‖ ^ 2 : ℝ) : ℂ) ^ s

/-- The finite part is the actual reflected coefficient, before its
norm power is inserted.  `W` is kept as the same source's value at one. -/
def reflectedTensor (θ : HeckeCharacter F) (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (y : R.A.G) : ℂ :=
  W * finiteMellinIntegrand R D θ u κ 0 y.2 * ∏ w, a w (y.1 w)

theorem reflectedTensor_weight (θ : HeckeCharacter F) (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (y : R.A.G) :
    (R.A.norm y : ℂ) ^ s * reflectedTensor R D θ W a u κ y =
      W * (∏ w, archWeighted a s w (y.1 w)) *
        finiteMellinIntegrand R D θ u κ s y.2 := by
  rw [norm_cpow]
  simp only [reflectedTensor, finiteMellinIntegrand, archWeighted,
    Complex.cpow_zero, mul_one, Finset.prod_mul_distrib]
  ring

theorem reflected_global_mellin
    (θ : HeckeCharacter F) (B : ThetaExpansion.FirstRootCutoffs R)
    (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)
    (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (ha : ∀ w, Integrable (archWeighted a s w) (archHaar R.A w (N.angularHaar w))) :
    Integrable (fun y => (R.A.norm y : ℂ) ^ s * reflectedTensor R D θ W a u κ y)
      N.groupHaar ∧
    (∫ y, (R.A.norm y : ℂ) ^ s * reflectedTensor R D θ W a u κ y ∂N.groupHaar) =
      W * finiteMellinFactor F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
        (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ) u κ s *
      ∏ w : InfinitePlace F, ∫ z, archWeighted a s w z ∂archHaar R.A w (N.angularHaar w) := by
  letI := N.finiteMultHaar_isHaar
  letI := N.angularHaar_isHaar
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => Units.isEmbedding_val₀.secondCountableTopology
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : ∀ p : R.A.Sf, TopologicalSpace.SeparableSpace (p.val.adicCompletion F) :=
    fun p => TopologicalSpace.SeparableSpace.of_denseRange _ (p.val.denseRange_algebraMap F)
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F) := fun p => inferInstance
  letI : ∀ p : R.A.Sf, SecondCountableTopology (p.val.adicCompletion F)ˣ :=
    fun p => Units.isEmbedding_val₀.secondCountableTopology
  letI : ∀ w : InfinitePlace F, LocallyCompactSpace w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (R.A.complex_place w)).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  have harch := Integrable.fintype_prod_dep ha
  have hfinite := (class_series_integral R D N θ B u κ s hs).1
  have hfiniteIntegral := finiteMellinFactor_integral R D N θ B C₀ hC₀ A₀ hA₀ u κ s hs
  rw [N.polar_transport]
  unfold productHaar
  rw [groupMeasurableSpace_eq_prod R.A, Measure.map_id']
  simp_rw [reflectedTensor_weight]
  refine ⟨((harch.mul_prod hfinite).const_mul W).congr
    (Filter.Eventually.of_forall (fun _ => (mul_assoc _ _ _).symm)), ?_⟩
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  refine congrArg (W * ·) ?_
  refine (MeasureTheory.integral_prod_mul
    (fun x : (∀ w : InfinitePlace F, w.Completionˣ) => ∏ w, archWeighted a s w (x w))
    (finiteMellinIntegrand R D θ u κ s)).trans ?_
  rw [integral_fintype_prod_eq_prod, ← hfiniteIntegral]
  ring

/-- The actual norm-one Haar profile, including the actual global scalar. -/
def reflectedSheet (θ : HeckeCharacter F) (W : ℂ)
    (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (v₀ : InfinitePlace F) (t : PositiveAxis) : ℂ :=
  MeasureTheory.integral R.probe.domain.measure
    (fun z : R.A.G1 => reflectedTensor R D θ W a u κ (sheetEquiv R v₀ (t, z)))

theorem reflected_sheet_mellin
    (θ : HeckeCharacter F) (B : ThetaExpansion.FirstRootCutoffs R)
    (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)
    (W : ℂ) (a : ∀ w : InfinitePlace F, w.Completionˣ → ℂ)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))))
    (v₀ : InfinitePlace F) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (ha : ∀ w, Integrable (archWeighted a s w) (archHaar R.A w (N.angularHaar w))) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s * reflectedSheet R D θ W a u κ v₀ t
      ∂positiveHaar) =
      W * finiteMellinFactor F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
        (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ) u κ s *
      ∏ w : InfinitePlace F, ∫ z, archWeighted a s w z ∂archHaar R.A w (N.angularHaar w) := by
  letI : LocallyCompactSpace R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).1
  letI : SecondCountableTopology R.A.G1 := (NormSheetsCoordinates.normOne_geometry R.A).2
  letI := R.probe.domain.haar
  have h := reflected_global_mellin R D N θ B C₀ hC₀ A₀ hA₀ W a u κ s hs ha
  exact (SheetMellin.sheet_transform_eq_global (sheetEquiv R v₀)
    (sheetEquiv_measurePreserving R N v₀) (normCoordinate R)
    (sheetEquiv_norm R v₀) (fun t : PositiveAxis => (t.val : ℂ) ^ s)
    (reflectedTensor R D θ W a u κ) h.1).trans h.2

end ThetaGlobal.FiniteSheetMellin

#print axioms ThetaGlobal.FiniteSheetMellin.reflected_global_mellin
#print axioms ThetaGlobal.FiniteSheetMellin.reflected_sheet_mellin
