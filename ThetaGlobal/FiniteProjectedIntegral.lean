import ThetaGlobal.FiniteProjectedMellin
import ThetaGlobal.FiniteTensorMellin
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Exact Haar-integral specification of the actual finite Mellin factor

This joins the source-specific coefficient construction to its complete
finite S-local Mellin integral.  All finite valuations and class-separation
indices are summed with proved absolute integrability.  The result retains
the actual source vectors, target Hecke period, Hilbert convention, and
the local Haar measures from the same trace transport.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ThetaGlobal.ProjectedFiniteIntegral

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteShell ThetaGlobal.FiniteClass ThetaGlobal.FiniteTensor
open ThetaGlobal.FiniteCanonicalVectors ThetaGlobal.ProjectedFiniteMellin
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (N : TraceHaarTransport R)

local instance (p : R.A.Sf) : MeasurableSpace (LocalIntegerRing F p.val)ˣ := borel _
local instance (p : R.A.Sf) : BorelSpace (LocalIntegerRing F p.val)ˣ := ⟨rfl⟩
local instance (p : R.A.Sf) : Fintype (ProjectFiniteClass.LocalClass R.A p) := Fintype.ofFinite _
local instance (p : R.A.Sf) : (N.finiteMultHaar p).IsHaarMeasure := N.finiteMultHaar_isHaar p
local instance (p : R.A.Sf) : IsFiniteMeasure (unitHaar R N p) :=
  ProjectFiniteHaar.localUnitMeasure_finite F p.val (N.finiteMultHaar p)

variable (θ : HeckeCharacter F) (B : FirstRootCutoffs R)

def maskedData (u : R.A.UnitQuotient) (p : R.A.Sf) :=
  withClassMask (X := fun q : R.A.Sf => (q.val.adicCompletion F)ˣ)
    (U := fun q : R.A.Sf => (LocalIntegerRing F q.val)ˣ)
    (C := fun q : R.A.Sf => ProjectFiniteClass.LocalClass R.A q)
    (ProjectFiniteClass.allowedClasses R.A R.probe.correction.B)
    (ProjectFiniteClass.reflectedHilbert R.A R.σ)
    (fun x y => (ProjectFiniteClass.reflectedHilbert_norm_one R.A R.σ x y).le)
    (ProjectFiniteClass.assemble R.A) D.scalarSlot
    (fun q z => (QuotientGroup.mk z : ProjectFiniteClass.LocalClass R.A q)) p
    (projectedShellData.{0} R D (TargetFinitePeriod.localPeriod R θ) u PUnit.unit p)

def localMellinFunction (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (σ : ∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p) (p : R.A.Sf)
    (s : ℂ) (z : (p.val.adicCompletion F)ˣ) : ℂ :=
  localMaskFactor D.scalarSlot (fun c => ProjectFiniteClass.reflectedClassMask R.A
    R.probe.correction.B R.σ κ (ProjectFiniteClass.assemble R.A c)) σ p
      (QuotientGroup.mk z) *
    ((TargetFinitePeriod.localPeriod R θ u p z : ℂ) *
      (weylValue R D p (normalizedSelectedVector R D u p) z * (‖z.val‖ : ℂ) ^ s))

include B in
theorem localMellinFunction_continuous (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (σ : ∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p) (p : R.A.Sf) (s : ℂ) :
    Continuous (localMellinFunction R D θ u κ σ p s) := by
  have hm : Continuous (fun z : (p.val.adicCompletion F)ˣ =>
      localMaskFactor D.scalarSlot (fun c => ProjectFiniteClass.reflectedClassMask R.A
        R.probe.correction.B R.σ κ (ProjectFiniteClass.assemble R.A c)) σ p
          (QuotientGroup.mk z)) :=
    ((TargetFinitePeriod.localClass_locallyConstant R B p).comp
      (fun c : ProjectFiniteClass.LocalClass R.A p => localMaskFactor D.scalarSlot
        (fun c => ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
          (ProjectFiniteClass.assemble R.A c)) σ p c)).continuous
  have hw : Continuous (fun z : (p.val.adicCompletion F)ˣ => (‖z.val‖ : ℂ) ^ s) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ContinuousAt.comp (g := fun r : ℝ => (r : ℂ) ^ s)
      (f := fun x : (p.val.adicCompletion F)ˣ => ‖x.val‖)
      (Complex.continuousAt_ofReal_cpow_const ‖z.val‖ s
        (Or.inr (norm_ne_zero_iff.mpr z.ne_zero)))
      (Units.continuous_val.norm.continuousAt)
  exact hm.mul ((TargetFinitePeriod.localPeriod_continuous R θ B u p).mul
    ((weylValue_locallyConstant R D p (normalizedSelectedVector R D u p)).continuous.mul hw))

include B in
/-- No shell-integrability hypothesis remains: each masked shell integrand
is continuous on the actual compact integral-unit group. -/
theorem maskedData_shellIntegrable (u : R.A.UnitQuotient) (p : R.A.Sf) :
    ShellIntegrable (maskedData R D θ u p) (unitHaar R N p) := by
  letI : CompactSpace (LocalIntegerRing F p.val) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F p.val
  intro b k
  have hi := ((localMellinFunction_continuous R D θ B u b.1 b.2 p 0).comp
    (ProjectFiniteHaar.shellPoint_continuous F p.val k)).integrable_of_hasCompactSupport
      (μ := unitHaar R N p) (HasCompactSupport.of_compactSpace _)
  simp only [Function.comp_def, localMellinFunction, Complex.cpow_zero, mul_one,
    mul_assoc] at hi
  simp only [maskedData, withClassMask, projectedShellData,
    vectorShellData, ProjectLocalShell.shellData, mul_assoc]
  exact hi

/-- The exact finite part of the reflected sheet's Mellin integrand. -/
def finiteMellinIntegrand (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) : ℂ :=
  ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
    (ProjectFiniteClass.assemble R.A (fun p => QuotientGroup.mk (z p))) *
      ∏ p, (TargetFinitePeriod.localPeriod R θ u p (z p) : ℂ) *
        (weylValue R D p (normalizedSelectedVector R D u p) (z p) * (‖(z p).val‖ : ℂ) ^ s)

theorem finiteMellinIntegrand_tensor_expansion (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    finiteMellinIntegrand R D θ u κ s z =
      ∑ σ : ∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p,
        ∏ p, localMellinFunction R D θ u κ σ p s (z p) := by
  refine Eq.trans (FiniteClass.tensor_expansion D.scalarSlot
    (fun c => ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
      (ProjectFiniteClass.assemble R.A c))
    (fun p => (QuotientGroup.mk (z p) : ProjectFiniteClass.LocalClass R.A p))
    (fun p => (TargetFinitePeriod.localPeriod R θ u p (z p) : ℂ) *
      (weylValue R D p (normalizedSelectedVector R D u p) (z p) *
        (‖(z p).val‖ : ℂ) ^ s))).symm ?_
  first
  | rfl
  | (congr 1; done)
  | (congr 1 <;> first | rfl | exact congrArg (fun I => @Finset.univ _ I) (Subsingleton.elim _ _))

include B in
/-- The full finite integrand is continuous because its actual class
mask has a finite tensor expansion into locally constant class factors. -/
theorem finiteMellinIntegrand_continuous (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (s : ℂ) : Continuous (finiteMellinIntegrand R D θ u κ s) := by
  have he : finiteMellinIntegrand R D θ u κ s =
      fun z => ∑ σ : ∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p,
        ∏ p, localMellinFunction R D θ u κ σ p s (z p) :=
    funext (finiteMellinIntegrand_tensor_expansion R D θ u κ s)
  rw [he]
  apply continuous_finset_sum
  intro σ _
  apply continuous_finset_prod
  intro p _
  exact (localMellinFunction_continuous R D θ B u κ σ p s).comp (continuous_apply p)

include B in
theorem class_series_integral (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (finiteMellinIntegrand R D θ u κ s) (Measure.pi N.finiteMultHaar) ∧
    (∑ σ : ∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p,
      ∏ p, ∑' k : ℤ, coefficient (maskedData R D θ u p) (unitHaar R N p) (κ, σ) k *
        (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s)) =
      ∫ z, finiteMellinIntegrand R D θ u κ s z ∂Measure.pi N.finiteMultHaar := by
  let d := fun p => projectedShellData.{0} R D (TargetFinitePeriod.localPeriod R θ) u PUnit.unit p
  obtain ⟨h1, h2⟩ := FiniteTensorMellin.finite_tensor_mellin_integral
    (ProjectFiniteClass.allowedClasses R.A R.probe.correction.B)
    (ProjectFiniteClass.reflectedHilbert R.A R.σ)
    (fun x y => (ProjectFiniteClass.reflectedHilbert_norm_one R.A R.σ x y).le)
    (ProjectFiniteClass.assemble R.A) D.scalarSlot
    (fun p z => (QuotientGroup.mk z : ProjectFiniteClass.LocalClass R.A p))
    d (unitHaar R N) N.finiteMultHaar
    (fun p z => (TargetFinitePeriod.localPeriod R θ u p z : ℂ))
    (fun p => projectedShellData_bounds.{0} R D (TargetFinitePeriod.localPeriod R θ) u PUnit.unit p)
    (fun p => ProjectFiniteHaar.local_haar_eq_shellMeasure F p.val (N.finiteMultHaar p) _ _)
    (fun p k => (ProjectFiniteHaar.shellPoint_continuous F p.val k).measurable.aemeasurable)
    (fun _ _ _ => rfl) (maskedData_shellIntegrable R D N θ B u) κ s hs
    (fun σ p k => (localMellinFunction_continuous R D θ B u κ σ p s).aestronglyMeasurable)
  refine ⟨h1, Eq.trans ?_ h2⟩
  first
  | rfl
  | (congr 1; done)
  | (congr 1 <;> first | rfl | exact congrArg (fun I => @Finset.univ _ I) (Subsingleton.elim _ _))

include B in
/-- TH-KP-DATA's full finite Mellin factor is the actual finite S-local
Haar integral.  The finite `Fin terms` indexing is only an enumeration of
the genuine local class tuples.  Both sides are now proved integrable. -/
theorem finiteMellinFactor_integral
    (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    finiteMellinFactor F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ) u κ s =
      ∫ z, finiteMellinIntegrand R D θ u κ s z ∂Measure.pi N.finiteMultHaar := by
  refine Eq.trans ?_ (class_series_integral R D N θ B u κ s hs).2
  unfold finiteMellinFactor
  apply Fintype.sum_equiv (termClassEquiv R D N C₀ hC₀ A₀ hA₀ θ)
  intro l
  rfl

end ThetaGlobal.ProjectedFiniteIntegral

#print axioms ThetaGlobal.ProjectedFiniteIntegral.maskedData_shellIntegrable
#print axioms ThetaGlobal.ProjectedFiniteIntegral.class_series_integral
#print axioms ThetaGlobal.ProjectedFiniteIntegral.finiteMellinFactor_integral
