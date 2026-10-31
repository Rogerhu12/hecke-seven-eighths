import ThetaGlobal.FiniteProjectedIntegral
import ThetaGlobal.FiniteTargetCutoff
import ThetaGlobal.ReflectedAbsoluteProject
import ThetaGlobal.GlobalSameChoice
import HeckeSkeleton.ThetaKernel

/-!
# Four project obligations on one fixed source and one arithmetic choice

The actual coefficient table, valuation estimates, full finite Haar-integral
specification, generic reflection kernel, and marked reflected absolute
convergence are assembled here.  The source factorization `D`, the Haar
transport `N`, the target Hecke character `θ`, and the local archimedean
normalizations `C₀,A₀` are fixed throughout.  Neither kernel estimates nor
marked reflected summability are assumptions.

The final theorem specializes the arithmetic coefficients to the very same
`ArithmeticChoice X` from which `GlobalSameChoice.recipe X hmod` is built.
This module does not import `HeckeSkeleton.Base` or `HeckeSkeleton.Theta`.
It therefore gives a proposed replacement interface for their four finite
data / absolute convergence obligations without importing those admissions.

The remaining reflection identity still requires the archimedean Mellin
pair and the global source-to-period identification for the same vector;
the parameters `C₀,A₀` are not asserted here to have that property merely
because they are nonzero/positive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.FiniteAssembly

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ProjectedFiniteMellin ThetaGlobal.ProjectedFiniteIntegral
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (N : TraceHaarTransport R)
variable (θ : HeckeCharacter F)
variable (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))

local instance (p : R.A.Sf) : MeasurableSpace (LocalIntegerRing F p.val)ˣ := borel _
local instance (p : R.A.Sf) : BorelSpace (LocalIntegerRing F p.val)ˣ := ⟨rfl⟩

/-- TH-KP-DATA, with the literal actual-source shell specification provided
by `actualCoefficient_shell_spec` below. -/
def actualFiniteMellinData : FiniteMellinData F Sf :=
  targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ

local notation "M" => actualFiniteMellinData R D N θ C₀ hC₀ A₀ hA₀

/-- TH-FINITE-VALUATION-CUTOFF for the exact table used in every theorem
of this module.  The cutoff is uniform in all sectors and local classes. -/
theorem actualFiniteValuationCutoff :
    ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → (M).coefficient u κ l p k = 0 :=
  targetFiniteMellinData_valuation_cutoff R D N C₀ hC₀ A₀ hA₀ θ

/-- TH-FINITE-VALUATION-DECAY, including all real `δ < 1/3`. -/
theorem actualFiniteValuationDecay :
    ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧ ∀ u κ l p k, 0 ≤ k →
      ‖(M).coefficient u κ l p k‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) :=
  targetFiniteMellinData_valuation_decay R D N C₀ hC₀ A₀ hA₀ θ

theorem actualFiniteAdmissible : FiniteMellinAdmissible F Sf M :=
  targetFiniteMellinData_admissible R D N C₀ hC₀ A₀ hA₀ θ

/-- The public shell specification uses the actual table's own enumeration
and the actual local Haar; no independent choice of coefficients occurs. -/
theorem actualCoefficient_shell_spec
    (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (l : Fin (M).terms) (p : R.A.Sf) (k : ℤ) :
    (M).coefficient u κ l p k =
      ∫ z,
        (if p = D.scalarSlot then ProjectFiniteClass.reflectedClassMask R.A
          R.probe.correction.B R.σ κ
          (ProjectFiniteClass.assemble R.A (termClassEquiv R D N C₀ hC₀ A₀ hA₀ θ l))
          else 1) *
        (if (QuotientGroup.mk (ProjectLocalShell.shellPoint F p.val k z) :
            ProjectFiniteClass.LocalClass R.A p) =
            termClassEquiv R D N C₀ hC₀ A₀ hA₀ θ l p then 1 else 0) *
        (TargetFinitePeriod.localPeriod R θ u p
          (ProjectLocalShell.shellPoint F p.val k z) : ℂ) *
        FiniteCanonicalVectors.weylValue R D p (normalizedSelectedVector R D u p)
          (ProjectLocalShell.shellPoint F p.val k z) ∂unitHaar R N p :=
  targetCoefficient_enumerated_spec R D N C₀ hC₀ A₀ hA₀ θ u κ l p k

/-- Exact finite S-local Mellin transform, with absolute integrability
proved before any interchange of shells and Haar integrals. -/
theorem actualFiniteMellin_integral (B : FirstRootCutoffs R)
    (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Integrable (finiteMellinIntegrand R D θ u κ s) (Measure.pi N.finiteMultHaar) ∧
    finiteMellinFactor F Sf M u κ s =
      ∫ z, finiteMellinIntegrand R D θ u κ s z ∂Measure.pi N.finiteMultHaar :=
  ⟨(class_series_integral R D N θ B u κ s hs).1,
    finiteMellinFactor_integral R D N θ B C₀ hC₀ A₀ hA₀ u κ s hs⟩

local instance actualSixthLocalClasses_finite : Finite (SixthLocalClasses F Sf) := by
  letI := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  exact HeckeSkeleton.SixthLocalFinite.sixthLocalClasses_finite F Sf

/-- The three already proved general kernel lemmas now apply to the
constructed table.  Thus `MellinKernelInput` is a conclusion here. -/
theorem actualMellinKernel : MellinKernelInput F Sf M θ where
  finite_admissible := actualFiniteAdmissible R D N θ C₀ hC₀ A₀ hA₀
  integrable := HeckeSkeleton.ThetaKernel.kernel_integrable F Sf M θ
    (actualFiniteAdmissible R D N θ C₀ hC₀ A₀ hA₀)
  line_independent := HeckeSkeleton.ThetaKernel.kernel_line_independent F Sf M θ
    (actualFiniteAdmissible R D N θ C₀ hC₀ A₀ hA₀)
  derivative_bound := HeckeSkeleton.ThetaKernel.kernel_derivative_bound F Sf M θ
    (actualFiniteAdmissible R D N θ C₀ hC₀ A₀ hA₀)

/-- TH-MARKED-REFLECTED-ABSOLUTE with all finite-Mellin and kernel inputs
discharged.  The arithmetic datum is explicit; the next theorem fixes it
to the same original arithmetic choice as the theta source. -/
theorem actualReflectedAbsolute (arithmetic : ThetaArithmeticData F Sf)
    (d : MarkedDatum F Sf) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    Summable (fun i : ReflectionIndex F Sf d =>
      reflectedTerm F Sf arithmetic d i M θ V.toFun X) :=
  ReflectedAbsoluteProject.marked_reflected_absolute F Sf arithmetic d M θ
    (actualMellinKernel R D N θ C₀ hC₀ A₀ hA₀) V hX

section SameArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {ζ : F} {σ : F →+* ℂ}
variable (X₀ : HeckeAxiom.ArithmeticChoice F S₀ ζ σ) (hmod : X₀.A.modulus = ⊤)
variable {Q₀ : AdmissibleFlatSources (GlobalSameChoice.recipe X₀ hmod)}
  {T₀ : Realization (GlobalSameChoice.recipe X₀ hmod) Q₀}
variable (D₀ : SourceFactorization (GlobalSameChoice.recipe X₀ hmod) Q₀ T₀)
  (N₀ : TraceHaarTransport (GlobalSameChoice.recipe X₀ hmod))

/-- The coefficient mask uses precisely `X₀.C.correction.B`, with the
same Hilbert pairing and embedding as `X₀.thetaData`. -/
theorem sameChoice_reflectedClassMask
    (κ c : SixthLocalClasses F (X₀.A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    ProjectFiniteClass.reflectedClassMask (GlobalSameChoice.recipe X₀ hmod).A
      (GlobalSameChoice.recipe X₀ hmod).probe.correction.B
      (GlobalSameChoice.recipe X₀ hmod).σ κ c =
      ProjectFiniteClass.reflectedClassMask X₀.A X₀.C.correction.B σ κ c := by
  change ProjectFiniteClass.reflectedClassMask X₀.A
    (GlobalSameChoice.recipe X₀ hmod).probe.correction.B σ κ c = _
  rw [GlobalSameChoice.recipe_correction]

/-- The final same-choice replacement for the marked reflected absolute
convergence obligation: arithmetic coefficients and finite Mellin table
are built from the single prescribed `X₀`, not two chosen contexts. -/
theorem sameChoice_actualReflectedAbsolute
    (d : MarkedDatum F (X₀.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    Summable (fun i : ReflectionIndex F (X₀.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) d =>
      reflectedTerm F (X₀.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) X₀.thetaData d i
        (actualFiniteMellinData (GlobalSameChoice.recipe X₀ hmod) D₀ N₀
          θ C₀ hC₀ A₀ hA₀) θ V.toFun X) :=
  actualReflectedAbsolute (GlobalSameChoice.recipe X₀ hmod) D₀ N₀ θ C₀ hC₀ A₀ hA₀
    X₀.thetaData d V hX

end SameArithmeticChoice

end ThetaGlobal.FiniteAssembly

#print axioms ThetaGlobal.FiniteAssembly.actualFiniteValuationCutoff
#print axioms ThetaGlobal.FiniteAssembly.actualFiniteValuationDecay
#print axioms ThetaGlobal.FiniteAssembly.actualMellinKernel
#print axioms ThetaGlobal.FiniteAssembly.actualReflectedAbsolute
#print axioms ThetaGlobal.FiniteAssembly.sameChoice_actualReflectedAbsolute
