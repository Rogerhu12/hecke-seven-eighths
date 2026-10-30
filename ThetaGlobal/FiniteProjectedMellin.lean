import ThetaGlobal.FiniteCanonicalVectors
import ThetaGlobal.FiniteHaarProject
import ThetaGlobal.FiniteClassProject
import ThetaGlobal.FiniteMellinProject
import ThetaGlobal.FiniteTargetPeriod
import DedekindZetaZeroFree.Theta.Whittaker.FirstRootNondegeneracy

/-!
# The finite Mellin table of an actual projected source

The vectors are extracted from the stored pure tensor of the specified
source factorization.  They are normalized by the actual local Whittaker
functional, Weyl-translated in the actual canonical representation, and
integrated on the actual integral-unit shells with the actual local Haar.
The class mask uses the recipe's chosen complement and Hilbert pairing.

The local period components and the nonzero archimedean forward Mellin
normalization are explicit inputs: identifying these with a newly chosen
infinity type belongs to the local period/Mellin calculation.  No free
coefficient sequence, coefficient estimate, or global reflection is input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.ProjectedFiniteMellin

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteCanonicalVectors
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

def frozenStage (u : R.A.UnitQuotient) : RestrictedTensorSimple.Level D.bad :=
  Classical.choose (D.selected_frozen_stage u)

def frozenTuple (u : R.A.UnitQuotient) :
    ∀ p : (frozenStage R D u).val, actualLocal R D.finiteData p :=
  Classical.choose (Classical.choose_spec (D.selected_frozen_stage u))

theorem frozenStage_exact (u : R.A.UnitQuotient) : (frozenStage R D u).val = D.bad :=
  (Classical.choose_spec (Classical.choose_spec (D.selected_frozen_stage u))).1

theorem frozenTuple_exact (u : R.A.UnitQuotient) :
    D.selected u = RestrictedTensorSimple.stageInclusion _ D.references D.bad
      (frozenStage R D u) (PiTensorProduct.tprod ℂ (frozenTuple R D u)) :=
  (Classical.choose_spec (Classical.choose_spec (D.selected_frozen_stage u))).2

theorem finite_mem_frozen (u : R.A.UnitQuotient) (p : R.A.Sf) :
    Sum.inr p.val ∈ (frozenStage R D u).val := by
  rw [frozenStage_exact]
  exact (D.bad_exact _).mpr (Or.inr ⟨p.val, rfl, p.property⟩)

def selectedFiniteVector (u : R.A.UnitQuotient) (p : R.A.Sf) : Vector R D p :=
  frozenTuple R D u ⟨Sum.inr p.val, finite_mem_frozen R D u p⟩

theorem selectedFiniteVector_nonzero
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (u : R.A.UnitQuotient) (p : R.A.Sf) :
    D.ell (Sum.inr p.val) (selectedFiniteVector R D u p) ≠ 0 := by
  have h := hn u
  rw [← D.selected_eq u, frozenTuple_exact, D.product_exact] at h
  exact (Finset.prod_ne_zero_iff.mp h)
    ⟨Sum.inr p.val, finite_mem_frozen R D u p⟩ (Finset.mem_univ _)

def normalizedSelectedVector (u : R.A.UnitQuotient) (p : R.A.Sf) : Vector R D p :=
  (D.ell (Sum.inr p.val) (selectedFiniteVector R D u p))⁻¹ • selectedFiniteVector R D u p

theorem normalizedSelectedVector_value
    (hn : ∀ u, fourier R Q.dq (T.theta u) 1 ≠ 0)
    (u : R.A.UnitQuotient) (p : R.A.Sf) :
    D.ell (Sum.inr p.val) (normalizedSelectedVector R D u p) = 1 := by
  rw [normalizedSelectedVector, map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ (selectedFiniteVector_nonzero R D hn u p)

/-- The extracted tuple is the actual source under its stored tensor map.
This provenance equality is independent of the coefficient construction. -/
theorem selected_source_provenance (u : R.A.UnitQuotient) :
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad
      (frozenStage R D u) (PiTensorProduct.tprod ℂ (frozenTuple R D u))) = T.theta u := by
  rw [← frozenTuple_exact, D.selected_eq]

local instance (p : R.A.Sf) : MeasurableSpace (LocalIntegerRing F p.val)ˣ := borel _
local instance (p : R.A.Sf) : BorelSpace (LocalIntegerRing F p.val)ˣ := ⟨rfl⟩
local instance (p : R.A.Sf) : Fintype (ProjectFiniteClass.LocalClass R.A p) :=
  Fintype.ofFinite _

variable (N : TraceHaarTransport R)

local instance (p : R.A.Sf) : (N.finiteMultHaar p).IsHaarMeasure := N.finiteMultHaar_isHaar p

def unitHaar (p : R.A.Sf) : Measure (LocalIntegerRing F p.val)ˣ :=
  ProjectFiniteHaar.localUnitMeasure F p.val (N.finiteMultHaar p)

local instance (p : R.A.Sf) : IsFiniteMeasure (unitHaar R N p) :=
  ProjectFiniteHaar.localUnitMeasure_finite F p.val (N.finiteMultHaar p)

variable (L : R.A.UnitQuotient → ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ → Circle)

def projectedShellData (u : R.A.UnitQuotient) (_t : PUnit) (p : R.A.Sf) :=
  vectorShellData R D p (normalizedSelectedVector R D u p) (L u p)

theorem projectedShellData_bounds (u : R.A.UnitQuotient) (t : PUnit) (p : R.A.Sf) :
    FiniteShell.LocalWhittakerBounds (projectedShellData R D L u t p) :=
  vectorShellData_bounds R D p (normalizedSelectedVector R D u p) (L u p)

variable (C₀ : ℂ) (hC₀ : C₀ ≠ 0) (A₀ : ℝ) (hA₀ : 0 < A₀)

/-- Actual source-specific finite Mellin data.  The only tensor index is a
tuple of genuine sixth-power classes: each source sector already has one
stored pure tensor.  The pivot is the source's actual scalar slot. -/
def finiteMellinData : FiniteMellinData F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
  ProjectFiniteMellin.finiteMellinDataOfClassShells F (R.A.Sf : Set _)
    (ProjectFiniteClass.allowedClasses R.A R.probe.correction.B)
    (ProjectFiniteClass.reflectedHilbert R.A R.σ)
    (fun x y => (ProjectFiniteClass.reflectedHilbert_norm_one R.A R.σ x y).le)
    (ProjectFiniteClass.assemble R.A) D.scalarSlot
    (fun p z => (QuotientGroup.mk z : ProjectFiniteClass.LocalClass R.A p))
    (projectedShellData R D L) (unitHaar R N) C₀ hC₀ A₀ hA₀

/-- Cutoff, all decay exponents, and absolute local Mellin convergence
are proved for this actual source-specific table. -/
theorem finiteMellinData_admissible :
    FiniteMellinAdmissible F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (finiteMellinData R D N L C₀ hC₀ A₀ hA₀) :=
  ProjectFiniteMellin.finiteAdmissible F (R.A.Sf : Set _)
    (ProjectFiniteClass.allowedClasses R.A R.probe.correction.B)
    (ProjectFiniteClass.reflectedHilbert R.A R.σ)
    (fun x y => (ProjectFiniteClass.reflectedHilbert_norm_one R.A R.σ x y).le)
    (ProjectFiniteClass.assemble R.A) D.scalarSlot
    (fun p z => (QuotientGroup.mk z : ProjectFiniteClass.LocalClass R.A p))
    (projectedShellData R D L) (unitHaar R N) C₀ hC₀ A₀ hA₀
    (fun _ _ _ => rfl) (projectedShellData_bounds R D L)

/-- The actual target Hecke character now supplies every local period;
there is no remaining arbitrary local phase in this constructor. -/
def targetFiniteMellinData (θ : HeckeCharacter F) :
    FiniteMellinData F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) :=
  finiteMellinData R D N (TargetFinitePeriod.localPeriod R θ) C₀ hC₀ A₀ hA₀

/-- The exact enumeration used by the constructed table.  This freezes the
dependent local-class `Fintype` instances to `Fintype.ofFinite` in this
module.  Any later reindexing can use this equivalence rather than choosing
another enumeration of the same finite type. -/
def termClassEquiv (θ : HeckeCharacter F) :
    Fin (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).terms ≃
      (∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p) :=
  (Fintype.equivFin
    (PUnit × (∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p))).symm.trans
      (Equiv.punitProd (∀ p : R.A.Sf, ProjectFiniteClass.LocalClass R.A p))

theorem targetFiniteMellinData_admissible (θ : HeckeCharacter F) :
    FiniteMellinAdmissible F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
      (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ) :=
  finiteMellinData_admissible R D N (TargetFinitePeriod.localPeriod R θ)
    C₀ hC₀ A₀ hA₀

/-- Direct replacement for TH-FINITE-VALUATION-CUTOFF, for the exact
target-period table constructed above. -/
theorem targetFiniteMellinData_valuation_cutoff (θ : HeckeCharacter F) :
    ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ →
      (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).coefficient u κ l p k = 0 :=
  (targetFiniteMellinData_admissible R D N C₀ hC₀ A₀ hA₀ θ).valuation_cutoff

/-- Direct replacement for TH-FINITE-VALUATION-DECAY, uniform over every
sector, class, tensor index and actual finite place. -/
theorem targetFiniteMellinData_valuation_decay (θ : HeckeCharacter F) :
    ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧ ∀ u κ l p k, 0 ≤ k →
      ‖(targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).coefficient u κ l p k‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ) :=
  (targetFiniteMellinData_admissible R D N C₀ hC₀ A₀ hA₀ θ).valuation_decay

theorem targetFiniteMellinData_absolute_mellin (θ : HeckeCharacter F)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (l : Fin (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).terms) (p : R.A.Sf)
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ =>
      (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).coefficient u κ l p k *
        (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s)) :=
  (targetFiniteMellinData_admissible R D N C₀ hC₀ A₀ hA₀ θ).absolute_mellin u κ l p s hs

/-- Fully specified target coefficient: chosen Haar, chosen source vector,
target period, actual power classes, chosen complement, and the inverse
Axiom Hilbert square are all retained in the literal shell integral. -/
theorem targetCoefficient_shell_spec (θ : HeckeCharacter F)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (l : Fin (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).terms)
    (p : R.A.Sf) (k : ℤ) :
    (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).coefficient u κ l p k =
      let tσ := (Fintype.equivFin
        (PUnit × (∀ q : R.A.Sf, ProjectFiniteClass.LocalClass R.A q))).symm l
      ∫ z,
        (if p = D.scalarSlot then ProjectFiniteClass.reflectedClassMask R.A
          R.probe.correction.B R.σ κ (ProjectFiniteClass.assemble R.A tσ.2) else 1) *
        (if (QuotientGroup.mk (ProjectLocalShell.shellPoint F p.val k z) :
            ProjectFiniteClass.LocalClass R.A p) = tσ.2 p then 1 else 0) *
        (TargetFinitePeriod.localPeriod R θ u p (ProjectLocalShell.shellPoint F p.val k z) : ℂ) *
        weylValue R D p (normalizedSelectedVector R D u p)
          (ProjectLocalShell.shellPoint F p.val k z) ∂unitHaar R N p := rfl

/-- The same coefficient specification expressed through the table's
stored enumeration.  In particular the `Fin terms` index is in bijection
with the genuine tuple of finite sixth-power classes. -/
theorem targetCoefficient_enumerated_spec (θ : HeckeCharacter F)
    (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))))
    (l : Fin (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).terms)
    (p : R.A.Sf) (k : ℤ) :
    (targetFiniteMellinData R D N C₀ hC₀ A₀ hA₀ θ).coefficient u κ l p k =
      ∫ z,
        (if p = D.scalarSlot then ProjectFiniteClass.reflectedClassMask R.A
          R.probe.correction.B R.σ κ
          (ProjectFiniteClass.assemble R.A (termClassEquiv R D N C₀ hC₀ A₀ hA₀ θ l))
          else 1) *
        (if (QuotientGroup.mk (ProjectLocalShell.shellPoint F p.val k z) :
            ProjectFiniteClass.LocalClass R.A p) =
            termClassEquiv R D N C₀ hC₀ A₀ hA₀ θ l p then 1 else 0) *
        (TargetFinitePeriod.localPeriod R θ u p (ProjectLocalShell.shellPoint F p.val k z) : ℂ) *
        weylValue R D p (normalizedSelectedVector R D u p)
          (ProjectLocalShell.shellPoint F p.val k z) ∂unitHaar R N p := rfl

section TargetProjectedSource

variable {N₁ : TraceHaarTransport R}
  {A : ThetaExpansion.FirstRootSphericalSeed R N₁}
  {B : ThetaExpansion.FirstRootCutoffs R}
  (J : ThetaExpansion.FirstRootProjected R N₁ A B)

/-- Nonzero local normalization for the actual target-projected source
follows from its proved unreflected radial profile. -/
theorem target_projected_source_nonzero (u : R.A.UnitQuotient) :
    fourier R J.base.sources.dq (J.base.realization.theta u) 1 ≠ 0 := by
  rw [← ThetaExpansion.diagonal_one R, J.radial]
  exact FiniteWhittakerProjectors.radialProfile_one_ne_zero R J.cutoffs

theorem target_projected_normalization (u : R.A.UnitQuotient) (p : R.A.Sf) :
    J.base.factorization.ell (Sum.inr p.val)
      (normalizedSelectedVector R J.base.factorization u p) = 1 :=
  normalizedSelectedVector_value R J.base.factorization
    (target_projected_source_nonzero R J) u p

end TargetProjectedSource

end ThetaGlobal.ProjectedFiniteMellin

#print axioms ThetaGlobal.ProjectedFiniteMellin.selected_source_provenance
#print axioms ThetaGlobal.ProjectedFiniteMellin.normalizedSelectedVector_value
#print axioms ThetaGlobal.ProjectedFiniteMellin.finiteMellinData_admissible
#print axioms ThetaGlobal.ProjectedFiniteMellin.targetCoefficient_shell_spec
#print axioms ThetaGlobal.ProjectedFiniteMellin.target_projected_normalization
