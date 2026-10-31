import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylSupport
import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods
import ThetaGlobal.FiniteLocalShellProject

/-!
# Whittaker bounds for actual finite vectors after target projection

The local vector in this file belongs to the actual canonical exceptional
image representation.  It may be any finite root-projector output, rather
than the old principal-period vector.  Large support and every positive
small-norm exponent below `1/3` are proved from the existing representation
theorems and the stored global Whittaker functional.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section

namespace ThetaGlobal.FiniteCanonicalVectors

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

abbrev Vector (p : R.A.Sf) := actualLocal R D.finiteData (Sum.inr p.val)

abbrev action (p : R.A.Sf) :=
  KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
    R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
    (D.finiteData p.val).inducing.polarization
    (D.finiteData p.val).haar (D.finiteData p.val).haar_integer

def functional (p : R.A.Sf) : CanonicalSmoothModule (Vector R D p) →L[ℂ] ℂ :=
  let f := (D.ell (Sum.inr p.val)).comp
    (canonicalSmoothModuleEquiv (Vector R D p)).toLinearMap
  ⟨f, canonicalSmoothModule_linear_continuous f⟩

/-- Actual Weyl-translated local Whittaker coefficient.  In particular the
vector is not a freely chosen function on the local multiplicative group. -/
def weylValue (p : R.A.Sf) (φ : Vector R D p)
    (z : (p.val.adicCompletion F)ˣ) : ℂ :=
  D.ell (Sum.inr p.val)
    (action R D p (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z)
      (action R D p (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) φ))

theorem functional_whittaker (p : R.A.Sf) :
    functional R D p ∈ localWhittakerSpace (Multiplicative (p.val.adicCompletion F))
      (CanonicalSmoothModule (Vector R D p))
      ((canonicalSmoothRepresentation (action R D p)).comp
        (KPLocalJacquetImage.root (D.finiteData p.val).inducing.borel))
      (SheetRescaling.finiteTrace p.val).toAddChar.toMonoidHom := by
  intro t b
  have h := ell_finite_root R D p.val t.toAdd b
  rw [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter] at h
  have hr := ((D.finiteData p.val).inducing.openCell
    (D.finiteData p.val).inducing.polarization).upper_eq t.toAdd
  change ((D.finiteData p.val).inducing.borel.upperRoot t :
    KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 p.val) = _ at hr
  change D.ell (Sum.inr p.val)
    (action R D p ((D.finiteData p.val).inducing.borel.upperRoot t) b) = _
  rw [hr]
  exact h

theorem weylValue_small_power (p : R.A.Sf) (φ : Vector R D p)
    (δ : ℝ) (hδ : 0 < δ) (hδthird : δ < 1 / 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : (p.val.adicCompletion F)ˣ,
      ‖z.val‖ ≤ 1 → ‖weylValue R D p φ z‖ ≤ B * ‖z.val‖ ^ δ := by
  obtain ⟨B, hB, hb⟩ := KPInterface.ActualFiniteOutputSteps.actual_small_norm_decay_canonical
    R.A.zeta12 R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
    (D.finiteData p.val).inducing.polarization
    (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
    (SheetRescaling.finiteTrace p.val) (functional R D p) (functional_whittaker R D p)
    (action R D p (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) φ)
    δ hδ hδthird
  exact ⟨B, hB, fun z hz => hb z (norm_pos_iff.mpr z.ne_zero) hz⟩

theorem weylValue_support (p : R.A.Sf) (φ : Vector R D p) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : (p.val.adicCompletion F)ˣ,
      M < ‖z.val‖ → weylValue R D p φ z = 0 := by
  have hsmooth := smoothRepresentation_orbit_isLocallyConstant (action R D p)
    (KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
      R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
      (D.finiteData p.val).inducing.polarization
      (D.finiteData p.val).haar (D.finiteData p.val).haar_integer)
  have hn := (KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 p.val
    (KPAdelicCoverRestrictedProduct.depth F R.A.zeta12 R.A.primitive_zeta12 p.val)
    (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 p.val)).1
  have hWh : ∀ t b, D.ell (Sum.inr p.val)
      (action R D p (SheetRescaling.finiteRoot R p.val t) b) =
      (localFiniteCharacter F p.val t : ℂ) * D.ell (Sum.inr p.val) b := by
    intro t b
    have h := ell_finite_root R D p.val t b
    simp only [CodifferentResidueSieve.localTraceCharacter_eq_localFiniteCharacter] at h
    exact h
  exact KPFiniteLocal.generic_fixed_vector_support p.val (action R D p) hsmooth
    (SheetRescaling.finiteRoot R p.val) hn
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (SheetRescaling.finite_conjugacy R p.val) (localFiniteCharacter F p.val)
    (SheetRescaling.finite_trace_nontrivial p.val) (D.ell (Sum.inr p.val)) hWh
    (action R D p (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) φ)

theorem weylValue_locallyConstant (p : R.A.Sf) (φ : Vector R D p) :
    IsLocallyConstant (weylValue R D p φ) := by
  have hsmooth := smoothRepresentation_orbit_isLocallyConstant (action R D p)
    (KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
      R.A.primitive_zeta12 p.val (D.finiteData p.val).inducing
      (D.finiteData p.val).inducing.polarization
      (D.finiteData p.val).haar (D.finiteData p.val).haar_integer)
  have ha := (KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 p.val
    (KPAdelicCoverRestrictedProduct.depth F R.A.zeta12 R.A.primitive_zeta12 p.val)
    (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 p.val)).2.2
  exact KPFiniteLocal.whittakerValue_locallyConstant (action R D p) hsmooth
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) ha
    (D.ell (Sum.inr p.val))
    (action R D p (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) φ)

/-- Literal shell data for the actual canonical vector and the supplied
local component of the target period. -/
def vectorShellData (p : R.A.Sf) (φ : Vector R D p)
    (L : (p.val.adicCompletion F)ˣ → Circle) :=
  ProjectLocalShell.shellData F p.val (weylValue R D p φ) L

/-- All support/decay hypotheses of the shell construction are discharged
by actual canonical-representation theorems, for every projected vector. -/
theorem vectorShellData_bounds (p : R.A.Sf) (φ : Vector R D p)
    (L : (p.val.adicCompletion F)ˣ → Circle) :
    FiniteShell.LocalWhittakerBounds (vectorShellData R D p φ L) :=
  ProjectLocalShell.shellData_bounds F p.val (weylValue R D p φ) L
    (weylValue_support R D p φ) (fun δ hδ hδ' => by
      obtain ⟨B, hB, hb⟩ := weylValue_small_power R D p φ δ hδ hδ'
      exact ⟨B, hB.le, hb⟩)

end ThetaGlobal.FiniteCanonicalVectors

#print axioms ThetaGlobal.FiniteCanonicalVectors.weylValue_support
#print axioms ThetaGlobal.FiniteCanonicalVectors.weylValue_small_power
#print axioms ThetaGlobal.FiniteCanonicalVectors.vectorShellData_bounds
