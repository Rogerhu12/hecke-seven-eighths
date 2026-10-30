module

public import ThetaGlobal.FiniteFixedSource
public import ThetaGlobal.GlobalProjectRadial
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.ResidualRadialCovariance

/-!
# Constant-term covariance for the actual projected finite source

The first-root lift's constructive proof already recovers the original
Harish-Chandra span.  Retaining that theorem lets its proved residual
constant term descend to the original projected source.  The source,
finite vectors, coefficient table, quotient Haar and high K-type tensor
remain the ones constructed in `FiniteFixedSource`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.FiniteSourceConstantTerm

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_flat_lift_with_recovery
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B)
    (hNative : RootDerivatives.SourceNativeLie R J.base.factorization) :
    ∃ L : FirstRootLift R N A B J,
      hcHeckeSpan J.base.realization ≤ hcHeckeSpan L.base.realization := by
  classical
  obtain ⟨Q, T, hdq, hpin, hsource, htheta, hperiod, hflat⟩ :=
    first_root_realization_exists  R hR N A B J
  obtain ⟨hcore, hfrozen⟩ := first_root_fixed_stage_tensors_exists R N A B J hNative
  obtain ⟨hhc, _, _⟩ := first_root_hc_span_recovery R N A B J hNative T
    hdq hpin hsource hperiod hfrozen
  choose s x hs hx hell hnx hpx using hfrozen
  let D := J.base.factorization
  let D' : SourceFactorization R Q T := {
    finiteData := D.finiteData
    references := D.references
    bad := D.bad
    bad_exact := D.bad_exact
    ell := D.ell
    reference_value := D.reference_value
    scalarSlot := D.scalarSlot
    coreMap := D.coreMap
    selected := fun v => RestrictedTensorSimple.stageInclusion _ D.references D.bad (s v)
      (PiTensorProduct.tprod ℂ (x v))
    selected_eq := fun v => (hx v).trans (hpin v).symm
    selected_frozen_stage := fun v => ⟨s v, x v, hs v, rfl⟩
    core_injective := D.core_injective
    core_same_residue := fun z => ⟨hhc (D.core_same_residue z).1, (D.core_same_residue z).2⟩
    finite_intertwining := D.finite_intertwining
    complex_intertwining := D.complex_intertwining
    product_integrable := by rw [hdq]; exact D.product_integrable
    product_exact := by rw [hdq]; exact D.product_exact
    spherical_reference := D.spherical_reference
    detected_tensor := by rw [hdq]; exact D.detected_tensor
    period_integrable := fun v g => FourierContinuation.theta_period_integrable T v g
    detected := by obtain ⟨v, _⟩ := D.detected; exact ⟨v, hperiod v⟩ }
  let C : JointExteriorCoefficientSources R N := {
    aligned := hR
    transport := N
    transport_exact := rfl
    sources := Q
    realization := T
    factorization := D'
    localHaarTransport := fun q => by
      have hh := J.base.localHaarTransport q
      rw [J.base.transport_exact] at hh
      exact hh
    exterior := ⟨J.base.exterior.rational_exact, J.base.exterior.crt_product,
      J.base.exterior.local_exact⟩ }
  exact ⟨⟨C, hdq, hpin⟩, hhc⟩

end ThetaGlobal.FiniteSourceConstantTerm

namespace ThetaGlobal.FiniteFixedSource

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

/-- The constant-term law is proved for the exact original projected
source; it is not a new field of the local high K-type input. -/
theorem Source.constantTerm (R : PrincipalMellin.ActualRecipe S η)
    (θ : HeckeGeneral.Characters.HeckeCharacter F) (C : Source R θ) :
    ResidualConstantTerm R C.projected.base.sources C.projected.base.realization := by
  obtain ⟨L, hrecover⟩ := FiniteSourceConstantTerm.first_root_flat_lift_with_recovery
    R C.projected.base.aligned C.transport C.spherical C.initialCutoffs C.projected C.native
  obtain ⟨hi, hd⟩ := first_root_derivative_period
    R C.transport C.spherical C.initialCutoffs C.projected
  let A := L.toJointForwardIdentitySources hi hd
  have hconstant : ResidualConstantTerm R L.base.sources L.base.realization :=
    ChamberPeriods.constantTerm_of_jointForwardIdentitySources A
  have hselected (u : R.A.UnitQuotient) :
      C.projected.base.realization.theta u ∈ hcHeckeSpan C.projected.base.realization := by
    rw [← C.projected.base.factorization.selected_eq u]
    exact (C.projected.base.factorization.core_same_residue _).1
  refine ⟨?_, ?_⟩
  · intro u g
    exact GlobalProjectRadial.hcHeckeSpan_upper_integrable R
      C.projected.base.realization (hselected u) g
  · intro u w z g
    have h := GlobalProjectRadial.hcHeckeSpan_upper_radial R hconstant
      (hrecover (hselected u)) w z g
    rw [L.dq_exact] at h
    exact h

end ThetaGlobal.FiniteFixedSource

#print axioms ThetaGlobal.FiniteSourceConstantTerm.first_root_flat_lift_with_recovery
#print axioms ThetaGlobal.FiniteFixedSource.Source.constantTerm
