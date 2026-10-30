import HeckeGeneral.Characters.LocalConductor
import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteProjector

/-!
# Project the actual finite source inside the target character's kernel

The target Hecke character is allowed arbitrary unitary uniformizer values.
Continuity supplies a small open neighborhood of integral units on which
each local component is one.  The existing sixth-power cutoff is shrunk
inside those neighborhoods, then the actual finite root projector is run
on that cutoff.  Its source, residue, local representations and exterior
coefficients are retained by the upstream projector theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.TargetFiniteCutoff

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open HeckeGeneral.Characters
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

/-- The source's compact sixth-power cutoffs can be chosen inside the
actual target local-character kernels, with all archimedean exponents
preserved.  No finite-order condition on uniformizer values is used. -/
theorem target_cutoffs_exist (θ : HeckeCharacter F) (B : FirstRootCutoffs R) :
    ∃ B' : FirstRootCutoffs R,
      B'.exponent = B.exponent ∧
      (∀ p, B'.cutoff p ≤ B.cutoff p) ∧
      ∀ p z, z ∈ B'.cutoff p → localComponent F p.val θ z = 1 := by
  choose ε hε htrivial using fun p : R.A.Sf =>
    exists_radius_trivial (localComponent F p.val θ)
  let V (p : R.A.Sf) : Set (p.val.adicCompletion F)ˣ :=
    {z | ‖z.val - 1‖ < ε p}
  have hV (p : R.A.Sf) : IsOpen (V p) :=
    isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
  have h1 (p : R.A.Sf) : (1 : (p.val.adicCompletion F)ˣ) ∈ V p := by
    change ‖(1 : p.val.adicCompletion F) - 1‖ < ε p
    simpa using hε p
  obtain ⟨B', he, hle, hsub⟩ := B.shrink V hV h1
  exact ⟨B', he, hle, fun p z hz => htrivial p z (hsub p hz)⟩

/-- Concrete target-kernel finite projection.  This constructs the
projected global source by the established finite root-translation words;
the target-kernel conclusion follows from the proved cutoff inclusion. -/
theorem target_projected_source_exists (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N)
    (B : FirstRootCutoffs R) (hNative : SourceNativeLie R A.base.factorization)
    (θ : HeckeCharacter F) :
    ∃ (B' : FirstRootCutoffs R) (J : FirstRootProjected R N A B'),
      B'.exponent = B.exponent ∧
      (∀ p, J.cutoffs.cutoff p ≤ B.cutoff p) ∧
      (∀ p z, z ∈ J.cutoffs.cutoff p → localComponent F p.val θ z = 1) ∧
      SourceNativeLie R J.base.factorization := by
  obtain ⟨B', he, hle, hker⟩ := target_cutoffs_exist R θ B
  obtain ⟨J, hJ⟩ := RootDerivatives.finite_projector_native R hR N A B' hNative
  exact ⟨B', J, he, fun p => (J.cutoff_le p).trans (hle p),
    fun p z hz => hker p z (J.cutoff_le p hz), hJ⟩

/-- The inverse period component is also one on the same cutoff. -/
theorem inverse_local_component_on_cutoff (θ : HeckeCharacter F)
    (B : FirstRootCutoffs R)
    (hker : ∀ p z, z ∈ B.cutoff p → localComponent F p.val θ z = 1)
    (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ) (hz : z ∈ B.cutoff p) :
    (localComponent F p.val θ z)⁻¹ = 1 := by rw [hker p z hz, inv_one]

end ThetaGlobal.TargetFiniteCutoff

#print axioms ThetaGlobal.TargetFiniteCutoff.target_cutoffs_exist
#print axioms ThetaGlobal.TargetFiniteCutoff.target_projected_source_exists
