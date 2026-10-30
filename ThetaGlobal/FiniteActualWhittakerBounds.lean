import DedekindZetaZeroFree.Theta.Whittaker.FiniteWeylSupport
import ThetaGlobal.FiniteShellCoefficients

/-!
# All small-norm exponents for the existing actual finite KP vectors

`FiniteWeylSupport.localWeyl_small_norm` fixes the exponent to `1/4`.
The underlying canonical-image theorem proves every positive exponent below
`1/3`.  This adapter retains that exponent and thus supplies the precise
local input needed by the finite Mellin half-plane.

It concerns the existing actual selected vector.  Matching that selected
vector to a newly chosen target-period test vector remains a separate local
realization task; this module does not assert such an identification.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace ThetaGlobal.ActualFiniteBounds

open NumberField MeasureTheory
open DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.SheetRescaling
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

/-- The actual normalized Weyl vector has every positive small-norm power
below `1/3`; the numerator comes from the canonical Jacquet-image theorem
and the denominator is the proved nonzero selected-tensor normalization. -/
theorem localWeyl_small_power (v : R.A.UnitQuotient) (p : R.A.Sf)
    (δ : ℝ) (hδ : 0 < δ) (hδthird : δ < 1 / 3) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : (p.val.adicCompletion F)ˣ,
      ‖(z : p.val.adicCompletion F)‖ ≤ 1 →
      ‖ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z‖ ≤
        D * Real.rpow ‖(z : p.val.adicCompletion F)‖ δ := by
  obtain ⟨s, x, hs, hx⟩ := C.factorization.selected_frozen_stage v
  have hp : Sum.inr p.val ∈ s.val := by
    rw [hs]
    exact (C.factorization.bad_exact _).mpr (Or.inr ⟨p.val, rfl, p.property⟩)
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
    R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
    (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
  let φ : CanonicalSmoothModule (actualLocal R C.factorization.finiteData (Sum.inr p.val)) :=
    ρ (KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
      (x ⟨Sum.inr p.val, hp⟩)
  obtain ⟨B, hB, hb⟩ := KPInterface.ActualFiniteOutputSteps.actual_small_norm_decay_canonical
    R.A.zeta12 R.A.primitive_zeta12 p.val (C.factorization.finiteData p.val).inducing
    (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer
    (finiteTrace p.val) (finiteEll R C p.val) (finiteEll_whittaker R C v s x hx p.val hp)
    φ δ hδ hδthird
  have hd : 0 < ‖C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩)‖ :=
    norm_pos_iff.mpr (selected_tensor_nonzero R C v s x hx ⟨Sum.inr p.val, hp⟩)
  refine ⟨B / ‖C.factorization.ell (Sum.inr p.val) (x ⟨Sum.inr p.val, hp⟩)‖,
    div_pos hB hd, ?_⟩
  intro z hz
  rw [localWeylValue_eq R C v s x hx p.val hp, norm_div]
  have h := hb z (norm_pos_iff.mpr z.ne_zero) hz
  have he : (finiteEll R C p.val)
      (canonicalSmoothRepresentation ρ (KPPGLLocalCover.A F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inr p.val) z) φ) =
      C.factorization.ell (Sum.inr p.val)
        (ρ (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z *
          KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
          (x ⟨Sum.inr p.val, hp⟩)) := by
    simp only [finiteEll, ContinuousLinearMap.coe_mk', LinearMap.comp_apply,
      canonicalSmoothModuleEquiv, LinearEquiv.refl_apply,
      canonicalSmoothRepresentation, φ, map_mul, Module.End.mul_apply]
    rfl
  change ‖(finiteEll R C p.val) (canonicalSmoothRepresentation ρ
    (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z) φ)‖ ≤ _ at h
  rw [he] at h
  exact (div_le_div_of_nonneg_right h hd.le).trans_eq (by ring)

/-- Attach the actual selected-vector bounds to any shell parametrization
of that same local Whittaker function.  The two equality hypotheses are
data-identification dictionaries; no coefficient estimate is assumed. -/
theorem actual_local_bounds {Branch U : Type*}
    (v : R.A.UnitQuotient) (p : R.A.Sf)
    (d : FiniteShell.LocalShellData Branch (p.val.adicCompletion F)ˣ U)
    (hradius : d.radius = fun z => ‖(z : p.val.adicCompletion F)‖)
    (hvalue : d.value = fun z =>
      ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr p.val) z) :
    FiniteShell.LocalWhittakerBounds d := by
  constructor
  · obtain ⟨M, hM, hm⟩ := localWeyl_support R C v p
    refine ⟨M, hM, ?_⟩
    intro z hz
    rw [hradius] at hz
    rw [hvalue]
    exact hm z hz
  · intro δ hδ hδthird
    obtain ⟨D, hD, hd⟩ := localWeyl_small_power R C v p δ hδ hδthird
    refine ⟨D, hD.le, ?_⟩
    intro z _ hz
    rw [hradius] at hz
    rw [hvalue, hradius]
    exact hd z hz

end ThetaGlobal.ActualFiniteBounds

#print axioms ThetaGlobal.ActualFiniteBounds.localWeyl_small_power
#print axioms ThetaGlobal.ActualFiniteBounds.actual_local_bounds
