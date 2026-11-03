import ThetaGlobal.FiniteTargetCutoff
import ThetaGlobal.FiniteClassProject
import Mathlib.Algebra.BigOperators.Pi

/-!
# The actual finite components of the target period

The Hecke component occurs inversely on the S-side.  The sector correction
uses Axiom's positive Hilbert pairing, which is the inverse of the paper's
pairing.  Thus this is exactly `L_base * H_paper(unit, ·)^(-1)`.
Uniformizer values are retained literally and need not have finite order.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.TargetFinitePeriod

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaExpansion
open HeckeGeneral.Characters
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def finiteSlot (p : R.A.Sf) : (p.val.adicCompletion F)ˣ →* R.A.G :=
  (1 : (p.val.adicCompletion F)ˣ →* (∀ w : InfinitePlace F, w.Completionˣ)).prod
    (MonoidHom.mulSingle (fun q : R.A.Sf => (q.val.adicCompletion F)ˣ) p)

@[simp] theorem finiteSlot_apply (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ) :
    finiteSlot R p z = (1, Pi.mulSingle p z) := rfl

theorem finiteSlot_prod (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    (∏ p, finiteSlot R p (z p)) = (1, z) := by
  apply Prod.ext
  · simp only [finiteSlot_apply, Prod.fst_prod, Finset.prod_const_one]
  · simp only [finiteSlot_apply, Prod.snd_prod]
    exact Finset.univ_prod_mulSingle z

def sectorPhaseHom (u : R.A.UnitQuotient) : R.A.G →* ℂ :=
  R.σ.toMonoidHom.comp ((Units.coeHom F).comp ((rootsOfUnity 6 F).subtype.comp
    ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)).comp
      (QuotientGroup.mk' R.A.sixthPowers))))

theorem sectorPhaseHom_norm (u : R.A.UnitQuotient) (y : R.A.G) :
    ‖sectorPhaseHom R u y‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
  change (R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
    (QuotientGroup.mk' R.A.sixthPowers y) : Fˣ) : F)) ^ 6 = 1
  rw [← map_pow]
  have h := congrArg (fun z : Fˣ => (z : F))
    (R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
      (QuotientGroup.mk' R.A.sixthPowers y)).property
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using congrArg R.σ h

def sectorPhase (u : R.A.UnitQuotient) (p : R.A.Sf)
    (z : (p.val.adicCompletion F)ˣ) : Circle :=
  ⟨sectorPhaseHom R u (finiteSlot R p z),
    mem_sphere_zero_iff_norm.mpr (sectorPhaseHom_norm R u _)⟩

/-- The genuine target local period, with its full uniformizer value. -/
def localPeriod (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (p : R.A.Sf)
    (z : (p.val.adicCompletion F)ˣ) : Circle :=
  (localComponent F p.val θ z)⁻¹ * sectorPhase R u p z

theorem localPeriod_spec (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ) :
    (localPeriod R θ u p z : ℂ) =
      (localComponent F p.val θ z : ℂ)⁻¹ *
      R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
        (QuotientGroup.mk' R.A.sixthPowers (finiteSlot R p z)) : Fˣ) : F) := rfl

/-- Reassembling the local components yields the exact finite part of
the target S-period, including the positive Axiom Hilbert sector phase. -/
theorem localPeriod_product (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    (∏ p, (localPeriod R θ u p (z p) : ℂ)) =
      (∏ p, (localComponent F p.val θ (z p) : ℂ)⁻¹) *
      sectorPhaseHom R u (1, z) := by
  change (∏ p, (localComponent F p.val θ (z p) : ℂ)⁻¹ *
    sectorPhaseHom R u (finiteSlot R p (z p))) = _
  rw [Finset.prod_mul_distrib, ← map_prod, finiteSlot_prod]

theorem sectorPhase_on_sixth_power (u : R.A.UnitQuotient) (p : R.A.Sf)
    (z : (p.val.adicCompletion F)ˣ) (hz : ∃ w, w ^ 6 = z) :
    sectorPhaseHom R u (finiteSlot R p z) = 1 := by
  obtain ⟨w, rfl⟩ := hz
  have hc : QuotientGroup.mk' R.A.sixthPowers (finiteSlot R p (w ^ 6)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨finiteSlot R p w, (map_pow (finiteSlot R p) w 6).symm⟩
  change R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
    (QuotientGroup.mk' R.A.sixthPowers (finiteSlot R p (w ^ 6))) : Fˣ) : F) = 1
  simp only [hc, map_one, OneMemClass.coe_one, Units.val_one]

/-- The target-kernel cutoff also kills the unit-sector correction, since
that cutoff consists of genuine sixth powers. -/
theorem localPeriod_on_cutoff (θ : HeckeCharacter F) (B : FirstRootCutoffs R)
    (hθ : ∀ p z, z ∈ B.cutoff p → localComponent F p.val θ z = 1)
    (u : R.A.UnitQuotient) (p : R.A.Sf) (z : (p.val.adicCompletion F)ˣ)
    (hz : z ∈ B.cutoff p) : localPeriod R θ u p z = 1 := by
  apply Subtype.ext
  change (localComponent F p.val θ z : ℂ)⁻¹ *
    sectorPhaseHom R u (finiteSlot R p z) = 1
  rw [hθ p z hz, Circle.coe_one, inv_one, one_mul,
    sectorPhase_on_sixth_power R u p z (B.sixth p z hz)]

theorem locallyConstant_of_open_kernel
    {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : G →* M) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hf : ∀ z ∈ U, f z = 1) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro x
  refine ⟨{y | x⁻¹ * y ∈ U}, hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using U.one_mem
  · intro y hy
    calc
      f y = f (x * (x⁻¹ * y)) := by rw [mul_inv_cancel_left]
      _ = f x * f (x⁻¹ * y) := map_mul f _ _
      _ = f x := by rw [hf _ hy, mul_one]

/-- Each actual finite sixth-power class is locally constant: the
explicit compact open cutoff is contained in the power subgroup. -/
theorem localClass_locallyConstant (B : FirstRootCutoffs R) (p : R.A.Sf) :
    IsLocallyConstant (fun z : (p.val.adicCompletion F)ˣ =>
      (QuotientGroup.mk z : ProjectFiniteClass.LocalClass R.A p)) := by
  apply locallyConstant_of_open_kernel
    (QuotientGroup.mk' (powMonoidHom (α := (p.val.adicCompletion F)ˣ) 6).range)
    (B.cutoff p) (B.open_cutoff p)
  intro z hz
  exact (QuotientGroup.eq_one_iff _).mpr (B.sixth p z hz)

theorem sectorPhase_continuous (B : FirstRootCutoffs R)
    (u : R.A.UnitQuotient) (p : R.A.Sf) :
    Continuous (fun z => (sectorPhase R u p z : ℂ)) := by
  exact (locallyConstant_of_open_kernel ((sectorPhaseHom R u).comp (finiteSlot R p))
    (B.cutoff p) (B.open_cutoff p)
    (fun z hz => sectorPhase_on_sixth_power R u p z (B.sixth p z hz))).continuous

theorem localPeriod_continuous (θ : HeckeCharacter F) (B : FirstRootCutoffs R)
    (u : R.A.UnitQuotient) (p : R.A.Sf) :
    Continuous (fun z => (localPeriod R θ u p z : ℂ)) := by
  have hθ : Continuous (fun z => (localComponent F p.val θ z : ℂ)) :=
    continuous_subtype_val.comp (localComponent F p.val θ).continuous
  exact (hθ.inv₀ (fun z => Circle.coe_ne_zero _)).mul (sectorPhase_continuous R B u p)

end ThetaGlobal.TargetFinitePeriod

#print axioms ThetaGlobal.TargetFinitePeriod.localPeriod_product
#print axioms ThetaGlobal.TargetFinitePeriod.localPeriod_on_cutoff
#print axioms ThetaGlobal.TargetFinitePeriod.localPeriod_continuous
