import ThetaGlobal.FiniteTargetPeriod
import ThetaGlobal.GlobalProjectAngular
import HeckeAxiom.RaySpan
import DedekindZetaZeroFree.Theta.Periods.WeightedQuotientIntegrability

/-!
# The target S-period on the actual chosen arithmetic group

The global Hecke character restricts to the product of its genuine local
components.  Its inverse is the S-period convention used in reflection.
The sector factor is the positive Axiom Hilbert pairing, equivalently
the inverse of the paper pairing.

The character is trivial on sixth powers of S-units when S contains the
finite conductor, and its value on the explicit complex rotation is -1.
The finite slots agree literally with `TargetFinitePeriod.localPeriod`.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalTargetPeriod

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

def sHeckeHom (θ : HeckeCharacter F) : R.A.G →* Circle where
  toFun y := (∏ w : InfinitePlace F, infiniteComponent F w θ (y.1 w)) *
    ∏ p : R.A.Sf, localComponent F p.val θ (y.2 p)
  map_one' := by simp
  map_mul' := by
    intro y z
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul,
      Finset.prod_mul_distrib]
    ac_rfl

def period (θ : HeckeCharacter F) (u : R.A.UnitQuotient) : R.A.G →* ℂ :=
  (Circle.coeHom.comp (sHeckeHom R θ)⁻¹) * TargetFinitePeriod.sectorPhaseHom R u

theorem period_spec (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (y : R.A.G) :
    period R θ u y =
      ((∏ w : InfinitePlace F, (infiniteComponent F w θ (y.1 w) : ℂ)) *
        ∏ p : R.A.Sf, (localComponent F p.val θ (y.2 p) : ℂ))⁻¹ *
      TargetFinitePeriod.sectorPhaseHom R u y := by
  change ((sHeckeHom R θ y : Circle) : ℂ)⁻¹ * TargetFinitePeriod.sectorPhaseHom R u y = _
  congr 2
  change Circle.coeHom (sHeckeHom R θ y) = _
  simp only [sHeckeHom, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_prod] <;> rfl

theorem period_norm (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (y : R.A.G) :
    ‖period R θ u y‖ = 1 := by
  change ‖((sHeckeHom R θ y : Circle) : ℂ)⁻¹ *
    TargetFinitePeriod.sectorPhaseHom R u y‖ = 1
  rw [norm_mul, norm_inv, Circle.norm_coe, inv_one,
    TargetFinitePeriod.sectorPhaseHom_norm, one_mul]

theorem period_ne_zero (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (y : R.A.G) :
    period R θ u y ≠ 0 := by
  intro hz
  have h := period_norm R θ u y
  rw [hz, norm_zero] at h
  exact zero_ne_one h

theorem sHeckeHom_continuous (θ : HeckeCharacter F) : Continuous (sHeckeHom R θ) := by
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w _
    exact (infiniteComponent F w θ).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  · apply continuous_finset_prod
    intro p _
    exact (localComponent F p.val θ).continuous.comp
      ((continuous_apply p).comp continuous_snd)

theorem period_measurable (θ : HeckeCharacter F) (u : R.A.UnitQuotient) :
    Measurable (period R θ u) := by
  have hbase : Measurable (fun y : R.A.G => (sHeckeHom R θ y : ℂ)⁻¹) :=
    (continuous_subtype_val.comp (sHeckeHom_continuous R θ)).measurable.inv
  have hphase : Measurable (TargetFinitePeriod.sectorPhaseHom R u) :=
    DigitMasks.finite_class_measurable R.A (fun κ =>
      R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val) κ : Fˣ) : F))
  exact hbase.mul hphase

theorem sHeckeHom_diagonal_unit (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (u : R.A.U) :
    sHeckeHom R θ (R.A.diagonal u.val) = 1 := by
  have hfinite : (∏ p : R.A.Sf,
      localComponent F p.val θ ((R.A.diagonal u.val).2 p)) =
      sUnitFiniteCharacter F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) θ u := by
    rw [HeckeAxiom.sUnitFiniteCharacter_eq_prod F R.A.Sf θ hS u]
    exact Finset.prod_coe_sort R.A.Sf
      (fun p => localComponent F p θ (sUnitLocal F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) p u))
  change (sUnitInfinityCharacter F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) θ u) *
    (∏ p : R.A.Sf, localComponent F p.val θ ((R.A.diagonal u.val).2 p)) = 1
  rw [hfinite, mul_comm]
  exact sUnitFinite_mul_infinity_eq_one F (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) θ u

theorem period_diagonal_unit_sixth (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (ε : R.A.U) :
    period R θ u (R.A.diagonal (ε.val ^ 6)) = 1 := by
  have hθ : sHeckeHom R θ (R.A.diagonal (ε.val ^ 6)) = 1 := by
    have h6 := sHeckeHom_diagonal_unit R θ hS (ε ^ 6)
    rwa [SubgroupClass.coe_pow] at h6
  have hk : QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal (ε.val ^ 6)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨R.A.diagonal ε.val, (map_pow R.A.diagonal ε.val 6).symm⟩
  change ((sHeckeHom R θ (R.A.diagonal (ε.val ^ 6)) : Circle) : ℂ)⁻¹ *
    R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
      (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal (ε.val ^ 6))) : Fˣ) : F) = 1
  simp only [hθ, hk, Circle.coe_one, inv_one, map_one,
    OneMemClass.coe_one, Units.val_one, one_mul]

theorem period_gamma (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (γ : R.A.Gamma1) :
    period R θ u γ.val.val = 1 := by
  let δ : R.A.Gamma := ⟨γ.val.val, γ.property⟩
  obtain ⟨q, ⟨ε, hε, rfl⟩, hq⟩ := δ.property
  change period R θ u δ.val = 1
  rw [← hq]
  exact period_diagonal_unit_sixth R θ hS u ⟨ε, hε⟩

theorem period_infiniteInsertion (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (w : InfinitePlace F) (z : w.Completionˣ) :
    period R θ u (IdeleInsertion.infiniteInsertion R.A w z) =
      (infiniteComponent F w θ z : ℂ)⁻¹ := by
  have hθ : sHeckeHom R θ (IdeleInsertion.infiniteInsertion R.A w z) =
      infiniteComponent F w θ z := by
    change (∏ v : InfinitePlace F, infiniteComponent F v θ
      ((IdeleInsertion.infiniteInsertion R.A w z).1 v)) *
      (∏ p : R.A.Sf, localComponent F p.val θ
        ((IdeleInsertion.infiniteInsertion R.A w z).2 p)) = _
    simp only [IdeleInsertion.infiniteInsertion, Pi.one_apply, map_one,
      Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single w]
    · simp
    · intro v _ hv
      simp [Function.update_of_ne hv]
    · simp
  have hphase : TargetFinitePeriod.sectorPhaseHom R u
      (IdeleInsertion.infiniteInsertion R.A w z) = 1 := by
    change R.σ ((R.A.H_S6 (R.A.sClass (R.probe.unitReps.representative u).val)
      (QuotientGroup.mk' R.A.sixthPowers
        (IdeleInsertion.infiniteInsertion R.A w z)) : Fˣ) : F) = 1
    rw [IdeleInsertion.insertion_class_eq_one R]
    simp only [map_one, OneMemClass.coe_one, Units.val_one]
  change ((sHeckeHom R θ (IdeleInsertion.infiniteInsertion R.A w z) : Circle) : ℂ)⁻¹ *
    TargetFinitePeriod.sectorPhaseHom R u (IdeleInsertion.infiniteInsertion R.A w z) = _
  rw [hθ, hphase, mul_one]

theorem period_rotation (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (w : InfinitePlace F) (hw : w.IsComplex)
    (hk : heckeComplexWeight F w hw θ ≠ 0) :
    period R θ u (IdeleInsertion.infiniteInsertion R.A w
      (GlobalProjectAngular.complexRotation θ w hw)) = -1 := by
  rw [period_infiniteInsertion,
    GlobalProjectAngular.complexRotation_inverse_character θ w hw hk]

/-- The finite product is exactly the table's local target period. -/
theorem period_finite_part (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (z : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) :
    period R θ u (1, z) =
      ∏ p, (TargetFinitePeriod.localPeriod R θ u p (z p) : ℂ) := by
  rw [TargetFinitePeriod.localPeriod_product, period_spec]
  simp only [Pi.one_apply, map_one, Circle.coe_one, Finset.prod_const_one,
    one_mul, Finset.prod_inv_distrib]

end ThetaGlobal.GlobalTargetPeriod
