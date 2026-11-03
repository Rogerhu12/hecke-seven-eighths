import HeckeGeneral.Characters.LocalComponent
import Mathlib.Algebra.BigOperators.Pi

/-!
# Infinite components of actual Hecke characters

All maps here use Mathlib's actual completions and idèle class group. The
normalized local modulus is the ordinary norm to the place multiplicity,
so complex places contribute the square of their ordinary complex norm.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField
open scoped BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem continuous_infiniteOfCompletion (v : InfinitePlace K) :
    Continuous (InfiniteAdeleRing.ofCompletion v) := continuous_mulSingle v

theorem continuous_adeleOfCompletion (v : InfinitePlace K) :
    Continuous (NumberField.AdeleRing.ofCompletion (𝓞 K) K v) :=
  (continuous_infiniteOfCompletion K v).prodMk continuous_const

/-- Embed a unit of the actual archimedean completion as a single-place idèle. -/
def infiniteIdeleEmbedding (v : InfinitePlace K) :
    v.Completionˣ →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := NumberField.IdeleGroup.ofCompletion (𝓞 K) K v
  continuous_toFun := Units.continuous_map (continuous_adeleOfCompletion K v)

def infiniteIdeleClassMap (v : InfinitePlace K) :
    v.Completionˣ →ₜ* IdeleClassGroup (𝓞 K) K :=
  (ideleClassMap K).comp (infiniteIdeleEmbedding K v)

/-- The infinite-place restriction of an actual continuous unitary Hecke character. -/
def infiniteComponent (v : InfinitePlace K) (χ : HeckeCharacter K) :
    UnitaryCharacter v.Completionˣ := pullback (infiniteIdeleClassMap K v) χ

@[simp] theorem infiniteComponent_apply (v : InfinitePlace K) (χ : HeckeCharacter K)
    (u : v.Completionˣ) :
    infiniteComponent K v χ u = χ (infiniteIdeleClassMap K v u) := rfl

omit [NumberField K] in
theorem infiniteOfCompletion_same (v : InfinitePlace K) (x : v.Completion) :
    InfiniteAdeleRing.ofCompletion v x v = x := Pi.mulSingle_eq_same v x

omit [NumberField K] in
theorem infiniteOfCompletion_ne (v w : InfinitePlace K) (x : v.Completion)
    (h : w ≠ v) : InfiniteAdeleRing.ofCompletion v x w = 1 :=
  Pi.mulSingle_eq_of_ne h x

/-- The place multiplicity is retained in the norm of the actual idèle. -/
theorem infiniteOfCompletion_norm (v : InfinitePlace K) (x : v.Completion) :
    ‖InfiniteAdeleRing.ofCompletion v x‖ = ‖x‖ ^ v.mult := by
  rw [InfiniteAdeleRing.norm_def]
  rw [Finset.prod_eq_single v]
  · rw [infiniteOfCompletion_same]
  · intro w _ hw
    rw [infiniteOfCompletion_ne K v w x hw, norm_one, one_pow]
  · simp

theorem finiteAdeleNorm_one :
    ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ = 1 := by
  have h := NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit
    (1 : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ)
  change ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ =
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖ at h
  simpa only [norm_one, finprod_one] using h

theorem idelicNorm_infiniteIdeleEmbedding (v : InfinitePlace K) (u : v.Completionˣ) :
    idelicNorm K (infiniteIdeleEmbedding K v u) = ‖u.val‖ ^ v.mult := by
  change ‖InfiniteAdeleRing.ofCompletion v u.val‖ *
    ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ = _
  rw [infiniteOfCompletion_norm, finiteAdeleNorm_one, mul_one]

theorem heckeNormTwist_infinite (v : InfinitePlace K) (t : ℝ) (u : v.Completionˣ) :
    infiniteComponent K v (heckeNormTwist K t) u =
      Circle.exp (-(t * v.mult * Real.log ‖u.val‖)) := by
  change Circle.exp (t * (-Real.log (idelicNorm K (infiniteIdeleEmbedding K v u)))) = _
  rw [idelicNorm_infiniteIdeleEmbedding, Real.log_pow]
  congr 1
  ring

@[simp] theorem infiniteComponent_mul (v : InfinitePlace K) (χ ψ : HeckeCharacter K) :
    infiniteComponent K v (χ * ψ) = infiniteComponent K v χ * infiniteComponent K v ψ := by
  ext u
  rfl

@[simp] theorem infiniteComponent_inv (v : InfinitePlace K) (χ : HeckeCharacter K) :
    infiniteComponent K v χ⁻¹ = (infiniteComponent K v χ)⁻¹ := by
  ext u
  rfl

/-- Assemble arbitrary units at all infinite places, with finite component one. -/
def archimedeanIdele (u : ∀ v : InfinitePlace K, v.Completionˣ) : IdeleGroup (𝓞 K) K where
  val := (fun v => (u v).val, 1)
  inv := (fun v => (u v).inv, 1)
  val_inv := Prod.ext (funext fun v => (u v).val_inv) (one_mul _)
  inv_val := Prod.ext (funext fun v => (u v).inv_val) (one_mul _)

theorem continuous_archimedeanIdele : Continuous (archimedeanIdele K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)).prodMk
      continuous_const
  · exact (continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)).prodMk
      continuous_const

theorem archimedeanIdele_eq_prod (u : ∀ v : InfinitePlace K, v.Completionˣ) :
    archimedeanIdele K u = ∏ v, infiniteIdeleEmbedding K v (u v) := by
  apply Units.ext
  change (archimedeanIdele K u).val =
    (Units.coeHom _) (∏ v, infiniteIdeleEmbedding K v (u v))
  rw [map_prod]
  change ((fun v => (u v).val), (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) =
    ∏ v, (InfiniteAdeleRing.ofCompletion v (u v).val,
      (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  apply Prod.ext
  · rw [Prod.fst_prod]
    change (fun v => (u v).val) = (∏ v, InfiniteAdeleRing.ofCompletion v (u v).val)
    exact (Finset.univ_prod_mulSingle (fun v => (u v).val)).symm
  · rw [Prod.snd_prod]
    change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = ∏ _ : InfinitePlace K, 1
    simp

/-- The actual archimedean character factors over all its local components. -/
theorem character_archimedeanIdele (χ : HeckeCharacter K)
    (u : ∀ v : InfinitePlace K, v.Completionˣ) :
    toIdeleCharacter K χ (archimedeanIdele K u) = ∏ v, infiniteComponent K v χ (u v) := by
  rw [archimedeanIdele_eq_prod, map_prod]
  rfl

theorem idelicNorm_archimedeanIdele (u : ∀ v : InfinitePlace K, v.Completionˣ) :
    idelicNorm K (archimedeanIdele K u) = ∏ v, ‖(u v).val‖ ^ v.mult := by
  unfold idelicNorm
  change ‖(show InfiniteAdeleRing K from fun v => (u v).val)‖ *
    ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ = _
  rw [finiteAdeleNorm_one, mul_one, InfiniteAdeleRing.norm_def]

end HeckeGeneral.Characters
