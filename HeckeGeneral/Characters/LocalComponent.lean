import HeckeGeneral.Characters.IdeleNormContinuity

/-!
# Finite local components of actual Hecke characters

The single-place embedding is Mathlib's multiplicative embedding, with every
other finite and infinite component equal to one.  Its continuity is proved
through a principal-filter stage of the restricted product.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Topology
open scoped RestrictedProduct Classical

variable (K : Type*) [Field K] [NumberField K]

private abbrev FiniteAdelesForLocal := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

private def localFiniteStage (v : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K) :
    Πʳ w : HeightOneSpectrum (𝓞 K), [w.adicCompletion K, w.adicCompletionIntegers K]_[𝓟 {v}ᶜ] where
  val := Pi.mulSingle v z
  property := by
    rw [eventually_principal]
    intro w hw
    have hne : w ≠ v := by simpa using hw
    rw [Pi.mulSingle_eq_of_ne hne]
    exact (w.adicCompletionIntegers K).one_mem

private theorem continuous_localFiniteStage (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localFiniteStage K v) := by
  apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
  intro w
  by_cases h : w = v
  · subst w
    change Continuous (fun z : v.adicCompletion K => Pi.mulSingle v z v)
    rw [show (fun z : v.adicCompletion K => Pi.mulSingle v z v) = id from
      funext (fun z => Pi.mulSingle_eq_same v z)]
    exact continuous_id
  · change Continuous (fun z : v.adicCompletion K => Pi.mulSingle v z w)
    simpa only [Pi.mulSingle_eq_of_ne h] using
      (continuous_const : Continuous (fun _ : v.adicCompletion K => (1 : w.adicCompletion K)))

theorem continuous_finiteOfAdicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v) := by
  have hfilter : cofinite ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by simp
  have heq : (IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v :
      v.adicCompletion K → FiniteAdelesForLocal K) =
      RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) hfilter ∘
        localFiniteStage K v := by
    funext z
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hfilter).comp (continuous_localFiniteStage K v)

theorem continuous_adeleOfAdicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (NumberField.AdeleRing.ofAdicCompletion (𝓞 K) K v) :=
  continuous_const.prodMk (continuous_finiteOfAdicCompletion K v)

/-- The actual continuous embedding of a finite local unit group into the idèle group. -/
def localIdeleEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* IdeleGroup (𝓞 K) K where
  toMonoidHom := NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v
  continuous_toFun := Units.continuous_map (continuous_adeleOfAdicCompletion K v)

/-- The corresponding continuous map into the actual idèle class group. -/
def localIdeleClassMap (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →ₜ* IdeleClassGroup (𝓞 K) K :=
  (ideleClassMap K).comp (localIdeleEmbedding K v)

@[simp] theorem localIdeleEmbedding_mul (v : HeightOneSpectrum (𝓞 K))
    (x y : (v.adicCompletion K)ˣ) :
    localIdeleEmbedding K v (x * y) = localIdeleEmbedding K v x * localIdeleEmbedding K v y :=
  map_mul _ x y

@[simp] theorem localIdeleEmbedding_inv (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    localIdeleEmbedding K v x⁻¹ = (localIdeleEmbedding K v x)⁻¹ := map_inv _ x

@[simp] theorem localIdeleEmbedding_zpow (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (n : ℤ) :
    localIdeleEmbedding K v (x ^ n) = localIdeleEmbedding K v x ^ n := map_zpow _ x n

/-- The continuous local component of an actual unitary Hecke character. -/
def localComponent (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) :
    UnitaryCharacter (v.adicCompletion K)ˣ := pullback (localIdeleClassMap K v) χ

@[simp] theorem localComponent_apply (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K)
    (u : (v.adicCompletion K)ˣ) :
    localComponent K v χ u = χ (localIdeleClassMap K v u) := rfl

@[simp] theorem localComponent_mul (v : HeightOneSpectrum (𝓞 K)) (χ ψ : HeckeCharacter K) :
    localComponent K v (χ * ψ) = localComponent K v χ * localComponent K v ψ := by
  apply ContinuousMonoidHom.ext
  intro u
  rfl

@[simp] theorem localComponent_inv (v : HeightOneSpectrum (𝓞 K)) (χ : HeckeCharacter K) :
    localComponent K v χ⁻¹ = (localComponent K v χ)⁻¹ := by
  apply ContinuousMonoidHom.ext
  intro u
  rfl

@[simp] theorem localComponent_zpow (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (n : ℤ) :
    localComponent K v (χ ^ n) = localComponent K v χ ^ n := by
  unfold localComponent
  exact pullback_zpow (G := IdeleClassGroup (𝓞 K) K) (H := (v.adicCompletion K)ˣ)
    (localIdeleClassMap K v) χ n

theorem finiteOfAdicCompletion_same (v : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K) :
    IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v z v = z :=
  Pi.mulSingle_eq_same v z

theorem finiteOfAdicCompletion_ne (v w : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K)
    (h : w ≠ v) : IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v z w = 1 :=
  Pi.mulSingle_eq_of_ne h z

theorem finiteOfAdicCompletion_norm (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ‖IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v u.val‖ = ‖u.val‖ := by
  rw [show ‖IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v u.val‖ =
      ∏ᶠ w, ‖IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v u.val w‖ from
    NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit
      (Units.map (IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v) u)]
  rw [finprod_eq_single _ v (fun w h => by rw [finiteOfAdicCompletion_ne K v w u.val h]; exact norm_one)]
  rw [finiteOfAdicCompletion_same]

theorem infiniteAdeleNorm_one : ‖(1 : InfiniteAdeleRing K)‖ = 1 := by
  rw [InfiniteAdeleRing.norm_def]
  change (∏ w : InfinitePlace K, ‖(1 : w.Completion)‖ ^ w.mult) = 1
  simp

theorem idelicNorm_localIdeleEmbedding (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) : idelicNorm K (localIdeleEmbedding K v u) = ‖u.val‖ := by
  change ‖(1 : InfiniteAdeleRing K)‖ *
    ‖IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion K v u.val‖ = ‖u.val‖
  rw [infiniteAdeleNorm_one, one_mul, finiteOfAdicCompletion_norm]

@[simp] theorem heckeNormTwist_local (v : HeightOneSpectrum (𝓞 K)) (t : ℝ)
    (u : (v.adicCompletion K)ˣ) :
    localComponent K v (heckeNormTwist K t) u = Circle.exp (t * (-Real.log ‖u.val‖)) := by
  change Circle.exp (t * (-Real.log (idelicNorm K (localIdeleEmbedding K v u)))) = _
  rw [idelicNorm_localIdeleEmbedding]

end HeckeGeneral.Characters
