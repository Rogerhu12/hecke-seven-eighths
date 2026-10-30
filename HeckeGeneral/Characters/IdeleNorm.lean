import HeckeGeneral.Characters.HeckeCharacter
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Algebraic properties of the real idelic norm

The finite part is handled as the finite product of local norms of a unit, using
Mathlib's finite-support theorem.  No normed-ring structure on the finite adèle
ring is used.  The negative logarithm agrees with the intended ideal norm sign.
Continuity and the prime-uniformizer normalization are not supplied by this file.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField

variable (K : Type*) [Field K] [NumberField K]

private abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

def infiniteIdelePart (x : IdeleGroup (𝓞 K) K) : (InfiniteAdeleRing K)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeles K)) x

def finiteIdelePart (x : IdeleGroup (𝓞 K) K) : (FiniteAdeles K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeles K)) x

@[simp] theorem infiniteIdelePart_val (x : IdeleGroup (𝓞 K) K) :
    (infiniteIdelePart K x).val = x.val.1 := rfl

@[simp] theorem finiteIdelePart_val (x : IdeleGroup (𝓞 K) K) :
    (finiteIdelePart K x).val = x.val.2 := rfl

theorem infiniteAdeleNorm_mul (x y : InfiniteAdeleRing K) :
    ‖x * y‖ = ‖x‖ * ‖y‖ := by
  rw [InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_def]
  change (∏ v, ‖x v * y v‖ ^ v.mult) = (∏ v, ‖x v‖ ^ v.mult) * ∏ v, ‖y v‖ ^ v.mult
  simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem infiniteIdeleNorm_pos (x : (InfiniteAdeleRing K)ˣ) : 0 < ‖x.val‖ := by
  rw [InfiniteAdeleRing.norm_def]
  apply Finset.prod_pos
  intro v _
  exact pow_pos (norm_pos_iff.mpr (isUnit_iff_ne_zero.mp (x.isUnit.apply v))) _

theorem finiteIdeleNorm_mul (x y : (FiniteAdeles K)ˣ) :
    ‖(x * y).val‖ = ‖x.val‖ * ‖y.val‖ := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit, FiniteAdeleRing.norm_eq_finprod_of_unit,
    FiniteAdeleRing.norm_eq_finprod_of_unit]
  change (∏ᶠ v, ‖x.val v * y.val v‖) = (∏ᶠ v, ‖x.val v‖) * ∏ᶠ v, ‖y.val v‖
  simp only [norm_mul]
  exact finprod_mul_distrib (FiniteAdeleRing.hasFiniteMulSupport_norm x)
    (FiniteAdeleRing.hasFiniteMulSupport_norm y)

theorem finiteIdeleNorm_pos (x : (FiniteAdeles K)ˣ) : 0 < ‖x.val‖ := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit]
  apply finprod_induction (fun z : ℝ => 0 < z) zero_lt_one (fun _ _ => mul_pos)
  intro v
  have hu : IsUnit (x.val v) :=
    IsUnit.map (RestrictedProduct.evalMonoidHom _ v) x.isUnit
  exact norm_pos_iff.mpr (isUnit_iff_ne_zero.mp hu)

theorem idelicNorm_pos (x : IdeleGroup (𝓞 K) K) : 0 < idelicNorm K x :=
  mul_pos (infiniteIdeleNorm_pos K (infiniteIdelePart K x))
    (finiteIdeleNorm_pos K (finiteIdelePart K x))

theorem idelicNorm_mul (x y : IdeleGroup (𝓞 K) K) :
    idelicNorm K (x * y) = idelicNorm K x * idelicNorm K y := by
  have hinf := infiniteAdeleNorm_mul K x.val.1 y.val.1
  have hfin := finiteIdeleNorm_mul K (finiteIdelePart K x) (finiteIdelePart K y)
  change ‖x.val.1 * y.val.1‖ * ‖x.val.2 * y.val.2‖ = _
  rw [hinf]
  change (‖x.val.1‖ * ‖y.val.1‖) * ‖(finiteIdelePart K x * finiteIdelePart K y).val‖ = _
  rw [hfin]
  unfold idelicNorm
  rw [finiteIdelePart_val, finiteIdelePart_val]
  ac_rfl

@[simp] theorem idelicNorm_one : idelicNorm K 1 = 1 := by
  apply mul_left_cancel₀ (idelicNorm_pos K 1).ne'
  simpa only [one_mul, mul_one] using (idelicNorm_mul K 1 1).symm

/-- The negative logarithm of the standard idelic modulus, as an algebraic homomorphism. -/
def ideleLogNormHom : IdeleGroup (𝓞 K) K →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (-Real.log (idelicNorm K x))
  map_one' := by simp
  map_mul' x y := by
    change -Real.log (idelicNorm K (x * y)) =
      -Real.log (idelicNorm K x) + -Real.log (idelicNorm K y)
    rw [idelicNorm_mul, Real.log_mul (idelicNorm_pos K x).ne' (idelicNorm_pos K y).ne']
    exact neg_add _ _

@[simp] theorem ideleLogNormHom_principal (u : Kˣ) :
    ideleLogNormHom K (IdeleGroup.unitEmbedding (𝓞 K) K u) = 1 := by
  change Multiplicative.ofAdd (-Real.log (idelicNorm K
    (IdeleGroup.unitEmbedding (𝓞 K) K u))) = 1
  rw [idelicNorm_principal]
  simp

/-- The genuine algebraic logarithmic norm on the actual idèle class group.
Its continuity remains to be proved before it can be used as a `LogNorm`. -/
def ideleClassLogNormHom : IdeleClassGroup (𝓞 K) K →* Multiplicative ℝ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) (ideleLogNormHom K) (by
    rintro x ⟨u, rfl⟩
    exact ideleLogNormHom_principal K u)

@[simp] theorem ideleClassLogNormHom_apply (x : IdeleGroup (𝓞 K) K) :
    ideleClassLogNormHom K (ideleClassMap K x) =
      Multiplicative.ofAdd (-Real.log (idelicNorm K x)) := rfl

end HeckeGeneral.Characters
