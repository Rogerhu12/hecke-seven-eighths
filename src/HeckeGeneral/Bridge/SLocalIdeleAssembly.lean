import HeckeGeneral.Bridge.FLTDefinitions
import HeckeGeneral.Characters.InfiniteComponent
import HeckeGeneral.Arithmetic.SLocalNormSection

/-!
# Assembly of the actual S-local multiplication group into ideles

The archimedean mixed-space unit is transported through Mathlib's ring
equivalence with the product of the actual infinite completions. Each finite
coordinate is inserted by the existing local idele embedding; all other
finite coordinates are one. The arithmetic norm, including the multiplicity
two at complex places, is identified with the real Haar modulus.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic
open IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The actual units of the infinite adele ring corresponding to a mixed unit. -/
def mixedUnitInfiniteAdele (u : (mixedEmbedding.mixedSpace K)ˣ) :
    (InfiniteAdeleRing K)ˣ :=
  Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toMonoidHom u

/-- Insert the mixed unit at all infinite places and put one at finite places. -/
def mixedUnitIdele (u : (mixedEmbedding.mixedSpace K)ˣ) : IdeleGroup (𝓞 K) K :=
  archimedeanIdele K (fun v =>
    Units.map (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) v)
      (mixedUnitInfiniteAdele K u))

@[simp] theorem mixedUnitIdele_arch (u : (mixedEmbedding.mixedSpace K)ˣ) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (mixedUnitIdele K u).val.1 = u.val := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace K)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.val) = u.val
  exact RingEquiv.apply_symm_apply _ _

@[simp] theorem mixedUnitIdele_finite (u : (mixedEmbedding.mixedSpace K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) : (mixedUnitIdele K u).val.2 v = 1 := rfl

theorem mixedUnitIdele_one : mixedUnitIdele K 1 = 1 := by
  apply Units.ext
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm 1, 1) = (1, 1)
  rw [map_one]

theorem mixedUnitIdele_mul (u w : (mixedEmbedding.mixedSpace K)ˣ) :
    mixedUnitIdele K (u * w) = mixedUnitIdele K u * mixedUnitIdele K w := by
  apply Units.ext
  change ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (u.val * w.val), 1) =
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.val *
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm w.val, 1 * 1)
  rw [map_mul, one_mul]

/-- The archimedean arithmetic norm is the infinite-adele normalized norm. -/
theorem norm_infiniteAdele_eq_mixed (x : InfiniteAdeleRing K) :
    ‖x‖ = mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K x) := by
  rw [InfiniteAdeleRing.norm_def, mixedEmbedding.norm_apply]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  by_cases hv : v.IsReal
  · change ‖x v‖ =
      mixedEmbedding.normAtPlace v (InfiniteAdeleRing.ringEquiv_mixedSpace K x)
    rw [mixedEmbedding.normAtPlace_apply_of_isReal hv]
    change ‖x v‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x v)‖
    have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).dist_eq
      (x v) 0
    simpa only [map_zero, dist_zero_right] using h.symm
  · change ‖x v‖ =
      mixedEmbedding.normAtPlace v (InfiniteAdeleRing.ringEquiv_mixedSpace K x)
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex (by simpa using hv)]
    change ‖x v‖ = ‖InfinitePlace.Completion.extensionEmbedding v (x v)‖
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq (x v) 0
    simpa only [map_zero, dist_zero_right] using h.symm

theorem idelicNorm_mixedUnitIdele (u : (mixedEmbedding.mixedSpace K)ˣ) :
    idelicNorm K (mixedUnitIdele K u) = mixedEmbedding.norm u.val := by
  unfold idelicNorm
  rw [show (mixedUnitIdele K u).val.2 = 1 from rfl,
    finiteAdeleNorm_one, mul_one, norm_infiniteAdele_eq_mixed, mixedUnitIdele_arch]

/-- A coordinate homomorphism used to evaluate finite products of local ideles. -/
def ideleFiniteCoordinate (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup (𝓞 K) K →* v.adicCompletion K where
  toFun x := x.val.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The mixed-space projection, with no normalization or choice of representatives. -/
def ideleMixedCoordinate : IdeleGroup (𝓞 K) K →* mixedEmbedding.mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toMonoidHom.comp
    ((MonoidHom.fst (InfiniteAdeleRing K)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).comp (Units.coeHom _))

@[simp] theorem ideleMixedCoordinate_local (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleMixedCoordinate K (localIdeleEmbedding K v u) = 1 := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace K 1 = 1
  exact map_one _

@[simp] theorem ideleFiniteCoordinate_local_same (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleFiniteCoordinate K v (localIdeleEmbedding K v u) = u.val :=
  finiteOfAdicCompletion_same K v u.val

@[simp] theorem ideleFiniteCoordinate_local_ne (v w : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (h : w ≠ v) :
    ideleFiniteCoordinate K w (localIdeleEmbedding K v u) = 1 :=
  finiteOfAdicCompletion_ne K v w u.val h

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Insert exactly the finitely many specified local coordinates. -/
def sLocalIdeleAssembly : sLocalMultiplicativeGroup K S →* IdeleGroup (𝓞 K) K where
  toFun p := mixedUnitIdele K p.1 * ∏ v : S, localIdeleEmbedding K v.val (p.2 v)
  map_one' := by simp [mixedUnitIdele_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mixedUnitIdele_mul,
      map_mul, Finset.prod_mul_distrib]
    ac_rfl

@[simp] theorem sLocalIdeleAssembly_arch (p : sLocalMultiplicativeGroup K S) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K
      (sLocalIdeleAssembly K S p).val.1 = p.1.val := by
  change ideleMixedCoordinate K
    (mixedUnitIdele K p.1 * ∏ v : S, localIdeleEmbedding K v.val (p.2 v)) = _
  rw [map_mul, map_prod]
  simp only [ideleMixedCoordinate_local, Finset.prod_const_one, mul_one]
  exact mixedUnitIdele_arch K p.1

@[simp] theorem sLocalIdeleAssembly_finite_mem
    (p : sLocalMultiplicativeGroup K S) (v : S) :
    (sLocalIdeleAssembly K S p).val.2 v.val = (p.2 v).val := by
  change ideleFiniteCoordinate K v.val
    (mixedUnitIdele K p.1 * ∏ w : S, localIdeleEmbedding K w.val (p.2 w)) = _
  rw [map_mul, map_prod]
  change 1 * (∏ w : S, ideleFiniteCoordinate K v.val
    (localIdeleEmbedding K w.val (p.2 w))) = _
  rw [one_mul, Finset.prod_eq_single v]
  · exact ideleFiniteCoordinate_local_same K v.val (p.2 v)
  · intro w _ hw
    exact ideleFiniteCoordinate_local_ne K w.val v.val (p.2 w)
      (fun h => hw (Subtype.ext h.symm))
  · simp

@[simp] theorem sLocalIdeleAssembly_finite_not_mem
    (p : sLocalMultiplicativeGroup K S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    (sLocalIdeleAssembly K S p).val.2 v = 1 := by
  change ideleFiniteCoordinate K v
    (mixedUnitIdele K p.1 * ∏ w : S, localIdeleEmbedding K w.val (p.2 w)) = _
  rw [map_mul, map_prod]
  change 1 * (∏ w : S, ideleFiniteCoordinate K v
    (localIdeleEmbedding K w.val (p.2 w))) = 1
  simp only [one_mul]
  apply Finset.prod_eq_one
  intro w _
  exact ideleFiniteCoordinate_local_ne K w.val v (p.2 w)
    (fun h => hv (h.symm ▸ w.property))

theorem sLocalIdeleAssembly_injective : Function.Injective (sLocalIdeleAssembly K S) := by
  intro p q hpq
  apply Prod.ext
  · apply Units.ext
    simpa only [sLocalIdeleAssembly_arch] using
      congrArg (fun x : IdeleGroup (𝓞 K) K =>
        InfiniteAdeleRing.ringEquiv_mixedSpace K x.val.1) hpq
  · funext v
    apply Units.ext
    simpa only [sLocalIdeleAssembly_finite_mem] using
      congrArg (fun x : IdeleGroup (𝓞 K) K => x.val.2 v.val) hpq

theorem idelicNorm_sLocalIdeleAssembly (p : sLocalMultiplicativeGroup K S) :
    idelicNorm K (sLocalIdeleAssembly K S p) = sLocalProductNorm K S p := by
  let n : IdeleGroup (𝓞 K) K →* ℝ :=
    { toFun := idelicNorm K
      map_one' := idelicNorm_one K
      map_mul' := idelicNorm_mul K }
  change n (mixedUnitIdele K p.1 * ∏ v : S, localIdeleEmbedding K v.val (p.2 v)) = _
  rw [map_mul, map_prod]
  change idelicNorm K (mixedUnitIdele K p.1) *
    (∏ v : S, idelicNorm K (localIdeleEmbedding K v.val (p.2 v))) = _
  simp only [idelicNorm_mixedUnitIdele, idelicNorm_localIdeleEmbedding]
  rfl

/-- The real Haar modulus of the assembled actual idele is the S-local product norm. -/
theorem distribHaarChar_sLocalIdeleAssembly (p : sLocalMultiplicativeGroup K S) :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K)
      (sLocalIdeleAssembly K S p) : ℝ) = sLocalProductNorm K S p := by
  change TateGlobal.ideleNorm K (sLocalIdeleAssembly K S p) = _
  rw [fltIdeleNorm_eq, idelicNorm_sLocalIdeleAssembly]

theorem distribHaarChar_sLocalIdeleAssembly_section_mul
    (r : {r : ℝ // 0 < r}) (x : sLocalMultiplicativeGroup K S)
    (hx : sLocalProductNorm K S x = 1) :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K)
      (sLocalIdeleAssembly K S (sLocalNormSection K S r * x)) : ℝ) = r.val := by
  rw [distribHaarChar_sLocalIdeleAssembly, sLocalProductNorm_mul,
    sLocalProductNorm_section, hx, mul_one]

end HeckeGeneral.Bridge
