import HeckeGeneral.Arithmetic.ArchimedeanUnitShape
import HeckeGeneral.Arithmetic.LocalValuationCompact
import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Compact representatives for the actual S-local product norm-one orbits

The finite valuation box and the lifted archimedean shape are actual compact
sets of local units. The radial scale is a positive continuous function of
the finite coordinates. Thus their parameter image is compact, and joint
reduction by Γ puts every actual norm-one point into it. No S-unit quotient
compactness, finite generation, or principal ideal hypothesis is assumed.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

abbrev SFiniteLocalGroup := (v : S) → (v.val.adicCompletion K)ˣ

def sFiniteProductNorm (x : SFiniteLocalGroup K S) : ℝ := ∏ v : S, ‖(x v).val‖

theorem sFiniteProductNorm_pos (x : SFiniteLocalGroup K S) :
    0 < sFiniteProductNorm K S x := by
  exact Finset.prod_pos fun v _ => norm_pos_iff.mpr (x v).ne_zero

theorem continuous_sFiniteProductNorm : Continuous (sFiniteProductNorm K S) := by
  exact continuous_finsetProd Finset.univ fun v _ =>
    continuous_norm.comp (Units.continuous_val.comp (continuous_apply v))

/-- The radius forced by product norm one and the finite local coordinates. -/
def sFiniteRadialScale (x : SFiniteLocalGroup K S) : ℝ :=
  (sFiniteProductNorm K S x)⁻¹ ^ ((Module.finrank ℚ K : ℝ)⁻¹)

theorem sFiniteRadialScale_pos (x : SFiniteLocalGroup K S) :
    0 < sFiniteRadialScale K S x :=
  Real.rpow_pos_of_pos (inv_pos.mpr (sFiniteProductNorm_pos K S x)) _

theorem continuous_sFiniteRadialScale : Continuous (sFiniteRadialScale K S) := by
  exact ((continuous_sFiniteProductNorm K S).inv₀
    (fun x => (sFiniteProductNorm_pos K S x).ne')).rpow_const
      (fun x => Or.inl (inv_ne_zero (sFiniteProductNorm_pos K S x).ne'))

theorem sFiniteRadialScale_eq_arithmeticNormRoot
    (x : sLocalMultiplicativeGroup K S) (hx : sLocalProductNorm K S x = 1) :
    sFiniteRadialScale K S x.2 = arithmeticNormRoot K (x.1 : mixedSpace K) := by
  have hnorm : mixedEmbedding.norm (x.1 : mixedSpace K) =
      (sFiniteProductNorm K S x.2)⁻¹ := by
    apply mul_right_cancel₀ (sFiniteProductNorm_pos K S x.2).ne'
    calc
      mixedEmbedding.norm (x.1 : mixedSpace K) * sFiniteProductNorm K S x.2 = 1 := hx
      _ = (sFiniteProductNorm K S x.2)⁻¹ * sFiniteProductNorm K S x.2 :=
        (inv_mul_cancel₀ (sFiniteProductNorm_pos K S x.2).ne').symm
  simp only [sFiniteRadialScale, arithmeticNormRoot, hnorm]

/-- Positive real dilation as a unit of the actual mixed algebra. -/
def realScaleMixedUnit (r : ℝ) (hr : r ≠ 0) : (mixedSpace K)ˣ :=
  Units.map (algebraMap ℝ (mixedSpace K)).toMonoidHom (Units.mk0 r hr)

omit [NumberField K] in
@[simp] theorem realScaleMixedUnit_val (r : ℝ) (hr : r ≠ 0) :
    (realScaleMixedUnit K r hr).val = algebraMap ℝ (mixedSpace K) r := rfl

theorem continuous_realScaleMixedUnit {T : Type*} [TopologicalSpace T]
    (r : T → ℝ) (hc : Continuous r) (hr : ∀ t, r t ≠ 0) :
    Continuous (fun t => realScaleMixedUnit K (r t) (hr t)) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun t => algebraMap ℝ (mixedSpace K) (r t))
    simp only [Algebra.algebraMap_eq_smul_one]
    exact continuous_smul.comp (hc.prodMk continuous_const)
  · change Continuous (fun t => algebraMap ℝ (mixedSpace K) ((r t)⁻¹))
    simp only [Algebra.algebraMap_eq_smul_one]
    exact continuous_smul.comp ((hc.inv₀ hr).prodMk continuous_const)

abbrev SUnitRepresentativeParameters (Γ : Subgroup (S.unit K)) :=
  {a : (mixedSpace K)ˣ // a ∈ finiteIndexArchUnitShape K (ordinaryUnitPullback K S Γ)} ×
  {z : SFiniteLocalGroup K S // z ∈
    finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)}

def sUnitRepresentativeMap (Γ : Subgroup (S.unit K))
    (p : SUnitRepresentativeParameters K S Γ) : sLocalMultiplicativeGroup K S :=
  (realScaleMixedUnit K (sFiniteRadialScale K S p.2.val)
    (sFiniteRadialScale_pos K S p.2.val).ne' * p.1.val, p.2.val)

theorem continuous_sUnitRepresentativeMap (Γ : Subgroup (S.unit K)) :
    Continuous (sUnitRepresentativeMap K S Γ) := by
  have hz : Continuous (fun p : SUnitRepresentativeParameters K S Γ => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hr := (continuous_sFiniteRadialScale K S).comp hz
  exact ((continuous_realScaleMixedUnit K _ hr
    (fun p => (sFiniteRadialScale_pos K S p.2.val).ne')).mul
      (continuous_subtype_val.comp continuous_fst)).prodMk hz

def sUnitCompactRepresentativeSet (Γ : Subgroup (S.unit K)) :
    Set (sLocalMultiplicativeGroup K S) := Set.range (sUnitRepresentativeMap K S Γ)

theorem isCompact_sUnitCompactRepresentativeSet (Γ : Subgroup (S.unit K))
    [Γ.FiniteIndex] : IsCompact (sUnitCompactRepresentativeSet K S Γ) := by
  have ha : IsCompact (Set.univ : Set {a : (mixedSpace K)ˣ //
      a ∈ finiteIndexArchUnitShape K (ordinaryUnitPullback K S Γ)}) :=
    isCompact_iff_isCompact_univ.mp
      (isCompact_finiteIndexArchUnitShape K (ordinaryUnitPullback K S Γ))
  have hz : IsCompact (Set.univ : Set {z : SFiniteLocalGroup K S //
      z ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)}) :=
    isCompact_iff_isCompact_univ.mp
      (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
  have hp : IsCompact (Set.univ : Set (SUnitRepresentativeParameters K S Γ)) := by
    simpa using ha.prod hz
  simpa only [sUnitCompactRepresentativeSet, Set.image_univ] using
    hp.image (continuous_sUnitRepresentativeMap K S Γ)

theorem exists_subgroup_mem_sUnitCompactRepresentativeSet
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (x : sLocalMultiplicativeGroup K S) (hx : sLocalProductNorm K S x = 1) :
    ∃ g : Γ, sLocalDiagonal K S (g : S.unit K) * x ∈
      sUnitCompactRepresentativeSet K S Γ := by
  obtain ⟨u, v, hshape, hbox⟩ := exists_subgroup_joint_local_reduction K S Γ x
  let y := sLocalDiagonal K S (u : S.unit K) * x
  let z := sLocalDiagonal K S ((v * u : Γ) : S.unit K) * x
  let r := arithmeticNormRoot K (y.1 : mixedSpace K)
  have hr : 0 < r := arithmeticNormRoot_pos K (sLocal_archNorm_ne_zero K S y)
  have hshape' : r⁻¹ • (z.1 : mixedSpace K) ∈
      finiteIndexBalancedShape K (ordinaryUnitPullback K S Γ) := hshape
  have hnormalized : mixedEmbedding.norm (r⁻¹ • (z.1 : mixedSpace K)) = 1 :=
    norm_eq_one_of_mem_finiteIndexBalancedShape K _ hshape'
  have hnorm : mixedEmbedding.norm (z.1 : mixedSpace K) =
      mixedEmbedding.norm (y.1 : mixedSpace K) := by
    have h := hnormalized
    rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr hr), inv_pow] at h
    have hpower := pow_ne_zero (Module.finrank ℚ K) hr.ne'
    have hm := congrArg (fun q : ℝ => r ^ Module.finrank ℚ K * q) h
    have heq : mixedEmbedding.norm (z.1 : mixedSpace K) = r ^ Module.finrank ℚ K := by
      simpa only [← mul_assoc, mul_inv_cancel₀ hpower, one_mul, mul_one] using hm
    exact heq.trans (arithmeticNormRoot_pow K (y.1 : mixedSpace K))
  have hzNorm : sLocalProductNorm K S z = 1 := by
    exact (sLocalProductNorm_diagonal_mul K S ((v * u : Γ) : S.unit K) x).trans hx
  have hscale : sFiniteRadialScale K S z.2 = r := by
    rw [sFiniteRadialScale_eq_arithmeticNormRoot K S z hzNorm]
    change mixedEmbedding.norm (z.1 : mixedSpace K) ^ _ =
      mixedEmbedding.norm (y.1 : mixedSpace K) ^ _
    rw [hnorm]
  have hzbox : z.2 ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) := by
    intro w
    exact mem_localValuationBox_of_bounds K w.val _ (z.2 w) (hbox w).1 (hbox w).2
  let a : (mixedSpace K)ˣ := mixedUnitOfNormNeZero K
    (r⁻¹ • (z.1 : mixedSpace K)) (by rw [hnormalized]; exact one_ne_zero)
  have ha : a ∈ finiteIndexArchUnitShape K (ordinaryUnitPullback K S Γ) :=
    (mem_finiteIndexArchUnitShape_iff K _ a).mpr hshape'
  refine ⟨v * u, ⟨(⟨a, ha⟩, ⟨z.2, hzbox⟩), ?_⟩⟩
  apply Prod.ext
  · apply Units.ext
    change algebraMap ℝ (mixedSpace K) (sFiniteRadialScale K S z.2) *
      (r⁻¹ • (z.1 : mixedSpace K)) = (z.1 : mixedSpace K)
    rw [hscale, ← Algebra.smul_def]
    exact smul_inv_smul₀ hr.ne' _
  · rfl

/-- An actual compact set meets every Γ-orbit in the product norm-one level. -/
theorem exists_compact_sUnit_normOne_representatives
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex] :
    ∃ C : Set (sLocalMultiplicativeGroup K S), IsCompact C ∧
      ∀ x, sLocalProductNorm K S x = 1 →
        ∃ g : Γ, sLocalDiagonal K S (g : S.unit K) * x ∈ C :=
  ⟨sUnitCompactRepresentativeSet K S Γ, isCompact_sUnitCompactRepresentativeSet K S Γ,
    exists_subgroup_mem_sUnitCompactRepresentativeSet K S Γ⟩

end HeckeGeneral.Arithmetic
