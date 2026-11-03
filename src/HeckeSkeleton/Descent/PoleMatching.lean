import HeckeSkeleton.ActualHeckeNormPullback
import HeckeGeneral.Characters.IdeleNormContinuity
import HeckeGeneral.Analysis.HeckeEndpointTarget
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm

/-!
Adapted from the read-only norm-pullback cache candidates dated 2026-10-11.

The upstream absolute norm is the INVERSE of the conventional Mathlib
idelic modulus used in this project. The finite and infinite comparisons
below prove that sign explicitly; compatibility is not supplied as a
hypothesis. The norm arithmetic comes from the vendored CFT package.

This proves preservation of the actual norm twist under the actual relative
norm, and pole matching for any finite family with a common norm pullback.
The Artin factor family and Euler factorization are supplied separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.PoleMatching

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Characters.NormPullbackDraft
open scoped NumberField NNReal

section Comparison

variable (K : Type*) [Field K] [NumberField K]

/-- A local prime contributes `Np^(-ord)` to the conventional modulus,
whereas the upstream absolute norm contributes `Np^ord`. -/
private theorem finiteLocalNorm_comparison
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ‖(x : v.adicCompletion K)‖ =
      ((((_root_.FiniteIdeleGroup.primeNorm v ^
          (_root_.FiniteIdeleGroup.localOrder v x).toAdd : ℝ≥0ˣ) : ℝ≥0) : ℝ))⁻¹ := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
  rw [FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) hx]
  simp only [_root_.FiniteIdeleGroup.localOrder_apply,
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, NNReal.coe_zpow, NNReal.coe_inv,
    _root_.FiniteIdeleGroup.primeNorm, Units.val_mk0,
    NNReal.coe_natCast, zpow_neg, inv_inv]

/-- Finite-support comparison, using the actual local-order vector. -/
theorem finiteIdeleNorm_comparison (a : _root_.FiniteIdeleGroup K) :
    ‖((_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a :
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
        IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ =
      (((_root_.FiniteIdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ := by
  classical
  let e := (_root_.FiniteIdeleGroup.valuationVector a).toAdd
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      ‖(a v : v.adicCompletion K)‖ =
        ((((_root_.FiniteIdeleGroup.primeNorm v ^ e v : ℝ≥0ˣ) : ℝ≥0) : ℝ))⁻¹ := by
    simpa only [e, _root_.FiniteIdeleGroup.valuationVector_apply] using
      finiteLocalNorm_comparison K v (a v)
  have hsupport : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => ‖(a v : v.adicCompletion K)‖) ⊆
      e.support := by
    intro v hv
    by_contra hnot
    have he : e v = 0 := Finsupp.notMem_support_iff.mp hnot
    exact hv (by simp only [hlocal, he, zpow_zero, Units.val_one,
      NNReal.coe_one, inv_one])
  rw [FiniteAdeleRing.norm_eq_finprod_of_unit]
  change (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a v : v.adicCompletion K)‖) = _
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupport,
    _root_.FiniteIdeleGroup.absoluteNorm_apply, Finsupp.prod]
  change (∏ v ∈ e.support, ‖(a v : v.adicCompletion K)‖) =
    (((∏ v ∈ e.support, _root_.FiniteIdeleGroup.primeNorm v ^ e v : ℝ≥0ˣ) :
      ℝ≥0) : ℝ)⁻¹
  simp only [Units.coe_prod, NNReal.coe_prod]
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl (fun v _ => hlocal v)

/-- The infinite comparison uses the actual normalized multiplicities. -/
theorem infiniteIdeleNorm_comparison (a : _root_.InfiniteIdeleGroup K) :
    ‖(a : InfiniteAdeleRing K)‖ =
      (((_root_.InfiniteIdeleGroup.archimedeanNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ) := by
  classical
  rw [InfiniteAdeleRing.norm_def, _root_.InfiniteIdeleGroup.archimedeanNorm_apply]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val,
    _root_.nnnormUnitHom_val, NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm]
  rfl

/-- The real conventional modulus is the inverse of upstream absolute norm.
In particular, the negative logarithm used for `heckeNormTwist` has the
same sign as the logarithm of upstream absolute norm. -/
theorem idelicNorm_comparison (a : _root_.IdeleGroup K) :
    idelicNorm K ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv K) a) =
      (((_root_.IdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ := by
  change ‖(a.1 : InfiniteAdeleRing K)‖ *
    ‖((_root_.IdeleGroup.finiteEquivFiniteAdeleUnits a.2 :
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
        IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ = _
  rw [finiteIdeleNorm_comparison K a.2, infiniteIdeleNorm_comparison K a.1,
    _root_.IdeleGroup.absoluteNorm_apply]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val,
    NNReal.coe_mul, NNReal.coe_inv, mul_inv_rev, inv_inv]

end Comparison

section Pullback

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

/-- The actual relative norm preserves the project's conventional modulus. -/
theorem idelicNorm_mathlibIdeleNorm (x : NumberField.IdeleGroup (𝓞 L) L) :
    idelicNorm K (mathlibIdeleNorm K L x) = idelicNorm L x := by
  let a := (_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).symm x
  calc
    idelicNorm K (mathlibIdeleNorm K L x) =
        (((_root_.IdeleGroup.absoluteNorm (_root_.IdeleGroup.norm K L a) :
            ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ :=
      idelicNorm_comparison K (_root_.IdeleGroup.norm K L a)
    _ = (((_root_.IdeleGroup.absoluteNorm a : ℝ≥0ˣ) : ℝ≥0) : ℝ)⁻¹ := by
      rw [_root_.IdeleGroup.absoluteNorm_norm]
    _ = idelicNorm L x := by
      rw [← idelicNorm_comparison L a]
      exact congrArg (idelicNorm L)
        ((_root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv L).apply_symm_apply x)

/-- Actual logarithmic norms are compatible, by quotient descent of the
proved modulus identity, not by an additional input. -/
theorem heckeLogNorm_norm_compatible :
    heckeLogNorm L = (heckeLogNorm K).comp (mathlibIdeleClassNorm K L) := by
  apply ContinuousMonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro x
  change heckeLogNorm L (ideleClassMap L x) =
    heckeLogNorm K (mathlibIdeleClassNorm K L (ideleClassMap L x))
  rw [mathlibIdeleClassNorm_ideleClassMap]
  change Multiplicative.ofAdd (-Real.log (idelicNorm L x)) =
    Multiplicative.ofAdd (-Real.log (idelicNorm K (mathlibIdeleNorm K L x)))
  rw [idelicNorm_mathlibIdeleNorm]

/-- A norm twist pulls back with the SAME real parameter. -/
@[simp] theorem heckeNormPullback_normTwist (t : ℝ) :
    heckeNormPullback K L (heckeNormTwist K t) = heckeNormTwist L t := by
  change pullback (mathlibIdeleClassNorm K L) (normTwist (heckeLogNorm K) t) =
    normTwist (heckeLogNorm L) t
  rw [pullback_normTwist, ← heckeLogNorm_norm_compatible K L]

end Pullback
end HeckeSkeleton.Descent.PoleMatching



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.PoleMatching

open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Characters.NormPullbackDraft
open scoped Topology BigOperators

section PoleClassification

variable (F : Type) [Field F] [NumberField F]

/-- Classification of failure of analyticity of the actual chosen function,
using its two explicit analytic branches. The forward implication does not
infer analyticity from a nonnegative meromorphic germ order. -/
theorem not_analyticAt_heckeContinuation_iff
    (χ : HeckeCharacter F) (s : ℂ) :
    ¬ AnalyticAt ℂ (heckeContinuation F χ) s ↔
      ∃ t : ℝ, χ = heckeNormTwist F t ∧ s = heckeNormPole t := by
  constructor
  · intro hnon
    by_cases hnorm : ∃ t : ℝ, χ = heckeNormTwist F t
    · obtain ⟨t, ht, ha⟩ :=
        heckeContinuation_normBranch_analyticAwayPole F χ hnorm
      refine ⟨t, ht, ?_⟩
      by_contra hne
      exact hnon (ha s hne)
    · have hn : ∀ t : ℝ, χ ≠ heckeNormTwist F t :=
        fun t ht => hnorm ⟨t, ht⟩
      exact False.elim
        (hnon ((differentiable_heckeContinuation_of_nonNorm F χ hn).analyticAt s))
  · rintro ⟨t, rfl, rfl⟩ ha
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg)
      ((heckeContinuation_pole_iff F (heckeNormTwist F t) (heckeNormPole t)).mpr
        ⟨t, rfl, rfl⟩)

end PoleClassification

/-- Equality of pole locations recovers the actual real twist parameter. -/
theorem heckeNormPole_injective : Function.Injective heckeNormPole := by
  intro t u h
  have hi := congrArg Complex.im h
  simpa [heckeNormPole] using hi

section CommonFiber

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K]

/-- Pole matching holds on the whole complex plane for a finite set in one
actual relative-norm pullback fiber. No boundary or zero-free input occurs. -/
theorem pole_matching_of_common_normPullback
    (factors : Finset (HeckeCharacter F)) (η : HeckeCharacter K)
    (hfiber : ∀ ψ ∈ factors, heckeNormPullback F K ψ = η) (s : ℂ) :
    (∀ ψ ∈ factors, AnalyticAt ℂ (heckeContinuation F ψ) s) ∨
      ∃ p ∈ factors,
        meromorphicOrderAt (heckeContinuation F p) s = (-1 : WithTop ℤ) ∧
        meromorphicOrderAt (heckeContinuation K η) s = (-1 : WithTop ℤ) ∧
        ∀ ψ ∈ factors, ψ ≠ p → AnalyticAt ℂ (heckeContinuation F ψ) s := by
  classical
  by_cases hall : ∀ ψ ∈ factors, AnalyticAt ℂ (heckeContinuation F ψ) s
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨p, hp, hnon⟩ := hall
    obtain ⟨t, hpt, hst⟩ := (not_analyticAt_heckeContinuation_iff F p s).mp hnon
    have hη : η = heckeNormTwist K t := by
      calc
        η = heckeNormPullback F K p := (hfiber p hp).symm
        _ = heckeNormPullback F K (heckeNormTwist F t) :=
          congrArg (heckeNormPullback F K) hpt
        _ = heckeNormTwist K t := heckeNormPullback_normTwist F K t
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · simpa only [hpt, hst] using
        meromorphicOrderAt_heckeContinuation_normTwist F t
    · simpa only [hη, hst] using
        meromorphicOrderAt_heckeContinuation_normTwist K t
    · intro ψ _hψ hne
      by_contra hnonψ
      obtain ⟨u, hψu, hsu⟩ :=
        (not_analyticAt_heckeContinuation_iff F ψ s).mp hnonψ
      have hut : u = t := heckeNormPole_injective (hsu.symm.trans hst)
      rw [hut] at hψu
      exact hne (hψu.trans hpt.symm)

/-- Build the formal descent data without a separate pole-matching input.
The equal-pullback condition refers to the actual constructed norm map. -/
def heckeFactorizationDescentData_of_common_normPullback
    (χ : HeckeCharacter F) (η : HeckeCharacter K)
    (factors : Finset (HeckeCharacter F)) (htarget : χ ∈ factors)
    (hfactorization : ∀ s ∈ rightHalfPlane (7 / 8),
      heckeContinuation K η =ᶠ[𝓝[≠] s]
        (fun w => ∏ ψ ∈ factors, heckeContinuation F ψ w))
    (hfiber : ∀ ψ ∈ factors, heckeNormPullback F K ψ = η) :
    HeckeFactorizationDescentData K F χ η where
  factors := factors
  target_mem := htarget
  factorization := hfactorization
  pole_matching := fun s _ => pole_matching_of_common_normPullback F K factors η hfiber s

end CommonFiber
end HeckeSkeleton.Descent.PoleMatching






