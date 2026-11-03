import HeckeSkeleton.FunctionalEquationConductor

/-!
The actual non-norm Hecke functional equation with explicit conductor scale.
The equation is taken directly from isNicePinned_heckeDatum, whose scale is
the actual vendor heckeConductor. The older existential-scale theorem is
used only for entire completed functions and their Gamma-times-L values;
its equation and its opaque scale witness are discarded.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.ExplicitHeckeFunctionalEquation

open NumberField IsDedekindDomain AutomorphicForm
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate
open HeckeSkeleton.FunctionalEquationConductor
open P2MW.S_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

def heckeConductorScale (χ : HeckeCharacter K) : ℝ :=
  ((NumberField.discr K).natAbs : ℝ) * ((finiteConductor K χ).val.absNorm : ℝ)

/-- The FE scale is fixed in the statement, rather than hidden behind an
existential witness. The norm-character pole-cleared branch is separate. -/
theorem exists_completed_functionalEquation_explicitScale_of_nonNorm
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) :
    ∃ (ε : ℂ) (Λ Λd : ℂ → ℂ),
      0 < heckeConductorScale K χ ∧ ‖ε‖ = 1 ∧
      Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
      LDatum.BoundedOnStrips Λ ∧ LDatum.BoundedOnStrips Λd ∧
      (∀ s : ℂ, 0 < s.re →
        Λ s = canonicalHeckeGammaProfile K χ s * heckeContinuation K χ s) ∧
      (∀ s : ℂ, 0 < s.re →
        Λd s = canonicalHeckeGammaProfile K χ⁻¹ s * heckeContinuation K χ⁻¹ s) ∧
      ∀ s : ℂ, Λd (1 - s) =
        ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) * Λ s := by
  obtain ⟨τ, m, _, _, Λ, Λd, hτ, hm, hτcan, hmcan, _, _, _, hΛ, hΛd,
    hΛid, hΛdid, _⟩ := exists_completed_heckeFunctionalEquation_of_nonNorm K χ hχ
  let χf := complexIdeleCharacter K χ
  have hcont : Continuous χf := F1Z.continuous_of_continuous_coe K χf
    (continuous_complexIdeleCharacter_coe K χ)
  have hadm : IsAdmissibleTwist K χf :=
    ⟨complexIdeleCharacter_isIdeleClass K χ, hcont, complexIdeleCharacter_isUnitary K χ⟩
  have hχ1 : ∃ x ∈ normOneIdeles K, χf x ≠ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K χf hcont
      (complexIdeleCharacter_isUnitary K χ) h
    exact ((complexIdeleCharacter_ne_normPow_iff K χ).mpr hχ) t ht
  let uR : ∀ w : InfinitePlace K, w.IsReal → ℂ := fun w _ => (τ w : ℂ) * Complex.I
  let aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2 := fun w _ => (m w : ZMod 2)
  let uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ := fun w _ => (τ w : ℂ) * Complex.I
  let kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ := fun w _ => m w
  have hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K χf w (uR w hw) ((aR w hw).val : ℤ) :=
    fun w hw => F1Z.isArchCompAt_real K χf τ m hτ hm w hw
  have hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K χf w (uC w hw) (kC w hw) :=
    fun w hw => F1Z.isArchCompAt_complex K χf τ m hτ hm w hw
  obtain ⟨_, _, hN, Θ, Θd, hΘ, hΘd, hbounded, hboundedd, h1, h2, hFE⟩ :=
    isNicePinned_heckeDatum K χf hadm hχ1 uR aR uC kC hR hC
  have hGamma (s : ℂ) : (heckeDatum K χf uR aR uC kC).archFactor s =
      heckeGammaProfile K τ m s := by
    rw [F1Z.archFactor_heckeDatum]
    exact (F1Z.gamma_eq_prod_subtype K τ m s).symm
  have hGammaD (s : ℂ) : (heckeDatum K χf uR aR uC kC).archFactorDual s =
      heckeGammaProfile K (-τ) (-m) s := by
    rw [F1Z.archFactorDual_heckeDatum, heckeGammaProfile_dual]
    exact (F1Z.gamma'_eq_prod_subtype K τ m s).symm
  have hEuler (s : ℂ) (hs : 1 < s.re) :
      (heckeDatum K χf uR aR uC kC).LFun s = heckeContinuation K χ s := by
    rw [F1Z.LFun_heckeDatum]
    change fltEulerProduct K χ s = heckeContinuation K χ s
    exact (heckeLSeries_eq_fltEulerProduct K χ hs).symm.trans
      (heckeContinuation_eq_series K χ hs).symm
  have hEulerD (s : ℂ) (hs : 1 < s.re) :
      (heckeDatum K χf uR aR uC kC).LFunDual s = heckeContinuation K χ⁻¹ s := by
    rw [F1Z.LFunDual_heckeDatum]
    change fltDualEulerProduct K χ s = heckeContinuation K χ⁻¹ s
    rw [fltDualEulerProduct_eq]
    exact (heckeLSeries_eq_fltEulerProduct K χ⁻¹ hs).symm.trans
      (heckeContinuation_eq_series K χ⁻¹ hs).symm
  have hΘeq : Θ = Λ := by
    apply entire_eq_of_eq_rightHalfPlane Θ Λ hΘ hΛ
    intro s hs
    rw [h1 s hs, hGamma s, hEuler s hs, hΛid s (by linarith), one_mul]
  have hΘdeq : Θd = Λd := by
    apply entire_eq_of_eq_rightHalfPlane Θd Λd hΘd hΛd
    intro s hs
    rw [h2 s hs, hGammaD s, hEulerD s hs, hΛdid s (by linarith), one_mul]
  let root : ℂ := heckeRootNumber K χf aR kC
  have hroot : ‖root‖ = 1 := F1Z.norm_heckeRootNumber K χf hadm aR kC
  have hroot0 : root ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hroot
    norm_num at hroot
  have hNexplicit : heckeConductor K χf = heckeConductorScale K χ :=
    fltHeckeConductor_eq_discr_mul_finiteConductor K χ
  have hNpos : 0 < heckeConductorScale K χ := by rwa [hNexplicit] at hN
  refine ⟨root⁻¹, Λ, Λd, hNpos, ?_, hΛ, hΛd,
    hΘeq ▸ hbounded, hΘdeq ▸ hboundedd, ?_, ?_, ?_⟩
  · rw [norm_inv, hroot, inv_one]
  · intro s hs
    simpa only [hτcan, hmcan, canonicalHeckeGammaProfile] using hΛid s hs
  · intro s hs
    rw [canonicalHeckeGammaProfile_inv]
    simpa only [hτcan, hmcan] using hΛdid s hs
  · intro s
    have hF : Λ s = root * (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s) * Λd (1 - s) := by
      have hh := hFE s
      rw [hΘeq, hΘdeq, hNexplicit] at hh
      convert hh using 1 <;> norm_num [heckeDatum, root]
    have hcancel : (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) *
        (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s) = 1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hNpos.ne'),
        show s - 1 / 2 + (1 / 2 - s) = 0 by ring, Complex.cpow_zero]
    have hcoefficient : root⁻¹ * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) * root *
        (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s) = 1 := by
      calc
        _ = (root⁻¹ * root) * ((heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) *
            (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hroot0, hcancel, one_mul]
    calc
      Λd (1 - s) = (root⁻¹ * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) * root *
          (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s)) * Λd (1 - s) := by
        rw [hcoefficient, one_mul]
      _ = (root⁻¹ * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)) *
          (root * (heckeConductorScale K χ : ℂ) ^ (1 / 2 - s) * Λd (1 - s)) := by ring
      _ = root⁻¹ * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) * Λ s := by rw [← hF]

end HeckeSkeleton.ExplicitHeckeFunctionalEquation
