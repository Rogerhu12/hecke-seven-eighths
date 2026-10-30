import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Bridge.FLTDuality
import HeckeGeneral.Bridge.FLTInfinityParameters
import FLTReuse.Mf6cc5d4cb452564c
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Completed functional equations for actual Hecke characters

The fixed Tate theorem is applied to the original character and its inverse,
with paired infinity parameters. In the non-norm branch the entire functions
are identified with the chosen continuation by the identity theorem. The norm
branch uses actual entire pole-cleared numerators, and identifies their
quotients with the chosen continuations as meromorphic germs. Total values at
a pole are deliberately not used to assert a cleared pointwise identity.

The positive scale `Nf` is the scale supplied by the proved Tate theorem for
the actual finite local data. Its identification with a discriminant and a
conductor norm is a separate obligation. All number fields here have the
explicit universe-zero scope of the imported vendor theorem.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Bridge
open scoped Classical Topology

variable (F : Type) [Field F] [NumberField F]

/-- Entire continuations are unique from the convergence half-plane. -/
theorem entire_eq_of_eq_rightHalfPlane (f g : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun s _ => hf.analyticAt s
  have hb : AnalyticOnNhd ℂ g Set.univ := fun s _ => hg.analyticAt s
  have he : f =ᶠ[nhds (2 : ℂ)] g := by
    have hhalf : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hhalf] with s hs
    exact hfg s hs
  exact ha.eq_of_frequently_eq hb
    ((he.filter_mono nhdsWithin_le_nhds).frequently)

/-- The vendor's entire continuation equals the actual chosen non-norm function. -/
theorem entire_eq_heckeContinuation_of_nonNorm (χ : HeckeCharacter F)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t) (L : ℂ → ℂ)
    (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s) :
    L = heckeContinuation F χ := by
  apply entire_eq_of_eq_rightHalfPlane L (heckeContinuation F χ) hL
    (differentiable_heckeContinuation_of_nonNorm F χ hχ)
  intro s hs
  exact (hLeq s hs).trans (heckeContinuation_eq_series F χ hs).symm

/-- The source dual Gamma product has exactly the paired negative parameters. -/
theorem heckeGammaProfile_dual (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
    (s : ℂ) :
    heckeGammaProfile F (-τ) (-m) s =
      ∏ v : InfinitePlace F,
        if v.IsReal then
          Complex.Gammaℝ (s - (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else
          Complex.Gammaℂ (s - (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2) := by
  simp only [heckeGammaProfile, Pi.neg_apply, Complex.ofReal_neg, neg_mul,
    sub_eq_add_neg, Int.natAbs_neg]

/-- The Gamma profile of the actual local frequencies, signs and angular weights. -/
def canonicalHeckeGammaProfile (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  heckeGammaProfile F (fun v => heckeRadialParameter F v χ) (heckeArchWeight F χ) s

/-- Inversion negates radial frequencies and complex weights. Real signs retain
their canonical parity; the absolute-weight Gamma shifts therefore agree. -/
theorem canonicalHeckeGammaProfile_inv (χ : HeckeCharacter F) (s : ℂ) :
    canonicalHeckeGammaProfile F χ⁻¹ s =
      heckeGammaProfile F (-(fun v => heckeRadialParameter F v χ))
        (-(heckeArchWeight F χ)) s := by
  unfold canonicalHeckeGammaProfile heckeGammaProfile
  apply Finset.prod_congr rfl
  intro v _
  have hw : (heckeArchWeight F χ⁻¹ v).natAbs = (heckeArchWeight F χ v).natAbs := by
    apply Int.ofNat_inj.mp
    simpa only [Int.natCast_natAbs] using abs_heckeArchWeight_inv F χ v
  simp only [heckeRadialParameter_inv, Pi.neg_apply, Int.natAbs_neg, hw]

/-- The completed FE of the chosen non-norm continuation and its actual dual.
The same infinity parameters are retained, rather than chosen independently. -/
theorem exists_completed_heckeFunctionalEquation_of_nonNorm (χ : HeckeCharacter F)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist F t) :
    ∃ (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
      (Nf : ℝ) (ε : ℂ) (Λ Λd : ℂ → ℂ),
      FLTArchRadialCondition F χ τ ∧ FLTArchAngularCondition F χ m ∧
      τ = (fun v => heckeRadialParameter F v χ) ∧ m = heckeArchWeight F χ ∧
      (∀ v : InfinitePlace F, v.IsReal → m v = 0 ∨ m v = 1) ∧
      0 < Nf ∧ ‖ε‖ = 1 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λd ∧
      (∀ s : ℂ, 0 < s.re →
        Λ s = heckeGammaProfile F τ m s * heckeContinuation F χ s) ∧
      (∀ s : ℂ, 0 < s.re →
        Λd s = heckeGammaProfile F (-τ) (-m) s * heckeContinuation F χ⁻¹ s) ∧
      ∀ s : ℂ, Λd (1 - s) = ε * (Nf : ℂ) ^ (s - 1 / 2) * Λ s := by
  obtain ⟨τ, m, hτ, hm, hmreal⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F
      (complexIdeleCharacter F χ) (complexIdeleCharacter_isUnitary F χ)
      (continuous_complexIdeleCharacter_coe F χ)
  have hrad : FLTArchRadialCondition F χ τ := hτ
  have hang : FLTArchAngularCondition F χ m := hm
  have hτcanonical := (heckeRadialParameter_eq_flt F hrad).symm
  have hmcanonical := (heckeArchWeight_eq_flt F hang hmreal).symm
  have hχd := nonNorm_inv F χ hχ
  have hconstruction :=
    NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
      F (complexIdeleCharacter F χ) (continuous_complexIdeleCharacter_coe F χ)
      (complexIdeleCharacter_isUnitary F χ) (complexIdeleCharacter_isIdeleClass F χ)
      τ m hτ hm
  have hconstructiond :=
    NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
      F (complexIdeleCharacter F χ⁻¹) (continuous_complexIdeleCharacter_coe F χ⁻¹)
      (complexIdeleCharacter_isUnitary F χ⁻¹) (complexIdeleCharacter_isIdeleClass F χ⁻¹)
      (-τ) (-m) (FLTArchRadialCondition.inv F hrad) (FLTArchAngularCondition.inv F hang)
  obtain ⟨L, Λ, hL, hΛ, hLeq, hΛeq⟩ :=
    hconstruction.1 ((complexIdeleCharacter_ne_normPow_iff F χ).mpr hχ)
  obtain ⟨Ld, Λd, hLd, hΛd, hLdeq, hΛdeq⟩ :=
    hconstructiond.1 ((complexIdeleCharacter_ne_normPow_iff F χ⁻¹).mpr hχd)
  have hLseries : ∀ s : ℂ, 1 < s.re → L s = heckeLSeries F χ s := by
    intro s hs
    exact (hLeq s hs).trans (heckeLSeries_eq_fltEulerProduct F χ hs).symm
  have hLdseries : ∀ s : ℂ, 1 < s.re → Ld s = heckeLSeries F χ⁻¹ s := by
    intro s hs
    exact (hLdeq s hs).trans (heckeLSeries_eq_fltEulerProduct F χ⁻¹ hs).symm
  have hLchosen := entire_eq_heckeContinuation_of_nonNorm F χ hχ L hL hLseries
  have hLdchosen := entire_eq_heckeContinuation_of_nonNorm F χ⁻¹ hχd Ld hLd hLdseries
  obtain ⟨S, hS⟩ := exists_finset_unramified F χ
  let ρ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ :=
    fun v => NumberField.TateGlobal.localChar (complexIdeleCharacter F χ) v
  obtain ⟨Nf, hNf, hfamily⟩ :=
    NumberField.TateGlobal.exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
      F S ρ
  have hpair := hfamily (complexIdeleCharacter F χ)
    (continuous_complexIdeleCharacter_coe F χ) (complexIdeleCharacter_isUnitary F χ)
    (complexIdeleCharacter_isIdeleClass F χ)
    (fun v hv => (fltUnramifiedAt_iff F χ v).mpr (hS v hv))
    (by intro v _ u _ _; rfl) τ m hτ hm
  have hLddual : ∀ s : ℂ, 1 < s.re → Ld s = fltDualEulerProduct F χ s := by
    intro s hs
    exact (hLdeq s hs).trans (fltDualEulerProduct_eq F χ s).symm
  have hΛdual : ∀ s : ℂ, 0 < s.re →
      Λd s = (∏ v : InfinitePlace F,
        if v.IsReal then
          Complex.Gammaℝ (s - (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else
          Complex.Gammaℂ (s - (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)) * Ld s := by
    simpa only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, sub_eq_add_neg,
      Int.natAbs_neg] using hΛdeq
  obtain ⟨ε, hε, hFE⟩ := hpair.1
    ((complexIdeleCharacter_ne_normPow_iff F χ).mpr hχ)
    L hL hLeq Ld hLd
    (by simpa only [fltDualEulerProduct, fltDualPrimeCoefficient] using hLddual)
    Λ Λd hΛ hΛd hΛeq hΛdual
  refine ⟨τ, m, Nf, ε, Λ, Λd, hrad, hang, hτcanonical, hmcanonical, hmreal,
    hNf, hε, hΛ, hΛd, ?_, ?_, hFE⟩
  · simpa only [heckeGammaProfile, hLchosen] using hΛeq
  · simpa only [heckeGammaProfile, hLdchosen] using hΛdeq

/-- A genuine entire numerator gives the chosen continuation as a meromorphic
germ at every point. This includes poles without assigning them artificial zeros. -/
theorem poleCleared_quotient_eventuallyEq_heckeContinuation (χ : HeckeCharacter F)
    (t : ℝ) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (hQeq : ∀ s : ℂ, 1 < s.re → Q s = (s - heckeNormPole t) * heckeLSeries F χ s)
    (s : ℂ) :
    (fun z => Q z / (z - heckeNormPole t)) =ᶠ[nhdsWithin s {s}ᶜ]
      heckeContinuation F χ := by
  apply heckeContinuation_eventuallyEq_of_meromorphic F χ
    (fun z => Q z / (z - heckeNormPole t))
  · intro z _
    exact (hQ.analyticAt z).meromorphicAt.div
      ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  · intro z hz
    rw [hQeq z hz]
    exact mul_div_cancel_left₀ _ (sub_heckeNormPole_ne_zero hz t)

/-- The regularized norm-branch FE. Both entire numerators and both entire
completed functions are constructed, and their quotient germs are attached to
the chosen continuations. No nonzero value at a pole is assumed or concluded. -/
theorem exists_regularized_heckeFunctionalEquation_of_norm (χ : HeckeCharacter F)
    (t : ℝ) (hχ : χ = heckeNormTwist F t) :
    ∃ (τ : InfinitePlace F → ℝ) (m : InfinitePlace F → ℤ)
      (Nf : ℝ) (ε : ℂ) (Q Qd ΛQ ΛQd : ℂ → ℂ),
      FLTArchRadialCondition F χ τ ∧ FLTArchAngularCondition F χ m ∧
      τ = (fun v => heckeRadialParameter F v χ) ∧ m = heckeArchWeight F χ ∧
      (∀ v : InfinitePlace F, v.IsReal → m v = 0 ∨ m v = 1) ∧
      0 < Nf ∧ ‖ε‖ = 1 ∧ Differentiable ℂ Q ∧ Differentiable ℂ Qd ∧
      Differentiable ℂ ΛQ ∧ Differentiable ℂ ΛQd ∧
      (∀ s : ℂ, 1 < s.re → Q s = (s - heckeNormPole t) * heckeLSeries F χ s) ∧
      (∀ s : ℂ, 1 < s.re → Qd s = (s - heckeNormPole (-t)) * heckeLSeries F χ⁻¹ s) ∧
      (∀ s : ℂ, 0 < s.re →
        ΛQ s = (s - (t : ℂ) * Complex.I) * (heckeGammaProfile F τ m s * Q s)) ∧
      (∀ s : ℂ, 0 < s.re →
        ΛQd s = (s + (t : ℂ) * Complex.I) * (heckeGammaProfile F (-τ) (-m) s * Qd s)) ∧
      (∀ s : ℂ, (fun z => Q z / (z - heckeNormPole t)) =ᶠ[nhdsWithin s {s}ᶜ]
        heckeContinuation F χ) ∧
      (∀ s : ℂ, (fun z => Qd z / (z - heckeNormPole (-t))) =ᶠ[nhdsWithin s {s}ᶜ]
        heckeContinuation F χ⁻¹) ∧
      ∀ s : ℂ, ΛQd (1 - s) = ε * (Nf : ℂ) ^ (s - 1 / 2) * ΛQ s := by
  obtain ⟨τ, m, hτ, hm, hmreal⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F
      (complexIdeleCharacter F χ) (complexIdeleCharacter_isUnitary F χ)
      (continuous_complexIdeleCharacter_coe F χ)
  have hrad : FLTArchRadialCondition F χ τ := hτ
  have hang : FLTArchAngularCondition F χ m := hm
  have hτcanonical := (heckeRadialParameter_eq_flt F hrad).symm
  have hmcanonical := (heckeArchWeight_eq_flt F hang hmreal).symm
  have hχd : χ⁻¹ = heckeNormTwist F (-t) := by rw [hχ, heckeNormTwist_neg]
  have hψ : complexIdeleCharacter F χ = NumberField.TateGlobal.normPowChar F (-t) :=
    (complexIdeleCharacter_eq_normPow_iff F χ (-t)).mpr (by simpa only [neg_neg] using hχ)
  have hψd : complexIdeleCharacter F χ⁻¹ = NumberField.TateGlobal.normPowChar F t :=
    (complexIdeleCharacter_eq_normPow_iff F χ⁻¹ t).mpr hχd
  have hconstruction :=
    NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
      F (complexIdeleCharacter F χ) (continuous_complexIdeleCharacter_coe F χ)
      (complexIdeleCharacter_isUnitary F χ) (complexIdeleCharacter_isIdeleClass F χ)
      τ m hτ hm
  have hconstructiond :=
    NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
      F (complexIdeleCharacter F χ⁻¹) (continuous_complexIdeleCharacter_coe F χ⁻¹)
      (complexIdeleCharacter_isUnitary F χ⁻¹) (complexIdeleCharacter_isIdeleClass F χ⁻¹)
      (-τ) (-m) (FLTArchRadialCondition.inv F hrad) (FLTArchAngularCondition.inv F hang)
  obtain ⟨Q, ΛQ, hQ, hΛQ, hQeq, hΛQeq⟩ := hconstruction.2 (-t) hψ
  obtain ⟨Qd, ΛQd, hQd, hΛQd, hQdeq, hΛQdeq⟩ := hconstructiond.2 t hψd
  have hQseries : ∀ s : ℂ, 1 < s.re →
      Q s = (s - heckeNormPole t) * heckeLSeries F χ s := by
    intro s hs
    have h := hQeq s hs
    change Q s = _ * fltEulerProduct F χ s at h
    rw [← heckeLSeries_eq_fltEulerProduct F χ hs] at h
    simpa only [heckeNormPole, Complex.ofReal_neg, neg_mul, sub_neg_eq_add] using h
  have hQdseries : ∀ s : ℂ, 1 < s.re →
      Qd s = (s - heckeNormPole (-t)) * heckeLSeries F χ⁻¹ s := by
    intro s hs
    have h := hQdeq s hs
    change Qd s = _ * fltEulerProduct F χ⁻¹ s at h
    rw [← heckeLSeries_eq_fltEulerProduct F χ⁻¹ hs] at h
    simpa only [heckeNormPole, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using h
  have hQddual : ∀ s : ℂ, 1 < s.re →
      Qd s = (s - ((1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) *
        fltDualEulerProduct F χ s := by
    intro s hs
    rw [fltDualEulerProduct_eq]
    simpa only [fltEulerProduct, fltPrimeCoefficient,
      Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hQdeq s hs
  have hΛdual : ∀ s : ℂ, 0 < s.re →
      ΛQd s = (s - ((-t : ℝ) : ℂ) * Complex.I) *
        ((∏ v : InfinitePlace F,
          if v.IsReal then
            Complex.Gammaℝ (s - (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else
            Complex.Gammaℂ (s - (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)) * Qd s) := by
    simpa only [Pi.neg_apply, Complex.ofReal_neg, neg_mul, sub_eq_add_neg,
      sub_neg_eq_add, neg_neg, Int.natAbs_neg] using hΛQdeq
  obtain ⟨S, hS⟩ := exists_finset_unramified F χ
  let ρ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ :=
    fun v => NumberField.TateGlobal.localChar (complexIdeleCharacter F χ) v
  obtain ⟨Nf, hNf, hfamily⟩ :=
    NumberField.TateGlobal.exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
      F S ρ
  have hpair := hfamily (complexIdeleCharacter F χ)
    (continuous_complexIdeleCharacter_coe F χ) (complexIdeleCharacter_isUnitary F χ)
    (complexIdeleCharacter_isIdeleClass F χ)
    (fun v hv => (fltUnramifiedAt_iff F χ v).mpr (hS v hv))
    (by intro v _ u _ _; rfl) τ m hτ hm
  obtain ⟨ε, hε, hFE⟩ := hpair.2 (-t) hψ Q hQ hQeq Qd hQd
    (by simpa only [fltDualEulerProduct, fltDualPrimeCoefficient] using hQddual)
    ΛQ ΛQd hΛQ hΛQd hΛQeq hΛdual
  refine ⟨τ, m, Nf, ε, Q, Qd, ΛQ, ΛQd, hrad, hang,
    hτcanonical, hmcanonical, hmreal, hNf, hε,
    hQ, hQd, hΛQ, hΛQd, hQseries, hQdseries, ?_, ?_, ?_, ?_, hFE⟩
  · simpa only [heckeGammaProfile, Complex.ofReal_neg, neg_mul, sub_eq_add_neg]
      using hΛQeq
  · simpa only [heckeGammaProfile] using hΛQdeq
  · exact poleCleared_quotient_eventuallyEq_heckeContinuation F χ t Q hQ hQseries
  · exact poleCleared_quotient_eventuallyEq_heckeContinuation F χ⁻¹ (-t) Qd hQd hQdseries

end HeckeGeneral.Analysis
