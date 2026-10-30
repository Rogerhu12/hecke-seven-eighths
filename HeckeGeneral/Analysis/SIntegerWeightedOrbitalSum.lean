import HeckeGeneral.Analysis.SIntegerOrbitalSum
import HeckeGeneral.Analysis.SIntegerInverseOrbitalSum
import HeckeGeneral.Arithmetic.SIntegerPeriodicWeights

/-!
# Bounded coefficients on the actual S-integer orbits

Absolute norm-integral summability precedes every weighted regrouping.
Both the original and inverse Haar variables give the same radial profile,
on the original fundamental domain and with all subgroup sectors retained.
For actual periodic coefficients the bound comes from the finite quotient.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic MeasureTheory
open scoped Classical

private theorem hasSum_bounded_weighted_fibers
    {A Q U X : Type*} [Countable A] [Countable U] [MeasurableSpace X]
    (μ : Measure X) (e : A ≃ Q × U) (F : A → X → ℂ) (P : Q → ℂ)
    (hF : ∀ a, Integrable (F a) μ)
    (hFnorm : Summable (fun a => ∫ x, ‖F a x‖ ∂μ))
    (hP : ∀ q, (∑' u, ∫ x, F (e.symm (q, u)) x ∂μ) = P q)
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    HasSum (fun q => w q * P q)
      (∫ x, ∑' a, w (e a).1 * F a x ∂μ) := by
  let H : A → X → ℂ := fun a x => w (e a).1 * F a x
  have hH : ∀ a, Integrable (H a) μ := fun a => (hF a).const_mul _
  have hmajor (a : A) : (∫ x, ‖H a x‖ ∂μ) ≤ B * (∫ x, ‖F a x‖ ∂μ) := by
    simp only [H, norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_right (hw _) (integral_nonneg (fun _ => norm_nonneg _))
  have hHnorm : Summable (fun a => ∫ x, ‖H a x‖ ∂μ) :=
    (hFnorm.mul_left B).of_nonneg_of_le
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hmajor
  have hHint : Summable (fun a => ∫ x, H a x ∂μ) :=
    hHnorm.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  have hprod : Summable (fun p : Q × U => ∫ x, H (e.symm p) x ∂μ) :=
    e.symm.summable_iff.mpr hHint
  have hq (q : Q) : (∑' u, ∫ x, H (e.symm (q, u)) x ∂μ) = w q * P q := by
    simp only [H, Equiv.apply_symm_apply, integral_const_mul]
    rw [tsum_mul_left, hP q]
  have htotal : (∑' q, ∑' u, ∫ x, H (e.symm (q, u)) x ∂μ) =
      ∫ x, ∑' a, H a x ∂μ := by
    rw [← hprod.tsum_prod]
    exact (e.symm.tsum_eq (fun a => ∫ x, H a x ∂μ)).trans
      (integral_tsum_of_summable_integral_norm hH hHnorm)
  change HasSum _ (∫ x, ∑' a, H a x ∂μ)
  rw [← htotal]
  exact hprod.prod.hasSum.congr_fun (fun q => (hq q).symm)

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "T" => sLocalNormOneGroup K S
local notation "G" => sLocalMultiplicativeGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Q" => SIntegerOrbits K S Γ

private theorem hasSum_sIntegerOrbitalProfile_weighted_comp
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (σ : T → T) (hσ : Continuous σ)
    (hunfold : ∀ p : G,
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
        sLocalTensorTestFunction K S φ ψ
          (p * (sLocalDiagonal K S (u : S.unit K) * ((σ x : T) : G)))
            ∂sUnitHaarMeasure K S) =
        sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
          ⟨sLocalProductNorm K S p, sLocalProductNorm_pos K S p⟩)
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    HasSum (fun q : Q => w q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        w (Quotient.mk _ a) * sIntegerSchwartzTerm K S φ ψ r a (σ x)
          ∂sUnitHaarMeasure K S) := by
  letI : Countable Γ := (sLocalGammaActionEquiv K S Γ).injective.countable
  let e := nonzeroSIntegerEquivOrbitProduct K S Γ
  let μT := (sUnitHaarMeasure K S).restrict (sUnitFundamentalDomain K S Γ)
  let F : N → T → ℂ := fun a x => sIntegerSchwartzTerm K S φ ψ r a (σ x)
  let P : Q → ℂ := fun q =>
    sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
      ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
        mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩
  have hF : ∀ a : N, Integrable (F a) μT :=
    integrable_sIntegerSchwartzTerm_comp_on_domain K S Γ φ ψ hψ hψsupport r σ hσ
  have hnorm : Summable (fun a : N => ∫ x : T, ‖F a x‖ ∂μT) :=
    summable_integral_norm_sIntegerSchwartzTerm_comp_on_domain K S Γ φ ψ hψ hψsupport r σ hσ
  have hq (q : Q) : (∑' u : Γ, ∫ x : T, F (e.symm (q, u)) x ∂μT) = P q := by
    have hj : Function.Injective (fun u : Γ => e.symm (q, u)) := by
      intro u v huv
      exact congrArg Prod.snd (e.symm.injective huv)
    rw [integral_tsum_of_summable_integral_norm (fun u => hF (e.symm (q, u)))
      (hnorm.comp_injective hj)]
    have hterm (u : Γ) (x : T) : F (e.symm (q, u)) x =
        sLocalTensorTestFunction K S φ ψ
          ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) *
            (sLocalDiagonal K S (u : S.unit K) * ((σ x : T) : G))) := by
      change sLocalTensorTestFunction K S φ ψ
        (sLocalNormSection K S r * ((σ x : T) : G) *
          sLocalNonzeroIntegerDiagonal K S
            ((nonzeroSIntegerEquivOrbitProduct K S Γ).symm (q, u))) = _
      rw [sLocalNonzeroIntegerDiagonal_orbitProduct_symm]
      congr 1
      ac_rfl
    calc
      _ = ∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
          sLocalTensorTestFunction K S φ ψ
            ((sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) *
              (sLocalDiagonal K S (u : S.unit K) * ((σ x : T) : G)))
            ∂sUnitHaarMeasure K S := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => tsum_congr (fun u => hterm u x))
      _ = P q := by
        rw [hunfold]
        unfold P
        congr 1
        apply Subtype.ext
        change sLocalProductNorm K S
          (sLocalNormSection K S r * sLocalNonzeroIntegerDiagonal K S q.out) =
            r.val * (sIntegerOrbitNorm K S Γ q).val
        rw [sLocalProductNorm_mul, sLocalProductNorm_section, ← sIntegerOrbitNorm_out K S Γ q]
        rfl
  have h := hasSum_bounded_weighted_fibers μT e F P hF hnorm hq w B hw
  simpa only [e, F, P, μT, nonzeroSIntegerEquivOrbitProduct_fst] using h

/-- A fixed norm-one shift is absorbed into the actual base point before
inverse unfolding. Its product norm is one, so the radial profile is unchanged. -/
theorem setIntegral_tsum_sLocalTensorTestFunction_shift_inv_eq_profile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (t : T) (p : G) :
    (∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
      sLocalTensorTestFunction K S φ ψ
        (p * (sLocalDiagonal K S (u : S.unit K) * ((t * x⁻¹ : T) : G)))
          ∂sUnitHaarMeasure K S) =
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨sLocalProductNorm K S p, sLocalProductNorm_pos K S p⟩ := by
  have ht : sLocalProductNorm K S (t : G) = 1 :=
    (mem_sLocalNormOneGroup K S t.val).mp t.property
  calc
    _ = ∫ x in sUnitFundamentalDomain K S Γ, ∑' u : Γ,
        sLocalTensorTestFunction K S φ ψ
          ((p * (t : G)) * (sLocalDiagonal K S (u : S.unit K) * ((x⁻¹ : T) : G)))
            ∂sUnitHaarMeasure K S := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      apply tsum_congr
      intro u
      simp only [Subgroup.coe_mul]
      congr 1
      ac_rfl
    _ = sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨sLocalProductNorm K S (p * (t : G)), sLocalProductNorm_pos K S _⟩ :=
      setIntegral_tsum_sLocalTensorTestFunction_inv_eq_profile K S Γ φ ψ hψ hψsupport _
    _ = _ := by
      congr 1
      apply Subtype.ext
      exact (sLocalProductNorm_mul K S p t.val).trans (by rw [ht, mul_one])

/-- Weighted absolute unfolding on the original Haar domain. -/
theorem hasSum_sIntegerOrbitalProfile_weighted
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    HasSum (fun q : Q => w q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        w (Quotient.mk _ a) * sIntegerSchwartzTerm K S φ ψ r a x
          ∂sUnitHaarMeasure K S) :=
  hasSum_sIntegerOrbitalProfile_weighted_comp K S Γ φ ψ hψ hψsupport r id continuous_id
    (setIntegral_tsum_sLocalTensorTestFunction_eq_profile K S Γ φ ψ hψ hψsupport) w B hw

/-- The same profile on the inverse Haar variable, with no inversion-invariant
fundamental-domain assumption. -/
theorem hasSum_sIntegerOrbitalProfile_weighted_inverse
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    HasSum (fun q : Q => w q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        w (Quotient.mk _ a) * sIntegerSchwartzTerm K S φ ψ r a x⁻¹
          ∂sUnitHaarMeasure K S) :=
  hasSum_sIntegerOrbitalProfile_weighted_comp K S Γ φ ψ hψ hψsupport r
    (fun x : T => x⁻¹) continuous_inv
    (setIntegral_tsum_sLocalTensorTestFunction_inv_eq_profile K S Γ φ ψ hψ hψsupport) w B hw

/-- Every fixed norm-one translate of the inverse variable gives the same
common profile, with absolute unfolding on the original fundamental domain. -/
theorem hasSum_sIntegerOrbitalProfile_weighted_shift_inverse
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (t : T)
    (w : Q → ℂ) (B : ℝ) (hw : ∀ q, ‖w q‖ ≤ B) :
    HasSum (fun q : Q => w q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        w (Quotient.mk _ a) * sIntegerSchwartzTerm K S φ ψ r a (t * x⁻¹)
          ∂sUnitHaarMeasure K S) :=
  hasSum_sIntegerOrbitalProfile_weighted_comp K S Γ φ ψ hψ hψsupport r
    (fun x : T => t * x⁻¹) (continuous_const.mul continuous_inv)
    (setIntegral_tsum_sLocalTensorTestFunction_shift_inv_eq_profile
      K S Γ φ ψ hψ hψsupport t) w B hw

/-- Actual periodic coefficients supply their own bound through the finite
principal quotient; no boundedness or convergence hypothesis is added. -/
theorem hasSum_sIntegerPeriodicOrbitalProfile
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (r : {r : ℝ // 0 < r})
    (c : S.integer K) (hc : c ≠ 0)
    (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    HasSum (fun q : Q => sIntegerPeriodicOrbitWeight K S Γ c f hinv q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        f (Ideal.Quotient.mk _ a.val) * sIntegerSchwartzTerm K S φ ψ r a x
          ∂sUnitHaarMeasure K S) := by
  simpa only [sIntegerPeriodicOrbitWeight_mk] using
    hasSum_sIntegerOrbitalProfile_weighted K S Γ φ ψ hψ hψsupport r
      (sIntegerPeriodicOrbitWeight K S Γ c f hinv)
      (sIntegerPeriodicResidueL1 K S c hc f)
      (norm_sIntegerPeriodicOrbitWeight_le_L1 K S Γ c hc f hinv)

/-- Periodic coefficients also unfold on the inverse Fourier-side Haar
variable, with the same actual profile and original unit subgroup. -/
theorem hasSum_sIntegerPeriodicOrbitalProfile_inverse
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ) (r : {r : ℝ // 0 < r})
    (c : S.integer K) (hc : c ≠ 0)
    (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    HasSum (fun q : Q => sIntegerPeriodicOrbitWeight K S Γ c f hinv q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        f (Ideal.Quotient.mk _ a.val) * sIntegerSchwartzTerm K S φ ψ r a x⁻¹
          ∂sUnitHaarMeasure K S) := by
  simpa only [sIntegerPeriodicOrbitWeight_mk] using
    hasSum_sIntegerOrbitalProfile_weighted_inverse K S Γ φ ψ hψ hψsupport r
      (sIntegerPeriodicOrbitWeight K S Γ c f hinv)
      (sIntegerPeriodicResidueL1 K S c hc f)
      (norm_sIntegerPeriodicOrbitWeight_le_L1 K S Γ c hc f hinv)

/-- The fixed norm-one part of a modulus does not change the common periodic
profile, including for the inverse Fourier-side variable. -/
theorem hasSum_sIntegerPeriodicOrbitalProfile_shift_inverse
    (φ : SchwartzMap V ℂ) (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (r : {r : ℝ // 0 < r}) (t : T) (c : S.integer K) (hc : c ≠ 0)
    (f : (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) → ℂ)
    (hinv : ∀ u : Γ, ∀ a : S.integer K,
      f (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u.val).val * a)) =
        f (Ideal.Quotient.mk _ a)) :
    HasSum (fun q : Q => sIntegerPeriodicOrbitWeight K S Γ c f hinv q *
      sUnitOrbitalProfile K S (sLocalTensorTestFunction K S φ ψ)
        ⟨r.val * (sIntegerOrbitNorm K S Γ q).val,
          mul_pos r.property (sIntegerOrbitNorm K S Γ q).property⟩)
      (∫ x in sUnitFundamentalDomain K S Γ, ∑' a : N,
        f (Ideal.Quotient.mk _ a.val) * sIntegerSchwartzTerm K S φ ψ r a (t * x⁻¹)
          ∂sUnitHaarMeasure K S) := by
  simpa only [sIntegerPeriodicOrbitWeight_mk] using
    hasSum_sIntegerOrbitalProfile_weighted_shift_inverse K S Γ φ ψ hψ hψsupport r t
      (sIntegerPeriodicOrbitWeight K S Γ c f hinv)
      (sIntegerPeriodicResidueL1 K S c hc f)
      (norm_sIntegerPeriodicOrbitWeight_le_L1 K S Γ c hc f hinv)

end HeckeGeneral.Analysis
