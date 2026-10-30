import HeckeSkeleton.SmallRadius.FiniteUnitShellFourierMellin
import HeckeGeneral.Analysis.SUnitSchwartzIntegrable
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Pi

/-!
Positive Mellin absolute moments for an arbitrary
continuous compactly supported test on the finite additive S-product.
The support may meet zero in any coordinate. Actual valuation-ball local
zeta integrability supplies the integrable product envelope; no integrability
or separation from zero is a premise.

The measure is precisely finiteMultiplicativeHaar. Its local Haar constants
are retained in the actual envelope integrals, not normalized to one.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SmallPositiveFiniteMomentDraft

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open HeckeGeneral.Arithmetic MeasureTheory Set WithZeroTopology
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierMellinDraft
open NumberField.AdelicFourier
open scoped Classical BigOperators WithZero

variable (K : Type) [Field K] [NumberField K]

-- The local-zeta provider uses the actual completion Borel structure.
attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]

local instance finiteUnitsSecondCountable (v : S) :
    SecondCountableTopology (v.val.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

set_option quotPrecheck false in
local notation "A" => ((v : S) → v.val.adicCompletion K)
set_option quotPrecheck false in
local notation "U" => ((v : S) → (v.val.adicCompletion K)ˣ)

/-- The literal finite-place absolute Mellin integrand. -/
def finiteWeightedAbsoluteTest (ψ : A → ℂ) (σ : ℝ) (u : U) : ℝ :=
  ‖ψ (fun v => (u v).val)‖ * ∏ v : S, ‖(u v).val‖ ^ σ

/-- Compact additive support has a fixed upper valuation bound at each
place, without a lower valuation bound or any punctured-support premise. -/
theorem exists_support_valuation_bounds (ψ : A → ℂ)
    (hψsupport : HasCompactSupport ψ) :
    ∃ k : S → ℤ, ∀ x : A, ψ x ≠ 0 →
      ∀ v : S, Valued.v (x v) ≤ WithZero.exp (k v) := by
  have hb (v : S) : ∃ k : ℤ, ∀ x : A, ψ x ≠ 0 →
      Valued.v (x v) ≤ WithZero.exp k := by
    have hv : Continuous (Valued.v : v.val.adicCompletion K → ℤᵐ⁰) :=
      Valued.continuous_valuation_of_surjective
        (valuedAdicCompletion_surjective K v.val)
    obtain ⟨b, hb⟩ :=
      (hψsupport.isCompact.image (hv.comp (continuous_apply v))).bddAbove
    refine ⟨WithZero.log b, fun x hx => ?_⟩
    exact (hb (Set.mem_image_of_mem _ (subset_closure hx))).trans WithZero.le_exp_log
  choose k hk using hb
  exact ⟨k, fun x hx v => hk v x hx⟩

/-- Real nonnegative envelope, defined from the actual local zeta test. -/
def localPositiveMomentEnvelope (v : S) (k : ℤ) (σ : ℝ)
    (u : (v.val.adicCompletion K)ˣ) : ℝ :=
  ‖weightedValuationBall K v.val k σ u‖

theorem localPositiveMomentEnvelope_integrable (v : S) (k : ℤ)
    (σ : ℝ) (hσ : 0 < σ) :
    Integrable (localPositiveMomentEnvelope K S v k σ)
      (Measure.haar : Measure (v.val.adicCompletion K)ˣ) :=
  (weightedValuationBall_integrable K v.val k hσ).norm

theorem localPositiveMomentEnvelope_eq (v : S) (k : ℤ) (σ : ℝ)
    (u : (v.val.adicCompletion K)ˣ)
    (hu : Valued.v (u.val) ≤ WithZero.exp k) :
    localPositiveMomentEnvelope K S v k σ u = ‖u.val‖ ^ σ := by
  simp only [localPositiveMomentEnvelope, weightedValuationBall, if_pos hu,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr u.ne_zero), Complex.ofReal_re]

/-- A genuine integrable product majorant for a possibly nonseparable
finite-place test. All constants depend only on the fixed test and sigma. -/
theorem exists_finite_weighted_integrable_envelope (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ k : S → ℤ, ∃ C : ℝ, 0 < C ∧
      Integrable (fun u : U =>
        ∏ v : S, localPositiveMomentEnvelope K S v (k v) σ (u v))
        (finiteMultiplicativeHaar K S) ∧
      ∀ u : U, finiteWeightedAbsoluteTest K S ψ σ u ≤
        C * ∏ v : S, localPositiveMomentEnvelope K S v (k v) σ (u v) := by
  obtain ⟨k, hk⟩ := exists_support_valuation_bounds K S ψ hψsupport
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_norm_finiteTestFunction_le K S ψ hψ hψsupport
  have henv : Integrable (fun u : U =>
      ∏ v : S, localPositiveMomentEnvelope K S v (k v) σ (u v))
      (finiteMultiplicativeHaar K S) :=
    Integrable.fintype_prod_dep (fun v =>
      localPositiveMomentEnvelope_integrable K S v (k v) σ hσ)
  refine ⟨k, C, hC, henv, fun u => ?_⟩
  by_cases hu : ψ (fun v => (u v).val) = 0
  · simp only [finiteWeightedAbsoluteTest, hu, norm_zero, zero_mul]
    exact mul_nonneg hC.le (Finset.prod_nonneg fun v _ => norm_nonneg _)
  · have he : (∏ v : S, localPositiveMomentEnvelope K S v (k v) σ (u v)) =
        ∏ v : S, ‖(u v).val‖ ^ σ := by
      apply Finset.prod_congr rfl
      intro v _
      exact localPositiveMomentEnvelope_eq K S v (k v) σ (u v) (hk _ hu v)
    rw [he]
    exact mul_le_mul_of_nonneg_right (hbound _)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (norm_nonneg _) _)

/-- Actual finite-S weighted L1, with a finite constant and no assumption
that the additive support avoids zero. The local Haar normalization remains
inside the displayed actual product measure. -/
theorem exists_finite_compactSupport_weightedL1_bound (ψ : A → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      Integrable (finiteWeightedAbsoluteTest K S ψ σ) (finiteMultiplicativeHaar K S) ∧
      (∫ u : U, finiteWeightedAbsoluteTest K S ψ σ u
        ∂finiteMultiplicativeHaar K S) ≤ C := by
  obtain ⟨k, B, hB, henv, hb⟩ :=
    exists_finite_weighted_integrable_envelope K S ψ hψ hψsupport σ hσ
  let G : U → ℝ := fun u =>
    ∏ v : S, localPositiveMomentEnvelope K S v (k v) σ (u v)
  have hG : Integrable G (finiteMultiplicativeHaar K S) := henv
  have hGpos (u : U) : 0 ≤ G u :=
    Finset.prod_nonneg fun v _ => norm_nonneg _
  have hFpos (u : U) : 0 ≤ finiteWeightedAbsoluteTest K S ψ σ u :=
    mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hFmeas : AEStronglyMeasurable (finiteWeightedAbsoluteTest K S ψ σ)
      (finiteMultiplicativeHaar K S) := by
    have hval : Continuous (fun u : U => (fun v : S => (u v).val)) := by
      fun_prop
    have hw : Measurable (fun u : U => ∏ v : S, ‖(u v).val‖ ^ σ) := by
      fun_prop
    exact ((hψ.comp hval).norm.measurable.mul hw).aestronglyMeasurable
  have hF : Integrable (finiteWeightedAbsoluteTest K S ψ σ)
      (finiteMultiplicativeHaar K S) := by
    apply (hG.const_mul B).mono' hFmeas
    exact Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFpos u)]
      exact hb u
  have hi : 0 ≤ ∫ u : U, G u ∂finiteMultiplicativeHaar K S :=
    integral_nonneg hGpos
  refine ⟨B * (∫ u : U, G u ∂finiteMultiplicativeHaar K S) + 1,
    by positivity, hF, ?_⟩
  have hle := integral_mono hF (hG.const_mul B) hb
  rw [integral_const_mul] at hle
  exact hle.trans (le_add_of_nonneg_right zero_le_one)

end HeckeGeneral.Analysis.SmallPositiveFiniteMomentDraft
