import HeckeSkeleton.ExpansionModels.SmallRowNormContinuation
import HeckeGeneral.Analysis.PhysicalProbePrincipal

/-!
# The actual deleted Dedekind zeta residues

The chosen norm-continuation numerator agrees with the original entire
Dedekind pole-cleared function by uniqueness.  Multiplication by the
actual deleted Euler polynomial therefore gives an entire numerator
whose value at one is exactly `deletedZetaResidue`.

The pointwise continuation formulas and both pole limits below concern
the literal chosen continuation.  No residue scalar or principal-row
identity is supplied as an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- Uniqueness identifies the entire function used by the norm branch
with the actual Dedekind numerator used in the physical normalization. -/
theorem normPoleNumerator_zero_eq_dedekindPoleCleared :
    normPoleNumerator K 0 = dedekindPoleCleared K := by
  obtain ⟨hR, _, hReq, _⟩ : Differentiable ℂ (dedekindPoleCleared K) ∧
      dedekindPoleCleared K 1 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → dedekindPoleCleared K s =
        (s - 1) * NumberField.dedekindZeta K s) ∧
      ∀ n : ℕ, dedekindPoleCleared K (-2 * (n + 1)) = 0 :=
    Classical.choose_spec
      (NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K)
  apply (show AnalyticOnNhd ℂ (normPoleNumerator K 0) Set.univ from
    fun s _ => (normPoleNumerator_differentiable K 0).analyticAt s).eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (dedekindPoleCleared K) Set.univ from fun s _ => hR.analyticAt s)
      (z₀ := (2 : ℂ))
  have hn : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hn] with s hs
  rw [normPoleNumerator_right K 0 s hs, hReq s hs]
  simpa [heckeNormTwist, heckeNormPole] using
    congrArg (fun y : ℂ => (s - 1) * y) (heckeLSeries_trivial_eq_dedekindZeta K hs)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def actualDeletedZetaNumerator (s : ℂ) : ℂ :=
  heckeEulerDeletionPolynomial K 1 (exceptionalPrimes K S) s * normPoleNumerator K 0 s

theorem actualDeletedZetaNumerator_differentiable :
    Differentiable ℂ (actualDeletedZetaNumerator K S) := by
  intro s
  exact (heckeEulerDeletionPolynomial_analyticAt K 1 (exceptionalPrimes K S) s).differentiableAt.mul
    (normPoleNumerator_differentiable K 0 s)

@[simp] theorem actualDeletedZetaNumerator_one :
    actualDeletedZetaNumerator K S 1 = deletedZetaResidue K S := by
  rw [actualDeletedZetaNumerator, normPoleNumerator_zero_eq_dedekindPoleCleared,
    deletedZetaResidue, mul_comm]

/-- The exact function equality includes the total-division value at one. -/
theorem actual_deletedZeta_eq_numerator_div (s : ℂ) :
    heckeDeletedContinuation K 1 (exceptionalPrimes K S) s =
      actualDeletedZetaNumerator K S s / (s - 1) := by
  have hformula : heckeContinuation K (1 : HeckeCharacter K) s =
      normPoleNumerator K 0 s / (s - 1) := by
    simpa [heckeNormTwist, heckeNormPole] using congrFun (heckeContinuation_normTwist_eq K 0) s
  rw [heckeDeletedContinuation, hformula, actualDeletedZetaNumerator]
  ring

theorem actual_deletedZeta_analyticAt (s : ℂ) (hs : s ≠ 1) :
    AnalyticAt ℂ (heckeDeletedContinuation K 1 (exceptionalPrimes K S)) s := by
  have heq : heckeDeletedContinuation K 1 (exceptionalPrimes K S) =
      fun z => actualDeletedZetaNumerator K S z / (z - 1) :=
    funext (actual_deletedZeta_eq_numerator_div K S)
  rw [heq]
  exact ((actualDeletedZetaNumerator_differentiable K S).analyticAt s).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)

/-- The residue at the actual w-pole is the original deleted residue. -/
theorem actual_deletedZeta_residue_one :
    Tendsto (fun w : ℂ => (w - 1) *
      heckeDeletedContinuation K 1 (exceptionalPrimes K S) w)
      (𝓝[≠] (1 : ℂ)) (𝓝 (deletedZetaResidue K S)) := by
  have hlim : Tendsto (actualDeletedZetaNumerator K S) (𝓝[≠] (1 : ℂ))
      (𝓝 (actualDeletedZetaNumerator K S 1)) :=
    ((actualDeletedZetaNumerator_differentiable K S).continuous.tendsto 1).mono_left
      nhdsWithin_le_nhds
  rw [actualDeletedZetaNumerator_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  rw [actual_deletedZeta_eq_numerator_div K S w]
  field_simp [hw'] <;> ring

/-- The factor six in z has its original Jacobian at the zeta pole. -/
theorem actual_deletedZeta_six_eq (z : ℂ) :
    heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) =
      (actualDeletedZetaNumerator K S (6 * z) / 6) / (z - 1 / 6) := by
  rw [actual_deletedZeta_eq_numerator_div K S (6 * z),
    show (6 : ℂ) * z - 1 = 6 * (z - 1 / 6) by ring]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem actual_deletedZeta_residue_one_sixth :
    Tendsto (fun z : ℂ => (z - 1 / 6) *
      heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z))
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (deletedZetaResidue K S / 6)) := by
  have hc : Continuous (fun z : ℂ => actualDeletedZetaNumerator K S (6 * z) / 6) :=
    ((actualDeletedZetaNumerator_differentiable K S).continuous.comp
      (continuous_const.mul continuous_id)).div_const 6
  have hlim : Tendsto (fun z : ℂ => actualDeletedZetaNumerator K S (6 * z) / 6)
      (𝓝[≠] (1 / 6 : ℂ)) (𝓝 (actualDeletedZetaNumerator K S (6 * (1 / 6)) / 6)) :=
    (hc.tendsto (1 / 6)).mono_left nhdsWithin_le_nhds
  norm_num only [show (6 : ℂ) * (1 / 6) = 1 by norm_num,
    actualDeletedZetaNumerator_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z - 1 / 6 ≠ 0 := sub_ne_zero.mpr hz
  rw [actual_deletedZeta_six_eq K S z]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hz']

end Expansion.Project

#print axioms Expansion.Project.normPoleNumerator_zero_eq_dedekindPoleCleared
#print axioms Expansion.Project.actualDeletedZetaNumerator_differentiable
#print axioms Expansion.Project.actual_deletedZeta_eq_numerator_div
#print axioms Expansion.Project.actual_deletedZeta_residue_one
#print axioms Expansion.Project.actual_deletedZeta_residue_one_sixth
