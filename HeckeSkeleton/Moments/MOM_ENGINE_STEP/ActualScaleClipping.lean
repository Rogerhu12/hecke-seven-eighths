import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact plain-scale clipping on actual moment data

Clipping a subunit plain scale to one changes the actual profile to
sqrt(c) times W(c x).  The square-root normalization is included, so the
whole plain polynomial and paired energy are exactly unchanged.

A nonempty original annular support gives c at most its fixed upper
annulus bound.  The clipping cost is therefore derived from a genuine
nonzero polynomial, rather than supplied as a length-error hypothesis.
Both plain factors are clipped together and the zero-slot case is
unrestricted.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {ω ψ : HeckeCharacter F}

/-- This is an actual IdealTest with its exact finite support at every
scale.  The prefactor compensates the changed central normalization. -/
def scaleIdealTest (W : IdealTest F) (c : ℝ) (hc : 0 < c) : IdealTest F where
  profile u t x := (Real.sqrt c : ℂ) * W.profile u t (c * x)
  support u t N := W.support u t (N / c)
  support_spec u t N I := by
    have hroot : (Real.sqrt c : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc).ne'
    have harg : idealNorm F I / (N / c) = c * (idealNorm F I / N) := by
      rw [div_div]
      ring
    rw [W.support_spec, harg, mul_ne_zero_iff]
    simp only [hroot, true_and]

/-- No change to a Hecke coefficient, row, common mask, or other factor is
needed for this exact normalization identity. -/
theorem plainPolynomial_scaleIdealTest
    (d : MomentData F ω ψ) (W : IdealTest F) (c : ℝ) (hc : 0 < c)
    (u : NonzeroIdeal F) (N t : ℝ) :
    plainPolynomial d (scaleIdealTest W c hc) u N t =
      plainPolynomial d W u (N / c) t := by
  have hnorm : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt c : ℂ) =
      (Real.sqrt (N / c) : ℂ)⁻¹ := by
    rw [Real.sqrt_div' N hc.le, Complex.ofReal_div, inv_div, div_eq_mul_inv, mul_comm]
  have harg (I : NonzeroIdeal F) :
      idealNorm F I / (N / c) = c * (idealNorm F I / N) := by
    rw [div_div]
    ring
  calc
    _ = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt c : ℂ)) *
        (∑ I ∈ W.support u t (N / c),
          heckeIdealCoefficient F (d.plainBackground * d.rowCharacter u) I *
            W.profile u t (idealNorm F I / (N / c)) * maskValue d u I.val) := by
      simp only [plainPolynomial, scaleIdealTest, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      rw [← harg I]
      ring
    _ = _ := by
      rw [hnorm]
      rfl

def plainClippingFactor (Z n : ℝ) : ℝ := Z ^ (max n 0 - n)

theorem plainClippingFactor_pos (Z n : ℝ) (hZ : 0 < Z) :
    0 < plainClippingFactor Z n := Real.rpow_pos_of_pos hZ _

theorem plainClippingFactor_one_le (Z n : ℝ) (hZ : 1 ≤ Z) :
    1 ≤ plainClippingFactor Z n :=
  Real.one_le_rpow hZ (sub_nonneg.mpr (le_max_left n 0))

theorem clipped_scale_div_factor (Z n : ℝ) (hZ : 0 < Z) :
    Z ^ max n 0 / plainClippingFactor Z n = Z ^ n := by
  rw [plainClippingFactor, Real.rpow_sub hZ]
  field_simp [(Real.rpow_pos_of_pos hZ (max n 0)).ne',
    (Real.rpow_pos_of_pos hZ n).ne']

def clipPlainParameters (a : RealParameters) : RealParameters :=
  { a with n₁ := max a.n₁ 0, n₂ := max a.n₂ 0 }

def clipPlainData (d : MomentData F ω ψ) (a : RealParameters) (Z : ℝ) (hZ : 0 < Z) :
    MomentData F ω ψ :=
  { d with
    plainTest₁ := scaleIdealTest d.plainTest₁ (plainClippingFactor Z a.n₁)
      (plainClippingFactor_pos Z a.n₁ hZ)
    plainTest₂ := scaleIdealTest d.plainTest₂ (plainClippingFactor Z a.n₂)
      (plainClippingFactor_pos Z a.n₂ hZ) }

theorem plainPolynomial_clipped_left (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 0 < Z) (u : NonzeroIdeal F) (t : ℝ) :
    plainPolynomial (clipPlainData d a Z hZ) (clipPlainData d a Z hZ).plainTest₁
      u (Z ^ (clipPlainParameters a).n₁) t =
        plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t := by
  change plainPolynomial d (scaleIdealTest d.plainTest₁ (plainClippingFactor Z a.n₁)
    (plainClippingFactor_pos Z a.n₁ hZ)) u (Z ^ max a.n₁ 0) t = _
  rw [plainPolynomial_scaleIdealTest, clipped_scale_div_factor Z a.n₁ hZ]

theorem plainPolynomial_clipped_right (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 0 < Z) (u : NonzeroIdeal F) (t : ℝ) :
    plainPolynomial (clipPlainData d a Z hZ) (clipPlainData d a Z hZ).plainTest₂
      u (Z ^ (clipPlainParameters a).n₂) t =
        plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t := by
  change plainPolynomial d (scaleIdealTest d.plainTest₂ (plainClippingFactor Z a.n₂)
    (plainClippingFactor_pos Z a.n₂ hZ)) u (Z ^ max a.n₂ 0) t = _
  rw [plainPolynomial_scaleIdealTest, clipped_scale_div_factor Z a.n₂ hZ]

theorem pairedRows_clipped (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 0 < Z) :
    pairedRows (clipPlainData d a Z hZ) (clipPlainParameters a) Z = pairedRows d a Z := rfl

theorem slotProduct_clipped (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 0 < Z) (u : NonzeroIdeal F) (t : ℝ) :
    slotProduct (clipPlainData d a Z hZ) u Z t = slotProduct d u Z t := rfl

/-- This includes every original row and every live slot, even when
there are no slots.  Clipping has introduced no multiplicative loss. -/
theorem pairedEnergy_clipped (d : MomentData F ω ψ) (a : RealParameters)
    (Z t : ℝ) (hZ : 0 < Z) :
    pairedEnergy (clipPlainData d a Z hZ) (clipPlainParameters a) Z t =
      pairedEnergy d a Z t := by
  unfold pairedEnergy
  rw [pairedRows_clipped]
  apply Finset.sum_congr rfl
  intro u _
  rw [plainPolynomial_clipped_left, plainPolynomial_clipped_right, slotProduct_clipped]

theorem clipped_parameters_invariants (a : RealParameters) :
    0 ≤ (clipPlainParameters a).n₁ ∧ 0 ≤ (clipPlainParameters a).n₂ ∧
      (clipPlainParameters a).m + (clipPlainParameters a).q = a.m + a.q ∧
      (clipPlainParameters a).z = a.z ∧ (clipPlainParameters a).κ = a.κ :=
  ⟨le_max_right _ _, le_max_right _ _, rfl, rfl, rfl⟩

theorem clipped_geometry (d : MomentData F ω ψ) (a : RealParameters)
    (Z : ℝ) (hZ : 0 < Z) :
    (clipPlainData d a Z hZ).geometry = d.geometry := rfl

private theorem clipping_idealNorm_one_le (I : NonzeroIdeal F) : 1 ≤ idealNorm F I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun hz => nonZeroDivisors.coe_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))

theorem plainPolynomial_support_nonempty
    (d : MomentData F ω ψ) (W : IdealTest F) (u : NonzeroIdeal F) (N t : ℝ)
    (hne : plainPolynomial d W u N t ≠ 0) : (W.support u t N).Nonempty := by
  by_contra hempty
  have he : W.support u t N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  apply hne
  simp only [plainPolynomial, he, Finset.sum_empty, mul_zero]

/-- The true ideal norm lower bound and the original annular support
bound the profile dilation uniformly whenever that plain factor occurs. -/
theorem clipping_factor_le_of_nonempty_support
    (W : IdealTest F) (u : NonzeroIdeal F) (Z n t B : ℝ)
    (hZ : 1 < Z) (hB : 1 ≤ B)
    (hannulus : ∀ x, W.profile u t x ≠ 0 → x ≤ B)
    (hne : (W.support u t (Z ^ n)).Nonempty) :
    plainClippingFactor Z n ≤ B := by
  by_cases hn : 0 ≤ n
  · simpa only [plainClippingFactor, max_eq_left hn, sub_self, Real.rpow_zero] using hB
  · have hn' : n ≤ 0 := le_of_not_ge hn
    obtain ⟨I, hI⟩ := hne
    have hbound := hannulus (idealNorm F I / Z ^ n) ((W.support_spec _ _ _ _).mp hI)
    have hnorm := div_le_div_of_nonneg_right (clipping_idealNorm_one_le I)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) n).le
    have hc : plainClippingFactor Z n = (Z ^ n)⁻¹ := by
      simp only [plainClippingFactor, max_eq_right hn', zero_sub,
        Real.rpow_neg (zero_lt_one.trans hZ).le]
    rw [hc]
    have hinv : (Z ^ n)⁻¹ ≤ idealNorm F I / Z ^ n := by
      simpa only [one_div] using hnorm
    exact hinv.trans hbound

theorem clipping_exponent_le_of_nonempty_support
    (W : IdealTest F) (u : NonzeroIdeal F) (Z n t B : ℝ)
    (hZ : 1 < Z) (hB : 1 ≤ B)
    (hannulus : ∀ x, W.profile u t x ≠ 0 → x ≤ B)
    (hne : (W.support u t (Z ^ n)).Nonempty) :
    max n 0 - n ≤ Real.log B / Real.log Z := by
  have hc := clipping_factor_le_of_nonempty_support W u Z n t B hZ hB hannulus hne
  have hl := Real.log_le_log (plainClippingFactor_pos Z n (zero_lt_one.trans hZ)) hc
  rw [plainClippingFactor, Real.log_rpow (zero_lt_one.trans hZ)] at hl
  exact (le_div_iff₀ (Real.log_pos hZ)).mpr hl

theorem nonzero_pairedEnergy_plain_witness (d : MomentData F ω ψ)
    (a : RealParameters) (Z t : ℝ) (hne : pairedEnergy d a Z t ≠ 0) :
    ∃ u ∈ pairedRows d a Z,
      plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t ≠ 0 ∧
        plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t ≠ 0 := by
  by_contra hnone
  apply hne
  unfold pairedEnergy
  apply Finset.sum_eq_zero
  intro u hu
  have hz : plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t = 0 ∨
      plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t = 0 := by
    by_contra h
    exact hnone ⟨u, hu,
      (fun he => h (Or.inl he)), (fun he => h (Or.inr he))⟩
  rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The actual two-factor clipping cost is paid by the fixed original
annulus endpoints.  If the original energy is zero, it is already a zero
branch and no length inequality is required. -/
theorem paired_clipping_budget (d : MomentData F ω ψ) (a : RealParameters)
    (Z t B₁ B₂ : ℝ) (hZ : 1 < Z) (hB₁ : 1 ≤ B₁) (hB₂ : 1 ≤ B₂)
    (hleft : ∀ u ∈ pairedRows d a Z, ∀ x, d.plainTest₁.profile u t x ≠ 0 → x ≤ B₁)
    (hright : ∀ u ∈ pairedRows d a Z, ∀ x, d.plainTest₂.profile u t x ≠ 0 → x ≤ B₂)
    (hne : pairedEnergy d a Z t ≠ 0) :
    (clipPlainParameters a).n₁ + (clipPlainParameters a).n₂ -
      (a.n₁ + a.n₂) ≤ (Real.log B₁ + Real.log B₂) / Real.log Z := by
  obtain ⟨u, hu, hne₁, hne₂⟩ := nonzero_pairedEnergy_plain_witness d a Z t hne
  have h₁ := clipping_exponent_le_of_nonempty_support d.plainTest₁ u Z a.n₁ t B₁
    hZ hB₁ (hleft u hu) (plainPolynomial_support_nonempty d d.plainTest₁ u _ t hne₁)
  have h₂ := clipping_exponent_le_of_nonempty_support d.plainTest₂ u Z a.n₂ t B₂
    hZ hB₂ (hright u hu) (plainPolynomial_support_nonempty d d.plainTest₂ u _ t hne₂)
  change max a.n₁ 0 + max a.n₂ 0 - (a.n₁ + a.n₂) ≤ _
  rw [add_div]
  linarith

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.plainPolynomial_scaleIdealTest
#print axioms HeckeSkeleton.Moments.EngineStep.pairedEnergy_clipped
#print axioms HeckeSkeleton.Moments.EngineStep.paired_clipping_budget

