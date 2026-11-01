import HeckeSkeleton.Moments.MOM_INV_STEP.SourceChildGeometry

/-!
# Actual centered child lengths and the prescribed descent margins

The fixed test centers have small, explicit logarithmic errors. They do
not coincide by definition with every individual extracted norm. This
module keeps that difference through clipping and pays for it using a
finer internal mesh before asserting the public single-step margins.
-/

noncomputable section
namespace HeckeSkeleton.Moments.MOMInvStep.CenteredChildGeometry

open NumberField IsDedekindDomain HeckePort.Moments FixedTripleFibers SourceLengths
open scoped Classical NumberField

/-- A supported actual child cannot have an arbitrarily negative
column length. The constant four is paid from the ordinary mesh width. -/
theorem live_length_lower {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (Z N h : ℝ) (hZ : 1 < Z) (hwidth : 2 ≤ Z ^ h)
    (hsupport : (Ideal.absNorm I : ℝ) ≤ 4 * Z ^ N) :
    -2 * h ≤ N := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfour : 4 ≤ Z ^ (2 * h) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Z ^ h) ^ 2 := pow_le_pow_left₀ (by norm_num) hwidth 2
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
        congr 1
        ring
  have hone := one_le_norm_cap I hI (4 * Z ^ N) hsupport
  have hp : Z ^ (0 : ℝ) ≤ Z ^ (N + 2 * h) := by
    rw [Real.rpow_zero, Real.rpow_add hz]
    exact hone.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour
        (Real.rpow_nonneg hz.le N))
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hp
  linarith

theorem clipped_shift (Nformal Nactual h : ℝ) (hh : 0 ≤ h)
    (hlo : Nformal - 5 * h ≤ Nactual) (hhi : Nactual ≤ Nformal + 8 * h)
    (hlive : -2 * h ≤ Nactual) :
    -h ≤ max 0 Nactual - Nformal + 4 * h ∧
      max 0 Nactual - Nformal + 4 * h ≤ 14 * h := by
  constructor
  · have hm := le_max_right (0 : ℝ) Nactual
    linarith
  · rcases le_total 0 Nactual with hn | hn
    · rw [max_eq_right hn]
      linarith
    · rw [max_eq_left hn]
      linarith

/-- The numerical margins for the actual centered/clipped child.
All annular and center errors use h; the public loss parameter eta is
chosen larger before the source data. -/
theorem centered_step
    (M r ell V Q Qnew z c d A B t g theta v j h eta Nactual Mactual : ℝ)
    (hparent : CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hell : 0 ≤ ell) (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hcommon : -2 * h ≤ g - theta)
    (hlabel : j ≤ 2 * ell + 3 * h)
    (hpuncture : Qnew ≤ Q + decrease ell A t g theta V + 4 * h)
    (hnonterminal : d ≤ ell + V)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual)
    (hrow : Mactual ≤ childM M ell A t g theta V j (5 * h)) :
    let Fc := max 0 Nactual + secondFormalLabel B theta v j + 4 * h
    c - 5 * eta ≤ Fc - Mactual - Qnew - z ∧
      c - 7 * eta ≤ 4 * Fc - 3 * Mactual - 6 * z ∧
      3 * d / 2 ≤ M - Mactual ∧ Fc ≤ r + 3 * ell + V + 11 * eta := by
  obtain ⟨hslo, hshi⟩ := clipped_shift (secondFormalColumn r A B t g v) Nactual h hh hlo hhi hlive
  obtain ⟨hp₁, hp₂⟩ := hparent
  dsimp only
  unfold secondFormalColumn at hslo hshi
  unfold secondFormalLabel childM decrease at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The same actual-center errors fit within the stated physical loss.
The distinct frozen-triple count is present once. -/
theorem physical_exponent_budget
    (M r ell V delta A B R j t g theta v h eta tau pi eps Nactual : ℝ)
    (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) :
    firstKappa M r ell V delta A B R +
      secondLambda M r ell V delta A B j t g theta +
      secondCount ell R j t g theta +
      2 * (max 0 Nactual + secondFormalLabel B theta v j + 4 * h) +
      (9 / 2 + 18 + 11 / 2) * h + tau + pi + eps ≤
      r + 3 * ell + V + 40 * eta + tau + pi + eps := by
  have hs := (clipped_shift (secondFormalColumn r A B t g v) Nactual h hh hlo hhi hlive).2
  have hi := physical_prefactor_identity M r ell V delta A B R j t g theta v
  linarith

theorem physical_power_budget
    (Z M r ell V delta A B R j t g theta v h eta tau pi eps Nactual : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hlo : secondFormalColumn r A B t g v - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r A B t g v + 8 * h)
    (hlive : -2 * h ≤ Nactual) :
    Z ^ (firstKappa M r ell V delta A B R + (9 / 2 : ℝ) * h) *
      Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * h + tau) *
      Z ^ (secondCount ell R j t g theta + (11 / 2 : ℝ) * h + pi) *
      Z ^ (2 * (max 0 Nactual + secondFormalLabel B theta v j + 4 * h) + eps) ≤
      Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  rw [← Real.rpow_add hz, ← Real.rpow_add hz, ← Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_exponent_budget M r ell V delta A B R j t g theta v
    h eta tau pi eps Nactual hh hmesh hlo hhi hlive
  linarith

end HeckeSkeleton.Moments.MOMInvStep.CenteredChildGeometry
end

