import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# Child margins constructed from actual source annuli

The actual reconstruction tuple supplies the common-divisor relation,
the cube-label relation and the puncture. Nonemptiness of the literal
norm-supported child gives the clipping allowance. Thus all fields of
the numerical geometry are conclusions of original source information.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.SourceChildGeometry

open NumberField IsDedekindDomain HeckePort.Moments
open FixedTripleFibers SourceLengths
open scoped Classical NumberField

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}

theorem clipping_from_nonzero (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (Z N eta : ℝ) (hZ : 1 < Z) (heta : 0 ≤ eta)
    (hfour : 4 ≤ Z ^ (6 * eta)) (hN : (Ideal.absNorm I : ℝ) ≤ 4 * Z ^ N) :
    max 0 N - N ≤ 6 * eta := by
  have hcap : 1 ≤ 4 * Z ^ N := one_le_norm_cap I hI _ hN
  have hh : Z ^ (0 : ℝ) ≤ Z ^ (N + 6 * eta) := by
    rw [Real.rpow_zero, Real.rpow_add (zero_lt_one.trans hZ)]
    exact hcap.trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hfour
        (Real.rpow_nonneg (zero_le_one.trans hZ.le) N))
  have hexp := (Real.rpow_le_rpow_left_iff hZ).mp hh
  rw [← max_sub_sub_right]
  apply max_le <;> linarith

/-- All numerical geometry fields are derived from the actual tuple,
original annuli and one supported nonzero child column. -/
def geometry {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k)
    (hf : f ≠ 0) (hcommon : x.extractedCommon ≠ 0)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (hq0 : γ.q0 ≠ 0) (ht0 : γ.quotient ≠ 0) (hr0 : γ.residual ≠ 0)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (Z M r ell V Q z c d A B t g theta v j eta : ℝ)
    (hZ : 1 < Z) (heta : 0 ≤ eta)
    (hell : 0 ≤ ell) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hfour : 4 ≤ Z ^ (6 * eta))
    (hparentPuncture : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta))
    (hJ : Z ^ (j - eta) ≤ (Ideal.absNorm (x.core 0) : ℝ))
    (htnorm : (Ideal.absNorm γ.quotient : ℝ) ≤ Z ^ (t + eta))
    (hdnorm : Z ^ (theta - eta) ≤ (Ideal.absNorm (x.core 2) : ℝ))
    (hgnorm : (Ideal.absNorm x.extractedCommon : ℝ) ≤ Z ^ (g + eta))
    (hcolumn : (Ideal.absNorm I : ℝ) ≤ Z ^ secondFormalColumn r A B t g v * 4)
    (hnonterminal : d ≤ ell + V) :
    ChildGeometry (r + 3 * ell + V) M Q z c d eta where
  ell := ell
  A := A
  t := t
  g := g
  theta := theta
  V := V
  j := j
  Qnew := Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ)
  clip := max 0 (secondFormalColumn r A B t g v) - secondFormalColumn r A B t g v
  ell_nonneg := hell
  A_nonneg := hA
  t_nonneg := ht
  V_nonneg := hV
  j_nonneg := hj
  common_divisor := common_gap hx hcommon Z g theta eta hZ hdnorm hgnorm
  label_bound := cube_label_length hx hf hq0 Z ell j eta hZ hb1 hb2 hJ
  puncture := puncture_length_from_source hx hf Rho hRho hq0 ht0 hr0
    Z Q ell A t g theta V eta hZ hA hV hparentPuncture hb1 hb2 htnorm hdnorm hgnorm
  clip_nonneg := sub_nonneg.mpr (le_max_right _ _)
  clip_bound := clipping_from_nonzero I hI Z (secondFormalColumn r A B t g v) eta
    hZ heta hfour (by simpa only [mul_comm] using hcolumn)
  nonterminal := hnonterminal

theorem actual_child_margins {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k)
    (hf : f ≠ 0) (hcommon : x.extractedCommon ≠ 0)
    (Rho : Ideal (𝓞 K)) (hRho : Rho ≠ 0)
    (hq0 : γ.q0 ≠ 0) (ht0 : γ.quotient ≠ 0) (hr0 : γ.residual ≠ 0)
    (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (Z M r ell V Q z c d A B t g theta v j eta : ℝ)
    (hZ : 1 < Z) (heta : 0 ≤ eta)
    (hell : 0 ≤ ell) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hfour : 4 ≤ Z ^ (6 * eta))
    (hparentPuncture : (Ideal.absNorm Rho.radical : ℝ) ≤ Z ^ Q)
    (hb1 : (Ideal.absNorm (x.core 4) : ℝ) ≤ Z ^ (ell + eta))
    (hb2 : (Ideal.absNorm x.secondCube : ℝ) ≤ Z ^ (ell + eta))
    (hJ : Z ^ (j - eta) ≤ (Ideal.absNorm (x.core 0) : ℝ))
    (htnorm : (Ideal.absNorm γ.quotient : ℝ) ≤ Z ^ (t + eta))
    (hdnorm : Z ^ (theta - eta) ≤ (Ideal.absNorm (x.core 2) : ℝ))
    (hgnorm : (Ideal.absNorm x.extractedCommon : ℝ) ≤ Z ^ (g + eta))
    (hcolumn : (Ideal.absNorm I : ℝ) ≤ Z ^ secondFormalColumn r A B t g v * 4)
    (hnonterminal : d ≤ ell + V)
    (hparent : CanonicalMargins (r + 3 * ell + V) M Q z c) (hstep : eta ≤ d / 16) :
    c - 5 * eta ≤
        (max 0 (secondFormalColumn r A B t g v) + secondFormalLabel B theta v j) -
          childM M ell A t g theta V j eta -
          Real.logb Z (Ideal.absNorm (childPuncture Rho γ).radical : ℝ) - z ∧
    c - 7 * eta ≤
        4 * (max 0 (secondFormalColumn r A B t g v) + secondFormalLabel B theta v j) -
          3 * childM M ell A t g theta V j eta - 6 * z ∧
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta ∧
    max 0 (secondFormalColumn r A B t g v) + secondFormalLabel B theta v j ≤
      (r + 3 * ell + V) + 11 * eta := by
  let T := geometry hx hf hcommon Rho hRho hq0 ht0 hr0 I hI
    Z M r ell V Q z c d A B t g theta v j eta hZ heta hell hA ht hV hj
    hfour hparentPuncture hb1 hb2 hJ htnorm hdnorm hgnorm hcolumn hnonterminal
  have hF : T.Fchild =
      max 0 (secondFormalColumn r A B t g v) + secondFormalLabel B theta v j := by
    dsimp only [T, geometry, ChildGeometry.Fchild, childF, decrease,
      secondFormalColumn, secondFormalLabel]
    ring
  have hs := T.step hparent heta hstep
  rw [hF] at hs
  exact hs

end HeckeSkeleton.Moments.MOMInvStep.SourceChildGeometry

end

