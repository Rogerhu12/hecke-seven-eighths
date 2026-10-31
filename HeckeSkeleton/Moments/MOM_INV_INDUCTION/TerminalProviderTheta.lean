import HeckeSkeleton.Moments.MOM_BASE.ThetaBridge
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionCanonical

/-!
# Exact cube completion of the actual finite canonical column

The finite squarefree column is converted to the literal completed theta
sum by the proved ideal cube inversion. The normalization uses
`Vstar(y) = sqrt(y) W(y)`, and every puncture and whole-index mark survives
the equality. The background, row, and label are arbitrary fixed data.
This is the source identity preceding the general reflected block
estimate consumed in `TerminalProvider`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE
open HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem canonicalVstar_support_upper (W : ℝ → ℂ) (U : ℝ)
    (hW : Function.support W ⊆ Set.Iic U) :
    Function.support (canonicalVstar W) ⊆ Set.Iic U := by
  intro y hy
  apply hW
  intro hw
  exact hy (by simp only [canonicalVstar, hw, mul_zero])

/-- The complete finite canonical column at the original scale. The
row and squarefree label enter only through their actual symbols. -/
def completeCanonicalColumn (θ : HeckeCharacter K) (k : S.integer K)
    (f r : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑ n ∈ squarefreePool K S X,
    thetaGamma K S D n 2 *
      canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val n.val.val *
      mark n.val.val * W (exteriorNorm K S n / X)

/-- Termwise normalization before the ideal Möbius cube inversion. -/
theorem completeCanonicalColumn_term (θ : HeckeCharacter K) (m : S.integer K)
    (r n : ExteriorIdeal K S) (mark : Ideal (𝓞 K) → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (hX : 0 < X) :
    thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val /
        (Real.sqrt (exteriorNorm K S n) : ℂ) * mark n.val.val *
          canonicalVstar W (exteriorNorm K S n / X) =
      (Real.sqrt X : ℂ)⁻¹ *
        (thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val *
          mark n.val.val * W (exteriorNorm K S n / X)) := by
  have hN : 0 < exteriorNorm K S n := idealNorm_pos K n.val
  calc
    _ = (thetaGamma K S D n 2 * canonicalTau K S D θ m r.val.val n.val.val *
        mark n.val.val) *
        ((Real.sqrt (exteriorNorm K S n) : ℂ)⁻¹ *
          canonicalVstar W (exteriorNorm K S n / X)) := by ring
    _ = _ := by
      rw [canonicalVstar_normalization W (exteriorNorm K S n) X hN hX]
      ring

/-- Exact completion of the full finite squarefree column. No terminal
estimate, reconstruction equality, or moment bound is supplied as a
premise; this is the literal cube-Möbius identity over exterior ideals. -/
theorem completeCanonicalColumn_cube_completion
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic 2) :
    completeCanonicalColumn K S D θ k f r mark W X =
      ∑' H : ExteriorIdeal K S,
        (moebius H.val.val : ℂ) *
          canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
          (exteriorNorm K S H : ℂ) *
          weightedCompletedTheta K S D θ (k * D.generator f ^ 4) r ∅
            (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
            (X / exteriorNorm K S H ^ 3) := by
  have hV := canonicalVstar_support_upper W 2 hW
  have hbridge := canonicalThetaBridge K S D θ (k * D.generator f ^ 4)
    r mark (canonicalVstar W) X 2 hX hV
  apply Eq.trans _ hbridge
  symm
  rw [tsum_eq_sum (squarefreePool K S X)]
  · unfold completeCanonicalColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos ((mem_squarefreePool K S X n).mp hn).1]
    exact completeCanonicalColumn_term K S D θ (k * D.generator f ^ 4)
      r n mark W X hX
  · intro n hn
    by_cases hsf : Squarefree n.val.val
    · rw [if_pos hsf]
      have hlarge : ¬ exteriorNorm K S n ≤ 2 * X := by
        intro hnorm
        exact hn ((mem_squarefreePool K S X n).mpr ⟨hsf, hnorm⟩)
      have hzero : W (exteriorNorm K S n / X) = 0 := by
        by_contra hne
        exact hlarge ((div_le_iff₀ hX).mp (hW hne))
      simp only [canonicalVstar, hzero, mul_zero]
    · rw [if_neg hsf]

/-- The same completion over all ideals, so the genuine short/long
partition and the reopened divisor coefficient apply without any
assumed subtype or source identity. -/
theorem completeCanonicalColumn_cube_completion_allIdeals
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic 2) :
    completeCanonicalColumn K S D θ k f r mark W X =
      ∑' H : Ideal (𝓞 K), extractedCubeTerm (exteriorGamma K S D)
        (canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val)
        mark (canonicalVstar W) X H := by
  rw [completeCanonicalColumn_cube_completion K S D θ k f r mark W X hX hW]
  have hinj : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) := by
    intro I J h
    exact Subtype.ext (Subtype.ext h)
  have hs : Function.support (extractedCubeTerm (exteriorGamma K S D)
      (canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val)
      mark (canonicalVstar W) X) ⊆
      Set.range (fun I : ExteriorIdeal K S => I.val.val) := by
    intro H hH
    have he : HeckePort.CenteredMomentGenerator.IsExterior K S H := by
      by_contra h
      have hz := canonicalTau_eq_zero_of_not_exterior K S D θ
        (k * D.generator f ^ 4) r.val.val H h
      exact hH (by simp [extractedCubeTerm, hz])
    exact ⟨HeckePort.CenteredMomentGenerator.toExterior K S H he, rfl⟩
  rw [← hinj.tsum_eq hs]
  apply tsum_congr
  intro H
  symm
  have hN : 0 < exteriorNorm K S H := idealNorm_pos K H.val
  have hscale : 0 < X / exteriorNorm K S H ^ 3 := div_pos hX (pow_pos hN 3)
  change (moebius H.val.val : ℂ) *
      canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
      (exteriorNorm K S H : ℂ) * _ = _
  congr 1
  simpa only [wholeMarkWeight_empty, one_mul, cubeIdealNorm, exteriorNorm] using
    canonicalCompletedSum_eq_weightedTheta K S D θ (k * D.generator f ^ 4) r ∅
      (fun A => mark (H.val.val ^ 3 * A)) (canonicalVstar W)
      (X / exteriorNorm K S H ^ 3) 2 hscale (canonicalVstar_support_upper W 2 hW)

/-- Exact original-column partition before any positive majorization.
The long term has one reopened coefficient depending only on its cube. -/
theorem completeCanonicalColumn_short_long
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X T : ℝ)
    (hX : 0 < X) (hW : Function.support W ⊆ Set.Iic 2) :
    let gamma := exteriorGamma K S D
    let tau := canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val
    completeCanonicalColumn K S D θ k f r mark W X =
      (∑' H : Ideal (𝓞 K), if cubeIdealNorm H < T then
        extractedCubeTerm gamma tau mark (canonicalVstar W) X H else 0) +
      ∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K),
        reopenedCubeCoefficient (fun H => T ≤ cubeIdealNorm H) CB.2 *
          canonicalCompletedTerm gamma tau mark (canonicalVstar W) X CB := by
  dsimp only
  rw [completeCanonicalColumn_cube_completion_allIdeals K S D θ k f r mark W X hX hW]
  exact canonical_completion_short_long _ _ mark (canonicalVstar W) X 2 T hX
    (canonicalVstar_support_upper W 2 hW)

/-- The literal joint test bounds both coordinates of every nonzero
completed summand. This supplies a complete rectangle, before dyadic
separation; no original-range mask is introduced as a coefficient. -/
theorem canonicalCompletedTerm_mem_pools
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (mark : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic 2)
    (C B : ExteriorIdeal K S)
    (hne : canonicalCompletedTerm gamma tau mark V X (C.val.val, B.val.val) ≠ 0) :
    C ∈ squarefreePool K S X ∧ B ∈ boundedPool K S X := by
  have hsf : Squarefree C.val.val := by
    by_contra h
    exact hne (by simp only [canonicalCompletedTerm, if_neg h])
  have ht : V (cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 / X) ≠ 0 := by
    intro hz
    exact hne (by simp only [canonicalCompletedTerm, if_pos hsf, hz, mul_zero])
  have hprod : cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 ≤ 2 * X :=
    (div_le_iff₀ hX).mp (hV ht)
  have hC : 1 ≤ cubeIdealNorm C.val.val :=
    cubeIdealNorm_one_le (nonZeroDivisors.coe_ne_zero C.val)
  have hB : 1 ≤ cubeIdealNorm B.val.val :=
    cubeIdealNorm_one_le (nonZeroDivisors.coe_ne_zero B.val)
  have hCBound : cubeIdealNorm C.val.val ≤ 2 * X := by
    calc
      _ = cubeIdealNorm C.val.val * 1 := (mul_one _).symm
      _ ≤ cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hB) (zero_le_one.trans hC)
      _ ≤ _ := hprod
  have hBBound : cubeIdealNorm B.val.val ≤ 2 * X := by
    calc
      _ = cubeIdealNorm B.val.val * 1 := (mul_one _).symm
      _ ≤ cubeIdealNorm B.val.val * cubeIdealNorm B.val.val ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hB) (zero_le_one.trans hB)
      _ = cubeIdealNorm B.val.val ^ 3 := by ring
      _ = 1 * cubeIdealNorm B.val.val ^ 3 := (one_mul _).symm
      _ ≤ cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 :=
        mul_le_mul_of_nonneg_right hC (pow_nonneg (zero_le_one.trans hB) _)
      _ ≤ _ := hprod
  constructor
  · exact (mem_squarefreePool K S X C).mpr ⟨hsf, hCBound⟩
  · simpa only [boundedPool, Finset.mem_preimage,
      DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals, cubeIdealNorm] using hBBound

/-- A nonzero literal joint test bounds the whole cube, before any
annular decomposition or Mellin separation is introduced. -/
theorem canonicalCompletedTerm_cube_bound
    (gamma : Ideal (𝓞 K) → ℂ) (tau : Ideal (𝓞 K) →* ℂ)
    (mark : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (hV : Function.support V ⊆ Set.Iic 2)
    (C B : ExteriorIdeal K S)
    (hne : canonicalCompletedTerm gamma tau mark V X (C.val.val, B.val.val) ≠ 0) :
    cubeIdealNorm B.val.val ^ 3 ≤ 2 * X := by
  have hsf : Squarefree C.val.val := by
    by_contra h
    exact hne (by simp only [canonicalCompletedTerm, if_neg h])
  have ht : V (cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 / X) ≠ 0 := by
    intro hz
    exact hne (by simp only [canonicalCompletedTerm, if_pos hsf, hz, mul_zero])
  have hprod : cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 ≤ 2 * X :=
    (div_le_iff₀ hX).mp (hV ht)
  have hC : 1 ≤ cubeIdealNorm C.val.val :=
    cubeIdealNorm_one_le (nonZeroDivisors.coe_ne_zero C.val)
  calc
    _ = 1 * cubeIdealNorm B.val.val ^ 3 := (one_mul _).symm
    _ ≤ cubeIdealNorm C.val.val * cubeIdealNorm B.val.val ^ 3 :=
      mul_le_mul_of_nonneg_right hC (pow_nonneg
        (by dsimp only [cubeIdealNorm]; positivity) _)
    _ ≤ _ := hprod

/-- The reopened all-ideal series is exactly a finite exterior cube
times complete squarefree-column rectangle. Every original zero of
`tau` and the full joint test are still inside the summand. -/
theorem reopenedCanonical_eq_finite
    (θ : HeckeCharacter K) (m : S.integer K) (r : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → ℂ) (mark : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic 2) :
    (∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K), beta CB.2 *
      canonicalCompletedTerm (exteriorGamma K S D) (canonicalTau K S D θ m r)
        mark V X CB) =
      ∑ B ∈ boundedPool K S X, ∑ C ∈ squarefreePool K S X,
        beta B.val.val * canonicalCompletedTerm (exteriorGamma K S D)
          (canonicalTau K S D θ m r) mark V X (C.val.val, B.val.val) := by
  let e : (ExteriorIdeal K S × ExteriorIdeal K S) →
      Ideal (𝓞 K) × Ideal (𝓞 K) := fun BC => (BC.2.val.val, BC.1.val.val)
  have hinj : Function.Injective e := by
    intro BC DE h
    exact Prod.ext
      (Subtype.ext (Subtype.ext (congrArg Prod.snd h)))
      (Subtype.ext (Subtype.ext (congrArg Prod.fst h)))
  have hs : Function.support (fun CB : Ideal (𝓞 K) × Ideal (𝓞 K) => beta CB.2 *
      canonicalCompletedTerm (exteriorGamma K S D) (canonicalTau K S D θ m r)
        mark V X CB) ⊆ Set.range e := by
    rintro ⟨C, B⟩ hCB
    have hC : HeckePort.CenteredMomentGenerator.IsExterior K S C := by
      by_contra h
      have hz := canonicalTau_eq_zero_of_not_exterior K S D θ m r C h
      exact hCB (by simp [canonicalCompletedTerm, map_mul, hz])
    have hB : HeckePort.CenteredMomentGenerator.IsExterior K S B := by
      by_contra h
      have hz := canonicalTau_eq_zero_of_not_exterior K S D θ m r B h
      exact hCB (by simp [canonicalCompletedTerm, map_mul, map_pow, hz])
    exact ⟨(HeckePort.CenteredMomentGenerator.toExterior K S B hB,
      HeckePort.CenteredMomentGenerator.toExterior K S C hC), rfl⟩
  rw [← hinj.tsum_eq hs,
    tsum_eq_sum (boundedPool K S X ×ˢ squarefreePool K S X), Finset.sum_product]
  · rfl
  · intro BC hnot
    by_contra hne
    have ht : canonicalCompletedTerm (exteriorGamma K S D)
        (canonicalTau K S D θ m r) mark V X (BC.2.val.val, BC.1.val.val) ≠ 0 := by
      intro hz
      exact hne (by change beta BC.1.val.val * _ = 0; rw [hz, mul_zero])
    have hp := canonicalCompletedTerm_mem_pools K S _ _ mark V X hX hV BC.2 BC.1 ht
    exact hnot (Finset.mem_product.mpr ⟨hp.2, hp.1⟩)

/-- The column rectangle may be enlarged before splitting the joint
profile. Its additional entries vanish in the literal completed source;
after separation they remain available to complete every child pool. -/
theorem reopenedCanonical_eq_finite_of_le
    (θ : HeckeCharacter K) (m : S.integer K) (r : Ideal (𝓞 K))
    (beta : Ideal (𝓞 K) → ℂ) (mark : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X R : ℝ) (hX : 0 < X) (hXR : X ≤ R)
    (hV : Function.support V ⊆ Set.Iic 2) :
    (∑' CB : Ideal (𝓞 K) × Ideal (𝓞 K), beta CB.2 *
      canonicalCompletedTerm (exteriorGamma K S D) (canonicalTau K S D θ m r)
        mark V X CB) =
      ∑ B ∈ boundedPool K S X, ∑ C ∈ squarefreePool K S R,
        beta B.val.val * canonicalCompletedTerm (exteriorGamma K S D)
          (canonicalTau K S D θ m r) mark V X (C.val.val, B.val.val) := by
  rw [reopenedCanonical_eq_finite K S D θ m r beta mark V X hX hV]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_subset
  · intro C hC
    obtain ⟨hsf, hnorm⟩ := (mem_squarefreePool K S X C).mp hC
    exact (mem_squarefreePool K S R C).mpr ⟨hsf,
      hnorm.trans (mul_le_mul_of_nonneg_left hXR (by norm_num))⟩
  · intro C hCR hCX
    have hz : canonicalCompletedTerm (exteriorGamma K S D)
        (canonicalTau K S D θ m r) mark V X (C.val.val, B.val.val) = 0 := by
      by_contra hne
      exact hCX (canonicalCompletedTerm_mem_pools K S _ _ mark V X hX hV C B hne).1
    rw [hz, mul_zero]

/-- The actual row-dependent frozen cube phase is bounded only after
retaining its full coefficient; no independence of that phase is asserted. -/
theorem completeCanonicalColumn_cube_coefficient_norm_le
    (θ : HeckeCharacter K) (k : S.integer K) (f r H : ExteriorIdeal K S) :
    ‖(moebius H.val.val : ℂ) *
        canonicalTau K S D θ (k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
        (exteriorNorm K S H : ℂ)‖ ≤ 1 / exteriorNorm K S H := by
  have hN : 0 ≤ exteriorNorm K S H := (idealNorm_pos K H.val).le
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN]
  apply div_le_div_of_nonneg_right _ hN
  exact (mul_le_mul
    (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one H.val.val)
    (norm_frozen_phase_le_one K S D θ k f H r.val.val)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)

/-- The same finite column written with its row, label and puncture
factors separate. This is the literal canonical coefficient shape used
by both the induction and the one-step provider. -/
theorem completeCanonicalColumn_eq_symbols
    (θ : HeckeCharacter K) (k : S.integer K) (f r : ExteriorIdeal K S)
    (mark : Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    completeCanonicalColumn K S D θ k f r mark W X =
      (Real.sqrt X : ℂ)⁻¹ * ∑ n ∈ squarefreePool K S X,
        thetaGamma K S D n 2 * heckeIdealCoefficient K θ n.val *
          idealSymbol K S D n k * idealSymbol K S D n (D.generator f) ^ 4 *
          (if IsCoprime n.val.val r.val.val then 1 else 0) *
          mark n.val.val * W (exteriorNorm K S n / X) := by
  unfold completeCanonicalColumn
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [canonicalTau_label]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
