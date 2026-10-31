import Expansion.ActualDeletedZetaResidue
import HeckeSkeleton.HeckeDeletedEulerControl

/-!
# Actual zeta growth away from the height of its pole

The entire principal numerator and the actual finite Euler deletion give
a polynomial bound on the complete middle strip.  A large imaginary
height bounds the pole denominator from below, uniformly in the real
part.  A separate elementary lemma absorbs such polynomial growth into
an already proved rapid Mellin estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeDeletedEulerControl
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem exists_actual_deletedZeta_midStrip_height_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ,
      1 / 2 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
        ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) s‖ ≤
          C * (1 + |s.im|) ^ k := by
  obtain ⟨C, k, hC, hk, hbound⟩ := exists_normPoleNumerator_strip_bound K hcomplex 0
  let D : ℝ := deletionUpperConstant K (exceptionalPrimes K S)
  have hD : 0 < D := deletionUpperConstant_pos K (exceptionalPrimes K S)
  refine ⟨D * C * (2 : ℝ) ^ k, k, by positivity, hk, ?_⟩
  intro s hs hs4 hh
  have hden : 1 ≤ ‖s - 1‖ := hh.trans (by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1))
  have hformula : heckeContinuation K (1 : HeckeCharacter K) s =
      normPoleNumerator K 0 s / (s - 1) := by
    simpa [heckeNormTwist, heckeNormPole] using congrFun (heckeContinuation_normTwist_eq K 0) s
  have hfull : ‖heckeContinuation K (1 : HeckeCharacter K) s‖ ≤ C * (2 + |s.im|) ^ k := by
    rw [hformula, norm_div]
    exact (div_le_self (norm_nonneg _) hden).trans (hbound s hs hs4)
  have hheight : (2 + |s.im|) ^ k ≤ (2 : ℝ) ^ k * (1 + |s.im|) ^ k := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hk
    nlinarith [abs_nonneg s.im]
  rw [heckeDeletedContinuation, norm_mul]
  calc
    _ ≤ D * (C * (2 + |s.im|) ^ k) :=
      mul_le_mul (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K S) 1 s (by linarith))
        hfull (norm_nonneg _) hD.le
    _ ≤ D * (C * ((2 : ℝ) ^ k * (1 + |s.im|) ^ k)) := by
      gcongr
    _ = _ := by ring

/-- A proved rapid factor absorbs any fixed polynomial factor.  The
requested remaining decay exponent is independent of the selected degree. -/
theorem rapid_mul_polynomial_bound
    {b D C k loss : ℝ} {n : ℕ} (hb : 1 ≤ b) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hn : k + loss ≤ (n : ℝ)) {f g : ℂ}
    (hf : b ^ n * ‖f‖ ≤ D) (hg : ‖g‖ ≤ C * b ^ k) :
    ‖f‖ * ‖g‖ ≤ D * C * b ^ (-loss) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hfd : ‖f‖ ≤ D / b ^ n := (le_div_iff₀ (pow_pos hbpos n)).mpr (by
    simpa only [mul_comm] using hf)
  calc
    _ ≤ ‖f‖ * (C * b ^ k) := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = C * (‖f‖ * b ^ k) := by ring
    _ ≤ C * ((D / b ^ n) * b ^ k) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfd (Real.rpow_nonneg hbpos.le _)) hC
    _ = D * C * b ^ (k - (n : ℝ)) := by
      rw [Real.rpow_sub hbpos, Real.rpow_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) (mul_nonneg hD hC)

end Expansion.Project

#print axioms Expansion.Project.exists_actual_deletedZeta_midStrip_height_bound
#print axioms Expansion.Project.rapid_mul_polynomial_bound
