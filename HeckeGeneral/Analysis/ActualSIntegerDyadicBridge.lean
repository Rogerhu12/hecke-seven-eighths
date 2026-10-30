import HeckeGeneral.Analysis.SIntegerSexticMellinAmplification
import HeckeGeneral.Analysis.IdealDyadicContinuation
import HeckeGeneral.Analysis.LocalThetaInput

/-!
The actual row at one is the actual deleted Moebius dyadic shell, with
its square-root and complex-power normalizations proved explicitly.
Compact-uniform single-row energy implies the compact shell growth needed
by analytic continuation. This is not a proof of that energy from MI.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.IdealMobiusReciprocal HeckeGeneral.Analysis.IdealDyadicMobius
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (τ : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

include τ in
theorem sexticIdealOutsideS_iff_avoids (I : NonzeroIdeal K) :
    sexticIdealOutsideS K (S : Set (HeightOneSpectrum (𝓞 K))) I ↔ avoids K S I := by
  constructor
  · intro h p hp hdvd
    exact (h p hdvd).1 hp
  · intro h p hdvd
    have hp : p ∉ S := fun hp => h p hp hdvd
    exact ⟨hp, τ.away_six p hp⟩

theorem zeroExtendedSexticIdealEvaluation_at_one (I : NonzeroIdeal K) :
    zeroExtendedSexticIdealEvaluation K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding I 1 = if avoids K S I then 1 else 0 := by
  unfold zeroExtendedSexticIdealEvaluation
  by_cases h : sexticIdealOutsideS K (S : Set (HeightOneSpectrum (𝓞 K))) I
  · rw [dite_eq_left h, ite_eq_left ((sexticIdealOutsideS_iff_avoids K S τ I).mp h)]
    exact sIntegerSexticIdealEvaluation_one ..
  · rw [dite_eq_right h,
      ite_eq_right (fun ha => h ((sexticIdealOutsideS_iff_avoids K S τ I).mpr ha))]

theorem scaled_mellin_term_eq_dyadicTerm (χ : HeckeCharacter K)
    (I : NonzeroIdeal K) (j : ℕ) (s : ℂ) :
    (Complex.ofReal ((2 : ℝ) ^ j) ^ (-s)) *
      sIntegerSexticInverseIdealTerm K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ 1 ((2 : ℝ) ^ j) (dyadicMellinWeight s) I =
      dyadicTerm K χ S I j s := by
  have hD : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
  have hscale : (Complex.ofReal ((2 : ℝ) ^ j) ^ (-s)) *
      ((idealNorm K I / (2 : ℝ) ^ j : ℝ) : ℂ) ^ (-s) =
        (idealNorm K I : ℂ) ^ (-s) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hD.le
      (div_nonneg (idealNorm_pos K I).le hD.le), ← Complex.ofReal_mul]
    congr 2
    field_simp [hD.ne']
  rw [sIntegerSexticInverseIdealTerm, zeroExtendedSexticIdealEvaluation_at_one,
    dyadicTerm, excludedTerm]
  split_ifs with h
  · simp only [one_zpow, mul_one, dyadicMellinWeight, sexticDyadicWeight,
      term, coefficient, dirichletTerm]
    calc
      _ = ((fixedDyadicWeight (idealNorm K I / (2 : ℝ) ^ j) : ℂ) *
          ((UniqueFactorizationMonoid.moebius I.val : ℂ) * heckeIdealCoefficient K χ I)) *
          ((Complex.ofReal ((2 : ℝ) ^ j) ^ (-s)) *
            ((idealNorm K I / (2 : ℝ) ^ j : ℝ) : ℂ) ^ (-s)) := by ring
      _ = _ := by
        rw [hscale]
        simp only [heckeIdealCoefficient]
        ring
  · simp

/-- Exact normalization bridge, valid for every complex parameter. -/
theorem shell_eq_scaled_actual_single_row (χ : HeckeCharacter K) (j : ℕ) (s : ℂ) :
    shell K χ S j s = (Complex.ofReal ((2 : ℝ) ^ j) ^ (-s)) *
      ((Real.sqrt ((2 : ℝ) ^ j) : ℂ) *
        dyadicSexticMellinInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
          τ.root6 τ.primitive6 τ.embedding χ 1 ((2 : ℝ) ^ j) s) := by
  have hD : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
  have hroot : (Real.sqrt ((2 : ℝ) ^ j) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  unfold dyadicSexticMellinInversePolynomial sIntegerSexticInverseIdealPolynomial
  rw [← mul_assoc (Real.sqrt ((2 : ℝ) ^ j) : ℂ), mul_inv_cancel₀ hroot, one_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun I _ => (scaled_mellin_term_eq_dyadicTerm K S τ χ I j s).symm)

/-- All scale and compact-parameter constants are simultaneous. No separate
pointwise BigO constants, holomorphy or zero-free conclusion are assumed. -/
def CompactSingleRowEnergy (χ : HeckeCharacter K) : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε → ∀ T : Set ℂ, IsCompact T →
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D → ∀ s ∈ T,
      ‖dyadicSexticMellinInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
        τ.root6 τ.primitive6 τ.embedding χ 1 D s‖ ^ 2 ≤
          C * D ^ (5 * (1 + c) / 6 + ε)

theorem CompactSingleRowEnergy.to_compactShellGrowth (χ : HeckeCharacter K)
    (h : CompactSingleRowEnergy K S τ χ) : CompactShellGrowth K χ S (11 / 12) := by
  intro ε hε T hT _hplane
  have hβ : 11 / 12 < (11 / 12 : ℝ) + ε := by linarith
  obtain ⟨c, e, hc, he, hmargin⟩ := seed_amplification_exponent_margin hβ
  obtain ⟨C, hC, hbound⟩ := h c e hc he T hT
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  intro j s hs
  have hD : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hDpos : 0 < (2 : ℝ) ^ j := lt_of_lt_of_le zero_lt_one hD
  have hb := norm_sqrt_mul_le_rpow_of_energy_bound
    (dyadicSexticMellinInversePolynomial K (S : Set (HeightOneSpectrum (𝓞 K)))
      τ.root6 τ.primitive6 τ.embedding χ 1 ((2 : ℝ) ^ j) s)
    hD hC.le (hbound _ hD s hs) hmargin.le
  rw [shell_eq_scaled_actual_single_row K S τ χ j s, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hDpos, Complex.neg_re]
  calc
    _ ≤ ((2 : ℝ) ^ j) ^ (-s.re) * (Real.sqrt C * ((2 : ℝ) ^ j) ^ (11 / 12 + ε)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDpos.le _)
    _ = _ := by
      rw [show (11 / 12 : ℝ) + ε - s.re = -s.re + (11 / 12 + ε) by ring,
        Real.rpow_add hDpos (-s.re) ((11 / 12 : ℝ) + ε)]
      ring

end HeckeGeneral.Analysis.ActualSIntegerMoments
