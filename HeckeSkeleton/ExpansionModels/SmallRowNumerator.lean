import RowCharacterNormTwistExclusion
import ArithmeticFrequencyRowConductorNorm
import HeckeSkeleton.HeckeUniformStripGrowth
import HeckeSkeleton.HeckeDeletedEulerControl
import HeckeGeneral.Analysis.FrequencyRowCounting
import Expansion.PhysicalRowSupport

/-!
# The actual nonprincipal numerator on the small-row contour

The character is the original calibrated row character.  Actual Kummer
faithfulness excludes every norm twist for every nonprincipal row, including
the bounded exceptional rows.  The conductor comparison is proved from the
same arithmetic constructor, and the fixed infinity type is derived from its
finite order.  Thus the uniform strip theorem with delta = 1/10 gives the
paper's row exponent 3/5 without a pointwise analytic estimate as an input.

Including the literal row factor N(u)^(-17/50) and the actual complete-row
count gives exponent 63/50.  At the cutoff Z^(1/16) its cost is 63/800; the
small-range scale exponent then has the exact margin 1/50.  Every unit sector
is retained.  This module does not assert the missing full-correction bound
or the three-fold contour identity.

Paper: `weil_seven_eighths_revised.tex`, small-row calculation in the
subsection "The two outer ranges", lines 4246--4277.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeUniformStripGrowth HeckeSkeleton.HeckeDeletedEulerControl
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The constant precedes the probe and the supplied calibrated provider. -/
theorem exists_row_conductorScale_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S),
        heckeConductorScale K (R.character u) ≤ A * frequencyRowNorm K S u := by
  let A : ℝ := ((NumberField.discr K).natAbs : ℝ) *
    (sexticSConductorNormConstant K S : ℝ)
  have hdisc : 0 < ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hA : 0 < A := mul_pos hdisc
    (Nat.cast_pos.mpr (sexticSConductorNormConstant_pos K S))
  refine ⟨A, hA, ?_⟩
  intro P R u
  have hN : ((finiteConductor K (arithmeticRowCharacter K S P u)).val.absNorm : ℝ) ≤
      (sexticSConductorNormConstant K S : ℝ) * (u.ideal.val.val.absNorm : ℝ) := by
    exact_mod_cast arithmeticRowCharacter_finiteConductor_absNorm_le_originalIdeal K S P u
  rw [rowCharacterInput_character_eq_arithmetic K S P R u]
  unfold heckeConductorScale frequencyRowNorm exteriorNorm
  exact (mul_le_mul_of_nonneg_left hN hdisc.le).trans_eq (by dsimp [A]; ring)

/-- One constant bounds the actual deleted numerator for all nonprincipal
rows, with no lower row-size cutoff and no norm-exclusion premise. -/
theorem exists_nonprincipal_row_numerator_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P),
      AllowedGeneratorInput K S P.arithmetic → ∀ u : FrequencyRow K S,
      ¬principalFrequencyRow K S u → ∀ w : ℂ, w.re = 1 / 2 →
        ‖heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖ ≤
          C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨D, hD, hstrip⟩ := exists_uniform_fixedType_strip_bound K hcomplex
    (fun _ => 0) (fun _ => 0) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨A, hA, hconductor⟩ := exists_row_conductorScale_bound K S
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K S)
  refine ⟨F * (D * A ^ (3 / 5 : ℝ)), by positivity, ?_⟩
  intro P R hAllowed u hu w hw
  have hτ : (fun v => heckeRadialParameter K v (R.character u)) = fun _ => 0 := by
    funext v
    exact heckeRadialParameter_finiteOrder K v (R.finite_order u)
  have hm : heckeArchWeight K (R.character u) = fun _ => 0 := by
    funext v
    rw [heckeArchWeight_of_complex K (R.character u) v (hcomplex v)]
    exact heckeComplexWeight_finiteOrder K v (hcomplex v) (R.finite_order u)
  have hL := hstrip (R.character u)
    (rowCharacterInput_ne_normTwist_of_not_principal K S P R hAllowed u hu)
    hτ hm w (by rw [hw]; constructor <;> norm_num)
  norm_num only at hL
  have hN : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hQ : 0 ≤ heckeConductorScale K (R.character u) := by
    unfold heckeConductorScale
    positivity
  have hscale : heckeConductorScale K (R.character u) ^ (3 / 5 : ℝ) ≤
      A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ) := by
    calc
      _ ≤ (A * frequencyRowNorm K S u) ^ (3 / 5 : ℝ) :=
        Real.rpow_le_rpow hQ (hconductor P R u) (by norm_num)
      _ = _ := Real.mul_rpow hA.le hN.le
  have hfull : ‖heckeContinuation K (R.character u) w‖ ≤
      (D * A ^ (3 / 5 : ℝ)) * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    apply hL.trans
    calc
      _ ≤ D * (A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ)) *
          (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hscale hD.le
      _ = _ := by ring
  have hEuler : ‖heckeEulerDeletionPolynomial K (R.character u)
      (exceptionalPrimes K S) w‖ ≤ F :=
    norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K S) (R.character u)
      w (by rw [hw]; norm_num)
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul hEuler hfull (norm_nonneg _) hF.le).trans_eq (by ring)

/-- The original physical row weight saves 17/50 before counting.  The
finite set may be any subset of the actual enumeration, but its supplied
data is never substituted for that enumeration or its arithmetic provider. -/
theorem exists_nonprincipal_weighted_numerator_sum_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P),
      AllowedGeneratorInput K S P.arithmetic → ∀ U : ℝ, 1 ≤ U →
      ∀ F : Finset (FrequencyRow K S), F ⊆ frequencyRows K S U →
      (∀ u ∈ F, ¬principalFrequencyRow K S u) →
      ∀ w z : ℂ, w.re = 1 / 2 → z.re = 17 / 50 →
        (∑ u ∈ F, ‖(frequencyRowNorm K S u : ℂ) ^ (-z) *
          heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖) ≤
            C * U ^ (63 / 50 : ℝ) *
              (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨D, hD, hnum⟩ := exists_nonprincipal_row_numerator_bound K S hcomplex
  obtain ⟨A, hA, hcount⟩ := frequencyRows_linear_count K S
  refine ⟨A * D, mul_pos hA hD, ?_⟩
  intro P R hAllowed U hU F hF hnon w z hw hz
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hcard : (F.card : ℝ) ≤ A * U :=
    (Nat.cast_le.mpr (Finset.card_le_card hF)).trans (hcount U hU)
  have hrow (u : FrequencyRow K S) (hu : u ∈ F) :
      ‖(frequencyRowNorm K S u : ℂ) ^ (-z) *
        heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖ ≤
        D * U ^ (13 / 50 : ℝ) *
          (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    have hN : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
    have hNU : frequencyRowNorm K S u ≤ U :=
      (_root_.Expansion.Project.mem_frequencyRows_iff K S U hU0.le u).mp (hF hu)
    have hpow : frequencyRowNorm K S u ^ (-(17 / 50 : ℝ)) *
        frequencyRowNorm K S u ^ (3 / 5 : ℝ) =
          frequencyRowNorm K S u ^ (13 / 50 : ℝ) := by
      rw [← Real.rpow_add hN]
      norm_num
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re, hz]
    calc
      _ ≤ frequencyRowNorm K S u ^ (-(17 / 50 : ℝ)) *
          (D * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K))) :=
        mul_le_mul_of_nonneg_left (hnum P R hAllowed u (hnon u hu) w hw)
          (Real.rpow_nonneg hN.le _)
      _ = D * frequencyRowNorm K S u ^ (13 / 50 : ℝ) *
          (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
        calc
          _ = D * (frequencyRowNorm K S u ^ (-(17 / 50 : ℝ)) *
              frequencyRowNorm K S u ^ (3 / 5 : ℝ)) *
              (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hN.le hNU (by norm_num : (0 : ℝ) ≤ 13 / 50)) hD.le)
        (by positivity)
  have hcombine : U * U ^ (13 / 50 : ℝ) = U ^ (63 / 50 : ℝ) := by
    calc
      _ = U ^ (1 : ℝ) * U ^ (13 / 50 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hU0]; norm_num
  calc
    _ ≤ ∑ _u ∈ F, D * U ^ (13 / 50 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
      Finset.sum_le_sum hrow
    _ = (F.card : ℝ) * D * U ^ (13 / 50 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (A * U) * D * U ^ (13 / 50 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right hcard hD.le
    _ = (A * D) * U ^ (63 / 50 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      calc
        _ = (A * D) * (U * U ^ (13 / 50 : ℝ)) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by ring
        _ = _ := by rw [hcombine]

/-- The complete literal small-row set, including all bounded exceptions,
costs 63/800 in the Z exponent. -/
theorem exists_small_row_weighted_numerator_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P),
      AllowedGeneratorInput K S P.arithmetic → ∀ Z : ℝ, 1 ≤ Z →
      ∀ w z : ℂ, w.re = 1 / 2 → z.re = 17 / 50 →
        (∑ u ∈ (frequencyRows K S (Z ^ (1 / 16 : ℝ))).filter
          (fun u => 0 < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u),
          ‖(frequencyRowNorm K S u : ℂ) ^ (-z) *
            heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖) ≤
          C * Z ^ (63 / 800 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨C, hC, hbound⟩ := exists_nonprincipal_weighted_numerator_sum_bound K S hcomplex
  refine ⟨C, hC, ?_⟩
  intro P R hAllowed Z hZ w z hw hz
  have h := hbound P R hAllowed (Z ^ (1 / 16 : ℝ))
    (Real.one_le_rpow hZ (by norm_num))
    ((frequencyRows K S (Z ^ (1 / 16 : ℝ))).filter
      (fun u => 0 < frequencyRowNorm K S u ∧ ¬principalFrequencyRow K S u))
    (Finset.filter_subset _ _)
    (fun u hu => (Finset.mem_filter.mp hu).2.2) w z hw hz
  have hp : (Z ^ (1 / 16 : ℝ)) ^ (63 / 50 : ℝ) = Z ^ (63 / 800 : ℝ) := by
    rw [← Real.rpow_mul (zero_le_one.trans hZ)]
    norm_num
  simpa only [hp] using h

theorem small_row_scale_exponent (B e : ℝ) :
    (B - 11 / 16 - 79 / 800 + e) + 63 / 800 =
      B - 11 / 16 - 1 / 50 + e := by ring

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_row_conductorScale_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_nonprincipal_row_numerator_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_nonprincipal_weighted_numerator_sum_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_small_row_weighted_numerator_bound
