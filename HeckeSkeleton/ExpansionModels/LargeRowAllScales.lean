import HeckeSkeleton.ExpansionModels.LargeRowCorrection

/-!
# All-scale control of the literal large-row correction

The quantitative asymptotic correction uses a common prime-window cutoff.
Absolute summability, however, is required at every Z >= 1.  This file
handles the remaining bounded scales using the original finite tuple and
subset sum itself.  Its scalar mass may depend on Z, but precedes every
original row and every height.  No local correction is divided out.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.LargeRows

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.CoarseEuler
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- An explicit finite scalar majorant, independent of the physical row,
probe, target, and imaginary coordinates.  All actual windows remain. -/
def largeCorrectionMass (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z sigma : ℝ) : ℝ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    (∏ i : Fin g.slots, ‖windowWeight K S g Z i (p i)‖) *
    ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
      exteriorNorm K S (subsetPrimeIdeal K S p J) ^ (sigma - 3) *
        exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ (sigma + 1) *
        markedBound ^ ((Finset.univ \ J).image p).card

theorem largeCorrectionMass_nonneg (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z sigma : ℝ) :
    0 ≤ largeCorrectionMass K S g T Z sigma := by
  unfold largeCorrectionMass
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  apply Finset.sum_nonneg
  intro J _
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (idealNorm_pos K _).le _)
      (Real.rpow_nonneg (idealNorm_pos K _).le _))
    (pow_nonneg (zero_le_one.trans one_le_markedBound) _)

/-- Uniform row-subpower control at each original scale, without any
asymptotic cutoff.  This proves actual convergence at bounded scales. -/
theorem exists_actual_large_fullCorrection_all_scales_bound
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
      (Z sigma : ℝ), 1 ≤ sigma → ∀ (P : ProbeData K S) (psi : HeckeCharacter K)
      (u : FrequencyRow K S) (s w z : ℂ), s.re = 2 → w.re = 2 → z.re = sigma →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤
            (C * largeCorrectionMass K S g T Z sigma) * frequencyRowNorm K S u ^ eta := by
  obtain ⟨C, hC, hrow⟩ := exists_uniform_rowCorrection_subpower K S
    (e := 1 / 20000) (by norm_num) (by norm_num) heta
  refine ⟨C, hC, ?_⟩
  intro g T Z sigma hsigma P psi u s w z hs hw hz
  have hv := outer_contour_mem_sweptTube s w z (by linarith) (by linarith) (by linarith)
  have hinner (p : Fin g.slots → ExteriorPrime K S) :
      ‖∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        (-1 : ℂ) ^ J.card * (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1) *
          conj (heckeIdealCoefficient K psi (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
          (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^ (s + z - 1) *
          rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
            ((Finset.univ \ J).image p) u s w z‖ ≤
        (∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          exteriorNorm K S (subsetPrimeIdeal K S p J) ^ (sigma - 3) *
            exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ (sigma + 1) *
            markedBound ^ ((Finset.univ \ J).image p).card) *
          (C * frequencyRowNorm K S u ^ eta) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro J _
    have hselpos : 0 < exteriorNorm K S (subsetPrimeIdeal K S p J) :=
      idealNorm_pos K _
    have hmarkpos : 0 < exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) :=
      idealNorm_pos K _
    have hsel : ‖(exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1)‖ =
        exteriorNorm K S (subsetPrimeIdeal K S p J) ^ (sigma - 3) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hselpos]
      congr 1
      simp only [Complex.sub_re, Complex.one_re, hz, hw]
      ring
    have hmark : ‖(exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^
        (s + z - 1)‖ =
        exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ (sigma + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hmarkpos]
      congr 1
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hs, hz]
      ring
    have hc := norm_heckeIdealCoefficient_le_one K psi
      (subsetPrimeIdeal K S p (Finset.univ \ J)).val
    have he := hrow P psi ((Finset.univ \ J).image p) u (3 / 4)
      (by norm_num) (by norm_num) (s, w, z) hv
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_conj, hsel, hmark]
    calc
      _ ≤ (exteriorNorm K S (subsetPrimeIdeal K S p J) ^ (sigma - 3) * 1) *
          exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ (sigma + 1) *
          (C * frequencyRowNorm K S u ^ eta * markedBound ^ ((Finset.univ \ J).image p).card) := by
        have hsel0 := Real.rpow_nonneg hselpos.le (sigma - 3)
        have hmark0 := Real.rpow_nonneg hmarkpos.le (sigma + 1)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hsel0) hmark0)
          he (norm_nonneg _)
          (mul_nonneg (mul_nonneg hsel0 zero_le_one) hmark0)
      _ = _ := by ring
  unfold compensatedRowFullCorrection
  dsimp only
  calc
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ‖(∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
          ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            (-1 : ℂ) ^ J.card * (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1) *
              conj (heckeIdealCoefficient K psi (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
              (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^ (s + z - 1) *
              rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
                ((Finset.univ \ J).image p) u s w z‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, ‖windowWeight K S g Z i (p i)‖) *
          ((∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            exteriorNorm K S (subsetPrimeIdeal K S p J) ^ (sigma - 3) *
              exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ (sigma + 1) *
              markedBound ^ ((Finset.univ \ J).image p).card) *
            (C * frequencyRowNorm K S u ^ eta)) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_left (hinner p) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (C * largeCorrectionMass K S g T Z sigma) * frequencyRowNorm K S u ^ eta := by
      unfold largeCorrectionMass
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro J _
      ring

end HeckeSkeleton.Expansion.LargeRows

#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_fullCorrection_all_scales_bound
