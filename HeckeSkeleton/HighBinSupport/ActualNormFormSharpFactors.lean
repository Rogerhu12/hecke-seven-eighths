import HeckeSkeleton.HighBinSupport.ActualLRatioStrip
import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeCap
import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeDeficit
import HeckeSkeleton.HighBinSupport.ActualEulerData

/-!
The sharp reflected L-factor for the constructed arithmetic frequency row.

The canonical Kummer conductor bound is applied before the row radical
is compared with the full ideal norm. Its positive radical exponent is
therefore still available to pay for the repeated-prime slots. The
original primitive twelfth root supplies the complex-place hypothesis.
There is no L-ratio bound or conductor estimate among the premises.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormSharpFactors

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.HeckeLRatioConductorBudget
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem one_le_actual_radicalNorm (u : FrequencyRow K S) :
    1 ≤ (u.ideal.val.val.radical.absNorm : ℝ) := by
  rw [NormFormActual.actual_radicalNorm_eq_primeSupport_product K u.ideal.val]
  apply Finset.one_le_prod₀
  intro p hp
  have h := one_lt_primeIdeal_absNorm K p
  exact_mod_cast h.le

/-- The actual deleted numerator and denominator retain the precise
radical power lambda + 2 epsilon. The constant is uniform over the
complete strip used by the fixed-bin contour move. -/
theorem exists_actual_deletedLRatio_radical_bound
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions) (P : ProbeData K S)
    {e eps : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H U : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ s w : ℂ, a + 16 * e ≤ s.re → s.re ≤ 2 →
        w.re = 1 - a - 6 * e → |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeDeletedContinuation K (arithmeticRowCharacter K S P u) (exceptionalPrimes K S) w‖ *
          ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K S P u))
            (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e + 2 * eps) *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
              2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by
  let E := arithmeticHighEulerData K S P psi
  obtain ⟨C, Z0, hC, hZ0, hratio⟩ :=
    HighBinBoundary.ActualLRatioStrip.exists_uniform_high_row_deletedLRatio_strip_bound
      K S (HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
        K P.arithmetic.primitive12) psi companions hcomp P E he (by linarith) he1 heps
  obtain ⟨A, hA, hconductor⟩ :=
    NormFormPrimeCap.exists_physicalFamily_radical_conductor_bound K S psi companions
  let D : ℝ := backgroundConductorBudget K psi A eps
  have hD : 0 < D := backgroundConductorBudget_pos K psi A eps hA
  refine ⟨C * D, Z0, mul_pos hC hD, hZ0, ?_⟩
  intro Z hZ d hd u hu a H U ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  have hmem : E.rows.character u ∈ physicalRowFamily K S psi companions P E u := by
    apply Finset.mem_biUnion.mpr
    refine ⟨1, hcomp, ?_⟩
    simp
  have hlam : 0 ≤ a - 1 / 2 + 6 * e := by linarith
  have hlam1 : a - 1 / 2 + 6 * e ≤ 1 := by linarith
  have hbudget := conductorPowers_le_radicalPower K psi (E.rows.character u) A
    (u.ideal.val.val.radical.absNorm : ℝ) (a - 1 / 2 + 6 * e) eps
    hA (one_le_actual_radicalNorm K S u) hlam hlam1 heps (hconductor P E u _ hmem)
  have hbase := hratio Z hZ d hd u hu a H U ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  change ‖heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S) w‖ *
    ‖(heckeDeletedContinuation K (psi * conjugate (E.rows.character u))
      (exceptionalPrimes K S) s)⁻¹‖ ≤ _
  apply hbase.trans
  calc
    _ = C * (heckeConductorScale K (E.rows.character u) ^ (a - 1 / 2 + 6 * e) *
        heckeConductorScale K ((E.rows.character u)⁻¹) ^ eps *
        heckeConductorScale K (psi * conjugate (E.rows.character u)) ^ eps) *
        (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
          2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by ring
    _ ≤ C * (D * (u.ideal.val.val.radical.absNorm : ℝ) ^
        (a - 1 / 2 + 6 * e + 2 * eps)) *
        (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
          2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hC.le)
        (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

/-- The three literal deleted L-factors of the full Mellin kernel,
including the fixed zeta factor at 6z. -/
theorem exists_actual_threeLFactor_radical_bound
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions) (P : ProbeData K S)
    {e eps : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H U : ℝ,
      51 / 100 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ U →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u U (a + 2 * e) →
      ∀ s w z : ℂ, a + 16 * e ≤ s.re → s.re ≤ 2 →
        w.re = 1 - a - 6 * e → z.re = 17 / 50 → |s.im| ≤ H → |w.im| ≤ H →
        ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z) *
            heckeDeletedContinuation K (arithmeticRowCharacter K S P u) (exceptionalPrimes K S) w /
          heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K S P u))
            (exceptionalPrimes K S) s‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e + 2 * eps) *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
              2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by
  obtain ⟨C, Z0, hC, hZ0, hratio⟩ :=
    exists_actual_deletedLRatio_radical_bound K S psi companions hcomp P he he1 heps
  obtain ⟨D, hD, hzeta⟩ := HighBinBoundary.ActualLRatioStrip.exists_uniform_deleted_zeta_six_bound K S
  refine ⟨D * C, Z0, mul_pos hD hC, hZ0, ?_⟩
  intro Z hZ d hd u hu a H U ha ha1 hH hHU hbelow s w z hs hs2 hw hz hsi hwi
  have hr := hratio Z hZ d hd u hu a H U ha ha1 hH hHU hbelow s w hs hs2 hw hsi hwi
  have hzeta' := hzeta z hz.ge
  have h := mul_le_mul hzeta' hr (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hD.le
  calc
    _ = ‖heckeDeletedContinuation K 1 (exceptionalPrimes K S) (6 * z)‖ *
        (‖heckeDeletedContinuation K (arithmeticRowCharacter K S P u) (exceptionalPrimes K S) w‖ *
          ‖(heckeDeletedContinuation K (psi * conjugate (arithmeticRowCharacter K S P u))
            (exceptionalPrimes K S) s)⁻¹‖) := by
      simp only [div_eq_mul_inv, norm_mul]
      ring
    _ ≤ _ := h.trans_eq (by ring)

end HighBinVerified.NormFormSharpFactors

#print axioms HighBinVerified.NormFormSharpFactors.exists_actual_deletedLRatio_radical_bound
#print axioms HighBinVerified.NormFormSharpFactors.exists_actual_threeLFactor_radical_bound
