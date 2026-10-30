import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Analysis.ActualSIntegerSobolevTests

/-! Literal six-test profiles and empty slot geometry for the zero-slot
source bridge. No row-to-Hecke realization, sector reindexing, seminorm
estimate or canonical-admissibility instance is supplied by this file.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The six actual tests, with an exact filtered finite ideal support.
The zero extension at nonpositive arguments is only for the all-real
IdealTest specification; every actual positive-scale norm ratio is positive. -/
def actualSobolevIdealTest (i : Fin 2) (m : Fin 3) (s : ℂ) : IdealTest K where
  profile _ _ y := if 0 < y then scaleSobolevTest i m s y else 0
  support _ _ D := if 0 < D then
    (dyadicIdealSupport K D).filter (fun I => scaleSobolevTest i m s (idealNorm K I / D) ≠ 0)
    else ∅
  support_spec _ _ D I := by
    by_cases hD : 0 < D
    · have hy : 0 < idealNorm K I / D := div_pos (idealNorm_pos K I) hD
      rw [ite_eq_left hD, ite_eq_left hy, Finset.mem_filter,
        mem_dyadicIdealSupport_iff K hD.le]
      constructor
      · exact And.right
      · intro h
        refine ⟨?_, h⟩
        have ht : idealNorm K I / D < 2 :=
          lt_of_not_ge (fun hh => h (scaleSobolevTest_zero_of_ge i m s hh))
        exact ((div_lt_iff₀ hD).mp ht).le
    · have hy : ¬0 < idealNorm K I / D := not_lt.mpr
        (div_nonpos_of_nonneg_of_nonpos (idealNorm_pos K I).le (le_of_not_gt hD))
      simp only [ite_eq_right hD, ite_eq_right hy, Finset.notMem_empty,
        ne_eq, not_true_eq_false]

/-- Filtering the actual norm envelope deletes only literal zero summands. -/
theorem actualSobolevIdealTest_sum_eq (i : Fin 2) (m : Fin 3) (s : ℂ)
    (c : NonzeroIdeal K → ℂ) (u : NonzeroIdeal K) {D : ℝ} (hD : 0 < D) :
    (∑ I ∈ (actualSobolevIdealTest K i m s).support u 0 D,
      c I * (actualSobolevIdealTest K i m s).profile u 0 (idealNorm K I / D)) =
      ∑ I ∈ dyadicIdealSupport K D, c I * scaleSobolevTest i m s (idealNorm K I / D) := by
  simp only [actualSobolevIdealTest, ite_eq_left hD, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  rw [ite_eq_left (div_pos (idealNorm_pos K I) hD)]
  by_cases h : scaleSobolevTest i m s (idealNorm K I / D) ≠ 0
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, not_ne_iff.mp h, mul_zero]

/-- Exact equality with the existing actual sextic polynomial. Its actual
coefficient is displayed, rather than assumed to be a Hecke row coefficient. -/
theorem actualSobolevIdealTest_polynomial_eq
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
    (η : HeckeCharacter K) (a : S.integer K)
    (i : Fin 2) (m : Fin 3) (s : ℂ) (u : NonzeroIdeal K) {D : ℝ} (hD : 0 < D) :
    (Real.sqrt D : ℂ)⁻¹ *
      (∑ I ∈ (actualSobolevIdealTest K i m s).support u 0 D,
        actualInverseIdealCoefficient K S ζ hζ σ η a I *
          (actualSobolevIdealTest K i m s).profile u 0 (idealNorm K I / D)) =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K D) a D (scaleSobolevTest i m s) := by
  rw [actualSobolevIdealTest_sum_eq K i m s _ u hD]
  rfl

/-- A genuinely empty slot system. -/
def zeroSlotGeometry : SlotGeometry K where
  slotCount := 0
  slots := Fin.elim0

@[simp] theorem zeroSlotGeometry_totalLength : (zeroSlotGeometry K).totalLength = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

@[simp] theorem zeroSlotGeometry_fitsMesh (mesh : ℝ) :
    (zeroSlotGeometry K).fitsMesh mesh := by
  intro i
  exact Fin.elim0 i

variable {K}

/-- A positive compact dilation transfers an independent scale into the
profile. Its support is the ORIGINAL test's support at the actual scale vD. -/
def IdealTest.positiveDilation (W : IdealTest K) (v : ℝ) (hv : 0 < v) : IdealTest K where
  profile u t y := (Real.sqrt v : ℂ)⁻¹ * W.profile u t (y / v)
  support u t D := W.support u t (v * D)
  support_spec u t D I := by
    rw [W.support_spec]
    have hsqrt : (Real.sqrt v : ℂ)⁻¹ ≠ 0 := inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hv)))
    rw [div_div, mul_comm D v]
    constructor
    · intro h
      exact mul_ne_zero hsqrt h
    · exact right_ne_zero_of_mul

/-- The sqrt(v) factor gives the ACTUAL normalization at independent scale
vD. This identity makes no analytic moment assertion. -/
theorem IdealTest.positiveDilation_polynomial (W : IdealTest K)
    (v : ℝ) (hv : 0 < v) (c : NonzeroIdeal K → ℂ)
    (u : NonzeroIdeal K) (t : ℝ) {D : ℝ} (_hD : 0 < D) :
    (Real.sqrt D : ℂ)⁻¹ *
      (∑ I ∈ (W.positiveDilation v hv).support u t D,
        c I * (W.positiveDilation v hv).profile u t (idealNorm K I / D)) =
      (Real.sqrt (v * D) : ℂ)⁻¹ *
        ∑ I ∈ W.support u t (v * D), c I * W.profile u t (idealNorm K I / (v * D)) := by
  simp only [positiveDilation, div_div, mul_comm D v, Real.sqrt_mul hv.le,
    Complex.ofReal_mul, mul_inv_rev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- Choosing a genuine test separately at each ideal row preserves its
exact support. No row-dependent prime profile is introduced. -/
def IdealTest.rowwise (W : NonzeroIdeal K → IdealTest K) : IdealTest K where
  profile u t y := (W u).profile u t y
  support u t D := (W u).support u t D
  support_spec u t D I := (W u).support_spec u t D I

/-- Two fixed real coordinates encode Re(s) and log(v); only the first
height coordinate is used for Im(s). Boundedness and seminorm estimates
are separate source obligations, rather than assertions of this constructor. -/
def actualSobolevParameterTest (i : Fin 2) (m : Fin 3)
    (σ τ : NonzeroIdeal K → Fin 2 → ℝ) : IdealTest K :=
  IdealTest.rowwise fun u =>
    (actualSobolevIdealTest K i m
      ((σ u 0 : ℂ) + (τ u 0 : ℂ) * Complex.I)).positiveDilation
      (Real.exp (σ u 1)) (Real.exp_pos _)

/-- Literal independent-scale, rowwise-complex-parameter identity for the
actual sextic coefficient, including its original zero extension. -/
theorem actualSobolevParameterTest_polynomial_eq
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (ι : K →+* ℂ)
    (η : HeckeCharacter K) (a : S.integer K)
    (i : Fin 2) (m : Fin 3) (σ τ : NonzeroIdeal K → Fin 2 → ℝ)
    (u : NonzeroIdeal K) {D : ℝ} (hD : 0 < D) :
    (Real.sqrt D : ℂ)⁻¹ *
      (∑ I ∈ (actualSobolevParameterTest i m σ τ).support u 0 D,
        actualInverseIdealCoefficient K S ζ hζ ι η a I *
          (actualSobolevParameterTest i m σ τ).profile u 0 (idealNorm K I / D)) =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ ι η
        (dyadicIdealSupport K (Real.exp (σ u 1) * D)) a
        (Real.exp (σ u 1) * D)
        (scaleSobolevTest i m ((σ u 0 : ℂ) + (τ u 0 : ℂ) * Complex.I)) := by
  exact (IdealTest.positiveDilation_polynomial
    (actualSobolevIdealTest K i m ((σ u 0 : ℂ) + (τ u 0 : ℂ) * Complex.I))
    (Real.exp (σ u 1)) (Real.exp_pos _) _ u 0 hD).trans
    (actualSobolevIdealTest_polynomial_eq K S ζ hζ ι η a i m _ u
      (mul_pos (Real.exp_pos _) hD))

end HeckeGeneral.Analysis.ConditionalMoments
