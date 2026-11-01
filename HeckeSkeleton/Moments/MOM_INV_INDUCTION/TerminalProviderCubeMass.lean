import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletion
import HeckeSkeleton.LowEnergy.IdealMass
import HeckeGeneral.Analysis.GlobalThetaData

/-!
# The actual short-cube divisor mass costs an arbitrary small power

The divisor count is taken on the original extracted cube ideal (or its
literal third power).  The ideal harmonic sum and divisor epsilon bound
are applied before any source, row, short cutoff or tuple is selected.
The stronger generic version allows any fixed ideal power and divisor
weight, so no comparison replacing the actual cube divisor mark is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalCubeMass

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.IdealMobiusDivisorSum DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.LowEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- One constant covers every injective finite presentation of nonzero
ideals and every cutoff.  The powers `e,k` are fixed before the constant. -/
theorem exists_divisor_power_harmonic_bound (e k : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type*} (f : ι → Ideal (𝓞 K)), Function.Injective f →
      ∀ T : ℝ, 1 ≤ T → ∀ B : Finset ι,
      (∀ I ∈ B, f I ≠ ⊥) → (∀ I ∈ B, ((f I).absNorm : ℝ) ≤ T) →
      (∑ I ∈ B, (((idealDivisors ((f I) ^ e)).card : ℝ) ^ k) /
        ((f I).absNorm : ℝ)) ≤ C * T ^ eps := by
  let delta := eps / (2 * ((e : ℝ) * (k : ℝ) + 1))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdeltaCost : (e : ℝ) * delta * (k : ℝ) ≤ eps / 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show (e : ℝ) * (k : ℝ) ≤ (e : ℝ) * (k : ℝ) + 1 by linarith) hdelta.le
    have heq : delta * ((e : ℝ) * (k : ℝ) + 1) = eps / 2 := by
      dsimp only [delta]
      field_simp [show (e : ℝ) * (k : ℝ) + 1 ≠ 0 by positivity]
      <;> ring
    rw [heq] at h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨Bdiv, hBdiv, hdiv⟩ := ideal_divisor_count_le_rpow K delta hdelta
  obtain ⟨Bharm, hBharm, hharm⟩ := ideal_harmonic_small_power_pullback K (eps / 2)
    (by positivity)
  refine ⟨Bdiv ^ k * Bharm, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBdiv) hBharm, ?_⟩
  intro ι f hf T hT B hne hnorm
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hweight (I : ι) (hI : I ∈ B) :
      ((idealDivisors ((f I) ^ e)).card : ℝ) ^ k ≤ Bdiv ^ k * T ^ (eps / 2) := by
    let N : ℝ := ((f I).absNorm : ℝ)
    have hN : 0 < N := ideal_norm_pos K (f I) (hne I hI)
    have hd : ((idealDivisors ((f I) ^ e)).card : ℝ) ≤ Bdiv * N ^ ((e : ℝ) * delta) := by
      have hb := hdiv ((f I) ^ e)
      change ((idealDivisors ((f I) ^ e)).card : ℝ) ≤
        Bdiv * (((f I) ^ e).absNorm : ℝ) ^ delta at hb
      rw [map_pow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN.le] at hb
      exact hb
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hd k
    rw [mul_pow, ← Real.rpow_mul_natCast hN.le] at hpow
    calc
      _ ≤ Bdiv ^ k * N ^ ((e : ℝ) * delta * (k : ℝ)) := hpow
      _ ≤ Bdiv ^ k * T ^ ((e : ℝ) * delta * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hBdiv) _)
        exact Real.rpow_le_rpow hN.le (hnorm I hI) (by positivity)
      _ ≤ Bdiv ^ k * T ^ (eps / 2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hdeltaCost)
        (pow_nonneg (zero_le_one.trans hBdiv) _)
  calc
    _ ≤ ∑ I ∈ B, (Bdiv ^ k * T ^ (eps / 2)) / ((f I).absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      exact div_le_div_of_nonneg_right (hweight I hI) (Nat.cast_nonneg _)
    _ = (Bdiv ^ k * T ^ (eps / 2)) * ∑ I ∈ B, 1 / ((f I).absNorm : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ ≤ (Bdiv ^ k * T ^ (eps / 2)) * (Bharm * T ^ (eps / 2)) :=
      mul_le_mul_of_nonneg_left (hharm f hf T hT B hne hnorm) (by positivity)
    _ = (Bdiv ^ k * Bharm) * T ^ eps := by
      have hp : T ^ (eps / 2) * T ^ (eps / 2) = T ^ eps := by
        rw [← Real.rpow_add hTp]
        congr 1
        ring
      calc
        _ = (Bdiv ^ k * Bharm) * (T ^ (eps / 2) * T ^ (eps / 2)) := by ring
        _ = _ := by rw [hp]

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- In particular the actual divisor count of H cubed is retained,
with one arbitrary-power bound for every finite short-cube pool. -/
theorem exists_exterior_cube_mass_bound (slotCap : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ B : Finset (ExteriorIdeal K S),
      (∀ H ∈ B, exteriorNorm K S H ≤ T) →
      (∑ H ∈ B, (((idealDivisors (H.val.val ^ 3)).card : ℝ) ^ slotCap) /
        exteriorNorm K S H) ≤ C * T ^ eps := by
  obtain ⟨C, hC, hb⟩ := exists_divisor_power_harmonic_bound K 3 slotCap eps heps
  refine ⟨C, hC, ?_⟩
  intro T hT B hnorm
  exact hb (fun H : ExteriorIdeal K S => H.val.val)
    (fun I J h => Subtype.ext (Subtype.ext h)) T hT B
    (fun H hH => nonZeroDivisors.coe_ne_zero H.val) hnorm

/-- The alternative normalized divisor weight used after reopening
the cube is controlled by the same proved ideal harmonic mechanism. -/
theorem exists_exterior_divisor_mass_bound (slotCap : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ B : Finset (ExteriorIdeal K S),
      (∀ H ∈ B, exteriorNorm K S H ≤ T) →
      (∑ H ∈ B, (((idealDivisors H.val.val).card : ℝ) ^ (3 * slotCap)) /
        exteriorNorm K S H) ≤ C * T ^ eps := by
  obtain ⟨C, hC, hb⟩ := exists_divisor_power_harmonic_bound K 1 (3 * slotCap) eps heps
  refine ⟨C, hC, ?_⟩
  intro T hT B hnorm
  simpa only [pow_one] using hb (fun H : ExteriorIdeal K S => H.val.val)
    (fun I J h => Subtype.ext (Subtype.ext h)) T hT B
    (fun H hH => nonZeroDivisors.coe_ne_zero H.val) hnorm

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalCubeMass

end
