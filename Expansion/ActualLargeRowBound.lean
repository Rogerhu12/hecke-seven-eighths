import Expansion.ActualPrimeNormalizer
import HeckeSkeleton.ExpansionModels.LargeRowSum

/-!
# The actual absolute large-row input

The real contour zInfinity=1+3/zeta is fixed before the target.  Actual row
counting and the complete local correction leave a 33/64 saving, and the
proved inverse prime normalizer uses only 1/64 of it.  The original infinite
absolute row sum is genuinely summable at every Z>=1.  No large-row bound,
normalizer estimate, or convergence assertion is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.LargeRows
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu p.val)

include nu in
/-- The literal absolute tail is O(Z^(-1/2) (1+H)^3) on the fixed absolute
contours.  The threshold and constant precede every scale and height. -/
theorem exists_actual_large_tail_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      (∑' u, absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ Z H zeta (1 + 3 / zeta) u) ≤ C * Z ^ (-(1 / 2 : ℝ)) * (1 + H) ^ (3 : ℕ) := by
  obtain ⟨C, Zk, hC, hZk, hk⟩ := exists_actual_large_tail_fixed_saving K S mu nu
    hcomplex P psi hcal hunram g ∅ hzeta
  obtain ⟨Zn, hZn, hn⟩ := exists_actual_primeNormalizer_inverse_bound K Sset hcomplex g
    (1 / 64) (by norm_num)
  refine ⟨C, max Zk Zn, hC, hZk.trans (le_max_left _ _), ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZk.trans ((le_max_left _ _).trans hZ))
  have hnormal := (hn Z ((le_max_right _ _).trans hZ)).2
  have hscale : Z ^ (1 / 64 : ℝ) * Z ^ (-(33 / 64 : ℝ)) = Z ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hZpos]
    congr 1
    norm_num
  calc
    _ ≤ C * ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ *
        Z ^ (-(33 / 64 : ℝ)) * (1 + H) ^ (3 : ℕ) := hk Z H ((le_max_left _ _).trans hZ) hH
    _ ≤ C * Z ^ (1 / 64 : ℝ) * Z ^ (-(33 / 64 : ℝ)) * (1 + H) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnormal hC.le)
          (Real.rpow_nonneg hZpos.le _)) (by positivity)
    _ = C * (Z ^ (1 / 64 : ℝ) * Z ^ (-(33 / 64 : ℝ))) * (1 + H) ^ (3 : ℕ) := by ring
    _ = _ := by rw [hscale]

include nu in
/-- The concrete TLargeRowInput, with a fixed half-power absolute saving.
Its convergence clause also covers every bounded original scale.  The
estimate holds at all H>=1, so the interface ceiling may be one. -/
theorem actual_tLargeRowInput
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) :
    TLargeRowInput K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ zeta (1 + 3 / zeta) (1 / 2) := by
  refine ⟨?_, ?_⟩
  · intro Z H hZ hH
    apply summable_actual_absoluteLargeRowTerm K S mu nu hcomplex P psi g ∅
      (by have : 0 < 3 / zeta := div_pos (by norm_num) hzeta; linarith) zeta Z H hZ hH
  · obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_large_tail_bound K S mu nu
      hcomplex P psi hcal hunram g hzeta
    refine ⟨C, Z0, 3, 1, hC, hZ0, by norm_num, by norm_num, ?_⟩
    intro Z H hZ hH _hceiling
    simpa only [Real.rpow_ofNat] using hb Z H hZ hH

end Expansion.Project

#print axioms Expansion.Project.exists_actual_large_tail_bound
#print axioms Expansion.Project.actual_tLargeRowInput
