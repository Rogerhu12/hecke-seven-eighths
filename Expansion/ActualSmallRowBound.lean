import Expansion.ActualPrimeNormalizer
import HeckeSkeleton.ExpansionModels.SmallRowSum

/-!
# The actual small-row input after normalizer absorption

The raw small-row block uses the genuine arithmetic Euler data and the
original common packet boundary. The independently proved normalizer
estimate consumes half the requested positive loss; the two row subpower
losses consume the other half. No normalizer bound or small-row conclusion
is an input, and no finite-height zero hypothesis is strengthened.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.SmallRows
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
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

include nu in
/-- The requested loss fixes both thresholds before Z and height. -/
theorem exists_actual_small_block_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e loss : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hloss : 0 < loss)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z₀ A : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z₀ ≤ Z → 1 ≤ H →
      ‖finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ Z H 0 (Z ^ (1 / 16 : ℝ)) (B + e) (1 / 2) (17 / 50)‖ ≤
        C * Z ^ (B - 11 / 16 - 1 / 50 + e + loss) * (1 + H) ^ A := by
  obtain ⟨C, Zk, A, hC, hZk, hA, hkernel⟩ :=
    exists_actual_small_block_before_normalizer_bound K S mu nu hcomplex
      P omega psi hpsi hAllowed hcal hunram g ∅ (eta := 4 * loss)
      hB hB1 he he1 (by linarith) hboundary
  obtain ⟨Zn, hZn, hnormalizer⟩ :=
    exists_actual_primeNormalizer_inverse_bound K Sset hcomplex g (loss / 2) (by linarith)
  refine ⟨C, max Zk Zn, A, hC, hZk.trans (le_max_left _ _), hA, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZk.trans ((le_max_left _ _).trans hZ)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hk := hkernel Z H ((le_max_left _ _).trans hZ) hH
  have hn := (hnormalizer Z ((le_max_right _ _).trans hZ)).2
  have hscale : Z ^ (loss / 2) *
      Z ^ (B - 11 / 16 - 1 / 50 + e + (4 * loss) / 8) =
      Z ^ (B - 11 / 16 - 1 / 50 + e + loss) := by
    rw [← Real.rpow_add hZpos]
    congr 1
    ring
  calc
    _ ≤ C * ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ *
        Z ^ (B - 11 / 16 - 1 / 50 + e + (4 * loss) / 8) * (1 + H) ^ A := hk
    _ ≤ C * Z ^ (loss / 2) *
        Z ^ (B - 11 / 16 - 1 / 50 + e + (4 * loss) / 8) * (1 + H) ^ A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC.le)
          (Real.rpow_nonneg hZpos.le _))
        (Real.rpow_nonneg (by linarith : 0 ≤ 1 + H) _)
    _ = C * (Z ^ (loss / 2) *
        Z ^ (B - 11 / 16 - 1 / 50 + e + (4 * loss) / 8)) * (1 + H) ^ A := by ring
    _ = _ := by rw [hscale]

include nu in
/-- Concrete small-row input. The bound already holds at every height at
least one; the interface's finite height ceiling can therefore be one. -/
theorem actual_tSmallRowInput
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e loss : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hloss : 0 < loss)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    TSmallRowInput K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ B e loss := by
  obtain ⟨C, Z₀, A, hC, hZ₀, hA, hbound⟩ :=
    exists_actual_small_block_bound K S mu nu hcomplex P omega psi hpsi hAllowed hcal
      hunram g hB hB1 he he1 hloss hboundary
  refine ⟨⟨C, Z₀, A, 1, hC, hZ₀, hA, by norm_num, ?_⟩⟩
  intro Z H hZ hH _hceiling
  exact hbound Z H hZ hH

end Expansion.Project

#print axioms Expansion.Project.exists_actual_small_block_bound
#print axioms Expansion.Project.actual_tSmallRowInput
