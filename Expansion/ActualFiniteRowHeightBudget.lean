import Expansion.ActualModerateKernelDecay
import Expansion.ActualOuterHeightBudget

/-!
# Uniform height budgets for every finite original moderate bin

The constants are chosen before the endpoint a, the cutoff exponent r,
the finite row set, Z and H.  The only cardinality estimate is the proved
linear count of all original frequency rows.  This covers the entire
moderate range through Z^(13/16+zeta), as well as arbitrary smaller bins.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

/-- True row counting bounds every finite subfamily at once.  The
constant is independent of the cutoff, exponent, and selected subfamily. -/
theorem exists_finite_frequencyRow_power_count
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    ∃ C : ℝ, 0 < C ∧ ∀ U p : ℝ, 1 ≤ U → 0 ≤ p →
      ∀ rows : Finset (FrequencyRow K S),
        (∀ u ∈ rows, frequencyRowNorm K S u ≤ U) →
        (∑ u ∈ rows, frequencyRowNorm K S u ^ p) ≤ C * U ^ (p + 1) := by
  obtain ⟨C, hC, hcount⟩ := frequencyRows_linear_count K S
  refine ⟨C, hC, ?_⟩
  intro U p hU hp rows hrows
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hsub : rows ⊆ frequencyRows K S U := by
    intro u hu
    exact (mem_frequencyRows_iff K S U hUpos.le u).mpr (hrows u hu)
  have hcard : (rows.card : ℝ) ≤ C * U :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcount U hU)
  calc
    _ ≤ ∑ _u ∈ rows, U ^ p := Finset.sum_le_sum (fun u hu =>
      Real.rpow_le_rpow (idealNorm_pos K u.ideal.val).le (hrows u hu) hp)
    _ = (rows.card : ℝ) * U ^ p := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * U) * U ^ p := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hUpos.le _)
    _ = C * U ^ (p + 1) := by rw [Real.rpow_add hUpos, Real.rpow_one]; ring

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
/-- The exact moderate starting contour has an arbitrary horizontal
height saving uniformly before the endpoint a. -/
theorem exists_actual_moderate_horizontal_row_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ B →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
        ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
          (B + 20 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ moderateBoundaryScalePower *
            frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n := by
  obtain ⟨Ck, Z0, hCk, hZ0, hk⟩ := exists_actual_moderate_sweep_kernel_rapid
    K S mu nu hcomplex P omega psi hpsi hAllowed g hB hB1 he he1 hboundary (n + 2)
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * 8 * Ck * 15, Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH a ha haB u hu
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  let M : ℝ := Ck * Z ^ moderateBoundaryScalePower * frequencyRowNorm K Sset u ^ (113 / 50 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hwidth : |5 - (B + 20 * e)| + |5 - (1 - a - 6 * e)| +
      |(3 : ℝ) - 17 / 50| ≤ 15 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 5 - (B + 20 * e)),
      abs_of_nonneg (by linarith : 0 ≤ 5 - (1 - a - 6 * e)),
      abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ) - 17 / 50)]
    linarith
  have hf := norm_three_faces_le_of_rapid
    (compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u Z) H 5 (B + 20 * e) 5 (1 - a - 6 * e) 3 (17 / 50) M n hH hM (by
      intro s w z hv
      have hs : s.re ∈ Icc (B + 20 * e) 5 := by
        simpa only [uIcc_of_ge (by linarith : B + 20 * e ≤ 5)] using hv.1
      have hw : w.re ∈ Icc (1 - a - 6 * e) 5 := by
        simpa only [uIcc_of_ge (by linarith : 1 - a - 6 * e ≤ 5)] using hv.2.1
      have hz : z.re ∈ Icc (17 / 50) 3 := by
        simpa only [uIcc_of_ge (by norm_num : (17 / 50 : ℝ) ≤ 3)] using hv.2.2
      exact hk Z hZ a ha haB u hu s w z hs.1 hs.2 hw.1 hw.2 hz.1 hz.2)
  unfold actualOuterHorizontalFaces
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hf hkappa).trans
  calc
    _ ≤ kappa * (8 * M * 15 / (1 + H) ^ n) := by gcongr
    _ ≤ ((kappa + 1) * 8 * Ck * 15) * Z ^ moderateBoundaryScalePower *
        frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n := by
      have hh := mul_le_mul_of_nonneg_right (by linarith : kappa ≤ kappa + 1)
        (show 0 ≤ 8 * M * 15 / (1 + H) ^ n by positivity)
      convert hh using 1 <;> dsimp only [M, kappa] <;> ring

include nu in
/-- A uniform initial-to-moderate horizontal budget for every finite
original bin.  Taking r=13/16+zeta covers the complete moderate range;
the row set and its finite-height zero filtering may be chosen afterward. -/
theorem exists_actual_finite_moderate_horizontal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ r Z H : ℝ, 0 ≤ r → Z0 ≤ Z → 0 ≤ H →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ B → ∀ rows : Finset (FrequencyRow K Sset),
      (∀ u ∈ rows, ¬principalFrequencyRow K Sset u) →
      (∀ u ∈ rows, frequencyRowNorm K Sset u ≤ Z ^ r) →
      ‖∑ u ∈ rows, actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
        (B + 20 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (moderateBoundaryScalePower + r * (163 / 50)) / (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_moderate_horizontal_row_bound
    K S mu nu hcomplex P omega psi hpsi hAllowed g hB hB1 he he1 hboundary n
  obtain ⟨Cc, hCc, hcount⟩ := exists_finite_frequencyRow_power_count K Sset
  refine ⟨Cr * Cc, Z0, mul_pos hCr hCc, hZ0, ?_⟩
  intro r Z H hr0 hZ hH a ha haB rows hnon hcut
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hU : 1 ≤ Z ^ r := Real.one_le_rpow (hZ0.trans hZ) hr0
  have hmass := hcount (Z ^ r) (113 / 50) hU (by norm_num) rows hcut
  norm_num only [show (113 / 50 : ℝ) + 1 = 163 / 50 by norm_num] at hmass
  have hscale : Z ^ moderateBoundaryScalePower * (Z ^ r) ^ (163 / 50 : ℝ) =
      Z ^ (moderateBoundaryScalePower + r * (163 / 50)) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  calc
    _ ≤ ∑ u ∈ rows, ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
        (B + 20 * e) (1 - a - 6 * e) (17 / 50)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ rows, Cr * Z ^ moderateBoundaryScalePower *
        frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n :=
      Finset.sum_le_sum (fun u hu => hr Z H hZ hH a ha haB u (hnon u hu))
    _ = (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        ∑ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (Cr * Z ^ moderateBoundaryScalePower / (1 + H) ^ n) *
        (Cc * (Z ^ r) ^ (163 / 50 : ℝ)) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cr * Cc) * (Z ^ moderateBoundaryScalePower * (Z ^ r) ^ (163 / 50 : ℝ)) /
        (1 + H) ^ n := by ring
    _ = _ := by rw [hscale]

end Expansion.Project

#print axioms Expansion.Project.exists_finite_frequencyRow_power_count
#print axioms Expansion.Project.exists_actual_finite_moderate_horizontal_bound
