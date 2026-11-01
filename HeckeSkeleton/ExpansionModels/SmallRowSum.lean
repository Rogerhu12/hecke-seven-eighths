import HeckeSkeleton.ExpansionModels.SmallRowKernel

/-!
# Summing and integrating the actual small rows

The complete finite small-row contour block is bounded on its original
three lines.  Its row set is fixed before integration, and the estimate
retains all nonprincipal rows below Z^(1/16), including the bounded norm
exceptions in the reciprocal factor.  The only remaining varying scalar
is the literal inverse prime normalizer.  A proved subpower estimate for
that independent scalar can be composed with this theorem to obtain the
project's `TSmallRowInput`; no such estimate is assumed below.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
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
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

/-- A direct norm bound for the original three iterated set integrals.
The general Bochner integral inequality applies separately at each step;
there is no exchange with a moving row set or a moving partition. -/
theorem norm_actual_rowContourBox_le
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (E : RowEulerData K Sset P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (u : FrequencyRow K Sset)
    (Z H sigma nuLine zLine : ℝ) (hH : 0 ≤ H) {b : ℝ}
    (hpoint : ∀ ts ∈ Icc (-H) H, ∀ tw ∈ Icc (-H) H, ∀ tz ∈ Icc (-H) H,
      ‖rowKernelOnLines K Sset muS P psi E g T u Z sigma nuLine zLine ts tw tz‖ ≤ b) :
    ‖rowContourBox K Sset muS P psi E g T u Z H sigma nuLine zLine‖ ≤
      (2 * Real.pi) ^ (-(3 : ℤ)) * (2 * H) ^ 3 * b := by
  let box := Icc (-H) H
  let F := rowKernelOnLines K Sset muS P psi E g T u Z sigma nuLine zLine
  have hfinite : volume box < ⊤ := isCompact_Icc.measure_lt_top
  have hvol : volume.real box = 2 * H := by
    rw [Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  have hz : ∀ ts ∈ box, ∀ tw ∈ box, ‖∫ tz in box, F ts tw tz‖ ≤ b * (2 * H) := by
    intro ts hts tw htw
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite (hpoint ts hts tw htw)
  have hw : ∀ ts ∈ box, ‖∫ tw in box, ∫ tz in box, F ts tw tz‖ ≤ (b * (2 * H)) * (2 * H) := by
    intro ts hts
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite (hz ts hts)
  have hs : ‖∫ ts in box, ∫ tw in box, ∫ tz in box, F ts tw tz‖ ≤
      ((b * (2 * H)) * (2 * H)) * (2 * H) := by
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite hw
  have hfactor : ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ = (2 * Real.pi) ^ (-(3 : ℤ)) := by
    simp only [norm_zpow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [rowContourBox, norm_mul, hfactor]
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

include nu in
/-- All actual nonprincipal rows in the small range, with the paper's exact
1/50 saving.  Eta/8 is the two row-subpower losses after the Z^(1/16) cutoff.
The independent prime normalizer is retained explicitly. -/
theorem exists_actual_small_block_before_normalizer_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      ‖finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H 0 (Z ^ (1 / 16 : ℝ)) (B + e) (1 / 2) (17 / 50)‖ ≤
        C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
          Z ^ (B - 11 / 16 - 1 / 50 + e + eta / 8) * (1 + H) ^ A := by
  obtain ⟨Ck, Z0, A, hCk, hZ0, hA, hkernel⟩ := exists_actual_small_kernel_bound K S mu nu
    hcomplex P omega psi hpsi hAllowed hcal hunram g T hB hB1 he he1 heta hboundary
  obtain ⟨Cc, hCc, hcount⟩ := frequencyRows_linear_count K Sset
  let Cline : ℝ := (2 * Real.pi) ^ (-(3 : ℤ))
  have hCline : 0 < Cline := by dsimp [Cline]; positivity
  refine ⟨Cline * 8 * Ck * Cc, Z0, A + 3, by positivity, hZ0, by linarith, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHpos : 0 < 1 + H := by linarith
  let U : ℝ := Z ^ (1 / 16 : ℝ)
  have hU : 1 ≤ U := Real.one_le_rpow hZ1 (by norm_num)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  let rows := (frequencyRows K Sset U).filter
    (fun u => 0 < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u)
  let p : ℝ := 13 / 50 + 2 * eta
  have hp : 0 ≤ p := by dsimp [p]; linarith
  let Ninv : ℝ := ‖(primeNormalizer K Sset g T Z)⁻¹‖
  let Zfactor : ℝ := Z ^ (B + e - 629 / 800)
  have hrow : ∀ u ∈ rows,
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H (B + e) (1 / 2) (17 / 50)‖ ≤
        Cline * (2 * H) ^ 3 *
          (Ck * Ninv * Zfactor * frequencyRowNorm K Sset u ^ p * (1 + H) ^ A) := by
    intro u hu
    have hnon := (Finset.mem_filter.mp hu).2.2
    apply norm_actual_rowContourBox_le K S mu P psi (arithmeticHighEulerData K Sset P psi)
      g T u Z H (B + e) (1 / 2) (17 / 50) hH0
    intro ts hts tw htw tz htz
    apply hkernel Z H hZ hH u hnon
    · simp
    · simp
    · simp
    · simpa using (abs_le.mpr hts : |ts| ≤ H)
    · simpa using (abs_le.mpr htw : |tw| ≤ H)
    · simpa using (abs_le.mpr htz : |tz| ≤ H)
  have hmass : ∑ u ∈ rows, frequencyRowNorm K Sset u ^ p ≤ Cc * U ^ (p + 1) := by
    have hterm : ∀ u ∈ rows, frequencyRowNorm K Sset u ^ p ≤ U ^ p := by
      intro u hu
      have hmem := (Finset.mem_filter.mp hu).1
      have hnorm := (_root_.Expansion.Project.mem_frequencyRows_iff K Sset U hUpos.le u).mp hmem
      exact Real.rpow_le_rpow (idealNorm_pos K u.ideal.val).le hnorm hp
    have hcard : (rows.card : ℝ) ≤ Cc * U :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans (hcount U hU)
    calc
      _ ≤ ∑ _u ∈ rows, U ^ p := Finset.sum_le_sum hterm
      _ = (rows.card : ℝ) * U ^ p := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Cc * U) * U ^ p := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hUpos.le _)
      _ = Cc * U ^ (p + 1) := by rw [Real.rpow_add hUpos p 1, Real.rpow_one]; ring
  have hscale : Zfactor * U ^ (p + 1) = Z ^ (B - 11 / 16 - 1 / 50 + e + eta / 8) := by
    dsimp only [Zfactor, U, p]
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
    congr 1
    ring
  have hheight : H ^ 3 * (1 + H) ^ A ≤ (1 + H) ^ (A + 3) := by
    rw [Real.rpow_add hHpos A 3, Real.rpow_ofNat]
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hH0 (by linarith : H ≤ 1 + H) 3) (by positivity)).trans_eq (mul_comm _ _)
  change ‖∑ u ∈ rows, rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
    g T u Z H (B + e) (1 / 2) (17 / 50)‖ ≤ _
  calc
    _ ≤ ∑ u ∈ rows, ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H (B + e) (1 / 2) (17 / 50)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ rows, Cline * (2 * H) ^ 3 *
        (Ck * Ninv * Zfactor * frequencyRowNorm K Sset u ^ p * (1 + H) ^ A) :=
      Finset.sum_le_sum hrow
    _ = (Cline * (2 * H) ^ 3 * Ck * Ninv * Zfactor * (1 + H) ^ A) *
        ∑ u ∈ rows, frequencyRowNorm K Sset u ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (Cline * (2 * H) ^ 3 * Ck * Ninv * Zfactor * (1 + H) ^ A) *
        (Cc * U ^ (p + 1)) := mul_le_mul_of_nonneg_left hmass (by dsimp [Ninv, Zfactor]; positivity)
    _ = (Cline * 8 * Ck * Cc) * Ninv * (Zfactor * U ^ (p + 1)) *
        (H ^ 3 * (1 + H) ^ A) := by ring
    _ ≤ (Cline * 8 * Ck * Cc) * Ninv * (Zfactor * U ^ (p + 1)) *
        (1 + H) ^ (A + 3) := by
      exact mul_le_mul_of_nonneg_left hheight (by dsimp [Ninv, Zfactor]; positivity)
    _ = _ := by rw [hscale]

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.norm_actual_rowContourBox_le
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_actual_small_block_before_normalizer_bound
