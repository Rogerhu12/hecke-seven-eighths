import HeckeSkeleton.ExpansionModels.LargeRowKernel
import HeckeSkeleton.ExpansionModels.LargeRowTail
import HeckeSkeleton.ExpansionModels.SmallRowSum
import HeckeGeneral.Analysis.TInputRanges

/-!
# The actual absolute large-row sum

The literal three iterated contour integrals are summed over the original
strict tail N(u)>Z^(13/16+zeta).  Summability holds at every Z>=1, including
the bounded scales before the common local cutoff.  The quantitative tail
has the paper's exact exponent, with the prime normalizer left visible.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.LargeRows

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
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
/-- Genuine convergence of the all-row absolute tail at every original
scale.  The original contour box and every sector are retained. -/
theorem summable_actual_absoluteLargeRowTerm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {sigma : ℝ} (hsigma : 1 < sigma) (zeta Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Summable (absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g T Z H zeta sigma) := by
  let eta : ℝ := (sigma - 1) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hp : eta - sigma < -1 := by dsimp [eta]; linarith
  obtain ⟨C, hC, hkernel⟩ := exists_actual_large_kernel_all_scales_bound K S mu nu
    hcomplex P psi g T hsigma.le heta
  let D : ℝ := (2 * Real.pi) ^ (-(3 : ℤ)) * (2 * H) ^ 3 *
    (C * largeCorrectionMass K Sset g T Z sigma * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
      Z ^ (53 / 32 + (31 / 48) * sigma))
  have hD : 0 ≤ D := by
    have hmass := largeCorrectionMass_nonneg K Sset g T Z sigma
    dsimp [D]
    positivity
  have hrow (u : FrequencyRow K Sset) :
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 2 2 sigma‖ ≤ D * frequencyRowNorm K Sset u ^ (eta - sigma) := by
    apply (norm_actual_rowContourBox_le K S mu P psi (arithmeticHighEulerData K Sset P psi)
      g T u Z H 2 2 sigma (by linarith)
      (b := (C * largeCorrectionMass K Sset g T Z sigma * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
        Z ^ (53 / 32 + (31 / 48) * sigma)) * frequencyRowNorm K Sset u ^ (eta - sigma))
      ?_).trans_eq (by dsimp [D]; ring)
    intro ts _ tw _ tz _
    apply hkernel Z (zero_lt_one.trans_le hZ) u
    · simp
    · simp
    · simp
  have hmajor := (summable_frequencyRowNorm_rpow K Sset hp).mul_left D
  apply hmajor.of_nonneg_of_le
  · intro u
    unfold absoluteLargeRowTerm
    split_ifs <;> positivity
  · intro u
    unfold absoluteLargeRowTerm
    split_ifs
    · exact hrow u
    · exact mul_nonneg hD (Real.rpow_nonneg (idealNorm_pos K u.ideal.val).le _)

include nu in
/-- The exact large-tail power before the independent prime normalizer.
All constants and the common cutoff precede Z, H, and the original rows. -/
theorem exists_actual_large_tail_before_normalizer_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {zeta eta : ℝ} (hzeta : 0 < zeta) (heta : 0 < eta) (hetaz : eta < 3 / zeta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      (∑' u, absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H zeta (1 + 3 / zeta) u) ≤
          C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ *
            Z ^ (-17 / 32 + (13 / 16 + zeta) * eta) * (1 + H) ^ (3 : ℕ) := by
  let sigma : ℝ := 1 + 3 / zeta
  let p : ℝ := eta - sigma
  have hsigma : 1 < sigma := by
    have hq : 0 < 3 / zeta := div_pos (by norm_num) hzeta
    dsimp only [sigma]
    linarith
  have hp : p < -1 := by dsimp [p, sigma]; linarith
  obtain ⟨Ck, Z0, hCk, hZ0, hkernel⟩ := exists_actual_large_kernel_bound K S mu nu
    hcomplex P psi hcal hunram g T hsigma.le heta
  obtain ⟨Ct, hCt, htail⟩ := exists_frequencyRowNorm_power_tail_bound K Sset hp
  let Cline : ℝ := (2 * Real.pi) ^ (-(3 : ℤ))
  have hCline : 0 < Cline := by dsimp [Cline]; positivity
  refine ⟨Cline * 8 * Ck * Ct, Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  let U : ℝ := Z ^ (13 / 16 + zeta)
  have hU : 1 ≤ U := Real.one_le_rpow hZ1 (by linarith)
  let rows := {u : FrequencyRow K Sset // U < frequencyRowNorm K Sset u}
  let Ninv : ℝ := ‖(primeNormalizer K Sset g T Z)⁻¹‖
  let Zfactor : ℝ := Z ^ (53 / 32 + (13 / 16) * sigma)
  let D : ℝ := Cline * (2 * H) ^ 3 * (Ck * Ninv * Zfactor)
  have hD : 0 ≤ D := by dsimp [D, Cline, Ninv, Zfactor]; positivity
  have hrow (u : rows) :
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u.val Z H 2 2 sigma‖ ≤ D * frequencyRowNorm K Sset u.val ^ p := by
    apply (norm_actual_rowContourBox_le K S mu P psi (arithmeticHighEulerData K Sset P psi)
      g T u.val Z H 2 2 sigma hH0
      (b := Ck * Ninv * Zfactor * frequencyRowNorm K Sset u.val ^ p)
      ?_).trans_eq (by dsimp [D]; ring)
    intro ts _ tw _ tz _
    apply hkernel Z hZ u.val
    · simp
    · simp
    · simp
  obtain ⟨hsum, hsum_bound⟩ := htail U hU
  have hnormsum : Summable (fun u : rows =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u.val Z H 2 2 sigma‖) :=
    (hsum.mul_left D).of_nonneg_of_le (fun _ => norm_nonneg _) hrow
  have heq :
      (∑' u, absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H zeta sigma u) =
      ∑' u : rows, ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u.val Z H 2 2 sigma‖ := by
    rw [tsum_subtype]
    rfl
  have hscale : Zfactor * U ^ (p + 1) = Z ^ (-17 / 32 + (13 / 16 + zeta) * eta) := by
    dsimp only [Zfactor, U, p, sigma]
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
    congr 1
    field_simp [hzeta.ne']
    <;> ring
  have hheight : H ^ 3 ≤ (1 + H) ^ 3 := pow_le_pow_left₀ hH0 (by linarith) 3
  change (∑' u, absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
    g T Z H zeta sigma u) ≤ _
  rw [heq]
  calc
    _ ≤ ∑' u : rows, D * frequencyRowNorm K Sset u.val ^ p :=
      hnormsum.tsum_le_tsum hrow (hsum.mul_left D)
    _ = D * ∑' u : rows, frequencyRowNorm K Sset u.val ^ p := tsum_mul_left
    _ ≤ D * (Ct * U ^ (p + 1)) := mul_le_mul_of_nonneg_left hsum_bound hD
    _ = (Cline * 8 * Ck * Ct) * Ninv * (Zfactor * U ^ (p + 1)) * H ^ 3 := by dsimp [D]; ring
    _ ≤ (Cline * 8 * Ck * Ct) * Ninv * (Zfactor * U ^ (p + 1)) * (1 + H) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hheight (by dsimp [Ninv, Zfactor]; positivity)
    _ = _ := by rw [hscale]

include nu in
/-- A fixed positive reserve, chosen entirely before the target and height.
The small row-count loss is explicit and keeps a 33/64 absolute Z saving
before the independent normalizer. -/
theorem exists_actual_large_tail_fixed_saving
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      (∑' u, absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H zeta (1 + 3 / zeta) u) ≤
          C * ‖(primeNormalizer K Sset g T Z)⁻¹‖ * Z ^ (-(33 / 64 : ℝ)) * (1 + H) ^ (3 : ℕ) := by
  let eta : ℝ := 1 / (64 * (1 + zeta))
  have hden : 0 < 64 * (1 + zeta) := by positivity
  have heta : 0 < eta := div_pos zero_lt_one hden
  have hetaz : eta < 3 / zeta := by
    dsimp only [eta]
    apply (div_lt_div_iff₀ hden hzeta).mpr
    nlinarith
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_large_tail_before_normalizer_bound K S mu nu
    hcomplex P psi hcal hunram g T hzeta heta hetaz
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z H hZ hH
  apply (hb Z H hZ hH).trans
  have hexp : -17 / 32 + (13 / 16 + zeta) * eta ≤ -(33 / 64 : ℝ) := by
    have hsmall : (13 / 16 + zeta) * eta ≤ 1 / 64 := by
      have h := mul_le_mul_of_nonneg_right (show 13 / 16 + zeta ≤ 1 + zeta by linarith) heta.le
      have heq : (1 + zeta) * eta = 1 / 64 := by
        dsimp only [eta]
        field_simp [show 1 + zeta ≠ 0 by positivity]
        <;> ring
      exact h.trans_eq heq
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hZ0.trans hZ) hexp) (by positivity)) (by positivity)

end HeckeSkeleton.Expansion.LargeRows

#print axioms HeckeSkeleton.Expansion.LargeRows.summable_actual_absoluteLargeRowTerm
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_tail_before_normalizer_bound
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_large_tail_fixed_saving
