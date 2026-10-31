import Expansion.ActualOuterKernelDecay
import Expansion.ActualOuterContourTransport
import HeckeSkeleton.ExpansionModels.LargeRowTail

/-!+# Actual outer horizontal faces with arbitrary height savings

The six faces are the literal finite rectangle integrals.  Uniform rapid
decay of the complete actual kernel absorbs their two remaining height
integrations.  The small-row exponent remains visible; the large-row
majorant is summable on the original complete frequency-row set.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.LargeRows
open scoped Classical BigOperators Topology

theorem coordinate_le_tripleHeightWeight (n : ℕ) (s w z : ℝ) :
    (1 + |s|) ^ n ≤ tripleHeightWeight n s w z ∧
      (1 + |w|) ^ n ≤ tripleHeightWeight n s w z ∧
        (1 + |z|) ^ n ≤ tripleHeightWeight n s w z := by
  have hs : 1 ≤ (1 + |s|) ^ n := one_le_pow₀ (by linarith [abs_nonneg s])
  have hw : 1 ≤ (1 + |w|) ^ n := one_le_pow₀ (by linarith [abs_nonneg w])
  have hz : 1 ≤ (1 + |z|) ^ n := one_le_pow₀ (by linarith [abs_nonneg z])
  unfold tripleHeightWeight
  constructor
  · exact (le_mul_of_one_le_right (by positivity) hw).trans
      (le_mul_of_one_le_right (by positivity) hz)
  constructor
  · exact (le_mul_of_one_le_left (by positivity) hs).trans
      (le_mul_of_one_le_right (by positivity) hz)
  · exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hs hw)

theorem norm_le_div_of_tripleHeightWeight (n : ℕ) (s w z H M : ℝ) (v : ℂ)
    (hH : 0 ≤ H) (hface : |s| = H ∨ |w| = H ∨ |z| = H)
    (hb : tripleHeightWeight n s w z * ‖v‖ ≤ M) :
    ‖v‖ ≤ M / (1 + H) ^ n := by
  have hcoord : (1 + H) ^ n ≤ tripleHeightWeight n s w z := by
    obtain ⟨hs, hw, hz⟩ := coordinate_le_tripleHeightWeight n s w z
    rcases hface with he | he | he
    · simpa only [he] using hs
    · simpa only [he] using hw
    · simpa only [he] using hz
  apply (le_div_iff₀ (by positivity : 0 < (1 + H) ^ n)).mpr
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_right hcoord (norm_nonneg v)).trans hb

theorem horizontal_height_volume_le (M L H : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hH : 0 ≤ H) :
    (2 * (M / (1 + H) ^ (n + 2)) * L) * (2 * H) ^ 2 ≤
      8 * M * L / (1 + H) ^ n := by
  have hbase : 0 < 1 + H := by linarith
  have hsquare : H ^ 2 ≤ (1 + H) ^ 2 := pow_le_pow_left₀ hH (by linarith) 2
  rw [pow_add]
  apply (le_div_iff₀ (pow_pos hbase n)).mpr
  calc
    _ = 8 * M * L * H ^ 2 / (1 + H) ^ 2 := by
      field_simp [hbase.ne', (pow_pos hbase n).ne']
      <;> ring
    _ ≤ 8 * M * L * (1 + H) ^ 2 / (1 + H) ^ 2 := by gcongr
    _ = 8 * M * L := by field_simp [hbase.ne']

/-- All three pairs of actual faces inherit any prescribed height loss.
The power two spent here is exactly their two finite height directions. -/
theorem norm_three_faces_le_of_rapid
    (F : ℂ → ℂ → ℂ → ℂ) (H s0 s1 w0 w1 z0 z1 M : ℝ) (n : ℕ)
    (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hb : ∀ s w z : ℂ,
      (s, w, z) ∈ FiniteTripleContour.sweptTube s0 s1 w0 w1 z0 z1 →
        tripleHeightWeight (n + 2) s.im w.im z.im * ‖F s w z‖ ≤ M) :
    ‖FiniteTripleContour.sFaces F H s0 s1 w0 z0 +
      FiniteTripleContour.wFaces F H s1 w0 w1 z0 +
        FiniteTripleContour.zFaces F H s1 w1 z0 z1‖ ≤
      8 * M * (|s0 - s1| + |w0 - w1| + |z0 - z1|) / (1 + H) ^ n := by
  have hpoint (sigma nu zeta ts tw tz : ℝ)
      (hs : sigma ∈ uIcc s0 s1) (hw : nu ∈ uIcc w0 w1) (hz : zeta ∈ uIcc z0 z1)
      (hface : |ts| = H ∨ |tw| = H ∨ |tz| = H) :
      ‖F (FiniteTripleContour.vertical sigma ts) (FiniteTripleContour.vertical nu tw)
        (FiniteTripleContour.vertical zeta tz)‖ ≤ M / (1 + H) ^ (n + 2) := by
    have hm : (FiniteTripleContour.vertical sigma ts, FiniteTripleContour.vertical nu tw,
        FiniteTripleContour.vertical zeta tz) ∈
          FiniteTripleContour.sweptTube s0 s1 w0 w1 z0 z1 := by
      simpa [FiniteTripleContour.sweptTube, FiniteTripleContour.vertical] using
        And.intro hs (And.intro hw hz)
    have hp := hb _ _ _ hm
    simp only [FiniteTripleContour.vertical, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] at hp
    exact norm_le_div_of_tripleHeightWeight (n + 2) ts tw tz H M _ hH hface hp
  have hsface : ‖FiniteTripleContour.sFaces F H s0 s1 w0 z0‖ ≤
      8 * M * |s0 - s1| / (1 + H) ^ n := by
    apply (FiniteTripleContour.norm_sFaces_le F H s0 s1 w0 z0
      (M / (1 + H) ^ (n + 2)) hH ?_ ?_).trans
        (horizontal_height_volume_le M |s0 - s1| H n hM (abs_nonneg _) hH)
    · intro tw _ tz _ x hx
      exact hpoint x w0 z0 (-H) tw tz hx left_mem_uIcc left_mem_uIcc
        (Or.inl (by rw [abs_neg, abs_of_nonneg hH]))
    · intro tw _ tz _ x hx
      exact hpoint x w0 z0 H tw tz hx left_mem_uIcc left_mem_uIcc
        (Or.inl (abs_of_nonneg hH))
  have hwface : ‖FiniteTripleContour.wFaces F H s1 w0 w1 z0‖ ≤
      8 * M * |w0 - w1| / (1 + H) ^ n := by
    apply (FiniteTripleContour.norm_wFaces_le F H s1 w0 w1 z0
      (M / (1 + H) ^ (n + 2)) hH ?_ ?_).trans
        (horizontal_height_volume_le M |w0 - w1| H n hM (abs_nonneg _) hH)
    · intro ts _ tz _ x hx
      exact hpoint s1 x z0 ts (-H) tz right_mem_uIcc hx left_mem_uIcc
        (Or.inr (Or.inl (by rw [abs_neg, abs_of_nonneg hH])))
    · intro ts _ tz _ x hx
      exact hpoint s1 x z0 ts H tz right_mem_uIcc hx left_mem_uIcc
        (Or.inr (Or.inl (abs_of_nonneg hH)))
  have hzface : ‖FiniteTripleContour.zFaces F H s1 w1 z0 z1‖ ≤
      8 * M * |z0 - z1| / (1 + H) ^ n := by
    apply (FiniteTripleContour.norm_zFaces_le F H s1 w1 z0 z1
      (M / (1 + H) ^ (n + 2)) hH ?_ ?_).trans
        (horizontal_height_volume_le M |z0 - z1| H n hM (abs_nonneg _) hH)
    · intro ts _ tw _ x hx
      exact hpoint s1 w1 x ts tw (-H) right_mem_uIcc right_mem_uIcc hx
        (Or.inr (Or.inr (by rw [abs_neg, abs_of_nonneg hH])))
    · intro ts _ tw _ x hx
      exact hpoint s1 w1 x ts tw H right_mem_uIcc right_mem_uIcc hx
        (Or.inr (Or.inr (abs_of_nonneg hH)))
  apply ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
  exact (add_le_add (add_le_add hsface hwface) hzface).trans_eq (by ring)

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
/-- The small-row horizontal estimate is uniform before the row cutoff
is imposed, with the original common zero boundary as its only zero input. -/
theorem exists_actual_small_horizontal_row_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
        ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H (B + e) (1 / 2) (17 / 50)‖ ≤
          C * Z ^ (outerBoundaryScalePower 5 5 3) *
            frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n := by
  obtain ⟨Ck, Z0, hCk, hZ0, hk⟩ := exists_actual_small_sweep_kernel_rapid
    K S mu nu hcomplex P omega psi hpsi hAllowed hcal hunram g hB hB1 he he1 hboundary (n + 2)
  let L : ℝ := |5 - (B + e)| + |(5 : ℝ) - 1 / 2| + |(3 : ℝ) - 17 / 50|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * 8 * Ck * (L + 1), Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH u hu
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  let M : ℝ := Ck * Z ^ (outerBoundaryScalePower 5 5 3) *
    frequencyRowNorm K Sset u ^ (113 / 50 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hf := norm_three_faces_le_of_rapid
    (compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u Z) H 5 (B + e) 5 (1 / 2) 3 (17 / 50) M n hH hM (by
      intro s w z hv
      have hs : s.re ∈ Icc (B + e) 5 := by
        simpa only [FiniteTripleContour.sweptTube, mem_setOf_eq,
          uIcc_of_ge (by linarith : B + e ≤ 5)] using hv.1
      have hw : w.re ∈ Icc (1 / 2) 5 := by
        simpa only [uIcc_of_ge (by norm_num : (1 / 2 : ℝ) ≤ 5)] using hv.2.1
      have hz : z.re ∈ Icc (17 / 50) 3 := by
        simpa only [uIcc_of_ge (by norm_num : (17 / 50 : ℝ) ≤ 3)] using hv.2.2
      exact hk Z hZ u hu s w z hs.1 hs.2 hw.1 hw.2 hz.1 hz.2)
  unfold actualOuterHorizontalFaces
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hf hkappa).trans
  dsimp only [M]
  have hcoef : kappa * L ≤ (kappa + 1) * (L + 1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ 8 * Ck * Z ^ (outerBoundaryScalePower 5 5 3) *
      frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n by positivity)
  convert hh using 1 <;> dsimp only [L, kappa] <;> ring

include nu in
/-- The complete large swept tube has a summable row majorant, uniformly
in Z and H.  This does not assume convergence of a contour series. -/
theorem exists_actual_large_horizontal_row_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ∀ u : FrequencyRow K Sset, ¬principalFrequencyRow K Sset u →
        ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H 2 2 (1 + 3 / zeta)‖ ≤
          C * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
            frequencyRowNorm K Sset u ^ largeSweepRowPower zeta / (1 + H) ^ n := by
  obtain ⟨Ck, Z0, hCk, hZ0, hk⟩ := exists_actual_large_sweep_kernel_rapid
    K S mu nu hcomplex P psi hcal hunram g hzeta (n + 2)
  let L : ℝ := |(5 : ℝ) - 2| + |(5 : ℝ) - 2| + |3 - (1 + 3 / zeta)|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * 8 * Ck * (L + 1), Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH u hu
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hNpos : 0 < frequencyRowNorm K Sset u := idealNorm_pos K u.ideal.val
  let M : ℝ := Ck * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
    frequencyRowNorm K Sset u ^ largeSweepRowPower zeta
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hf := norm_three_faces_le_of_rapid
    (compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u Z) H 5 2 5 2 3 (1 + 3 / zeta) M n hH hM (by
      intro s w z hv
      have hs : s.re ∈ Icc 2 5 := by
        simpa only [uIcc_of_ge (by norm_num : (2 : ℝ) ≤ 5)] using hv.1
      have hw : w.re ∈ Icc 2 5 := by
        simpa only [uIcc_of_ge (by norm_num : (2 : ℝ) ≤ 5)] using hv.2.1
      exact hk Z hZ u hu s w z hs.1 hs.2 hw.1 hw.2 hv.2.2.1 hv.2.2.2)
  unfold actualOuterHorizontalFaces
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hf hkappa).trans
  dsimp only [M]
  have hcoef : kappa * L ≤ (kappa + 1) * (L + 1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ 8 * Ck * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
      frequencyRowNorm K Sset u ^ largeSweepRowPower zeta / (1 + H) ^ n by positivity)
  convert hh using 1 <;> dsimp only [L, kappa] <;> ring

include nu in
/-- The original finite small-row enumeration costs only its actual
linear count and the explicit nonnegative conductor power. -/
theorem exists_actual_small_horizontal_sum_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      ‖actualSmallRowHorizontalFaces K S mu P psi g ∅ Z H B e‖ ≤
        C * Z ^ (outerBoundaryScalePower 5 5 3 + 163 / 800) / (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_small_horizontal_row_bound
    K S mu nu hcomplex P omega psi hpsi hAllowed hcal hunram g hB hB1 he he1 hboundary n
  obtain ⟨Cc, hCc, hcount⟩ := frequencyRows_linear_count K Sset
  refine ⟨Cr * Cc, Z0, mul_pos hCr hCc, hZ0, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let U : ℝ := Z ^ (1 / 16 : ℝ)
  have hU : 1 ≤ U := Real.one_le_rpow hZ1 (by norm_num)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  let rows := (frequencyRows K Sset U).filter
    (fun u => 0 < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u)
  have hmass : ∑ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) ≤
      Cc * U ^ (163 / 50 : ℝ) := by
    have hterm : ∀ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) ≤
        U ^ (113 / 50 : ℝ) := by
      intro u hu
      have hn := (mem_frequencyRows_iff K Sset U hUpos.le u).mp (Finset.mem_filter.mp hu).1
      exact Real.rpow_le_rpow (idealNorm_pos K u.ideal.val).le hn (by norm_num)
    have hcard : (rows.card : ℝ) ≤ Cc * U :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))).trans (hcount U hU)
    calc
      _ ≤ ∑ _u ∈ rows, U ^ (113 / 50 : ℝ) := Finset.sum_le_sum hterm
      _ = (rows.card : ℝ) * U ^ (113 / 50 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Cc * U) * U ^ (113 / 50 : ℝ) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cc * U ^ (163 / 50 : ℝ) := by
        rw [show (163 / 50 : ℝ) = 1 + 113 / 50 by norm_num, Real.rpow_add hUpos, Real.rpow_one]
        ring
  have hscale : Z ^ (outerBoundaryScalePower 5 5 3) * U ^ (163 / 50 : ℝ) =
      Z ^ (outerBoundaryScalePower 5 5 3 + 163 / 800) := by
    dsimp only [U]
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
    congr 1
    ring
  change ‖∑ u ∈ rows, actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
    (B + e) (1 / 2) (17 / 50)‖ ≤ _
  calc
    _ ≤ ∑ u ∈ rows, ‖actualOuterHorizontalFaces K S mu P psi g ∅ u Z H
        (B + e) (1 / 2) (17 / 50)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ rows, Cr * Z ^ (outerBoundaryScalePower 5 5 3) *
        frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) / (1 + H) ^ n :=
      Finset.sum_le_sum (fun u hu => hr Z H hZ hH u (Finset.mem_filter.mp hu).2.2)
    _ = (Cr * Z ^ (outerBoundaryScalePower 5 5 3) / (1 + H) ^ n) *
        ∑ u ∈ rows, frequencyRowNorm K Sset u ^ (113 / 50 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (Cr * Z ^ (outerBoundaryScalePower 5 5 3) / (1 + H) ^ n) *
        (Cc * U ^ (163 / 50 : ℝ)) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cr * Cc) * (Z ^ (outerBoundaryScalePower 5 5 3) * U ^ (163 / 50 : ℝ)) /
        (1 + H) ^ n := by ring
    _ = _ := by rw [hscale]

def actualLargeHorizontalFaces
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H zeta : ℝ) : ℂ :=
  ∑' u : {u : FrequencyRow K Sset // Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u},
    actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2 (1 + 3 / zeta)

include nu in
/-- The literal infinite large-row horizontal sum is absolutely convergent
and has arbitrary height loss.  Its threshold precedes both Z and H. -/
theorem exists_actual_large_horizontal_sum_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) (n : ℕ) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 0 ≤ H →
      Summable (fun u : {u : FrequencyRow K Sset //
          Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u} =>
        ‖actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖) ∧
      ‖actualLargeHorizontalFaces K S mu P psi g Z H zeta‖ ≤
        C * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta) +
          (13 / 16 + zeta) * (largeSweepRowPower zeta + 1)) / (1 + H) ^ n := by
  obtain ⟨Cr, Z0, hCr, hZ0, hr⟩ := exists_actual_large_horizontal_row_bound
    K S mu nu hcomplex P psi hcal hunram g hzeta n
  obtain ⟨Ct, hCt, ht⟩ := exists_frequencyRowNorm_power_tail_bound K Sset
    (largeSweepRowPower_lt_neg_one hzeta)
  refine ⟨Cr * Ct, Z0, mul_pos hCr hCt, hZ0, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  let U : ℝ := Z ^ (13 / 16 + zeta)
  have hU : 1 ≤ U := Real.one_le_rpow hZ1 (by linarith)
  let rows := {u : FrequencyRow K Sset // U < frequencyRowNorm K Sset u}
  let D : ℝ := Cr * Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) / (1 + H) ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrow (u : rows) :
      ‖actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖ ≤
        D * frequencyRowNorm K Sset u.val ^ largeSweepRowPower zeta := by
    have hnon : ¬principalFrequencyRow K Sset u.val := by
      intro hp
      have hh := hU.trans_lt u.property
      rw [frequencyRowNorm_of_principal K S u.val hp] at hh
      exact (lt_irrefl (1 : ℝ)) hh
    exact (hr Z H hZ hH u.val hnon).trans_eq (by dsimp [D]; ring)
  obtain ⟨hsum, htail⟩ := ht U hU
  have hn : Summable (fun u : rows =>
      ‖actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖) :=
    (hsum.mul_left D).of_nonneg_of_le (fun _ => norm_nonneg _) hrow
  refine ⟨hn, ?_⟩
  have hscale : Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
      U ^ (largeSweepRowPower zeta + 1) =
      Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta) +
        (13 / 16 + zeta) * (largeSweepRowPower zeta + 1)) := by
    dsimp only [U]
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  change ‖∑' u : rows,
    actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖ ≤ _
  calc
    _ ≤ ∑' u : rows, ‖actualOuterHorizontalFaces K S mu P psi g ∅ u.val Z H 2 2
        (1 + 3 / zeta)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' u : rows, D * frequencyRowNorm K Sset u.val ^ largeSweepRowPower zeta :=
      hn.tsum_le_tsum hrow (hsum.mul_left D)
    _ = D * ∑' u : rows, frequencyRowNorm K Sset u.val ^ largeSweepRowPower zeta := tsum_mul_left
    _ ≤ D * (Ct * U ^ (largeSweepRowPower zeta + 1)) :=
      mul_le_mul_of_nonneg_left htail hD
    _ = (Cr * Ct) * (Z ^ (outerBoundaryScalePower 5 5 (largeSweepUpper zeta)) *
        U ^ (largeSweepRowPower zeta + 1)) / (1 + H) ^ n := by dsimp [D]; ring
    _ = _ := by rw [hscale]

end Expansion.Project

#print axioms Expansion.Project.exists_actual_small_horizontal_row_bound
#print axioms Expansion.Project.exists_actual_large_horizontal_row_bound
#print axioms Expansion.Project.exists_actual_small_horizontal_sum_bound
#print axioms Expansion.Project.exists_actual_large_horizontal_sum_bound
