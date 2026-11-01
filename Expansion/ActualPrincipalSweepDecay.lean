import Expansion.ActualPrincipalInitialTransport
import Expansion.ActualOuterHeightBudget
import Expansion.PowerHeightTailAlgebra

/-!
# Rapid decay on the complete actual principal initial sweep

The empty original row support controls the full correction all the way
up to Re z = 3.  The two zeta numerators are in their actual absolute Euler
regions on this initial sweep.  A fixed polynomial bound for the original
target reciprocal is absorbed by the coupled Gaussian and the actual
additive Mellin profile.  The scale exponent 14 is fixed for every height
order; it is used only for genuine horizontal and truncation errors.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.PrincipalRows
open HeckeSkeleton.HighBinContinuation
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeDeletedEulerControl
open HighBinVerified.NormFormFullCorrection HighBinVerified.NormFormActual
open scoped Classical Topology BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Extending the principal rectangle to z=3 costs only the fixed prime
power q^2 in each original slot, with no ramified-row loss. -/
theorem exists_actual_principal_fullCorrection_sweep_bound
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (g : PrimeWindowGeometry) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (T : Finset (HeckeCharacter K)) (u : FrequencyRow K S), exteriorSupport K S u.ideal = ∅ →
      ∀ s w z : ℂ, 7 / 8 ≤ s.re → 19 / 20 ≤ w.re → 33 / 200 ≤ z.re → z.re ≤ 3 →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤ C * Z ^ (1 / 2 : ℝ) := by
  obtain ⟨Z0, hZ0, hcut⟩ := exists_principal_window_local_cutoff K S g
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  obtain ⟨A, hA, hcount⟩ := exists_primeWindow_linear_count K S
  let Creg : ℝ := 1 + 48 / sweptTubeEulerMargin
  have hCreg : 0 < Creg := by dsimp [Creg]; have := sweptTubeEulerMargin_pos; positivity
  let Cs : ℝ := 4 * A * M * Creg
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hCe := principalEulerConstant_pos K S
  refine ⟨principalEulerConstant K S * Cs ^ g.slots, Z0, by positivity, hZ0, ?_⟩
  intro Z hZ P psi hpsi T u hrow s w z hs hw hz hz3
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hJ : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hX : 1 ≤ primeScale g Z := Real.one_le_rpow hZ1 (div_pos (by norm_num) hJ).le
  have hXpos : 0 < primeScale g Z := zero_lt_one.trans_le hX
  have hne : ∀ i : Fin g.slots, ∀ p ∈ primeWindow K S g T Z i,
      actualLocalUnmarked K S P psi u s w z p ≠ 0 := by
    intro i p hp hh
    have hb := hcut Z hZ P psi T u hrow s w z hs hw hz i p hp
    rw [hh, zero_sub, norm_neg, norm_one] at hb
    norm_num at hb
  have hslot (i : Fin g.slots) :
      ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖ ≤ Cs * (primeScale g Z) ^ (3 : ℝ) := by
    have hterm (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
        ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ ≤
          (4 * M * Creg) * (primeScale g Z) ^ (2 : ℝ) := by
      have hlocal := actualLocalCompensation_principal_rectangle_bound K S P psi u s w z hs hw hz p
        (by simp only [hrow, Finset.notMem_empty, not_false_eq_true]) (hpsi p)
        (hcut Z hZ P psi T u hrow s w z hs hw hz i p hp)
      have hq1 : 1 ≤ (p.val.asIdeal.absNorm : ℝ) :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (exteriorPrime_norm_two_le K S p)
      have hpow : (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1) ≤
          4 * (primeScale g Z) ^ (2 : ℝ) := by
        calc
          _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
          _ ≤ (2 * primeScale g Z) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _)
              (actual_primeWindow_norm_range K S g T Z i p hp).2.2.le (by norm_num)
          _ = _ := by rw [Real.mul_rpow (by norm_num) hXpos.le]; norm_num
      rw [norm_mul]
      calc
        _ ≤ M * (Creg * (p.val.asIdeal.absNorm : ℝ) ^ (z.re - 1)) :=
          mul_le_mul (hprofile i _) hlocal (norm_nonneg _) hM.le
        _ ≤ M * (Creg * (4 * (primeScale g Z) ^ (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpow hCreg.le) hM.le
        _ = _ := by ring
    have hcard := hcount g T Z i hX
    unfold actualFullCorrectionSlot
    calc
      _ ≤ ∑ p ∈ primeWindow K S g T Z i,
          ‖windowWeight K S g Z i p * actualLocalCompensation K S P psi u s w z p‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ primeWindow K S g T Z i, (4 * M * Creg) * (primeScale g Z) ^ (2 : ℝ) :=
        Finset.sum_le_sum hterm
      _ = ((primeWindow K S g T Z i).card : ℝ) * ((4 * M * Creg) * (primeScale g Z) ^ (2 : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A * primeScale g Z) * ((4 * M * Creg) * (primeScale g Z) ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by norm_num only [Real.rpow_ofNat]; dsimp only [Cs]; ring
  rw [actualFullCorrection_eq_product_region K S P psi g T u Z s w z
    (principal_rectangle_mem_rowEulerRegion s w z hs hw hz) hne, norm_mul, norm_prod]
  have he := actual_principal_unmarked_bound K S P psi u hrow s w z hs hw hz
  have hp : (∏ i : Fin g.slots, ‖actualFullCorrectionSlot K S P psi g T u Z s w z i‖) ≤
      (Cs * (primeScale g Z) ^ (3 : ℝ)) ^ g.slots := by
    calc
      _ ≤ ∏ _i : Fin g.slots, Cs * (primeScale g Z) ^ (3 : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hslot i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hscale : ((primeScale g Z) ^ (3 : ℝ)) ^ g.slots = Z ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hXpos.le]
    unfold primeScale
    rw [← Real.rpow_mul hZpos.le]
    congr 1
    field_simp [hJ.ne']
    <;> ring
  exact (mul_le_mul he hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hCe.le).trans_eq (by
    rw [mul_pow, hscale]
    ring)

private theorem exists_actual_target_sweep_reciprocal_bound
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧ ∀ s : ℂ, B + e ≤ s.re →
      ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S) s)⁻¹‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨C, k, hC, hk, hb⟩ := exists_actual_target_strip_reciprocal_bound
    K S hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨D, hD, hd⟩ := exists_deleted_reciprocal_right_bound K S (sigma := 2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_ge k
  refine ⟨C * (4 : ℝ) ^ k + D, n, by positivity, ?_⟩
  intro s hs
  have hbase : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  by_cases hs2 : s.re ≤ 2
  · apply (hb s hs hs2).trans
    have hh := shifted_height_rpow_le_nat 4 k n (by norm_num) hk hn s.im
    apply (mul_le_mul_of_nonneg_left hh hC.le).trans
    nlinarith [show 0 ≤ D * (1 + |s.im|) ^ n by positivity]
  · have hh := hd psi s (by linarith)
    apply hh.trans
    have hp : 1 ≤ (1 + |s.im|) ^ n := one_le_pow₀ hbase
    nlinarith [show 0 ≤ (C * (4 : ℝ) ^ k) * (1 + |s.im|) ^ n by positivity]

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

include nu in
theorem exists_actual_principal_sweep_kernel_rapid
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ s w z : ℂ, B + e ≤ s.re → s.re ≤ 5 → 1 + e ≤ w.re → w.re ≤ 5 →
        1 / 6 + e ≤ z.re → z.re ≤ 3 →
        tripleHeightWeight n s.im w.im z.im *
          ‖compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
            g ∅ (physicalPrincipalRow K Sset) Z s w z‖ ≤ C * Z ^ (14 : ℝ) := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  obtain ⟨Cr, kr, hCr, hr⟩ := exists_actual_target_sweep_reciprocal_bound
    K Sset hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨Ch, Zh, hCh, hZh, hh⟩ := exists_actual_principal_fullCorrection_sweep_bound K Sset g
  obtain ⟨Zn, hZn, hn⟩ := exists_actual_primeNormalizer_inverse_bound K Sset hcomplex g 1 zero_lt_one
  obtain ⟨Clw, hClw, hlw⟩ := exists_uniform_rightHalfPlane_bound K (1 + e) (by linarith)
  obtain ⟨Clz, hClz, hlz⟩ := exists_uniform_rightHalfPlane_bound K (1 + 6 * e) (by linarith)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K Sset)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K Sset)
  let Cp : ℝ := ‖(physicalPoissonScalar K : ℂ)‖
  let Cm : ℝ := ‖(physicalResidueNormalizer K Sset muS P)⁻¹‖
  let C0 : ℝ := Cp * Real.exp 81 * ((F * Clz) * (F * Clw) * Cr) * Ch * Cm
  have hC0 : 0 ≤ C0 := by dsimp [C0, Cp, Cm]; positivity
  refine ⟨max Zh Zn, hZh.trans (le_max_left _ _), ?_⟩
  intro n
  obtain ⟨Ca, hCa, ha⟩ := exists_actual_additiveMellin_strip_rapid_bound K S mu nu
    P.additive (1 / 6 + e) 3 (by linarith) (by linarith) (2 * n + kr)
  obtain ⟨Cd, hCd, hd⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator.toSmoothAnnularTest (1 + e) 5 n
  let D : ℝ := HighBinBoundary.gaussianMoment (n + kr) * Ca * Cd
  have hD : 0 < D := by dsimp [D]; exact mul_pos (mul_pos (HighBinBoundary.gaussianMoment_pos _) hCa) hCd
  refine ⟨(C0 + 1) * D, by positivity, ?_⟩
  intro Z hZ s w z hs hs5 hw hw5 hz hz3
  have hZH : Zh ≤ Z := (le_max_left _ _).trans hZ
  have hZN : Zn ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZh.trans hZH
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hnormal : ‖(primeNormalizer K Sset g ∅ Z)⁻¹‖ ≤ Z := by
    simpa only [Real.rpow_one] using (hn Z hZN).2
  have hcor0 := hh Z hZH P psi hunram ∅ (physicalPrincipalRow K Sset)
    (physicalPrincipalRow_support K Sset) s w z (by linarith) (by linarith) (by linarith) hz3
  have hcor : ‖compensatedRowFullCorrection K Sset P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z s w z‖ ≤ Ch * Z :=
    hcor0.trans (mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq
        (Real.rpow_one _)) hCh.le)
  have hrec := hr s hs
  have hadd : (1 + |z.im|) ^ (2 * n + kr) * ‖additiveMellin K Sset muS P.additive z‖ ≤ Ca := by
    simpa only [Complex.re_add_im] using ha z.re ⟨hz, hz3⟩ z.im
  have hden : (1 + |w.im|) ^ n * ‖mellin P.denominator.toFun w‖ ≤ Cd := by
    simpa only [Complex.re_add_im] using hd w.re w.im hw hw5
  have hzet : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) (6 * z)‖ ≤ F * Clz := by
    have hzr : 1 + 6 * e ≤ (6 * z).re := by simp; linarith
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) 1 (6 * z) (by linarith))
      (hlz 1 (6 * z) hzr) (norm_nonneg _) hF.le
  have hnum : ‖heckeDeletedContinuation K 1 (exceptionalPrimes K Sset) w‖ ≤ F * Clw := by
    rw [heckeDeletedContinuation, norm_mul]
    exact mul_le_mul
      (norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K Sset) 1 w (by linarith))
      (hlw 1 w hw) (norm_nonneg _) hF.le
  have hgauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤
      Real.exp 81 * Real.exp (-((s.im + z.im) ^ 2)) := by
    have hs0 : 0 ≤ s.re + z.re - 1 := by linarith
    have hs9 : s.re + z.re - 1 ≤ 9 := by linarith
    have hsquare := pow_le_pow_left₀ hs0 hs9 2
    have heq : ((s + z - 1) ^ 2).re =
        (s.re + z.re - 1) ^ 2 - (s.im + z.im) ^ 2 := by
      simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.add_re,
        Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero]
    rw [Complex.norm_exp, heq, sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_nonneg _)
  have hxpow : ‖((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z)‖ ≤ Z := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _)]
    have hre : ((1 / 2 : ℂ) - z).re = (1 / 2 : ℝ) - z.re := by simp
    rw [hre, ← Real.rpow_mul hZpos.le]
    exact (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)).trans_eq (Real.rpow_one _)
  have hzpow : ‖(Z : ℂ) ^ (s + z - 1)‖ ≤ Z ^ (8 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos, Complex.sub_re, Complex.add_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hypow : ‖((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1)‖ ≤ Z ^ (3 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZpos _),
      Complex.sub_re, Complex.one_re, ← Real.rpow_mul hZpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hkernel : ‖compensatedRowMellinKernel K Sset muS P psi
      (arithmeticHighEulerData K Sset P psi) g ∅ (physicalPrincipalRow K Sset) Z s w z‖ ≤
      (C0 * Z ^ (14 : ℝ)) *
        (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K Sset muS P.additive z‖ *
          ‖mellin P.denominator.toFun w‖ * (1 + |s.im|) ^ kr * (1 + |w.im|) ^ (0 : ℕ)) := by
    rw [actualPrincipalKernel_eq_core K S mu P psi hAllowed g Z hZpos]
    rw [actualPrincipalKernelCore,
      div_eq_mul_inv _
        (physicalResidueNormalizer K Sset muS P * primeNormalizer K Sset g ∅ Z),
      div_eq_mul_inv _
        (heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s)]
    simp only [mul_inv, norm_mul]
    calc
      _ ≤ Cp * (Real.exp 81 * Real.exp (-((s.im + z.im) ^ 2))) *
          ‖additiveMellin K Sset muS P.additive z‖ * ‖mellin P.denominator.toFun w‖ *
          Z * Z ^ (8 : ℝ) * Z ^ (3 : ℝ) *
          ((F * Clz) * (F * Clw) * (Cr * (1 + |s.im|) ^ kr)) * (Ch * Z) * (Cm * Z) := by
        change Cp * _ * _ * _ * _ * _ * _ * (_ * _ * _) * _ * (Cm * _) ≤ _
        gcongr
      _ = _ := by
        dsimp only [C0]
        norm_num only [Real.rpow_ofNat, pow_zero]
        ring
  have hweights := coupled_three_height_bound n kr 0 s.im w.im z.im
    ‖additiveMellin K Sset muS P.additive z‖ ‖mellin P.denominator.toFun w‖ Ca Cd
    (norm_nonneg _) (norm_nonneg _) hCa.le hadd (by simpa using hden)
  calc
    _ ≤ tripleHeightWeight n s.im w.im z.im * ((C0 * Z ^ (14 : ℝ)) *
        (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K Sset muS P.additive z‖ *
          ‖mellin P.denominator.toFun w‖ * (1 + |s.im|) ^ kr * (1 + |w.im|) ^ (0 : ℕ))) :=
      mul_le_mul_of_nonneg_left hkernel (tripleHeightWeight_nonneg _ _ _ _)
    _ = (C0 * Z ^ (14 : ℝ)) * (tripleHeightWeight n s.im w.im z.im *
        (Real.exp (-((s.im + z.im) ^ 2)) * ‖additiveMellin K Sset muS P.additive z‖ *
          ‖mellin P.denominator.toFun w‖ * (1 + |s.im|) ^ kr * (1 + |w.im|) ^ (0 : ℕ))) := by ring
    _ ≤ (C0 * Z ^ (14 : ℝ)) * D := mul_le_mul_of_nonneg_left hweights (by positivity)
    _ ≤ _ := by dsimp only [D]; nlinarith [show 0 ≤ Z ^ (14 : ℝ) * D by positivity]

include nu in
theorem actualPrincipal_initial_horizontal_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (fun Z H => actualPrincipalInitialHorizontal K S mu P psi g Z H B e) := by
  obtain ⟨Z0, hZ0, hrapid⟩ := exists_actual_principal_sweep_kernel_rapid K S mu nu
    hcomplex P omega psi hpsi hAllowed hunram g hB hB1 he he1 hboundary
  apply PowerHeightTailBound.of_uniform_decay (A := 0) (R := 14) le_rfl
  intro N
  obtain ⟨C, hC, hc⟩ := hrapid (N + 2)
  let L : ℝ := |5 - (B + e)| + |5 - (1 + e)| + |3 - (1 / 6 + e)|
  let kappa : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hkappa : 0 ≤ kappa := norm_nonneg _
  refine ⟨(kappa + 1) * 8 * C * (L + 1), Z0, by positivity, hZ0, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hf := norm_three_faces_le_of_rapid
    (compensatedRowMellinKernel K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z)
    H 5 (B + e) 5 (1 + e) 3 (1 / 6 + e) (C * Z ^ (14 : ℝ)) N
    (by linarith) (by positivity) (by
      intro s w z hv
      have hs : s.re ∈ Icc (B + e) 5 := by
        simpa only [uIcc_of_ge (by linarith : B + e ≤ 5)] using hv.1
      have hw : w.re ∈ Icc (1 + e) 5 := by
        simpa only [uIcc_of_ge (by linarith : 1 + e ≤ 5)] using hv.2.1
      have hz : z.re ∈ Icc (1 / 6 + e) 3 := by
        simpa only [uIcc_of_ge (by linarith : 1 / 6 + e ≤ 3)] using hv.2.2
      exact hc Z hZ s w z hs.1 hs.2 hw.1 hw.2 hz.1 hz.2)
  have hheight : ((1 + H) ^ N)⁻¹ ≤ H ^ (-(N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith : 0 ≤ 1 + H)]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
      (by linarith [show (0 : ℝ) ≤ (N : ℝ) by positivity])
  unfold actualPrincipalInitialHorizontal
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hf hkappa).trans
  have hcoef : kappa * L ≤ (kappa + 1) * (L + 1) := by nlinarith
  simp only [Real.rpow_zero, mul_one, div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hheight
    (show 0 ≤ kappa * 8 * C * Z ^ (14 : ℝ) * L by positivity)
  have hh' := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ 8 * C * Z ^ (14 : ℝ) * H ^ (-(N : ℝ)) by positivity)
  dsimp only [L, kappa] at hh hh' ⊢
  nlinarith [hh, hh']

end Expansion.Project

#print axioms Expansion.Project.exists_actual_principal_fullCorrection_sweep_bound
#print axioms Expansion.Project.exists_actual_principal_sweep_kernel_rapid
#print axioms Expansion.Project.actualPrincipal_initial_horizontal_tail
