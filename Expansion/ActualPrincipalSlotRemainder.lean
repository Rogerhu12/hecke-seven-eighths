import Expansion.ActualPrimeNormalizer
import HeckeSkeleton.ActualPrincipalWindowError
import HeckeSkeleton.ExpansionModels.SmallRowReciprocal
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual finite-height principal slot remainder

Both line integrals below use the original Gaussian, the actual deleted
target continuation, and the same line s = B+e+it. Their difference retains
the literal compensated-principal correction divided by the original
normalizer. The relative window error cancels that denominator only after
the proved normalizer positivity supplies nonvanishing. Measurability and
finite-line integrability justify subtracting the two actual integrals.
This module makes no assertion identifying line 2 with line B+e.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set Filter MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualPrincipalWindowDraft
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckeUniformBufferedControl HeckeSkeleton.HeckeDeletedEulerControl
open HeckeSkeleton.HeckeConductorNorm ExpansionInterfaces.Mellin
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A target-dependent polynomial bound on the original common line. Both
the pure norm and non-norm branches are retained. -/
theorem exists_actual_target_common_line_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, s.re = B + e →
      ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S) s)⁻¹‖ ≤
        C * (4 + |s.im|) ^ k := by
  have hupper : ∀ H : ℝ, ZeroUpperBound K psi H B := by
    intro H rho hrho hlo hhi _hheight
    exact hboundary ⟨psi, hpsi⟩ rho.re ⟨rho, rfl, hrho⟩ hlo hhi
  let F : ℝ := deletionInverseConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionInverseConstant_pos K (exceptionalPrimes K S)
  by_cases hnorm : ∃ t : ℝ, psi = heckeNormTwist K t
  · obtain ⟨t, ht⟩ := hnorm
    have hu : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t) H B := by
      simpa only [← ht] using hupper
    obtain ⟨C, k, hC, hk, hb⟩ := exists_common_line_normTwist_reciprocal_bound K
      hcomplex t hB hB1 he he1 hu
    refine ⟨F * C, k, mul_pos hF hC, hk, ?_⟩
    intro s hs
    have hdel := norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S)
      psi s (by linarith)
    have hfull : ‖(heckeContinuation K psi s)⁻¹‖ ≤ C * (4 + |s.im|) ^ k := by
      simpa only [ht] using hb s hs
    rw [heckeDeletedContinuation, mul_inv, norm_mul]
    exact (mul_le_mul hdel hfull (norm_nonneg _) hF.le).trans_eq (by ring)
  · have hnon : ∀ t : ℝ, psi ≠ heckeNormTwist K t := fun t ht => hnorm ⟨t, ht⟩
    let kappa : ℝ := e / 8
    let a : ℝ := B - e / 4
    have hkappa : 0 < kappa := div_pos he (by norm_num)
    have hkappa1 : kappa < 1 / 1000 := by dsimp [kappa]; linarith
    obtain ⟨D, hD, hb⟩ := exists_uniform_fixedType_buffered_control K hcomplex
      (fun v => heckeRadialParameter K v psi) (heckeArchWeight K psi)
      hkappa hkappa1 (by norm_num : (0 : ℝ) < 1)
    let k : ℝ := ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)
    refine ⟨F * D * heckeConductorScale K psi, k, by
      exact mul_pos (mul_pos hF hD) (conductorScale_pos K psi), by dsimp [k]; positivity, ?_⟩
    intro s hs
    have hz : ZeroUpperBound K psi (|s.im| + 2) (a + 2 * kappa) := by
      have heq : a + 2 * kappa = B := by dsimp [a, kappa]; ring
      rw [heq]
      exact hupper _
    have hh := hb psi a |s.im| (|s.im| + 2) hnon rfl rfl
      (by dsimp [a]; linarith) (by dsimp [a]; linarith)
      (abs_nonneg _) (by linarith) hz s
      (by dsimp [a, kappa]; linarith) (by linarith) le_rfl
    have hfull : ‖(heckeContinuation K psi s)⁻¹‖ ≤
        D * heckeConductorScale K psi * (4 + |s.im|) ^ k := by
      have hh' := (le_add_of_nonneg_left (norm_nonneg (heckeContinuation K psi s))).trans hh
      have hheight : 2 + (|s.im| + 2) = 4 + |s.im| := by ring
      simpa only [hheight, Real.rpow_one, mul_one, k] using hh'
    have hdel := norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S)
      psi s (by linarith)
    rw [heckeDeletedContinuation, mul_inv, norm_mul]
    exact (mul_le_mul hdel hfull (norm_nonneg _) hF.le).trans_eq (by ring)

/-! Global measurability of the literal local rational formulas. Division
is total here; finite-line bounds below supply actual integrability. -/

@[fun_prop] theorem measurable_actual_primeNorm_cpow
    (p : ExteriorPrime K S) (f : ℂ → ℂ) (hf : Measurable f) :
    Measurable (fun s => (p.val.asIdeal.absNorm : ℂ) ^ f s) := by
  have hq : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)))
  exact (continuous_id.const_cpow (Or.inl hq)).measurable.comp hf

@[fun_prop] theorem measurable_actual_localProbeEulerSum
    (P : ProbeData K S) (psi chi : HeckeCharacter K)
    (p : ExteriorPrime K S) (w z : ℂ) :
    Measurable (fun s : ℂ => localProbeEulerSum K S P psi chi p s w z) := by
  unfold localProbeEulerSum
  dsimp only
  fun_prop

@[fun_prop] theorem measurable_actual_localPrincipalCorrection
    (P : ProbeData K S) (psi : HeckeCharacter K) (p : ExteriorPrime K S) :
    Measurable (localPrincipalCorrection K S P psi p) := by
  unfold localPrincipalCorrection
  dsimp only
  fun_prop

@[fun_prop] theorem measurable_actual_localMarkedProbeEulerSum
    (P : ProbeData K S) (psi chi : HeckeCharacter K)
    (p : ExteriorPrime K S) (w z : ℂ) :
    Measurable (fun s : ℂ => localMarkedProbeEulerSum K S P psi chi p s w z) := by
  unfold localMarkedProbeEulerSum
  dsimp only
  fun_prop

@[fun_prop] theorem measurable_actual_localCompensatedEulerCorrection
    (P : ProbeData K S) (psi chi : HeckeCharacter K)
    (p : ExteriorPrime K S) (w z : ℂ) :
    Measurable (fun s : ℂ => localCompensatedEulerCorrection K S P psi chi p s w z) := by
  unfold localCompensatedEulerCorrection
  dsimp only
  fun_prop

theorem measurable_actual_principalCorrection
    (P : ProbeData K S) (psi : HeckeCharacter K) :
    Measurable (principalCorrection K S P psi) := by
  unfold principalCorrection
  exact Measurable.tprod (fun p => measurable_actual_localPrincipalCorrection K S P psi p)

theorem measurable_actual_compensatedPrincipalCorrection
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry) (Z : ℝ) :
    Measurable (compensatedPrincipalCorrection K S P psi g ∅ Z) := by
  unfold compensatedPrincipalCorrection
  apply Finset.measurable_sum
  intro p _hp
  apply Measurable.mul
  · apply Measurable.tprod
    intro q
    by_cases hq : q ∈ Finset.univ.image p
    · simp only [hq, if_true]
      exact measurable_const
    · simp only [hq, if_false]
      exact measurable_actual_localPrincipalCorrection K S P psi q
  · apply Finset.measurable_prod
    intro i _hi
    exact measurable_const.mul
      (measurable_actual_localCompensatedEulerCorrection K S P psi 1 (p i) 1 (1 / 6))

/-- The exact correction left after dividing out the original prime normalizer. -/
def actualNormalizedPrincipalCorrection
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z : ℝ) (s : ℂ) : ℂ :=
  compensatedPrincipalCorrection K S P psi g ∅ Z s /
    ((Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g ∅ Z)

theorem exists_actual_normalizedPrincipal_correction_error
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (hunram : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ ∀ (Z : ℝ) (s : ℂ), Z₀ ≤ Z → 7 / 8 < s.re →
      ‖actualNormalizedPrincipalCorrection K S P psi g Z s - principalCorrection K S P psi s‖ ≤
        C * Z ^ (-principalSlotSaving g) := by
  obtain ⟨Cw, Zw, hCw, hZw, hwindow⟩ := actual_principal_window_error K S P psi g ∅ hunram
  obtain ⟨Zn, hZn, hpositive⟩ := exists_actual_primeNormalizer_positive K S hcomplex g
  obtain ⟨CH, hCH, hH⟩ := exists_norm_principalCorrection_le K S P psi
    (σ₁ := (7 / 8 : ℝ)) (by norm_num)
  refine ⟨Cw * (1 + CH), max Zw Zn, mul_pos hCw (by linarith),
    hZw.trans (le_max_left _ _), ?_⟩
  intro Z s hZ hs
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZw.trans ((le_max_left _ _).trans hZ))
  have hN : primeNormalizer K S g ∅ Z ≠ 0 := by
    intro hz
    have hh := hpositive Z ((le_max_right _ _).trans hZ)
    rw [hz, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  let d : ℂ := (Z : ℂ) ^ (1 / 36 : ℂ) * primeNormalizer K S g ∅ Z
  have hd : d ≠ 0 := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hZpos.ne'))) hN
  have hh : ‖compensatedPrincipalCorrection K S P psi g ∅ Z s -
      principalCorrection K S P psi s * d‖ ≤
      Cw * Z ^ (-principalSlotSaving g) * ‖principalCorrection K S P psi s * d‖ := by
    simpa only [d, mul_assoc] using hwindow Z s ((le_max_left _ _).trans hZ) hs
  have he : actualNormalizedPrincipalCorrection K S P psi g Z s -
      principalCorrection K S P psi s =
      (compensatedPrincipalCorrection K S P psi g ∅ Z s -
        principalCorrection K S P psi s * d) / d := by
    change _ / d - _ = _
    rw [sub_div, mul_div_cancel_right₀ _ hd]
  rw [he, norm_div]
  calc
    _ ≤ (Cw * Z ^ (-principalSlotSaving g) *
        ‖principalCorrection K S P psi s * d‖) / ‖d‖ :=
      div_le_div_of_nonneg_right hh (norm_nonneg _)
    _ = Cw * Z ^ (-principalSlotSaving g) * ‖principalCorrection K S P psi s‖ := by
      rw [norm_mul]
      field_simp [norm_ne_zero_iff.mpr hd]
      <;> ring
    _ ≤ Cw * Z ^ (-principalSlotSaving g) * (1 + CH) :=
      mul_le_mul_of_nonneg_left ((hH s hs.le).trans (by linarith)) (by positivity)
    _ = _ := by ring

/-- The original principal Gaussian and deleted target denominator, with
an explicit correction value. -/
def actualPrincipalWeightedTerm (psi : HeckeCharacter K) (Z : ℝ) (s c : ℂ) : ℂ :=
  (Z : ℂ) ^ (s - 11 / 16) * Complex.exp ((s - 5 / 6) ^ 2) * c /
    heckeDeletedContinuation K psi (exceptionalPrimes K S) s

/-- Finite truncation of the original principal-line integrand on a stated line. -/
def actualPrincipalLineTruncation
    (P : ProbeData K S) (psi : HeckeCharacter K) (Z H sigma : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ in Icc (-H) H,
    actualPrincipalWeightedTerm K S psi Z (vertical sigma t)
      (principalCorrection K S P psi (vertical sigma t))

/-- The literal normalized double-residue line before the principal slot
replacement; no contour shift is part of this definition. -/
def actualDoubleResidueLineTruncation
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H sigma : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ in Icc (-H) H,
    actualPrincipalWeightedTerm K S psi Z (vertical sigma t)
      (actualNormalizedPrincipalCorrection K S P psi g Z (vertical sigma t))

def actualPrincipalSlotRemainder
    (P : ProbeData K S) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H sigma : ℝ) : ℂ :=
  actualDoubleResidueLineTruncation K S P psi g Z H sigma -
    actualPrincipalLineTruncation K S P psi Z H sigma

theorem norm_actual_principalGaussian_le (sigma t : ℝ) :
    ‖Complex.exp ((vertical sigma t - 5 / 6) ^ 2)‖ ≤
      Real.exp ((sigma - 5 / 6) ^ 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : ((vertical sigma t - (5 / 6 : ℂ)) ^ 2).re =
      (sigma - 5 / 6) ^ 2 - t ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      vertical_re, vertical_im]
    norm_num
    <;> ring
  rw [he]
  linarith [sq_nonneg t]

theorem norm_actualPrincipalWeightedTerm_le
    (psi : HeckeCharacter K) (Z H sigma t C k M : ℝ) (c : ℂ)
    (hZ : 0 < Z) (hH : 0 ≤ H) (hk : 0 ≤ k) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ht : |t| ≤ H) (hc : ‖c‖ ≤ M)
    (hrec : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S)
      (vertical sigma t))⁻¹‖ ≤ C * (4 + |t|) ^ k) :
    ‖actualPrincipalWeightedTerm K S psi Z (vertical sigma t) c‖ ≤
      (Z ^ (sigma - 11 / 16) * Real.exp ((sigma - 5 / 6) ^ 2) * M) *
        (C * (4 : ℝ) ^ k * (1 + H) ^ k) := by
  have hheight : (4 + |t|) ^ k ≤ (4 : ℝ) ^ k * (1 + H) ^ k := by
    rw [← Real.mul_rpow (by norm_num) (by linarith : 0 ≤ 1 + H)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hk
  have hr : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S)
      (vertical sigma t))⁻¹‖ ≤ C * (4 : ℝ) ^ k * (1 + H) ^ k := by
    exact hrec.trans ((mul_le_mul_of_nonneg_left hheight hC).trans_eq (by ring))
  have hre : (vertical sigma t - (11 / 16 : ℂ)).re = sigma - 11 / 16 := by simp
  simp only [actualPrincipalWeightedTerm, div_eq_mul_inv, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hZ, hre]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_actual_principalGaussian_le sigma t)
      (Real.rpow_nonneg hZ.le _)) hc (norm_nonneg _) (by positivity))
    hr (norm_nonneg _) (by positivity)

theorem measurable_actualPrincipalWeightedTerm
    (psi : HeckeCharacter K) (Z : ℝ) (hZ : 0 < Z)
    (f : ℂ → ℂ) (hf : Measurable f) :
    Measurable (fun s => actualPrincipalWeightedTerm K S psi Z s (f s)) := by
  have hp : Measurable (fun s : ℂ => (Z : ℂ) ^ (s - 11 / 16)) :=
    ((continuous_id.sub continuous_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).measurable
  have hg : Measurable (fun s : ℂ => Complex.exp ((s - 5 / 6) ^ 2)) := by fun_prop
  have hL : Measurable (heckeDeletedContinuation K psi (exceptionalPrimes K S)) :=
    (meromorphicOn_univ.mp (meromorphicOn_heckeDeletedContinuation K psi
      (exceptionalPrimes K S))).measurable
  exact ((hp.mul hg).mul hf).div hL

theorem actual_integrableOn_Icc_of_measurable_bound
    (f : ℝ → ℂ) (hf : Measurable f) (H M : ℝ)
    (hbound : ∀ t ∈ Icc (-H) H, ‖f t‖ ≤ M) : IntegrableOn f (Icc (-H) H) := by
  have hm : IntegrableOn (fun _ : ℝ => M) (Icc (-H) H) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  exact hm.mono' hf.aestronglyMeasurable.restrict
    (ae_restrict_of_forall_mem measurableSet_Icc hbound)

/-- All arithmetic, Mellin, normalization and reciprocal constants precede
Z and H. The conclusion concerns the actual difference of finite integrals. -/
theorem exists_actual_principalSlot_remainder_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K S) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega) (g : PrimeWindowGeometry)
    (hunram : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z₀ A : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z₀ ≤ Z → 1 ≤ H →
      ‖actualPrincipalSlotRemainder K S P psi g Z H (B + e)‖ ≤
        C * Z ^ (B - 11 / 16 - principalSlotSaving g + e + eta) * (1 + H) ^ A := by
  obtain ⟨Ce, Z₀, hCe, hZ₀, herror⟩ :=
    exists_actual_normalizedPrincipal_correction_error K S hcomplex P psi g hunram
  obtain ⟨Cr, k, hCr, hk, hrec⟩ := exists_actual_target_common_line_reciprocal_bound
    K S hcomplex omega psi hpsi hB hB1 he he1 hboundary
  obtain ⟨CH, hCH, hHbound⟩ := exists_norm_principalCorrection_le K S P psi
    (σ₁ := (7 / 8 : ℝ)) (by norm_num)
  let Cpoint : ℝ := Real.exp ((B + e - 5 / 6) ^ 2) * Ce * Cr * (4 : ℝ) ^ k
  have hCpoint : 0 < Cpoint := by dsimp [Cpoint]; positivity
  let Cline : ℝ := ‖(2 * (Real.pi : ℂ))⁻¹‖
  have hCline : 0 < Cline := norm_pos_iff.mpr (inv_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  refine ⟨2 * Cline * Cpoint, Z₀, k + 1, by positivity, hZ₀, by linarith, ?_⟩
  intro Z H hZ hH
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  let r : ℝ := B - 11 / 16 - principalSlotSaving g + e + eta
  let f : ℝ → ℂ := fun t => actualPrincipalWeightedTerm K S psi Z (vertical (B + e) t)
    (principalCorrection K S P psi (vertical (B + e) t))
  let d : ℝ → ℂ := fun t => actualPrincipalWeightedTerm K S psi Z (vertical (B + e) t)
    (actualNormalizedPrincipalCorrection K S P psi g Z (vertical (B + e) t) -
      principalCorrection K S P psi (vertical (B + e) t))
  let j : ℝ → ℂ := fun t => actualPrincipalWeightedTerm K S psi Z (vertical (B + e) t)
    (actualNormalizedPrincipalCorrection K S P psi g Z (vertical (B + e) t))
  have hvertical : Measurable (fun t : ℝ => vertical (B + e) t) := by unfold vertical; fun_prop
  have hfmeas : Measurable f :=
    (measurable_actualPrincipalWeightedTerm K S psi Z hZpos _
      (measurable_actual_principalCorrection K S P psi)).comp hvertical
  have hdmeas : Measurable d := by
    have hnormalized : Measurable (actualNormalizedPrincipalCorrection K S P psi g Z) :=
      (measurable_actual_compensatedPrincipalCorrection K S P psi g Z).div_const _
    exact (measurable_actualPrincipalWeightedTerm K S psi Z hZpos _
      (hnormalized.sub (measurable_actual_principalCorrection K S P psi))).comp hvertical
  have hrecLine (t : ℝ) : ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S)
      (vertical (B + e) t))⁻¹‖ ≤ Cr * (4 + |t|) ^ k := by
    simpa only [vertical_im] using hrec (vertical (B + e) t) (by simp)
  have hpoint : ∀ t ∈ Icc (-H) H, ‖d t‖ ≤ Cpoint * Z ^ r * (1 + H) ^ k := by
    intro t ht
    have hcorr := herror Z (vertical (B + e) t) hZ (by simp only [vertical_re]; linarith)
    have hh := norm_actualPrincipalWeightedTerm_le K S psi Z H (B + e) t Cr k
      (Ce * Z ^ (-principalSlotSaving g)) _ hZpos hH0 hk hCr.le (by positivity)
      (abs_le.mpr ht) hcorr (hrecLine t)
    have hscale : Z ^ (B + e - 11 / 16) * Z ^ (-principalSlotSaving g) =
        Z ^ (B - 11 / 16 - principalSlotSaving g + e) := by
      rw [← Real.rpow_add hZpos]
      congr 1
      ring
    have hp : Z ^ (B - 11 / 16 - principalSlotSaving g + e) ≤ Z ^ r :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by dsimp [r]; linarith)
    calc
      ‖d t‖ ≤ (Z ^ (B + e - 11 / 16) * Real.exp ((B + e - 5 / 6) ^ 2) *
          (Ce * Z ^ (-principalSlotSaving g))) * (Cr * (4 : ℝ) ^ k * (1 + H) ^ k) := hh
      _ = Cpoint * (Z ^ (B + e - 11 / 16) * Z ^ (-principalSlotSaving g)) * (1 + H) ^ k := by
        dsimp [Cpoint]
        ring
      _ = Cpoint * Z ^ (B - 11 / 16 - principalSlotSaving g + e) * (1 + H) ^ k := by rw [hscale]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hCpoint.le) (by positivity)
  have hdint : IntegrableOn d (Icc (-H) H) :=
    actual_integrableOn_Icc_of_measurable_bound d hdmeas H _ hpoint
  have hfint : IntegrableOn f (Icc (-H) H) := by
    apply actual_integrableOn_Icc_of_measurable_bound f hfmeas H
      ((Z ^ (B + e - 11 / 16) * Real.exp ((B + e - 5 / 6) ^ 2) * CH) *
        (Cr * (4 : ℝ) ^ k * (1 + H) ^ k))
    intro t ht
    exact norm_actualPrincipalWeightedTerm_le K S psi Z H (B + e) t Cr k CH _
      hZpos hH0 hk hCr.le hCH (abs_le.mpr ht)
      (hHbound _ (by simp only [vertical_re]; linarith)) (hrecLine t)
  have heq : j = fun t => f t + d t := by
    funext t
    dsimp [j, f, d, actualPrincipalWeightedTerm]
    ring
  have hjint : IntegrableOn j (Icc (-H) H) := by
    rw [heq]
    exact hfint.add hdint
  have hdiff : actualPrincipalSlotRemainder K S P psi g Z H (B + e) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ in Icc (-H) H, d t := by
    change _ * (∫ t : ℝ in Icc (-H) H, j t) -
      _ * (∫ t : ℝ in Icc (-H) H, f t) = _
    rw [← mul_sub, ← integral_sub hjint hfint]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [heq]
    dsimp only
    ring
  have hvol : volume.real (Icc (-H) H) = 2 * H := by
    rw [Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  have hint : ‖∫ t : ℝ in Icc (-H) H, d t‖ ≤
      (Cpoint * Z ^ r * (1 + H) ^ k) * (2 * H) := by
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const
      isCompact_Icc.measure_lt_top hpoint
  have hheight : H * (1 + H) ^ k ≤ (1 + H) ^ (k + 1) := by
    rw [Real.rpow_add_one (by linarith : 1 + H ≠ 0)]
    exact (mul_le_mul_of_nonneg_right (by linarith : H ≤ 1 + H) (by positivity)).trans_eq
      (mul_comm _ _)
  rw [hdiff, norm_mul]
  calc
    _ ≤ Cline * ((Cpoint * Z ^ r * (1 + H) ^ k) * (2 * H)) :=
      mul_le_mul_of_nonneg_left hint hCline.le
    _ = (2 * Cline * Cpoint) * Z ^ r * (H * (1 + H) ^ k) := by ring
    _ ≤ (2 * Cline * Cpoint) * Z ^ r * (1 + H) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)

end Expansion.Project

#print axioms Expansion.Project.exists_actual_target_common_line_reciprocal_bound
#print axioms Expansion.Project.measurable_actual_compensatedPrincipalCorrection
#print axioms Expansion.Project.exists_actual_normalizedPrincipal_correction_error
#print axioms Expansion.Project.exists_actual_principalSlot_remainder_bound
