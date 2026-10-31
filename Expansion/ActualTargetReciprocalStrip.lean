import HeckeSkeleton.ExpansionModels.SmallRowReciprocal

/-!
# The actual target reciprocal on the principal strip

The original common packet boundary excludes zeros at each requested
height.  For a norm twist the literal reciprocal is (s-pole)/Q(s), so its
chosen value at the pole is the analytic removable value.  The same
rectangle argument that controls a common line controls its whole strip
up to Re = 2, with constants chosen before the point or its height.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckeUniformBufferedControl HeckeSkeleton.HeckeDeletedEulerControl
open HeckeSkeleton.HeckeConductorNorm
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The original packet premise supplies precisely the requested finite
height upper bound, without a new zero detector. -/
theorem actual_target_zeroUpperBound
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B : ℝ}
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (H : ℝ) : ZeroUpperBound K psi H B := by
  intro rho hrho hlo hhi _hheight
  exact hboundary ⟨psi, hpsi⟩ rho.re ⟨rho, rfl, hrho⟩ hlo hhi

/-- The actual deleted reciprocal is analytic to the right of the
original common boundary, including the removable norm pole. -/
theorem differentiableOn_actual_target_reciprocal
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B : ℝ} (hB : 1 / 2 ≤ B)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    DifferentiableOn ℂ
      (fun s => (heckeDeletedContinuation K psi (exceptionalPrimes K S) s)⁻¹)
      (rightHalfPlane B) := by
  intro s hs
  have hupper := actual_target_zeroUpperBound K omega psi hpsi hboundary |s.im|
  have hfull : DifferentiableAt ℂ (fun z => (heckeContinuation K psi z)⁻¹) s := by
    by_cases hnorm : ∃ t : ℝ, psi = heckeNormTwist K t
    · obtain ⟨t, ht⟩ := hnorm
      have hu : ZeroUpperBound K (heckeNormTwist K t) |s.im| B := by
        simpa only [← ht] using hupper
      have heq : (fun z => (heckeContinuation K (heckeNormTwist K t) z)⁻¹) =
          fun z => (z - heckeNormPole t) / normPoleNumerator K t z := by
        funext z
        rw [heckeContinuation_normTwist_eq K t]
        exact inv_div _ _
      rw [ht, heq]
      exact (differentiableAt_id.sub_const _).div
        (normPoleNumerator_differentiable K t s)
        (normPoleNumerator_ne_zero_of_upper K t |s.im| B hB hu s hs le_rfl)
    · have hnon : ∀ t : ℝ, psi ≠ heckeNormTwist K t := fun t ht => hnorm ⟨t, ht⟩
      exact (differentiable_heckeContinuation_of_nonNorm K psi hnon s).inv
        (continuation_ne_zero_of_upper K psi hnon |s.im| B hB hupper s hs le_rfl)
  have hdel : DifferentiableAt ℂ
      (fun z => (heckeEulerDeletionPolynomial K psi (exceptionalPrimes K S) z)⁻¹) s :=
    (heckeEulerDeletionPolynomial_analyticAt K psi (exceptionalPrimes K S) s).differentiableAt.inv
      (heckeEulerDeletionPolynomial_ne_zero K psi _ (by
        have : B < s.re := hs
        linarith))
  simpa only [heckeDeletedContinuation, mul_inv] using
    (hdel.mul hfull).differentiableWithinAt

/-- The pole-cleared norm branch is controlled on the complete principal
strip, including every bounded exceptional point. -/
theorem exists_actual_normTwist_strip_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) (t : ℝ)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hupper : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t) H B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, B + e ≤ s.re → s.re ≤ 2 →
      ‖(heckeContinuation K (heckeNormTwist K t) s)⁻¹‖ ≤ C * (4 + |s.im|) ^ k := by
  let kappa : ℝ := e / 8
  let a : ℝ := B - e / 4
  have hkappa : 0 < kappa := div_pos he (by norm_num)
  have hkappa1 : kappa < 1 / 1000 := by dsimp [kappa]; linarith
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hab : a + 2 * kappa = B := by dsimp [a, kappa]; ring
  obtain ⟨A, k, hA, hk, hpoly⟩ := exists_normPoleRegularization_rightStrip_bound K hcomplex t
  obtain ⟨L, hL, hlog⟩ := exists_normRegularizedEulerLog_bound K
  obtain ⟨D, hD, hcontrol⟩ := HeckeSkeleton.BufferedReciprocal.buffered_value_and_reciprocal_of_rectangle
    (e := kappa) (A := L) (M := 1) (ε := 1) hkappa hkappa1 hL (by norm_num) (by norm_num)
  let A0 : ℝ := Real.exp 1 * max 1 A
  have hmax : 0 < max 1 A := zero_lt_one.trans_le (le_max_left _ _)
  have hA0 : 0 < A0 := mul_pos (Real.exp_pos _) hmax
  have hAA0 : A ≤ A0 := by
    apply (le_max_right 1 A).trans
    exact le_mul_of_one_le_left hmax.le (Real.one_le_exp (by norm_num))
  have hexp : Real.exp 1 ≤ A0 := le_mul_of_one_le_right (Real.exp_pos _).le (le_max_left _ _)
  refine ⟨D * A0, k, mul_pos hD hA0, hk, ?_⟩
  intro s hs hs2
  let H : ℝ := |s.im|
  let HU : ℝ := |s.im| + 2
  let C : ℝ := A0 * (2 + HU) ^ k
  have hHU : 0 ≤ HU := by dsimp [HU]; positivity
  have hheight : 1 ≤ (2 + HU) ^ k := Real.one_le_rpow (by linarith) hk
  have hAC : A0 ≤ C := le_mul_of_one_le_right hA0.le hheight
  have hC : Real.exp 1 ≤ C := hexp.trans hAC
  have hf := (normPoleRegularization_differentiableOn K t).mono
    (show {z : ℂ | a + 2 * kappa < z.re ∧ |z.im| ≤ HU} ⊆ {z : ℂ | 0 < z.re} from by
      intro z hz
      rw [hab] at hz
      linarith [hz.1])
  have hz : ∀ z : ℂ, a + 2 * kappa < z.re → |z.im| ≤ HU →
      normPoleRegularization K t z ≠ 0 := by
    intro z hz hh
    rw [hab] at hz
    exact normPoleRegularization_ne_zero_of_upper K t HU B (by linarith) (hupper HU) z hz hh
  have hp : ∀ z : ℂ, a + 2 * kappa < z.re → |z.im| ≤ HU →
      ‖normPoleRegularization K t z‖ ≤ C ^ (1 : ℝ) := by
    intro z hz hh
    rw [hab] at hz
    rw [Real.rpow_one]
    exact (hpoly z (by linarith)).trans
      (mul_le_mul hAA0 (Real.rpow_le_rpow (by positivity) (by linarith) hk)
        (by positivity) hA0.le)
  have hbound := hcontrol a C H HU (normPoleRegularization K t) (normRegularizedEulerLog K t)
    ha ha1 hC (by dsimp [H, HU]; linarith) hf hz hp
    (normRegularizedEulerLog_differentiableOn K t)
    (exp_normRegularizedEulerLog K t) (hlog t)
    s (by dsimp [a, kappa]; linarith) hs2 le_rfl
  have hrec := (normTwist_reciprocal_le_regularized K t s (by linarith)).trans
    ((le_add_of_nonneg_left (norm_nonneg (normPoleRegularization K t s))).trans hbound)
  rw [Real.rpow_one] at hrec
  have hheight_eq : 2 + HU = 4 + |s.im| := by dsimp only [HU]; ring
  dsimp only [C] at hrec
  rw [hheight_eq] at hrec
  exact hrec.trans_eq (by ring)

/-- Constants precede the point and its height; the actual finite S
deletion and both target-character branches are included. -/
theorem exists_actual_target_strip_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, B + e ≤ s.re → s.re ≤ 2 →
      ‖(heckeDeletedContinuation K psi (exceptionalPrimes K S) s)⁻¹‖ ≤
        C * (4 + |s.im|) ^ k := by
  have hupper : ∀ H : ℝ, ZeroUpperBound K psi H B :=
    actual_target_zeroUpperBound K omega psi hpsi hboundary
  let F : ℝ := deletionInverseConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionInverseConstant_pos K (exceptionalPrimes K S)
  by_cases hnorm : ∃ t : ℝ, psi = heckeNormTwist K t
  · obtain ⟨t, ht⟩ := hnorm
    have hu : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t) H B := by
      simpa only [← ht] using hupper
    obtain ⟨C, k, hC, hk, hb⟩ := exists_actual_normTwist_strip_reciprocal_bound K
      hcomplex t hB hB1 he he1 hu
    refine ⟨F * C, k, mul_pos hF hC, hk, ?_⟩
    intro s hs hs2
    have hdel := norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S)
      psi s (by linarith)
    have hfull : ‖(heckeContinuation K psi s)⁻¹‖ ≤ C * (4 + |s.im|) ^ k := by
      simpa only [ht] using hb s hs hs2
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
    refine ⟨F * D * heckeConductorScale K psi, k,
      mul_pos (mul_pos hF hD) (conductorScale_pos K psi), by dsimp [k]; positivity, ?_⟩
    intro s hs hs2
    have hz : ZeroUpperBound K psi (|s.im| + 2) (a + 2 * kappa) := by
      have heq : a + 2 * kappa = B := by dsimp [a, kappa]; ring
      rw [heq]
      exact hupper _
    have hh := hb psi a |s.im| (|s.im| + 2) hnon rfl rfl
      (by dsimp [a]; linarith) (by dsimp [a]; linarith)
      (abs_nonneg _) (by linarith) hz s
      (by dsimp [a, kappa]; linarith) hs2 le_rfl
    have hfull : ‖(heckeContinuation K psi s)⁻¹‖ ≤
        D * heckeConductorScale K psi * (4 + |s.im|) ^ k := by
      have hh' := (le_add_of_nonneg_left (norm_nonneg (heckeContinuation K psi s))).trans hh
      have hheight : 2 + (|s.im| + 2) = 4 + |s.im| := by ring
      simpa only [hheight, Real.rpow_one, mul_one, k] using hh'
    have hdel := norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S)
      psi s (by linarith)
    rw [heckeDeletedContinuation, mul_inv, norm_mul]
    exact (mul_le_mul hdel hfull (norm_nonneg _) hF.le).trans_eq (by ring)

end Expansion.Project

#print axioms Expansion.Project.differentiableOn_actual_target_reciprocal
#print axioms Expansion.Project.exists_actual_target_strip_reciprocal_bound
