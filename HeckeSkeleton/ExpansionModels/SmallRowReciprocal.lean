import HeckeSkeleton.ExpansionModels.SmallRowNumerator
import HeckeSkeleton.HeckeFiniteBackgroundControl
import HeckeSkeleton.HeckeConductorNorm
import HeckeGeneral.Analysis.PhysicalRowPacketBoundary
import HeckeSkeleton.ExpansionModels.SmallRowNormReciprocal
import HeckeSkeleton.HighNormBackgroundExclusion

/-!
# Actual reciprocal factors on the common small-row line

The non-norm branch uses the old common packet boundary at every height,
the proved fixed-type buffered estimate, and the actual row conductor.
The endpoint B=1 is covered for every character by the Euler logarithm.
The interior pure norm branch uses its actual pole-cleared continuation.
Finite-order row factors force its norm parameter to one fixed value, so
the final constant covers all rows, including every bounded exception.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.SmallRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.ActualEulerLogarithm HeckeSkeleton.HeckeDeletedEulerControl
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeUniformBufferedControl
open HeckeSkeleton.HeckeFiniteBackgroundControl HeckeSkeleton.HeckeConductorNorm
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Above one the actual fixed-S reciprocal is uniformly bounded for all
unitary characters, with no norm-character exclusion. -/
theorem exists_deleted_reciprocal_right_bound {sigma : ℝ} (hsigma : 1 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : HeckeCharacter K) (s : ℂ), sigma ≤ s.re →
      ‖(heckeDeletedContinuation K chi (exceptionalPrimes K S) s)⁻¹‖ ≤ C := by
  let A : ℝ := (3 / 2 : ℝ) * ∑' I : NonzeroIdeal K, idealNorm K I ^ (-sigma)
  let F : ℝ := deletionInverseConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionInverseConstant_pos K (exceptionalPrimes K S)
  refine ⟨F * Real.exp A, mul_pos hF (Real.exp_pos _), ?_⟩
  intro chi s hs
  have hfull : ‖(heckeContinuation K chi s)⁻¹‖ ≤ Real.exp A := by
    rw [← exp_heckeEulerLog_eq_continuation K chi s (hsigma.trans_le hs),
      ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr ((neg_le_abs _).trans
      ((Complex.abs_re_le_norm _).trans (heckeEulerLog_norm_le K chi sigma hsigma s hs)))
  have hdeletion : ‖(heckeEulerDeletionPolynomial K chi (exceptionalPrimes K S) s)⁻¹‖ ≤ F :=
    norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S) chi s (by linarith)
  rw [heckeDeletedContinuation, mul_inv, norm_mul]
  exact mul_le_mul hdeletion hfull (norm_nonneg _) hF.le

/-- The old packet boundary supplies the zero upper bound on the original
common line.  This is the non-norm case of the actual denominator, not a
new input carrying a reciprocal estimate. -/
theorem exists_common_line_nonNorm_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S),
      (∀ t : ℝ, psi * conjugate (R.character u) ≠ heckeNormTwist K t) →
      ∀ s : ℂ, s.re = B + e →
        ‖(heckeDeletedContinuation K (psi * conjugate (R.character u))
          (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * frequencyRowNorm K S u ^ eta *
            (4 + |s.im|) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eta) := by
  let kappa : ℝ := e / 8
  let a : ℝ := B - e / 4
  have hkappa : 0 < kappa := div_pos he (by norm_num)
  have hkappa1 : kappa < 1 / 1000 := by dsimp [kappa]; linarith
  obtain ⟨D, hD, hbuffered⟩ := exists_uniform_fixedType_buffered_control K hcomplex
    (fun v => heckeRadialParameter K v psi) (heckeArchWeight K psi) hkappa hkappa1 heta
  obtain ⟨A, hA, hconductor⟩ := exists_row_conductorScale_bound K S
  let Q : ℝ := ((finiteConductor K psi).val.absNorm : ℝ) * A
  have hQ : 0 < Q := mul_pos
    (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K psi))) hA
  let F : ℝ := deletionInverseConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionInverseConstant_pos K (exceptionalPrimes K S)
  refine ⟨F * D * Q ^ eta, by positivity, ?_⟩
  intro P R u hnon s hs
  let chi := psi * conjugate (R.character u)
  have hpacket : chi ∈ HeckePacket K omega :=
    packet_mul_finiteOrder (heckeLogNorm K) omega hpsi (R.finite_order u).inv
  have hz : ZeroUpperBound K chi (|s.im| + 2) (a + 2 * kappa) := by
    intro rho hrho hlo hhi _hheight
    have hb := hboundary ⟨chi, hpacket⟩ rho.re ⟨rho, rfl, hrho⟩ hlo hhi
    dsimp only [a, kappa]
    linarith
  have hτ : (fun v => heckeRadialParameter K v chi) =
      fun v => heckeRadialParameter K v psi :=
    radialParameters_mul_finiteOrder K psi (conjugate (R.character u)) (R.finite_order u).inv
  have hm : heckeArchWeight K chi = heckeArchWeight K psi :=
    archWeight_mul_finiteOrder_of_complex K hcomplex psi
      (conjugate (R.character u)) (R.finite_order u).inv
  have hcontrol := hbuffered chi a |s.im| (|s.im| + 2) hnon hτ hm
    (by dsimp [a]; linarith) (by dsimp [a]; linarith) (abs_nonneg _) (by linarith) hz
    s (by dsimp [a, kappa]; linarith) (by linarith) le_rfl
  have hraw : ‖(heckeContinuation K chi s)⁻¹‖ ≤
      D * heckeConductorScale K chi ^ eta *
        (4 + |s.im|) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eta) := by
    have hh := (le_add_of_nonneg_left (norm_nonneg (heckeContinuation K chi s))).trans hcontrol
    have hheight_eq : 2 + (|s.im| + 2) = 4 + |s.im| := by ring
    simpa only [hheight_eq] using hh
  have hscale : heckeConductorScale K chi ≤ Q * frequencyRowNorm K S u := by
    apply (conductorScale_mul_conjugate_le K psi (R.character u)).trans
    exact (mul_le_mul_of_nonneg_left (hconductor P R u) (Nat.cast_nonneg _)).trans_eq (by dsimp [Q]; ring)
  have hN0 : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hqpow : heckeConductorScale K chi ^ eta ≤
      Q ^ eta * frequencyRowNorm K S u ^ eta := by
    calc
      _ ≤ (Q * frequencyRowNorm K S u) ^ eta :=
        Real.rpow_le_rpow (conductorScale_pos K chi).le hscale heta.le
      _ = _ := Real.mul_rpow hQ.le hN0.le
  have hfull : ‖(heckeContinuation K chi s)⁻¹‖ ≤
      D * (Q ^ eta * frequencyRowNorm K S u ^ eta) *
        (4 + |s.im|) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eta) :=
    hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqpow hD.le) (by positivity))
  have hdeletion : ‖(heckeEulerDeletionPolynomial K chi (exceptionalPrimes K S) s)⁻¹‖ ≤ F :=
    norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S) chi s (by linarith)
  change ‖(heckeDeletedContinuation K chi (exceptionalPrimes K S) s)⁻¹‖ ≤ _
  rw [heckeDeletedContinuation, mul_inv, norm_mul]
  exact (mul_le_mul hdeletion hfull (norm_nonneg _) hF.le).trans_eq (by ring)

/-- One actual bound covers both branches of every physical denominator.
The only zero premise is the original common packet boundary; the norm
exception is included with its fixed parameter, never removed by a cutoff. -/
theorem exists_common_line_row_reciprocal_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S) (s : ℂ), s.re = B + e →
        ‖(heckeDeletedContinuation K (psi * conjugate (R.character u))
          (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * frequencyRowNorm K S u ^ eta * (4 + |s.im|) ^ k := by
  obtain ⟨Cn, hCn, hn⟩ := exists_common_line_nonNorm_reciprocal_bound K S hcomplex
    omega psi hpsi hB hB1 he he1 heta hboundary
  let v : InfinitePlace K := Classical.choice inferInstance
  let t0 : ℝ := -heckeRadialParameter K v psi
  have hnorm : ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ _hmem : heckeNormTwist K t0 ∈ HeckePacket K omega,
      ∀ s : ℂ, s.re = B + e →
        ‖(heckeContinuation K (heckeNormTwist K t0) s)⁻¹‖ ≤ C * (4 + |s.im|) ^ k := by
    by_cases hmem : heckeNormTwist K t0 ∈ HeckePacket K omega
    · have hupper : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t0) H B := by
        intro H rho hrho hlo hhi _hheight
        exact hboundary ⟨heckeNormTwist K t0, hmem⟩ rho.re ⟨rho, rfl, hrho⟩ hlo hhi
      obtain ⟨C, k, hC, hk, hb⟩ := exists_common_line_normTwist_reciprocal_bound K
        hcomplex t0 hB hB1 he he1 hupper
      exact ⟨C, k, hC, hk, fun _ => hb⟩
    · exact ⟨1, 0, zero_lt_one, le_rfl, fun hm => False.elim (hmem hm)⟩
  obtain ⟨Cp, kp, hCp, hkp, hp⟩ := hnorm
  let F : ℝ := deletionInverseConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionInverseConstant_pos K (exceptionalPrimes K S)
  let kn : ℝ := (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eta)
  let k : ℝ := max kn kp
  have hkn : 0 ≤ kn := by dsimp [kn]; positivity
  have hk : 0 ≤ k := hkn.trans (le_max_left _ _)
  refine ⟨Cn + F * Cp, k, by positivity, hk, ?_⟩
  intro P R u s hs
  have hpacket : psi * conjugate (R.character u) ∈ HeckePacket K omega :=
    packet_mul_finiteOrder (heckeLogNorm K) omega hpsi (R.finite_order u).inv
  have hN : 1 ≤ frequencyRowNorm K S u ^ eta :=
    Real.one_le_rpow (one_le_idealNorm K u.ideal.val) heta.le
  have hheight : 1 ≤ 4 + |s.im| := by linarith [abs_nonneg s.im]
  by_cases hnorm : ∃ t : ℝ, psi * conjugate (R.character u) = heckeNormTwist K t
  · obtain ⟨t, ht⟩ := hnorm
    have htt : t = t0 := HeckeSkeleton.HighNormBackgroundExclusion.norm_twist_parameter_forced
      K v psi (conjugate (R.character u)) (R.finite_order u).inv t ht
    rw [htt] at ht
    have hpkt : heckeNormTwist K t0 ∈ HeckePacket K omega := by rwa [ht] at hpacket
    have hb := hp hpkt s hs
    have hdel : ‖(heckeEulerDeletionPolynomial K (heckeNormTwist K t0)
        (exceptionalPrimes K S) s)⁻¹‖ ≤ F :=
      norm_heckeEulerDeletionPolynomial_inv_le K (exceptionalPrimes K S)
        (heckeNormTwist K t0) s (by linarith)
    rw [ht, heckeDeletedContinuation, mul_inv, norm_mul]
    have hkpow : (4 + |s.im|) ^ kp ≤ (4 + |s.im|) ^ k :=
      Real.rpow_le_rpow_of_exponent_le hheight (le_max_right _ _)
    calc
      _ ≤ F * (Cp * (4 + |s.im|) ^ kp) :=
        mul_le_mul hdel hb (norm_nonneg _) hF.le
      _ ≤ (F * Cp) * (4 + |s.im|) ^ k := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hkpow (mul_pos hF hCp).le
      _ ≤ ((Cn + F * Cp) * frequencyRowNorm K S u ^ eta) * (4 + |s.im|) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (le_add_of_nonneg_left hCn.le).trans
          (le_mul_of_one_le_right (by positivity) hN)
  · have hnon : ∀ t : ℝ, psi * conjugate (R.character u) ≠ heckeNormTwist K t :=
      fun t ht => hnorm ⟨t, ht⟩
    have hb := hn P R u hnon s hs
    have hkpow : (4 + |s.im|) ^ kn ≤ (4 + |s.im|) ^ k :=
      Real.rpow_le_rpow_of_exponent_le hheight (le_max_left _ _)
    exact hb.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_pos hF hCp).le) (by positivity))
      hkpow (by positivity) (by positivity))

end HeckeSkeleton.Expansion.SmallRows

#print axioms HeckeSkeleton.Expansion.SmallRows.exists_deleted_reciprocal_right_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_common_line_nonNorm_reciprocal_bound
#print axioms HeckeSkeleton.Expansion.SmallRows.exists_common_line_row_reciprocal_bound
