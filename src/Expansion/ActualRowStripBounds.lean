import Expansion.ActualTargetReciprocalStrip

/-!
# Uniform actual row denominators on the complete outer swept strip

The original common packet boundary controls the entire interval of real
parts to the right of B+e. The bounded norm exceptions share the forced
norm parameter of the fixed target; they are retained by the actual
pole-cleared continuation. All constants precede the arithmetic row and
both height and real part. The right Euler region extends the finite
strip estimate to all larger real parts.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.ActualEulerLogarithm HeckeSkeleton.HeckeDeletedEulerControl
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeUniformBufferedControl
open HeckeSkeleton.HeckeFiniteBackgroundControl HeckeSkeleton.HeckeConductorNorm
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The old packet boundary supplies the zero upper bound on the original
common line.  This is the non-norm case of the actual denominator, not a
new input carrying a reciprocal estimate. -/
theorem exists_actual_row_nonNorm_reciprocal_strip
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S),
      (∀ t : ℝ, psi * conjugate (R.character u) ≠ heckeNormTwist K t) →
      ∀ s : ℂ, B + e ≤ s.re → s.re ≤ 2 →
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
  intro P R u hnon s hs hs2
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
theorem exists_actual_row_reciprocal_closedStrip
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S) (s : ℂ), B + e ≤ s.re → s.re ≤ 2 →
        ‖(heckeDeletedContinuation K (psi * conjugate (R.character u))
          (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * frequencyRowNorm K S u ^ eta * (4 + |s.im|) ^ k := by
  obtain ⟨Cn, hCn, hn⟩ := exists_actual_row_nonNorm_reciprocal_strip K S hcomplex
    omega psi hpsi hB hB1 he he1 heta hboundary
  let v : InfinitePlace K := Classical.choice inferInstance
  let t0 : ℝ := -heckeRadialParameter K v psi
  have hnorm : ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
      ∀ _hmem : heckeNormTwist K t0 ∈ HeckePacket K omega,
      ∀ s : ℂ, B + e ≤ s.re → s.re ≤ 2 →
        ‖(heckeContinuation K (heckeNormTwist K t0) s)⁻¹‖ ≤ C * (4 + |s.im|) ^ k := by
    by_cases hmem : heckeNormTwist K t0 ∈ HeckePacket K omega
    · have hupper : ∀ H : ℝ, ZeroUpperBound K (heckeNormTwist K t0) H B := by
        intro H rho hrho hlo hhi _hheight
        exact hboundary ⟨heckeNormTwist K t0, hmem⟩ rho.re ⟨rho, rfl, hrho⟩ hlo hhi
      obtain ⟨C, k, hC, hk, hb⟩ := exists_actual_normTwist_strip_reciprocal_bound K
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
  intro P R u s hs hs2
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
    have hb := hp hpkt s hs hs2
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
    have hb := hn P R u hnon s hs hs2
    have hkpow : (4 + |s.im|) ^ kn ≤ (4 + |s.im|) ^ k :=
      Real.rpow_le_rpow_of_exponent_le hheight (le_max_left _ _)
    exact hb.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_pos hF hCp).le) (by positivity))
      hkpow (by positivity) (by positivity))


/-- A single row-conductor bound covers the whole right half-strip,
including its absolute-convergence part above Re = 2. -/
theorem exists_actual_row_reciprocal_rightStrip
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    {B e eta : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P)
      (u : FrequencyRow K S) (s : ℂ), B + e ≤ s.re →
        ‖(heckeDeletedContinuation K (psi * conjugate (R.character u))
          (exceptionalPrimes K S) s)⁻¹‖ ≤
          C * frequencyRowNorm K S u ^ eta * (4 + |s.im|) ^ k := by
  obtain ⟨Cs, k, hCs, hk, hs⟩ := exists_actual_row_reciprocal_closedStrip
    K S hcomplex omega psi hpsi hB hB1 he he1 heta hboundary
  obtain ⟨Cr, hCr, hr⟩ := exists_deleted_reciprocal_right_bound K S
    (sigma := 2) (by norm_num)
  refine ⟨Cs + Cr, k, add_pos hCs hCr, hk, ?_⟩
  intro P R u s hleft
  have hN : 1 ≤ frequencyRowNorm K S u ^ eta :=
    Real.one_le_rpow (one_le_idealNorm K u.ideal.val) heta.le
  have hheight : 1 ≤ (4 + |s.im|) ^ k :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) hk
  by_cases hs2 : s.re ≤ 2
  · exact (hs P R u s hleft hs2).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCr.le) (by positivity)) (by positivity))
  · apply (hr (psi * conjugate (R.character u)) s (le_of_not_ge hs2)).trans
    calc
      Cr ≤ Cs + Cr := le_add_of_nonneg_left hCs.le
      _ ≤ (Cs + Cr) * frequencyRowNorm K S u ^ eta :=
        le_mul_of_one_le_right (add_pos hCs hCr).le hN
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hheight

open HeckeSkeleton.HeckeUniformStripGrowth

/-- The actual nonprincipal numerator has one polynomial bound for every
real part at least one half, including the initial line Re = 5. -/
theorem exists_actual_nonprincipal_numerator_rightStrip
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P),
      AllowedGeneratorInput K S P.arithmetic → ∀ u : FrequencyRow K S,
      ¬principalFrequencyRow K S u → ∀ w : ℂ, 1 / 2 ≤ w.re →
        ‖heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖ ≤
          C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨D, hD, hstrip⟩ := exists_uniform_fixedType_strip_bound K hcomplex
    (fun _ => 0) (fun _ => 0) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨A, hA, hconductor⟩ := exists_row_conductorScale_bound K S
  obtain ⟨E, hE, hright⟩ := exists_uniform_rightHalfPlane_bound K (11 / 10) (by norm_num)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K S)
  let C : ℝ := D * A ^ (3 / 5 : ℝ) + E
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨F * C, mul_pos hF hC, ?_⟩
  intro P R hAllowed u hu w hw
  have hN : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hNp : 1 ≤ frequencyRowNorm K S u ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (one_le_idealNorm K u.ideal.val) (by norm_num)
  have hheight : 1 ≤ (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
    one_le_pow₀ (by linarith [abs_nonneg w.im])
  have hfull : ‖heckeContinuation K (R.character u) w‖ ≤
      C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    by_cases hwupper : w.re ≤ 11 / 10
    · have hτ : (fun v => heckeRadialParameter K v (R.character u)) = fun _ => 0 := by
        funext v
        exact heckeRadialParameter_finiteOrder K v (R.finite_order u)
      have hm : heckeArchWeight K (R.character u) = fun _ => 0 := by
        funext v
        rw [heckeArchWeight_of_complex K (R.character u) v (hcomplex v)]
        exact heckeComplexWeight_finiteOrder K v (hcomplex v) (R.finite_order u)
      have hL := hstrip (R.character u)
        (rowCharacterInput_ne_normTwist_of_not_principal K S P R hAllowed u hu)
        hτ hm w ⟨by linarith, by linarith⟩
      norm_num only at hL
      have hscale : heckeConductorScale K (R.character u) ^ (3 / 5 : ℝ) ≤
          A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ) := by
        calc
          _ ≤ (A * frequencyRowNorm K S u) ^ (3 / 5 : ℝ) :=
            Real.rpow_le_rpow (conductorScale_pos K _).le (hconductor P R u) (by norm_num)
          _ = _ := Real.mul_rpow hA.le hN.le
      apply hL.trans
      have hc : D * A ^ (3 / 5 : ℝ) ≤ C := le_add_of_nonneg_right hE.le
      calc
        _ ≤ D * (A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ)) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by gcongr
        _ ≤ C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    · apply (hright (R.character u) w (le_of_not_ge hwupper)).trans
      calc
        E ≤ C := le_add_of_nonneg_left (by positivity)
        _ ≤ C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC.le hNp
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hheight
  have hEuler : ‖heckeEulerDeletionPolynomial K (R.character u)
      (exceptionalPrimes K S) w‖ ≤ F :=
    norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K S) (R.character u) w (by linarith)
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul hEuler hfull (norm_nonneg _) hF.le).trans_eq (by ring)

end Expansion.Project

#print axioms Expansion.Project.exists_actual_row_reciprocal_rightStrip
#print axioms Expansion.Project.exists_actual_nonprincipal_numerator_rightStrip
