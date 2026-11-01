import HeckeSkeleton.LowEnergy.RawIdealHybrid

/-!
# Amplitude normalization and retained row coefficients

These exact identities connect a frozen full-cube coefficient bounded by
`Cf / (sqrt N * B)` to the normalized raw hybrid theorem.  The scalar is
removed before invoking the arbitrary-coefficient sieves.  A row-only
factor is bounded only after the entire row is formed.
-/

namespace HeckeSkeleton.LowEnergy.HybridScaling

open NumberField Ideal
open HeckeSkeleton.LowEnergy.KeepOriginalRow
open HeckeSkeleton.LowEnergy.IdealCanonicalColumns
open scoped NumberField Classical BigOperators
noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem hybridRow_scale_coefficients
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (A B : ℂ) (k : Ideal (𝓞 K)) :
    hybridRow cubic quad ps ns bs (fun P => A * a P) (fun n b => B * beta n b) k =
      A * B * hybridRow cubic quad ps ns bs a beta k := by
  unfold hybridRow hybridInner
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem finite_row_contraction {I : Type*} (rows : Finset I) (rho f : I → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hrho : ∀ i ∈ rows, ‖rho i‖ ≤ R) :
    (∑ i ∈ rows, ‖rho i * f i‖ ^ 2) ≤ R ^ 2 * ∑ i ∈ rows, ‖f i‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hrho i hi) 2) (sq_nonneg _)

theorem hybridRow_zero_of_beta_norm
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hbeta : ∀ n ∈ ns, ∀ b ∈ bs, ‖beta n b‖ ≤ 0) (k : Ideal (𝓞 K)) :
    hybridRow cubic quad ps ns bs a beta k = 0 := by
  have hz (n : Ideal (𝓞 K)) (hn : n ∈ ns) (b : Ideal (𝓞 K)) (hb : b ∈ bs) :
      beta n b = 0 := norm_eq_zero.mp (le_antisymm (hbeta n hn b hb) (norm_nonneg _))
  unfold hybridRow
  apply Finset.sum_eq_zero
  intro P hP
  have hi : hybridInner cubic quad ns bs beta k P = 0 := by
    unfold hybridInner
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro b hb
    simp only [hz n hn b hb, zero_mul]
  rw [hi, mul_zero]

/-- The frozen-cube amplitude has precisely the squared denominator used
in the physical ledger; no extra B or squarefree-column factor is lost. -/
theorem frozen_amplitude_sq (frozen nLower bLower : ℝ) (hn : 0 ≤ nLower) :
    (frozen / (Real.sqrt nLower * bLower)) ^ 2 =
      frozen ^ 2 / (nLower * bLower ^ 2) := by
  rw [div_pow, mul_pow, Real.sq_sqrt hn]

/-- The nonzero amplitude case, including a retained row-only coefficient.
The constant is exactly the constant of the normalized raw hybrid theorem. -/
theorem raw_hybrid_energy_with_amplitudes
    (Ext : Ideal (𝓞 K) → Prop)
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows ns bs ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ ns, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bs, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ a rho : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
      ∀ A B R : ℝ, 0 < A → 0 < B → 0 ≤ R →
      (∀ P ∈ ps, ‖a P‖ ≤ A) →
      (∀ n ∈ ns, ∀ b ∈ bs, ‖beta n b‖ ≤ B) →
      (∀ k ∈ rows, ‖rho k‖ ≤ R) →
      (∑ k ∈ rows, ‖rho k * hybridRow cubic quad ps ns bs a beta k‖ ^ 2) ≤
        (R * A * B) ^ 2 * C * (K0 * N0 * B0 * L0) ^ eps *
          (K0 + N0 * B0) * B0 * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := RawIdealHybrid.raw_ideal_hybrid_energy
    Ext hext_ne hext_mul hext_dvd cubic quad hκ hsquare hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp
    a rho beta A B R hA hBeta hR ha hbeta hrho
  let a' : Ideal (𝓞 K) → ℂ := fun P => a P / (A : ℂ)
  let beta' : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ := fun n b => beta n b / (B : ℂ)
  have ha' (P : Ideal (𝓞 K)) (hP : P ∈ ps) : ‖a' P‖ ≤ 1 := by
    dsimp [a']
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    exact (div_le_iff₀ hA).mpr (by simpa using ha P hP)
  have hb' (n : Ideal (𝓞 K)) (hn0 : n ∈ ns) (b : Ideal (𝓞 K)) (hb0 : b ∈ bs) :
      ‖beta' n b‖ ≤ 1 := by
    dsimp [beta']
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBeta]
    exact (div_le_iff₀ hBeta).mpr (by simpa using hbeta n hn0 b hb0)
  have hAn : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hA)
  have hBn : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hBeta)
  have heqa : (fun P => (A : ℂ) * a' P) = a := by
    funext P
    dsimp [a']
    field_simp [hAn]
  have heqb : (fun n b => (B : ℂ) * beta' n b) = beta := by
    funext n b
    dsimp [beta']
    field_simp [hBn]
  have heq (k : Ideal (𝓞 K)) :
      hybridRow cubic quad ps ns bs a beta k =
        (A : ℂ) * (B : ℂ) * hybridRow cubic quad ps ns bs a' beta' k := by
    rw [← hybridRow_scale_coefficients cubic quad ps ns bs a' beta' (A : ℂ) (B : ℂ) k,
      heqa, heqb]
  have henergy := hbound K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp a' beta' ha' hb'
  have hscale : (∑ k ∈ rows, ‖hybridRow cubic quad ps ns bs a beta k‖ ^ 2) =
      (A * B) ^ 2 * ∑ k ∈ rows, ‖hybridRow cubic quad ps ns bs a' beta' k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hA, abs_of_pos hBeta, mul_pow]
  calc
    _ ≤ R ^ 2 * ∑ k ∈ rows, ‖hybridRow cubic quad ps ns bs a beta k‖ ^ 2 :=
      finite_row_contraction rows rho _ R hR hrho
    _ = R ^ 2 * ((A * B) ^ 2 *
        ∑ k ∈ rows, ‖hybridRow cubic quad ps ns bs a' beta' k‖ ^ 2) := by rw [hscale]
    _ ≤ R ^ 2 * ((A * B) ^ 2 *
        (C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

/-- A full-cube coefficient with its actual pointwise norm denominator
feeds the raw theorem with the exact factor `Cf² / (C B²)`.  The case
`Cf=0` is proved separately from the vanishing original row. -/
theorem raw_hybrid_energy_frozen_cube
    (Ext : Ideal (𝓞 K) → Prop)
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows ns bs ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ ns, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bs, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ a rho : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
      ∀ frozen nLower bLower : ℝ, 0 ≤ frozen → 0 < nLower → 0 < bLower →
      (∀ n ∈ ns, nLower ≤ (Ideal.absNorm n : ℝ)) →
      (∀ b ∈ bs, bLower ≤ (Ideal.absNorm b : ℝ)) →
      (∀ P ∈ ps, ‖a P‖ ≤ 1) →
      (∀ n ∈ ns, ∀ b ∈ bs, ‖beta n b‖ ≤
        frozen / (Real.sqrt (Ideal.absNorm n : ℝ) * (Ideal.absNorm b : ℝ))) →
      (∀ k ∈ rows, ‖rho k‖ ≤ 1) →
      (∑ k ∈ rows, ‖rho k * hybridRow cubic quad ps ns bs a beta k‖ ^ 2) ≤
        (frozen ^ 2 / (nLower * bLower ^ 2)) * C * (K0 * N0 * B0 * L0) ^ eps *
          (K0 + N0 * B0) * B0 * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := raw_hybrid_energy_with_amplitudes
    Ext hext_ne hext_mul hext_dvd cubic quad hκ hsquare hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp
    a rho beta frozen nLower bLower hfrozen hnLower hbLower hncut hbcut ha hbeta hrho
  by_cases hfzero : frozen = 0
  · have hz (k : Ideal (𝓞 K)) : hybridRow cubic quad ps ns bs a beta k = 0 := by
      apply hybridRow_zero_of_beta_norm cubic quad ps ns bs a beta
      intro n hn0 b hb0
      simpa only [hfzero, zero_div] using hbeta n hn0 b hb0
    simp only [hz, mul_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, hfzero, zero_div, zero_mul, le_refl]
  · have hfp : 0 < frozen := lt_of_le_of_ne hfrozen (Ne.symm hfzero)
    let M : ℝ := frozen / (Real.sqrt nLower * bLower)
    have hden : 0 < Real.sqrt nLower * bLower := mul_pos (Real.sqrt_pos.mpr hnLower) hbLower
    have hM : 0 < M := div_pos hfp hden
    have hbetaM (n : Ideal (𝓞 K)) (hn0 : n ∈ ns) (b : Ideal (𝓞 K)) (hb0 : b ∈ bs) :
        ‖beta n b‖ ≤ M := by
      apply (hbeta n hn0 b hb0).trans
      apply div_le_div_of_nonneg_left hfrozen hden
      exact mul_le_mul (Real.sqrt_le_sqrt (hncut n hn0)) (hbcut b hb0)
        hbLower.le (Real.sqrt_nonneg _)
    have he := hbound K0 N0 B0 L0 hK hN hB hL rows ns bs ps hrows hn hb hp
      a rho beta 1 M 1 (by norm_num) hM (by norm_num) ha hbetaM hrho
    simp only [one_mul, mul_one] at he
    have hMsq : M ^ 2 = frozen ^ 2 / (nLower * bLower ^ 2) :=
      frozen_amplitude_sq frozen nLower bLower hnLower.le
    rw [hMsq] at he
    exact he

#print axioms raw_hybrid_energy_with_amplitudes
#print axioms raw_hybrid_energy_frozen_cube

end
end HeckeSkeleton.LowEnergy.HybridScaling
