import HeckeGeneral.Analysis.GlobalThetaData

/-! Holomorphy and uniform boundedness of the finite Mellin factor on closed
vertical strips inside `Re s > -1/3`, using only absolute Mellin summability. -/

noncomputable section
namespace HeckeSkeleton.ThetaKernel
open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S)

theorem norm_coeff_mul_cpow (a : ℂ) (N : ℕ) (hN : 0 < N) (k : ℤ) (s : ℂ) :
    ‖a * (N : ℂ) ^ (-(k : ℂ) * s)‖ = ‖a‖ * (N : ℝ) ^ (-(k : ℝ) * s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  congr 2
  simp [Complex.mul_re]

theorem natpow_strip_le (N : ℕ) (hN : 1 ≤ N) (k : ℤ) {σ σ0 Λ : ℝ} (h0 : σ0 ≤ σ) (h1 : σ ≤ Λ) :
    (N : ℝ) ^ (-(k : ℝ) * σ) ≤ (N : ℝ) ^ (-(k : ℝ) * σ0) + (N : ℝ) ^ (-(k : ℝ) * Λ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have p0 : 0 ≤ (N : ℝ) ^ (-(k : ℝ) * σ0) := by positivity
  have p1 : 0 ≤ (N : ℝ) ^ (-(k : ℝ) * Λ) := by positivity
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have : (N : ℝ) ^ (-(k : ℝ) * σ) ≤ (N : ℝ) ^ (-(k : ℝ) * σ0) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    linarith
  · have hk' : (k : ℝ) < 0 := by exact_mod_cast hk
    have : (N : ℝ) ^ (-(k : ℝ) * σ) ≤ (N : ℝ) ^ (-(k : ℝ) * Λ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
    linarith

variable {K S F}

/-- Summable majorant on a closed strip. -/
theorem finite_term_majorant (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (l : Fin F.terms) (p : S)
    {σ0 Λ : ℝ} (h0 : -(1 / 3 : ℝ) < σ0) (hΛ : -(1 / 3 : ℝ) < Λ) :
    Summable (fun k : ℤ => ‖F.coefficient u κ l p k‖ *
      ((p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * σ0) +
        (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * Λ))) := by
  have hN : 0 < p.val.asIdeal.absNorm :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  have h1 := (hF.absolute_mellin u κ l p (σ0 : ℂ) (by simpa using h0)).norm
  have h2 := (hF.absolute_mellin u κ l p (Λ : ℂ) (by simpa using hΛ)).norm
  have e : ∀ x : ℝ, ∀ k : ℤ, ‖F.coefficient u κ l p k *
      (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * (x : ℂ))‖ =
      ‖F.coefficient u κ l p k‖ * (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * x) := by
    intro x k
    rw [norm_coeff_mul_cpow _ _ hN]; simp
  simp only [e] at h1 h2
  convert h1.add h2 using 1
  ext k; ring

theorem local_series_norm_le (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (l : Fin F.terms) (p : S)
    {σ0 Λ : ℝ} (h0 : -(1 / 3 : ℝ) < σ0) (hΛ : -(1 / 3 : ℝ) < Λ) (s : ℂ)
    (hs0 : σ0 ≤ s.re) (hs1 : s.re ≤ Λ) :
    ‖localMellinSeries K S F u κ l p s‖ ≤
      ∑' k : ℤ, ‖F.coefficient u κ l p k‖ *
        ((p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * σ0) +
          (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * Λ)) := by
  have hN : 0 < p.val.asIdeal.absNorm :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  unfold localMellinSeries
  refine tsum_of_norm_bounded (finite_term_majorant hF u κ l p h0 hΛ).hasSum (fun k => ?_)
  rw [norm_coeff_mul_cpow _ _ hN]
  exact mul_le_mul_of_nonneg_left
    (natpow_strip_le _ (le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)) k hs0 hs1)
    (norm_nonneg _)

theorem differentiableOn_localMellinSeries (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (l : Fin F.terms) (p : S)
    {σ0 Λ : ℝ} (h0 : -(1 / 3 : ℝ) < σ0) (hΛ : -(1 / 3 : ℝ) < Λ) :
    DifferentiableOn ℂ (localMellinSeries K S F u κ l p) {s : ℂ | σ0 < s.re ∧ s.re < Λ} := by
  have hN : 0 < p.val.asIdeal.absNorm :=
    lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
  have hU : IsOpen {s : ℂ | σ0 < s.re ∧ s.re < Λ} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  unfold localMellinSeries
  refine Complex.differentiableOn_tsum_of_summable_norm (finite_term_majorant hF u κ l p h0 hΛ)
    (fun k => ?_) hU (fun k s hs => ?_)
  · apply Differentiable.differentiableOn
    have : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    exact (differentiable_const _).mul
      (Differentiable.const_cpow (by fun_prop) (Or.inl this))
  · rw [norm_coeff_mul_cpow _ _ hN]
    exact mul_le_mul_of_nonneg_left
      (natpow_strip_le _ (le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)) k
        hs.1.le hs.2.le) (norm_nonneg _)

theorem differentiableAt_finiteMellinFactor (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) {s : ℂ}
    (hs : -(1 / 3 : ℝ) < s.re) : DifferentiableAt ℂ (finiteMellinFactor K S F u κ) s := by
  set σ0 : ℝ := (-(1 / 3) + s.re) / 2 with hσ0
  have h0 : -(1 / 3 : ℝ) < σ0 := by rw [hσ0]; linarith
  have h1 : σ0 < s.re := by rw [hσ0]; linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = s.re + 1 := ⟨_, rfl⟩
  have hΛ : -(1 / 3 : ℝ) < Λ := by rw [hΛdef]; linarith
  have hU : IsOpen {s : ℂ | σ0 < s.re ∧ s.re < Λ} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : s ∈ {s' : ℂ | σ0 < s'.re ∧ s'.re < Λ} := ⟨h1, by rw [hΛdef]; linarith⟩
  have hd : DifferentiableOn ℂ (finiteMellinFactor K S F u κ)
      {s' : ℂ | σ0 < s'.re ∧ s'.re < Λ} := by
    unfold finiteMellinFactor
    refine DifferentiableOn.fun_sum (fun l _ => ?_)
    exact DifferentiableOn.fun_finsetProd (fun p _ =>
      differentiableOn_localMellinSeries hF u κ l p h0 hΛ)
  exact (hd.differentiableAt (hU.mem_nhds hmem))

/-- The explicit strip constant for the finite factor at one pair of classes. -/
def finiteStripConst (hF : FiniteMellinAdmissible K S F) (u : SixthUnitClasses K S)
    (κ : SixthLocalClasses K S) (σlo Λ : ℝ) : ℝ :=
  ∑ l : Fin F.terms, ∏ p : S,
    ∑' k : ℤ, ‖F.coefficient u κ l p k‖ *
        ((p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * σlo) +
          (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * Λ))

theorem finiteMellinFactor_norm_le (hF : FiniteMellinAdmissible K S F)
    (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) {σlo Λ : ℝ}
    (hlo : -(1 / 3 : ℝ) < σlo) (hΛ : -(1 / 3 : ℝ) < Λ) (s : ℂ)
    (hs0 : σlo ≤ s.re) (hs1 : s.re ≤ Λ) :
    ‖finiteMellinFactor K S F u κ s‖ ≤ finiteStripConst hF u κ σlo Λ := by
  unfold finiteMellinFactor finiteStripConst
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => ?_))
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => local_series_norm_le hF u κ l p hlo hΛ s hs0 hs1)

/-- Uniformity of the finite strip constants in the sector `u` and local class `κ`.
It holds as soon as the set of sixth local classes is finite. -/
def StripUniform (hF : FiniteMellinAdmissible K S F) : Prop :=
  ∀ σlo Λ : ℝ, -(1 / 3 : ℝ) < σlo → -(1 / 3 : ℝ) < Λ →
    ∃ B : ℝ, ∀ (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S),
      finiteStripConst hF u κ σlo Λ ≤ B

theorem stripUniform_of_finite [Finite (SixthUnitClasses K S)] [Finite (SixthLocalClasses K S)]
    (hF : FiniteMellinAdmissible K S F) : StripUniform hF := by
  intro σlo Λ _ _
  obtain ⟨M₀, hM⟩ := (Set.finite_range
    (fun x : SixthUnitClasses K S × SixthLocalClasses K S =>
      finiteStripConst hF x.1 x.2 σlo Λ)).bddAbove
  exact ⟨M₀, fun u κ => hM ⟨(u, κ), rfl⟩⟩

theorem finiteMellinFactor_bound (hF : FiniteMellinAdmissible K S F) (hU : StripUniform hF)
    {σlo Λ : ℝ} (hlo : -(1 / 3 : ℝ) < σlo)
    (hΛ : -(1 / 3 : ℝ) < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SixthUnitClasses K S) (κ : SixthLocalClasses K S) (s : ℂ),
      σlo ≤ s.re → s.re ≤ Λ → ‖finiteMellinFactor K S F u κ s‖ ≤ C := by
  obtain ⟨M₀, hM⟩ := hU σlo Λ hlo hΛ
  refine ⟨max M₀ 0, le_max_right _ _, fun u κ s h0 h1 => ?_⟩
  exact (finiteMellinFactor_norm_le hF u κ hlo hΛ s h0 h1).trans
    ((hM u κ).trans (le_max_left _ _))

end HeckeSkeleton.ThetaKernel
