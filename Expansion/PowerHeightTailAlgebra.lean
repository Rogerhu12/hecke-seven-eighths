import HeckeGeneral.Analysis.PowerHeightComparison

/-! Finite assembly preserves the order of the external height-tail
quantifiers. Both scale powers and height degrees are fixed before tau and
the external decay order. No actual tail estimate is assumed in a source
constructor; this file contains only the algebra for combining proved ones. -/

set_option autoImplicit false
noncomputable section
namespace HeckeGeneral.Analysis

theorem PowerHeightTailBound.of_uniform_decay {E : ℝ → ℝ → ℂ}
    {A R : ℝ} (hA : 0 ≤ A)
    (h : ∀ N : ℕ, ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z H : ℝ, Z₀ ≤ Z → 1 ≤ H →
        ‖E Z H‖ ≤ C * Z ^ R * (1 + H) ^ A * H ^ (-(N : ℝ))) :
    PowerHeightTailBound E := by
  refine ⟨A, R, 1, hA, by norm_num, ?_⟩
  intro τ hτ _ N
  obtain ⟨C, Z₀, hC, hZ₀, hb⟩ := h N
  exact ⟨C, Z₀, hC, hZ₀, fun Z hZ =>
    hb Z (Z ^ τ) hZ (Real.one_le_rpow (hZ₀.trans hZ) hτ.le)⟩

theorem PowerHeightTailBound.add {E F : ℝ → ℝ → ℂ}
    (hE : PowerHeightTailBound E) (hF : PowerHeightTailBound F) :
    PowerHeightTailBound (fun Z H => E Z H + F Z H) := by
  obtain ⟨AE, RE, cE, hAE, hcE, hbE⟩ := hE
  obtain ⟨AF, RF, cF, hAF, hcF, hbF⟩ := hF
  refine ⟨max AE AF, max RE RF, min cE cF,
    hAE.trans (le_max_left _ _), lt_min hcE hcF, ?_⟩
  intro τ hτ hτc N
  obtain ⟨CE, ZE, hCE, hZE, he⟩ := hbE τ hτ (hτc.trans (min_le_left _ _)) N
  obtain ⟨CF, ZF, hCF, hZF, hf⟩ := hbF τ hτ (hτc.trans (min_le_right _ _)) N
  refine ⟨CE + CF, max ZE ZF, add_pos hCE hCF,
    hZE.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hZe : ZE ≤ Z := (le_max_left _ _).trans hZ
  have hZf : ZF ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZE.trans hZe
  have hH1 : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  have hRE := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_left RE RF)
  have hRF := Real.rpow_le_rpow_of_exponent_le hZ1 (le_max_right RE RF)
  have hAE' := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ 1 + Z ^ τ by linarith) (le_max_left AE AF)
  have hAF' := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ 1 + Z ^ τ by linarith) (le_max_right AE AF)
  have htail : 0 ≤ (Z ^ τ) ^ (-(N : ℝ)) := Real.rpow_nonneg (by linarith) _
  have he' : ‖E Z (Z ^ τ)‖ ≤
      CE * Z ^ max RE RF * (1 + Z ^ τ) ^ max AE AF * (Z ^ τ) ^ (-(N : ℝ)) := by
    apply (he Z hZe).trans
    gcongr
  have hf' : ‖F Z (Z ^ τ)‖ ≤
      CF * Z ^ max RE RF * (1 + Z ^ τ) ^ max AE AF * (Z ^ τ) ^ (-(N : ℝ)) := by
    apply (hf Z hZf).trans
    gcongr
  calc
    ‖E Z (Z ^ τ) + F Z (Z ^ τ)‖ ≤ ‖E Z (Z ^ τ)‖ + ‖F Z (Z ^ τ)‖ := norm_add_le _ _
    _ ≤ CE * Z ^ max RE RF * (1 + Z ^ τ) ^ max AE AF * (Z ^ τ) ^ (-(N : ℝ)) +
        CF * Z ^ max RE RF * (1 + Z ^ τ) ^ max AE AF * (Z ^ τ) ^ (-(N : ℝ)) :=
      add_le_add he' hf'
    _ = _ := by ring

theorem PowerHeightTailBound.neg {E : ℝ → ℝ → ℂ}
    (h : PowerHeightTailBound E) : PowerHeightTailBound (fun Z H => -E Z H) := by
  simpa only [PowerHeightTailBound, norm_neg] using h

theorem PowerHeightTailBound.sub {E F : ℝ → ℝ → ℂ}
    (hE : PowerHeightTailBound E) (hF : PowerHeightTailBound F) :
    PowerHeightTailBound (fun Z H => E Z H - F Z H) := by
  simpa only [sub_eq_add_neg] using hE.add hF.neg

theorem PowerHeightTailBound.of_eventuallyEq {E F : ℝ → ℝ → ℂ}
    (hE : PowerHeightTailBound E) (Zmin : ℝ)
    (heq : ∀ Z H : ℝ, Zmin ≤ Z → 1 ≤ H → E Z H = F Z H) :
    PowerHeightTailBound F := by
  obtain ⟨A, R, ceiling, hA, hc, hb⟩ := hE
  refine ⟨A, R, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc N
  obtain ⟨C, Z₀, hC, hZ₀, h⟩ := hb τ hτ hτc N
  refine ⟨C, max Z₀ Zmin, hC, hZ₀.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hZ' := (le_max_left _ _).trans hZ
  rw [← heq Z (Z ^ τ) ((le_max_right _ _).trans hZ)
    (Real.one_le_rpow (hZ₀.trans hZ') hτ.le)]
  exact h Z hZ'

end HeckeGeneral.Analysis

#print axioms HeckeGeneral.Analysis.PowerHeightTailBound.of_uniform_decay
#print axioms HeckeGeneral.Analysis.PowerHeightTailBound.add
#print axioms HeckeGeneral.Analysis.PowerHeightTailBound.sub
#print axioms HeckeGeneral.Analysis.PowerHeightTailBound.of_eventuallyEq
