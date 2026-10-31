import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernel

/-!
# Uniform mass of the common Fourier kernel

A continuous linear map between genuine Schwartz spaces has a weighted
L¹ bound controlled by finitely many original seminorms.  The finite set,
constant and polynomial order are chosen before the test function and
all row and column data.  The proof uses actual temperate-volume decay
and continuity of the pulled-back finite supremum of seminorms.

The final paired estimate applies this to Fourier transformation after
the fixed kernel transport.  Its hypotheses are bounds on the two
separated child energies.  No parent moment inequality is assumed.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap
open MeasureTheory MeasureTheory.Measure

namespace HeckeSkeleton.Moments.EngineStep

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Uniform weighted L¹ control for any actual continuous Schwartz operator. -/
theorem schwartz_operator_weighted_L1_bound
    (T : 𝓢(E, ℂ) →L[ℝ] 𝓢(V, ℂ)) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(E, ℂ),
      Integrable (fun ξ : V => ‖T F ξ‖ * (1 + ‖ξ‖) ^ J) ∧
      (∫ ξ : V, ‖T F ξ‖ * (1 + ‖ξ‖) ^ J) ≤
        C * s.sup (schwartzSeminormFamily ℝ E ℂ) F := by
  let n : ℕ := (volume : Measure V).integrablePower
  let t : Finset (ℕ × ℕ) := Finset.Iic (n + J, 0)
  let Q : Seminorm ℝ 𝓢(E, ℂ) :=
    (t.sup (schwartzSeminormFamily ℝ V ℂ)).comp T.toLinearMap
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (s := t)
      (fun i hi => (schwartz_withSeminorms ℝ V ℂ).continuous_seminorm i)).comp T.continuous
  obtain ⟨s, D, hD, hTD⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E ℂ) Q hQ
  have hdecay : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ (-(n : ℝ))) :=
    integrable_pow_neg_integrablePower volume
  let C₀ : ℝ := (2 : ℝ) ^ (n + J) * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(n : ℝ))
  have hC₀ : 0 ≤ C₀ := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun ξ => Real.rpow_nonneg (by positivity) _)
  let C : ℝ := 1 + C₀ * (D : ℝ)
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hC₀ D.coe_nonneg)
  refine ⟨s, C, hC, fun F => ?_⟩
  have hsup : t.sup (schwartzSeminormFamily ℝ V ℂ) (T F) ≤
      (D : ℝ) * s.sup (schwartzSeminormFamily ℝ E ℂ) F := by
    exact Seminorm.le_def.mp hTD F
  have hpoint (ξ : V) : ‖T F ξ‖ * (1 + ‖ξ‖) ^ J ≤
      (1 + ‖ξ‖) ^ (-(n : ℝ)) *
        ((2 : ℝ) ^ (n + J) * t.sup (schwartzSeminormFamily ℝ V ℂ) (T F)) := by
    have hp : 0 < 1 + ‖ξ‖ := by positivity
    have hh : (1 + ‖ξ‖) ^ (n + J) * ‖T F ξ‖ ≤
        (2 : ℝ) ^ (n + J) * t.sup (schwartzSeminormFamily ℝ V ℂ) (T F) := by
      change (1 + ‖ξ‖) ^ (n + J) * ‖T F ξ‖ ≤
        (2 : ℝ) ^ (n + J) *
          ((Finset.Iic (n + J, 0)).sup
            (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) (T F)
      simpa only [norm_iteratedFDeriv_zero] using
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
          (m := (n + J, 0)) (k := n + J) (n := 0) le_rfl le_rfl (T F) ξ)
    rw [Real.rpow_neg hp.le, ← div_eq_inv_mul,
      le_div_iff₀' (Real.rpow_pos_of_pos hp (n : ℝ)), Real.rpow_natCast]
    simpa only [pow_add, mul_assoc, mul_left_comm, mul_comm] using hh
  have hcont : Continuous (fun ξ : V => ‖T F ξ‖ * (1 + ‖ξ‖) ^ J) :=
    (T F).continuous.norm.mul ((continuous_const.add continuous_norm).pow J)
  have hmajorant := hdecay.mul_const
    ((2 : ℝ) ^ (n + J) * t.sup (schwartzSeminormFamily ℝ V ℂ) (T F))
  have hint : Integrable (fun ξ : V => ‖T F ξ‖ * (1 + ‖ξ‖) ^ J) := by
    apply hmajorant.mono' hcont.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
      exact hpoint ξ
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ ξ : V, (1 + ‖ξ‖) ^ (-(n : ℝ)) *
        ((2 : ℝ) ^ (n + J) * t.sup (schwartzSeminormFamily ℝ V ℂ) (T F)) :=
      integral_mono hint hmajorant hpoint
    _ = C₀ * t.sup (schwartzSeminormFamily ℝ V ℂ) (T F) := by
      rw [integral_mul_const]
      dsimp only [C₀]
      ring
    _ ≤ C₀ * ((D : ℝ) * s.sup (schwartzSeminormFamily ℝ E ℂ) F) :=
      mul_le_mul_of_nonneg_left hsup hC₀
    _ ≤ C * s.sup (schwartzSeminormFamily ℝ E ℂ) F := by
      dsimp only [C]
      nlinarith [apply_nonneg (s.sup (schwartzSeminormFamily ℝ E ℂ)) F]

/-- The requested weighted mass for the actual Fourier transform, with
the controlling seminorms fixed before the Schwartz function. -/
theorem joint_fourier_mass_bound (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(V, ℂ),
      Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ * (1 + ‖ξ‖) ^ J) ∧
      (∫ ξ : V, ‖(𝓕 F) ξ‖ * (1 + ‖ξ‖) ^ J) ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) F :=
  schwartz_operator_weighted_L1_bound (SchwartzMap.fourierTransformCLM ℝ) J

/-- After a fixed actual kernel transport, the common Fourier mass is
uniformly paid by original seminorms.  The constants precede all columns,
rows, coefficients and child-energy bounds. -/
theorem joint_kernel_paired_cauchy_uniform
    (transport : 𝓢(E, ℂ) →L[ℝ] 𝓢(V, ℂ)) (J₁ J₂ : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(E, ℂ),
      ∀ {H ι κ : Type*} (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
        (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
        (x : H → ι → V) (y : H → κ → V) (B₁ B₂ : ℝ),
      0 ≤ B₁ → 0 ≤ B₂ →
      (∀ ξ : V, Real.sqrt (jointColumnEnergy rows leftColumns q c x ξ) ≤
        B₁ * (1 + ‖ξ‖) ^ J₁) →
      (∀ ξ : V, Real.sqrt
          (jointColumnEnergy rows rightColumns q (fun h b => star (d h b)) y ξ) ≤
        B₂ * (1 + ‖ξ‖) ^ J₂) →
      ‖jointKernelPairing (transport F) rows leftColumns rightColumns q c d x y‖ ≤
        C * s.sup (schwartzSeminormFamily ℝ E ℂ) F * B₁ * B₂ := by
  let T : 𝓢(E, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ).comp transport
  obtain ⟨s, C, hC, hmass⟩ := schwartz_operator_weighted_L1_bound T (J₁ + J₂)
  refine ⟨s, C, hC, ?_⟩
  intro F H ι κ rows leftColumns rightColumns q c d x y B₁ B₂ hB₁ hB₂ hleft hright
  have hI : Integrable (fun ξ : V => ‖(𝓕 (transport F)) ξ‖ * (1 + ‖ξ‖) ^ (J₁ + J₂)) :=
    (hmass F).1
  have hM : (∫ ξ : V, ‖(𝓕 (transport F)) ξ‖ * (1 + ‖ξ‖) ^ (J₁ + J₂)) ≤
      C * s.sup (schwartzSeminormFamily ℝ E ℂ) F := (hmass F).2
  calc
    _ ≤ ∫ ξ : V, ‖(𝓕 (transport F)) ξ‖ *
        (Real.sqrt (jointColumnEnergy rows leftColumns q c x ξ) *
          Real.sqrt (jointColumnEnergy rows rightColumns q (fun h b => star (d h b)) y ξ)) :=
      joint_kernel_paired_cauchy (transport F) rows leftColumns rightColumns q c d x y
    _ ≤ ∫ ξ : V, (B₁ * B₂) *
        (‖(𝓕 (transport F)) ξ‖ * (1 + ‖ξ‖) ^ (J₁ + J₂)) := by
      apply integral_mono
        (joint_kernel_energy_integrable (transport F) rows leftColumns rightColumns q c
          (fun h b => star (d h b)) x y) (hI.const_mul (B₁ * B₂))
      intro ξ
      have hh := mul_le_mul (hleft ξ) (hright ξ) (Real.sqrt_nonneg _)
        (mul_nonneg hB₁ (by positivity))
      have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg ((𝓕 (transport F)) ξ))
      convert hh' using 1 <;> simp only [pow_add] <;> ring
    _ = (B₁ * B₂) * ∫ ξ : V, ‖(𝓕 (transport F)) ξ‖ * (1 + ‖ξ‖) ^ (J₁ + J₂) :=
      integral_const_mul _ _
    _ ≤ (B₁ * B₂) * (C * s.sup (schwartzSeminormFamily ℝ E ℂ) F) :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg hB₁ hB₂)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.schwartz_operator_weighted_L1_bound
#print axioms HeckeSkeleton.Moments.EngineStep.joint_fourier_mass_bound
#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_paired_cauchy_uniform

