import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildMomentDataAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernelBounds

/-!
# The common Fourier kernel bounded by actual child moments

This adapter combines the actual finite row and polynomial calibration with
the common-kernel Cauchy estimate.  Its analytic inputs are bounds for the
repository's `pairedEnergy` of the two child families.  The comparison of
the separated column energies with these moments is proved, rather than
assumed.  Both sides use the same actual row weight and the same Fourier
measure.  One finite set of original Schwartz seminorms is fixed before
the profiles, rows, columns, and children.

The Fourier parameter ranges over the whole Euclidean space.  The child
profiles may depend on that parameter.  A capacity removal theorem can
provide the displayed child bounds when its geometric slot choice has
already been fixed uniformly for the family; this theorem makes no
parameter-dependent choice of slots.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A genuine common-kernel bound from pointwise actual child calibration.
The only moment estimates in the assumptions are those of the two actual
children; no bound for the parent or for `jointColumnEnergy` is an input. -/
theorem joint_kernel_bound_of_actual_children
    (transport : 𝓢(E, ℂ) →L[ℝ] 𝓢(V, ℂ)) (J₁ J₂ : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ F : 𝓢(E, ℂ),
      ∀ {H ι κ : Type*} {ω₁ ψ₁ ω₂ ψ₂ : HeckeCharacter K}
        (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
        (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
        (x : H → ι → V) (y : H → κ → V)
        (D₁ : V → MomentData K ω₁ ψ₁) (D₂ : V → MomentData K ω₂ ψ₂)
        (a₁ a₂ : RealParameters) (Z : ℝ) (t₁ t₂ : V → ℝ)
        (rowMap₁ rowMap₂ : H → NonzeroIdeal K)
        (W : ℝ) (B₁ B₂ : ℕ) (A₁ A₂ : ℝ),
      0 ≤ W → 0 ≤ A₁ → 0 ≤ A₂ →
      (∀ h ∈ rows, ‖q h‖ ≤ W) →
      (∀ ξ : V, ∀ h ∈ rows, rowMap₁ h ∈ pairedRows (D₁ ξ) a₁ Z) →
      (∀ ξ : V, ∀ h ∈ rows, rowMap₂ h ∈ pairedRows (D₂ ξ) a₂ Z) →
      (∀ u : NonzeroIdeal K,
        (rows.filter (fun h => rowMap₁ h = u)).card ≤ B₁) →
      (∀ u : NonzeroIdeal K,
        (rows.filter (fun h => rowMap₂ h = u)).card ≤ B₂) →
      (∀ ξ : V, ∀ h ∈ rows,
        jointFourierColumn leftColumns (c h) (x h) ξ =
          plainPolynomial (D₁ ξ) (D₁ ξ).plainTest₁ (rowMap₁ h)
              (Z ^ a₁.n₁) (t₁ ξ) *
            plainPolynomial (D₁ ξ) (D₁ ξ).plainTest₂ (rowMap₁ h)
              (Z ^ a₁.n₂) (t₁ ξ) *
            slotProduct (D₁ ξ) (rowMap₁ h) Z (t₁ ξ)) →
      (∀ ξ : V, ∀ h ∈ rows,
        jointFourierColumn rightColumns (fun b => star (d h b)) (y h) ξ =
          plainPolynomial (D₂ ξ) (D₂ ξ).plainTest₁ (rowMap₂ h)
              (Z ^ a₂.n₁) (t₂ ξ) *
            plainPolynomial (D₂ ξ) (D₂ ξ).plainTest₂ (rowMap₂ h)
              (Z ^ a₂.n₂) (t₂ ξ) *
            slotProduct (D₂ ξ) (rowMap₂ h) Z (t₂ ξ)) →
      (∀ ξ : V, Real.sqrt (pairedEnergy (D₁ ξ) a₁ Z (t₁ ξ)) ≤
        A₁ * (1 + ‖ξ‖) ^ J₁) →
      (∀ ξ : V, Real.sqrt (pairedEnergy (D₂ ξ) a₂ Z (t₂ ξ)) ≤
        A₂ * (1 + ‖ξ‖) ^ J₂) →
      ‖jointKernelPairing (transport F) rows leftColumns rightColumns q c d x y‖ ≤
        C * s.sup (schwartzSeminormFamily ℝ E ℂ) F *
          (Real.sqrt (W * (B₁ : ℝ)) * A₁) *
          (Real.sqrt (W * (B₂ : ℝ)) * A₂) := by
  obtain ⟨s, C, hC, hkernel⟩ :=
    joint_kernel_paired_cauchy_uniform transport J₁ J₂
  refine ⟨s, C, hC, ?_⟩
  intro F H ι κ ω₁ ψ₁ ω₂ ψ₂ rows leftColumns rightColumns q c d x y
    D₁ D₂ a₁ a₂ Z t₁ t₂ rowMap₁ rowMap₂ W B₁ B₂ A₁ A₂
    hW hA₁ hA₂ hweight hrows₁ hrows₂ hfiber₁ hfiber₂ hpoly₁ hpoly₂ hchild₁ hchild₂
  have henergy₁ := joint_column_energy_le_actual_paired rows leftColumns q c x
    D₁ a₁ Z t₁ rowMap₁ W B₁ hW hweight hrows₁ hfiber₁ hpoly₁
  have henergy₂ := joint_column_energy_le_actual_paired rows rightColumns q
    (fun h b => star (d h b)) y D₂ a₂ Z t₂ rowMap₂ W B₂
    hW hweight hrows₂ hfiber₂ hpoly₂
  apply hkernel F rows leftColumns rightColumns q c d x y
    (Real.sqrt (W * (B₁ : ℝ)) * A₁) (Real.sqrt (W * (B₂ : ℝ)) * A₂)
    (mul_nonneg (Real.sqrt_nonneg _) hA₁)
    (mul_nonneg (Real.sqrt_nonneg _) hA₂)
  · intro ξ
    calc
      _ ≤ Real.sqrt (W * (B₁ : ℝ) * pairedEnergy (D₁ ξ) a₁ Z (t₁ ξ)) :=
        Real.sqrt_le_sqrt (henergy₁ ξ)
      _ = Real.sqrt (W * (B₁ : ℝ)) *
          Real.sqrt (pairedEnergy (D₁ ξ) a₁ Z (t₁ ξ)) :=
        Real.sqrt_mul (mul_nonneg hW (Nat.cast_nonneg _)) _
      _ ≤ Real.sqrt (W * (B₁ : ℝ)) * (A₁ * (1 + ‖ξ‖) ^ J₁) :=
        mul_le_mul_of_nonneg_left (hchild₁ ξ) (Real.sqrt_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  · intro ξ
    calc
      _ ≤ Real.sqrt (W * (B₂ : ℝ) * pairedEnergy (D₂ ξ) a₂ Z (t₂ ξ)) :=
        Real.sqrt_le_sqrt (henergy₂ ξ)
      _ = Real.sqrt (W * (B₂ : ℝ)) *
          Real.sqrt (pairedEnergy (D₂ ξ) a₂ Z (t₂ ξ)) :=
        Real.sqrt_mul (mul_nonneg hW (Nat.cast_nonneg _)) _
      _ ≤ Real.sqrt (W * (B₂ : ℝ)) * (A₂ * (1 + ‖ξ‖) ^ J₂) :=
        mul_le_mul_of_nonneg_left (hchild₂ ξ) (Real.sqrt_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_bound_of_actual_children
