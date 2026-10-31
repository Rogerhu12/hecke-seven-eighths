import HeckeGeneral.Characters.FiniteCircleFourier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildren

/-!
# Fixed finite-ray phase expansion with uniform coefficient mass

The carrier is the full circle-valued dual of a fixed finite group `G × G`.
Its coefficients are the normalized finite Fourier coefficients of the
actual circle-valued phase table.  Thus neither the expansion coefficients
nor their aggregate norm are additional inputs.

For the sextic source, MOM_BASE supplies only the pointwise calibration of
`actualCommonPhase` with a phase table on the fixed ray quotient.  The last
theorem derives the exact hypothesis used by `actual_full_correlation_children`
and the uniform mass bound from that calibration.  The group must be fixed
before the scale, rows, columns and frozen common factors are chosen.

`FiniteRayCoefficientExpansion` separately treats the identity-ray filter;
it does not by itself identify the two-variable reciprocity phase table.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open HeckeGeneral.Characters

variable (G : Type*) [CommGroup G] [Fintype G]

local instance : Fintype ((G × G) →* Circle) := Fintype.ofFinite _

/-- Canonical normalized coefficients on the actual finite circle dual. -/
def fixedPhaseCoefficient (Φ : G × G → Circle) (χ : (G × G) →* Circle) : ℂ :=
  (Nat.card (G × G) : ℂ)⁻¹ *
    finiteFourierCoeff (G × G) (fun z => (Φ z : ℂ)) χ

/-- The left-coordinate restriction is an actual finite-order character. -/
def fixedLeftPhase (χ : (G × G) →* Circle) : G →* Circle :=
  χ.comp (MonoidHom.inl G G)

/-- The inverse right restriction matches the star on the second column. -/
def fixedRightPhase (χ : (G × G) →* Circle) : G →* Circle :=
  (χ.comp (MonoidHom.inr G G))⁻¹

theorem fixed_phase_characters_finite_order (χ : (G × G) →* Circle) :
    IsOfFinOrder (fixedLeftPhase G χ) ∧ IsOfFinOrder (fixedRightPhase G χ) :=
  ⟨circleCharacter_isOfFinOrder G _, circleCharacter_isOfFinOrder G _⟩

@[simp] theorem fixed_left_phase_norm (χ : (G × G) →* Circle) (x : G) :
    ‖(fixedLeftPhase G χ x : ℂ)‖ = 1 := Circle.norm_coe _

@[simp] theorem fixed_right_phase_norm (χ : (G × G) →* Circle) (y : G) :
    ‖(fixedRightPhase G χ y : ℂ)‖ = 1 := Circle.norm_coe _

theorem fixed_phase_character_factor (χ : (G × G) →* Circle) (x y : G) :
    (χ (x, y) : ℂ) =
      (fixedLeftPhase G χ x : ℂ) * star (fixedRightPhase G χ y : ℂ) := by
  have hright : star (fixedRightPhase G χ y : ℂ) = (χ (1, y) : ℂ) := by
    change star (((χ (1, y))⁻¹ : Circle) : ℂ) = (χ (1, y) : ℂ)
    rw [Circle.coe_inv_eq_conj]
    exact star_star _
  rw [hright]
  change (χ (x, y) : ℂ) = (χ (x, 1) : ℂ) * (χ (1, y) : ℂ)
  rw [← Circle.coe_mul, ← map_mul]
  simp

/-- The separated expansion is finite Fourier inversion, including its
normalizing denominator; the right character is conjugated exactly once. -/
theorem fixed_phase_expansion (Φ : G × G → Circle) (x y : G) :
    (Φ (x, y) : ℂ) =
      ∑ χ : (G × G) →* Circle, fixedPhaseCoefficient G Φ χ *
        (fixedLeftPhase G χ x : ℂ) * star (fixedRightPhase G χ y : ℂ) := by
  have hinv := congrFun
    (finiteFourier_inverse_coeff (G × G) (fun z => (Φ z : ℂ))) (x, y)
  calc
    (Φ (x, y) : ℂ) = (Nat.card (G × G) : ℂ)⁻¹ *
        ∑ χ : (G × G) →* Circle,
          finiteFourierCoeff (G × G) (fun z => (Φ z : ℂ)) χ * (χ (x, y) : ℂ) :=
      hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [fixed_phase_character_factor G]
      simp only [fixedPhaseCoefficient]
      ring

/-- Every normalized coefficient has norm at most one. -/
theorem fixed_phase_coefficient_norm (Φ : G × G → Circle)
    (χ : (G × G) →* Circle) : ‖fixedPhaseCoefficient G Φ χ‖ ≤ 1 := by
  have hsum :
      ‖finiteFourierCoeff (G × G) (fun z => (Φ z : ℂ)) χ‖ ≤
        (Nat.card (G × G) : ℝ) := by
    calc
      _ ≤ ∑ z : G × G, ‖(Φ z : ℂ) * (χ z : ℂ)⁻¹‖ := norm_sum_le _ _
      _ = _ := by simp [norm_mul, norm_inv, Nat.card_eq_fintype_card]
  calc
    ‖fixedPhaseCoefficient G Φ χ‖ = (Nat.card (G × G) : ℝ)⁻¹ *
        ‖finiteFourierCoeff (G × G) (fun z => (Φ z : ℂ)) χ‖ := by
      simp only [fixedPhaseCoefficient, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.card (G × G) : ℝ)⁻¹ * (Nat.card (G × G) : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G × G)).ne')

/-- The coefficient mass is bounded solely by the fixed ray quotient.
In particular the bound is uniform in the phase table and every frozen label. -/
theorem fixed_phase_coefficient_mass (Φ : G × G → Circle) :
    (∑ χ : (G × G) →* Circle, ‖fixedPhaseCoefficient G Φ χ‖) ≤
      (Nat.card G : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _χ : (G × G) →* Circle, (1 : ℝ) :=
      Finset.sum_le_sum (fun χ _ => fixed_phase_coefficient_norm G Φ χ)
    _ = (Nat.card ((G × G) →* Circle) : ℝ) := by
      simp [Nat.card_eq_fintype_card]
    _ = (Nat.card G : ℝ) ^ 2 := by
      rw [natCard_circleDual, Nat.card_prod, Nat.cast_mul, pow_two]

/-- One constant works before any phase table is chosen. -/
theorem fixed_phase_uniform_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ Φ : G × G → Circle,
      (∑ χ : (G × G) →* Circle, ‖fixedPhaseCoefficient G Φ χ‖) ≤ C := by
  refine ⟨(Nat.card G : ℝ) ^ 2, ?_, fixed_phase_coefficient_mass G⟩
  exact pow_pos (Nat.cast_pos.mpr (Nat.card_pos (α := G))) 2

section ActualSource

open NumberField IsDedekindDomain DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

/-- Pointwise fixed-ray calibration gives the actual child phase expansion
and its uniform aggregate mass.  It assumes neither a correlation identity
nor a bound on the parent moment. -/
theorem actual_common_phase_fixed_ray_expansion {ι κ : Type*}
    (rayLeft : ι → G) (rayRight : κ → G) (Φ : G × G → Circle)
    (ID IE : A.Exterior) (IA : ι → A.Exterior) (IB : κ → A.Exterior)
    (d e : A.R) (a : ι → A.R) (b : κ → A.R)
    (hquot : ∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        (Φ (rayLeft i, rayRight j) : ℂ)) :
    (∀ i j, IsCoprime (IA i).val (IB j).val →
      actualCommonPhase (σ := σ) ID IE (IA i) (IB j) d e (a i) (b j) =
        ∑ χ : (G × G) →* Circle, fixedPhaseCoefficient G Φ χ *
          (fixedLeftPhase G χ (rayLeft i) : ℂ) *
            star (fixedRightPhase G χ (rayRight j) : ℂ)) ∧
    (∑ χ : (G × G) →* Circle, ‖fixedPhaseCoefficient G Φ χ‖) ≤
      (Nat.card G : ℝ) ^ 2 := by
  refine ⟨?_, fixed_phase_coefficient_mass G Φ⟩
  intro i j hcop
  rw [hquot i j hcop]
  exact fixed_phase_expansion G Φ (rayLeft i) (rayRight j)

end ActualSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.fixed_phase_expansion
#print axioms HeckeSkeleton.Moments.EngineStep.fixed_phase_uniform_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_common_phase_fixed_ray_expansion
