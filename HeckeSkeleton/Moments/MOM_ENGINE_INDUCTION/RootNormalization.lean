import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Family
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual row cutoffs and the physical source exponent

The physical rows lie in a dyadic envelope `2 * U`.  The polynomial tests
still use the base `U`, so that envelope belongs in the row-enumeration
exponent.  A bound with `U ^ rowWidth` returns to the physical source
power `U` by a fixed multiplicative constant; it uses no additional scale
loss and does not change any height degree, ceiling or threshold.

The transfer below allows any uniformly bounded row-envelope factor.
The logarithmic exponent gives the exact factor `2` for the dyadic case.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

/-- A bounded row-envelope factor stays a constant after adding the
reserved arithmetic loss. -/
theorem rpow_add_le_of_row_bound {U w D loss : ℝ}
    (hU : 0 < U) (hrow : U ^ w ≤ D * U) :
    U ^ (w + loss) ≤ D * U ^ (1 + loss) := by
  rw [Real.rpow_add hU, Real.rpow_add hU, Real.rpow_one]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hU.le loss)

/-- The exact exponent for a fixed enlargement of the row cutoff. -/
theorem rpow_log_row_width {U D : ℝ} (hU : 1 < U) (hD : 0 < D) :
    U ^ (1 + Real.log D / Real.log U) = D * U := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlogU : Real.log U ≠ 0 := (Real.log_pos hU).ne'
  rw [Real.rpow_add hU0, Real.rpow_one]
  have hpower : U ^ (Real.log D / Real.log U) = D := by
    rw [Real.rpow_def_of_pos hU0]
    have hcancel : Real.log U * (Real.log D / Real.log U) = Real.log D := by
      field_simp
    rw [hcancel, Real.exp_log hD]
  rw [hpower, mul_comm]

/-- The actual dyadic row width is uniformly bounded by two once `U ≥ 2`. -/
theorem dyadic_row_width_bounds {U : ℝ} (hU : 2 ≤ U) :
    1 < 1 + Real.log 2 / Real.log U ∧
      1 + Real.log 2 / Real.log U ≤ 2 := by
  have hU1 : 1 < U := lt_of_lt_of_le (by norm_num) hU
  have hlogU : 0 < Real.log U := Real.log_pos hU1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨lt_add_of_pos_right 1 (div_pos hlog2 hlogU), ?_⟩
  have hdiv : Real.log 2 / Real.log U ≤ 1 :=
    (div_le_one hlogU).mpr (Real.log_le_log (by norm_num) hU)
  linarith

namespace SourceFamily

open NumberField HeckeGeneral.Characters

universe u v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Index : ℝ → ℝ → Type u} {Sector : Type v}
variable (F : SourceFamily K ω ψ Index Sector)

/-- Transfer a proved source-family bound at its actual row width to
physical power one.  The fixed row-envelope constant is chosen before
the uniform-bound quantifiers; only the scalar is multiplied by it. -/
theorem uniformBound_of_rowWidth_le
    (E : ∀ Z T, Index Z T → ℝ)
    (eligible : ∀ Z T, Index Z T → Prop)
    {D : ℝ} (hD : 0 ≤ D)
    (hscale : ∀ (Z T : ℝ) (i : Index Z T), 1 ≤ Z →
      0 < F.base i ∧ F.base i ^ F.rowWidth i ≤ D * F.base i)
    (h : F.UniformBound E (fun _ _ i => F.rowWidth i) eligible) :
    F.UniformBound E (fun _ _ _ => 1) eligible := by
  obtain ⟨A, ceiling, hA, hc, hb⟩ := h
  refine ⟨A, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hbound⟩ := hb τ hτ hτc
  refine ⟨Z₀, D * C, hZ₀, mul_nonneg hD hC, ?_⟩
  intro Z hZ i hbin heligible
  obtain ⟨hU, hrow⟩ := hscale Z (Z ^ τ) i (hZ₀.trans hZ)
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  have hheight : 0 ≤ (1 + Z ^ τ) ^ A :=
    Real.rpow_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg hZn τ)) A
  calc
    E Z (Z ^ τ) i ≤
        C * F.base i ^ (F.rowWidth i + F.loss) * (1 + Z ^ τ) ^ A :=
      hbound Z hZ i hbin heligible
    _ ≤ C * (D * F.base i ^ (1 + F.loss)) * (1 + Z ^ τ) ^ A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rpow_add_le_of_row_bound hU hrow) hC) hheight
    _ = (D * C) * F.base i ^ (1 + F.loss) * (1 + Z ^ τ) ^ A := by ring

/-- The true dyadic row exponent costs exactly a factor of two in the
source constant.  Every original model, row set and selected slot is retained. -/
theorem uniformBound_of_dyadic_rowWidth
    (E : ∀ Z T, Index Z T → ℝ)
    (eligible : ∀ Z T, Index Z T → Prop)
    (hbase : ∀ (Z T : ℝ) (i : Index Z T), 1 ≤ Z → 1 < F.base i)
    (hwidth : ∀ U : ℝ, 1 < U →
      F.rowExponent U = 1 + Real.log 2 / Real.log U)
    (h : F.UniformBound E (fun _ _ i => F.rowWidth i) eligible) :
    F.UniformBound E (fun _ _ _ => 1) eligible := by
  apply F.uniformBound_of_rowWidth_le E eligible (D := 2) (by norm_num) ?_ h
  intro Z T i hZ
  have hU := hbase Z T i hZ
  refine ⟨zero_lt_one.trans hU, ?_⟩
  change F.base i ^ F.rowExponent (F.base i) ≤ 2 * F.base i
  rw [hwidth _ hU]
  exact (rpow_log_row_width hU (by norm_num : (0 : ℝ) < 2)).le

/-- The physical row-envelope bound is only needed above its own fixed
threshold and on the retained bins.  Joining that threshold with the
moment threshold preserves the order of all uniform constants.  In
particular, this version makes no strict-base assertion at `Z = 1`. -/
theorem uniformBound_of_rowWidth_le_from
    (E : ∀ Z T, Index Z T → ℝ)
    (eligible : ∀ Z T, Index Z T → Prop)
    {D : ℝ} (hD : 0 ≤ D) (Zrow : ℝ)
    (hscale : ∀ (Z T : ℝ) (i : Index Z T), Zrow ≤ Z →
      51 / 100 < F.bin Z T i →
      0 < F.base i ∧ F.base i ^ F.rowWidth i ≤ D * F.base i)
    (h : F.UniformBound E (fun _ _ i => F.rowWidth i) eligible) :
    F.UniformBound E (fun _ _ _ => 1) eligible := by
  obtain ⟨A, ceiling, hA, hc, hb⟩ := h
  refine ⟨A, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hbound⟩ := hb τ hτ hτc
  refine ⟨max Z₀ Zrow, D * C, hZ₀.trans (le_max_left _ _),
    mul_nonneg hD hC, ?_⟩
  intro Z hZ i hbin heligible
  have hZ₀' : Z₀ ≤ Z := (le_max_left _ _).trans hZ
  have hZrow : Zrow ≤ Z := (le_max_right _ _).trans hZ
  obtain ⟨hU, hrow⟩ := hscale Z (Z ^ τ) i hZrow hbin
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ₀')
  have hheight : 0 ≤ (1 + Z ^ τ) ^ A :=
    Real.rpow_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg hZn τ)) A
  calc
    E Z (Z ^ τ) i ≤
        C * F.base i ^ (F.rowWidth i + F.loss) * (1 + Z ^ τ) ^ A :=
      hbound Z hZ₀' i hbin heligible
    _ ≤ C * (D * F.base i ^ (1 + F.loss)) * (1 + Z ^ τ) ^ A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rpow_add_le_of_row_bound hU hrow) hC) hheight
    _ = (D * C) * F.base i ^ (1 + F.loss) * (1 + Z ^ τ) ^ A := by ring

end SourceFamily

end HeckeSkeleton.Moments.EngineInduction
