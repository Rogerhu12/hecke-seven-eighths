import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstDualTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# The original central scale in the whole parent coefficient

The two plain atoms and every prime occurrence contain their actual
inverse square-root scale. Both comparison rectangles have the same
product of plain scales. Their full coefficients consequently retain
the exponent minus one half of the original total length, before either
Poisson transform or any finite common-support decomposition.

Only individual unscaled original atom bounds are used. The coefficient
bound, including the centered subtraction and all slots, is proved here.
The fixed coefficient constant depends on the original slot cap and
profile bound, not on the moving columns, scale, or common labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

theorem original_inverse_sqrt_rpow (Z length : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ length))⁻¹ = Z ^ (-length / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le, ← Real.rpow_neg hZ.le]
  congr 1
  ring

private theorem original_normalized_atom_norm_le
    (N B : ℝ) (v : ℂ) (hv : ‖v‖ ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * v‖ ≤ B * (Real.sqrt N)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg N)]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg N))

/-- The original normalization is a single product, including the
empty product when there are no prime slots. -/
theorem original_central_scale_product
    (slots : ℕ) (length : Fin slots → ℝ) (Z B N₁ N₂ plainLength : ℝ)
    (hZ : 0 < Z) (hN₁ : 0 ≤ N₁) (hproduct : N₁ * N₂ = Z ^ plainLength) :
    (B * (Real.sqrt N₁)⁻¹) * (B * (Real.sqrt N₂)⁻¹) *
        (∏ i, B * (Real.sqrt (Z ^ length i))⁻¹) =
      B ^ (slots + 2) * Z ^ (-(plainLength + ∑ i, length i) / 2) := by
  have hplain : (Real.sqrt N₁)⁻¹ * (Real.sqrt N₂)⁻¹ =
      Z ^ (-plainLength / 2) := by
    calc
      _ = (Real.sqrt N₁ * Real.sqrt N₂)⁻¹ := by rw [mul_inv_rev]; ring
      _ = (Real.sqrt (N₁ * N₂))⁻¹ := by rw [Real.sqrt_mul hN₁]
      _ = _ := by rw [hproduct, original_inverse_sqrt_rpow Z plainLength hZ]
  have hslots : (∏ i, (Real.sqrt (Z ^ length i))⁻¹) =
      Z ^ (-(∑ i, length i) / 2) := by
    simp_rw [original_inverse_sqrt_rpow Z _ hZ]
    rw [← Real.rpow_sum_of_pos hZ]
    congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hslots]
  calc
    _ = B ^ (slots + 2) *
        ((Real.sqrt N₁)⁻¹ * (Real.sqrt N₂)⁻¹ * Z ^ (-(∑ i, length i) / 2)) := by
      rw [pow_add, pow_two]
      ring
    _ = _ := by
      rw [hplain, ← Real.rpow_add hZ]
      congr 1
      congr 1
      ring

variable {K : Type} [Field K] [NumberField K]

namespace ParentConstantAtoms

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

/-- A rectangle is bounded on the literal original support. The raw
atom bounds do not contain any central scale or whole-column product. -/
theorem rectangle_norm_le_original_central_scales
    (B : ℝ) (hB : 0 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (comparison : Bool)
    (hN₁ : 0 ≤ (if comparison then Y₁ else Z ^ a.n₁))
    (hproduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).rectangle comparison v‖ ≤
      B ^ (d.geometry.slotCount + 2) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  have h := (atoms.values Y₁ Y₂).rectangle_norm_le_original_atoms
    (fun comparison => B * (Real.sqrt (if comparison then Y₁ else Z ^ a.n₁))⁻¹)
    (fun comparison => B * (Real.sqrt (if comparison then Y₂ else Z ^ a.n₂))⁻¹)
    (fun i => B * (Real.sqrt (Z ^ (d.geometry.slots i).length))⁻¹)
    (fun _ => mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (fun _ => mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (fun comparison I hI => original_normalized_atom_norm_le _ B _ (hleft comparison I hI))
    (fun comparison I hI => original_normalized_atom_norm_le _ B _ (hright comparison I hI))
    (fun i p hp => original_normalized_atom_norm_le _ B _ (hprime i p hp))
    comparison v hv
  apply h.trans_eq
  simpa only [SlotGeometry.totalLength] using
    original_central_scale_product d.geometry.slotCount
      (fun i => (d.geometry.slots i).length) Z B
      (if comparison then Y₁ else Z ^ a.n₁)
      (if comparison then Y₂ else Z ^ a.n₂) (a.n₁ + a.n₂) hZ hN₁ hproduct

/-- The sharp original coefficient exponent is proved before the
common supports are extracted. Both rectangles retain the same scales
and every original slot; the constant uses only the fixed slot cap. -/
theorem coefficient_norm_le_original_central_cap
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (B : ℝ) (hB : 1 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  let bound := B ^ (cap + 2) *
    Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2)
  have hbound : 0 ≤ bound :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hB) _) (Real.rpow_nonneg hZ.le _)
  have hrectangle (comparison : Bool)
      (hN : 0 ≤ (if comparison then Y₁ else Z ^ a.n₁))
      (hprod : (if comparison then Y₁ else Z ^ a.n₁) *
        (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂)) :
      ‖(atoms.values Y₁ Y₂).rectangle comparison v‖ ≤ bound := by
    apply (atoms.rectangle_norm_le_original_central_scales B (zero_le_one.trans hB) hZ
      hleft hright hprime comparison hN hprod v hv).trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hB (Nat.add_le_add_right hcap 2)) (Real.rpow_nonneg hZ.le _)
  have hfalse := hrectangle false (Real.rpow_nonneg hZ.le _)
    (by simpa only [Bool.false_eq_true, if_false] using (Real.rpow_add hZ a.n₁ a.n₂).symm)
  have hcoefficient : ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤ 2 * bound := by
    cases centered with
    | false =>
        change ‖(atoms.values Y₁ Y₂).rectangle false v - 0‖ ≤ 2 * bound
        simpa only [sub_zero] using hfalse.trans (by linarith)
    | true =>
        change ‖(atoms.values Y₁ Y₂).rectangle false v -
          (atoms.values Y₁ Y₂).rectangle true v‖ ≤ 2 * bound
        have htrue := hrectangle true (hY₁ rfl) (hcomparison rfl)
        exact (norm_sub_le _ _).trans ((add_le_add hfalse htrue).trans_eq (by ring))
  simpa only [bound, mul_assoc] using hcoefficient

end ParentConstantAtoms

namespace PairedEngineDomain

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)

include domain in
theorem comparison_scale_left_nonneg (hc : centered = true) : 0 ≤ Y₁ := by
  rw [domain.comparison_left hc]
  exact Real.rpow_nonneg (zero_le_one.trans domain.scale.le) _

include domain in
theorem comparison_product_eq_power (hc : centered = true) :
    Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂) := by
  rw [domain.comparison_left hc, domain.comparison_right hc,
    ← Real.rpow_add (zero_lt_one.trans domain.scale)]
  congr 1
  ring

end PairedEngineDomain
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_central_scale_product
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.rectangle_norm_le_original_central_scales
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.coefficient_norm_le_original_central_cap
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.comparison_product_eq_power
