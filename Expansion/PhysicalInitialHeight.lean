import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Height coordinates for the actual initial Mellin integral

The change from the independent Gaussian coordinate a to s=a-z+1 is
the volume-preserving shear (ts,tw,tz) ↦ (ts+tz,tw,tz).  These elementary
measure identities apply directly to the actual physical integrands.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialHeight

open MeasureTheory
open scoped BigOperators

def heightEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))

theorem heightEquiv_apply (t : Fin 3 → ℝ) : heightEquiv t = (t 0, t 1, t 2) := rfl

theorem heightEquiv_symm_apply (t : ℝ × ℝ × ℝ) :
    heightEquiv.symm t = ![t.1, t.2.1, t.2.2] := by
  ext i
  fin_cases i <;> rfl

theorem heightEquiv_preserving : MeasurePreserving heightEquiv volume volume :=
  ((MeasurePreserving.id volume).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

def heightShear : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun t := ![t 0 + t 2, t 1, t 2]
  invFun t := ![t 0 - t 2, t 1, t 2]
  left_inv t := by ext i; fin_cases i <;> simp
  right_inv t := by ext i; fin_cases i <;> simp
  measurable_toFun := by
    change Measurable (fun t : Fin 3 → ℝ => ![t 0 + t 2, t 1, t 2])
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop
  measurable_invFun := by
    change Measurable (fun t : Fin 3 → ℝ => ![t 0 - t 2, t 1, t 2])
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    all_goals fun_prop

theorem heightShear_preserving : MeasurePreserving heightShear volume volume := by
  let T : Matrix.TransvectionStruct (Fin 3) ℝ := ⟨0, 2, by decide, 1⟩
  convert Real.volume_preserving_transvectionStruct T using 1
  ext t i
  fin_cases i <;> simp [heightShear, T, Matrix.transvection, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem integral_heightShear (f : (Fin 3 → ℝ) → ℂ) :
    (∫ t, f (heightShear t)) = ∫ t, f t :=
  heightShear_preserving.integral_comp' f

theorem integrable_heightShear_iff (f : (Fin 3 → ℝ) → ℂ) :
    Integrable (fun t => f (heightShear t)) ↔ Integrable f :=
  heightShear_preserving.integrable_comp_emb heightShear.measurableEmbedding

theorem integral_three_product (f g h : ℝ → ℂ) :
    (∫ t : Fin 3 → ℝ, f (t 0) * g (t 1) * h (t 2)) =
      (∫ t, f t) * (∫ t, g t) * (∫ t, h t) := by
  simpa [Fin.prod_univ_succ, mul_assoc] using
    integral_fin_nat_prod_volume_eq_prod (![f, g, h] : Fin 3 → ℝ → ℂ)

theorem integrable_three_product {f g h : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h) :
    Integrable (fun t : Fin 3 → ℝ => f (t 0) * g (t 1) * h (t 2)) := by
  have hi : Integrable (fun t : ℝ × ℝ × ℝ => f t.1 * (g t.2.1 * h t.2.2)) := by
    simpa only [Measure.volume_eq_prod] using hf.mul_prod (hg.mul_prod hh)
  have hp := heightEquiv_preserving.integrable_comp_emb
    heightEquiv.measurableEmbedding |>.mpr hi
  simpa only [Function.comp_def, heightEquiv_apply, mul_assoc] using hp

theorem integral_eq_initial_order (f : (Fin 3 → ℝ) → ℂ) (hf : Integrable f) :
    (∫ t, f t) = ∫ ts : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f ![ts, tw, tz] := by
  have hp : Integrable (fun t : ℝ × ℝ × ℝ => f (heightEquiv.symm t)) :=
    (heightEquiv_preserving.symm heightEquiv).integrable_comp_emb
      heightEquiv.symm.measurableEmbedding |>.mpr hf
  rw [← (heightEquiv_preserving.symm heightEquiv).integral_comp' f]
  simp only [Measure.volume_eq_prod] at hp ⊢
  rw [integral_prod _ hp]
  apply integral_congr_ae
  filter_upwards [hp.prod_right_ae] with ts hts
  rw [integral_prod _ hts]
  simp only [heightEquiv_symm_apply]

end Expansion.PhysicalInitialHeight
