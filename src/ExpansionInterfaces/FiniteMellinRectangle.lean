import ExpansionInterfaces.AnnularMellinProfile
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.LinearCombination

/-!
# A finite-height Mellin contour move with both horizontal faces retained

No limiting contour shift is used.  The exact boundary identity and its
norm bound retain both horizontal integrals.  The full initial line is
then compared with this finite rectangle by its actual complementary tail.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open scoped Classical Topology

def closedRectangle (a b H : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ H}

def verticalSegment (F : ℂ → ℂ) (σ H : ℝ) : ℂ :=
  ∫ t : ℝ in -H..H, F (vertical σ t)

def horizontalSegment (F : ℂ → ℂ) (a b y : ℝ) : ℂ :=
  ∫ x : ℝ in a..b, F (vertical x y)

theorem rectangle_identity (F : ℂ → ℂ) {a b H : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (closedRectangle a b H)) :
    horizontalSegment F a b (-H) - horizontalSegment F a b H +
      Complex.I * verticalSegment F b H - Complex.I * verticalSegment F a H = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    (vertical a (-H)) (vertical b H) (hF.mono ?_)
  · simpa [verticalSegment, horizontalSegment, vertical, smul_eq_mul] using h
  · intro z hz
    have hr : a ≤ z.re ∧ z.re ≤ b := by
      simpa only [vertical_re, uIcc_of_le hab, mem_preimage, mem_Icc] using hz.1
    have hi : -H ≤ z.im ∧ z.im ≤ H := by
      simpa only [vertical_im, uIcc_of_le (by linarith : -H ≤ H), mem_preimage, mem_Icc] using hz.2
    exact ⟨hr.1, hr.2, abs_le.mpr hi⟩

theorem horizontalSegment_norm_le (F : ℂ → ℂ) {a b y C : ℝ}
    (hab : a ≤ b) (hbound : ∀ x ∈ Icc a b, ‖F (vertical x y)‖ ≤ C) :
    ‖horizontalSegment F a b y‖ ≤ C * (b - a) := by
  have h : ‖∫ x : ℝ in a..b, F (vertical x y)‖ ≤ C * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound x (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx)
  simpa only [horizontalSegment, abs_of_nonneg (sub_nonneg.mpr hab)] using h

theorem rectangle_shift_norm (F : ℂ → ℂ) {a b H Cbot Ctop : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (closedRectangle a b H))
    (hbot : ∀ x ∈ Icc a b, ‖F (vertical x (-H))‖ ≤ Cbot)
    (htop : ∀ x ∈ Icc a b, ‖F (vertical x H)‖ ≤ Ctop) :
    ‖verticalSegment F b H‖ ≤
      ‖verticalSegment F a H‖ + (Cbot + Ctop) * (b - a) := by
  have hr := rectangle_identity F hab hH hF
  have heq : Complex.I * (verticalSegment F b H - verticalSegment F a H) =
      horizontalSegment F a b H - horizontalSegment F a b (-H) := by
    linear_combination hr
  have hdiff : ‖verticalSegment F b H - verticalSegment F a H‖ ≤
      ‖horizontalSegment F a b H‖ + ‖horizontalSegment F a b (-H)‖ := by
    have hnorm := congrArg norm heq
    simpa only [norm_mul, Complex.norm_I, one_mul] using
      hnorm.trans_le (norm_sub_le _ _)
  have htri : ‖verticalSegment F b H‖ ≤
      ‖verticalSegment F b H - verticalSegment F a H‖ + ‖verticalSegment F a H‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (verticalSegment F b H - verticalSegment F a H) (verticalSegment F a H)
  have hb := horizontalSegment_norm_le F hab hbot
  have ht := horizontalSegment_norm_le F hab htop
  nlinarith

theorem interval_compl_eq_abs_tail (H : ℝ) :
    (Icc (-H) H : Set ℝ)ᶜ = {t | H < |t|} := by
  ext t
  simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, ← abs_le, not_le]

theorem full_line_sub_segment_norm_le (f w : ℝ → ℂ) {E H : ℝ}
    (hH : 0 ≤ H) (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ t, ‖f t‖ ≤ E * ‖w t‖) :
    ‖(∫ t : ℝ, f t) - (∫ t : ℝ in -H..H, f t)‖ ≤
      E * (∫ t : ℝ in {t | H < |t|}, ‖w t‖) := by
  have hsplit := integral_add_compl (s := Icc (-H) H) measurableSet_Icc hf
  have hsegment : (∫ t : ℝ in -H..H, f t) = ∫ t : ℝ in Icc (-H) H, f t := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have heq : (∫ t : ℝ, f t) - (∫ t : ℝ in -H..H, f t) =
      ∫ t : ℝ in {t | H < |t|}, f t := by
    rw [hsegment, ← hsplit, interval_compl_eq_abs_tail]
    abel
  rw [heq]
  have hm : MeasurableSet {t : ℝ | H < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  calc
    _ ≤ ∫ t : ℝ in {t | H < |t|}, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in {t | H < |t|}, E * ‖w t‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun t _ => hbound t)
    _ = _ := integral_const_mul _ _

theorem full_line_from_rectangle (F : ℂ → ℂ) (w : ℝ → ℂ)
    {a b H Cbot Ctop E : ℝ} (hab : a ≤ b) (hH : 0 ≤ H)
    (hF : DifferentiableOn ℂ F (closedRectangle a b H))
    (hi : Integrable (fun t : ℝ => F (vertical b t))) (hw : Integrable w)
    (hbot : ∀ x ∈ Icc a b, ‖F (vertical x (-H))‖ ≤ Cbot)
    (htop : ∀ x ∈ Icc a b, ‖F (vertical x H)‖ ≤ Ctop)
    (hright : ∀ t, ‖F (vertical b t)‖ ≤ E * ‖w t‖) :
    ‖∫ t : ℝ, F (vertical b t)‖ ≤
      ‖verticalSegment F a H‖ + (Cbot + Ctop) * (b - a) +
        E * (∫ t : ℝ in {t | H < |t|}, ‖w t‖) := by
  have hr := rectangle_shift_norm F hab hH hF hbot htop
  have ht := full_line_sub_segment_norm_le (fun t => F (vertical b t)) w hH hi hw hright
  have htri : ‖∫ t : ℝ, F (vertical b t)‖ ≤
      ‖(∫ t : ℝ, F (vertical b t)) - verticalSegment F b H‖ + ‖verticalSegment F b H‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      ((∫ t : ℝ, F (vertical b t)) - verticalSegment F b H) (verticalSegment F b H)
  change ‖(∫ t : ℝ, F (vertical b t)) - verticalSegment F b H‖ ≤ _ at ht
  linarith

end ExpansionInterfaces.Mellin
