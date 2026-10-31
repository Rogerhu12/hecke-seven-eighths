import HeckeGeneral.Analysis.ExpansionBufferedPolynomials
import ExpansionInterfaces.AnnularCutoffFamily

/-! The actual deleted ordinary/inverse bounds with one Mellin constant
for the entire W(x)V(Rx) family. In the inverse recipe R = D/U^t;
this theorem is uniform for every R >= 0. -/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionBufferedPolynomials

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Bridge IdealMobiusReciprocal ExpansionDetectorInitial ExpansionDeletedControl
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeConductorNorm
open ExpansionInterfaces.Mellin
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

theorem exists_actual_buffered_cutoff_annular_upper
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (reciprocal : Bool) (W : AnnularProfile)
      (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
      (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
      (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (order : ℕ) (R : ℝ), 0 ≤ R → ∀
      (χ : HeckeCharacter K) (I : Ideal (𝓞 K))
      (E : Finset (HeightOneSpectrum (𝓞 K))) (a H Hupper X : ℝ) (s : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      1 / 2 ≤ a → a ≤ 1 → 0 < H → |s.im| + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      1 ≤ X → 1 / 2 ≤ s.re → s.re ≤ 1 →
      ∀ S : Finset (NonzeroIdeal K), (∀ J, idealNorm K J ≤ W.upper * X → J ∈ S) →
      let B := bufferedCost K χ I C ε Hupper
      let CW := W.cutoffContourConstant V hV hone hzero (-2) 2 order
      ‖∑ J ∈ S, smoothedTerm (W.cutoffFamily V hV R) (deletedAnnularCoefficient K reciprocal χ E)
        (idealNorm K) s X J‖ ≤ (1 / (2 * Real.pi)) *
        ((B * X ^ (a + 6 * e - s.re)) * CW +
          2 * (CW / (1 + H) ^ order) * B * X ^ (2 - s.re) * (2 - a - 6 * e) +
          (initialMass K * X ^ (2 - s.re)) * (CW / H ^ order)) := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_deleted_buffered_control K hcomplex τ m he he' hε
  refine ⟨C, hC, ?_⟩
  intro reciprocal W V hV hone hzero order R hR χ I E a H Hupper X s hχ hτ hm hI hE ha ha' hH
    hpadding hupper hX hs hs' S hS
  let B := bufferedCost K χ I C ε Hupper
  let CW := W.cutoffContourConstant V hV hone hzero (-2) 2 order
  have hHU : 0 ≤ Hupper := by linarith [abs_nonneg s.im]
  have hB : 0 ≤ B := by
    unfold B bufferedCost
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (by positivity))
      (Real.rpow_nonneg (conductorScale_pos K χ).le _)) (by positivity)
  have hpoint : ∀ z : ℂ, a + 6 * e ≤ z.re → z.re ≤ 2 →
      |z.im| ≤ |s.im| + H → ‖deletedFunction K reciprocal χ E z‖ ≤ B := by
    intro z hz hz' hh
    exact (deletedFunction_norm_le_sum K reciprocal χ E z).trans
      (hbound χ I E a (|s.im| + H) Hupper hχ hτ hm hI hE ha ha'
        (by positivity) hpadding hupper z hz hz' hh)
  have hrect : ∀ z ∈ closedRectangle (a + 6 * e - s.re) (2 - s.re) H,
      ‖deletedFunction K reciprocal χ E (s + z)‖ ≤ B := by
    intro z hz
    apply hpoint
    · simp only [Complex.add_re]
      linarith [hz.1]
    · simp only [Complex.add_re]
      linarith [hz.2.1]
    · exact (abs_add s.im z.im).trans (add_le_add_left hz.2.2 _)
  have hleft : ∀ t : ℝ, |t| ≤ H →
      ‖deletedFunction K reciprocal χ E (s + vertical (a + 6 * e - s.re) t)‖ ≤ B := by
    intro t ht
    apply hrect
    simp only [closedRectangle, Set.mem_setOf_eq, vertical_re, vertical_im]
    exact ⟨le_rfl, by linarith, ht⟩
  have hsum : Summable (fun J => ‖deletedAnnularCoefficient K reciprocal χ E J‖ *
      idealNorm K J ^ (-(s.re + (2 - s.re)))) := by
    convert deletedAnnularCoefficient_summable K reciprocal χ E (σ := 2) (by norm_num) using 1 <;> ring
  have hline : ∀ t : ℝ, deletedFunction K reciprocal χ E (s + vertical (2 - s.re) t) =
      ExpansionInterfaces.Mellin.dirichletSeries (deletedAnnularCoefficient K reciprocal χ E)
        (idealNorm K) (s + vertical (2 - s.re) t) := by
    intro t
    apply deletedFunction_initial_series K reciprocal χ E
    simp only [Complex.add_re, vertical_re]
    linarith
  have hb := annular_cutoff_polynomial_uniform_upper W V hV hone hzero (-2) 2 order R hR
    (deletedAnnularCoefficient K reciprocal χ E) (idealNorm K) (idealNorm_pos K)
    (deletedFunction K reciprocal χ E) s hX (by linarith) (by linarith) (by linarith) hH
    hB hB hsum hline
    (deletedFunction_rectangle_differentiable K reciprocal χ E hχ ha he s
      (by linarith) hupper) hrect hleft S hS
  have hmass : (∑' J, ‖deletedAnnularCoefficient K reciprocal χ E J‖ *
      idealNorm K J ^ (-(s.re + (2 - s.re)))) ≤ initialMass K := by
    convert deleted_initial_mass_le K reciprocal χ E using 1 <;> ring
  have hCW : 0 ≤ CW := (W.cutoffContourConstant_spec V hV hone hzero (-2) 2 order).1
  dsimp only at hb ⊢
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  have htail := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (zero_le_one.trans hX) _))
    (div_nonneg hCW (pow_nonneg hH.le order))
  have hwidth : (2 - s.re) - (a + 6 * e - s.re) = 2 - a - 6 * e := by ring
  rw [hwidth]
  exact add_le_add_left htail _


end HeckeGeneral.Analysis.ExpansionBufferedPolynomials
