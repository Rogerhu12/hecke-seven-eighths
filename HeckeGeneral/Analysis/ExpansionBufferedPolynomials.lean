import HeckeGeneral.Analysis.ExpansionDeletedControl
import ExpansionInterfaces.AnnularContourUniform

/-!
# Finite annular polynomial bounds for the actual Hecke coefficients

The ordinary and inverse branches use the repository's deleted prime
coefficients and its actual ideal Moebius function. Their initial-line
identities and absolute convergence are proved below; the only analytic
selection premise of the final upper bound is the actual upper-zero bound.

The rectangle is finite. The displayed error consists of its two horizontal
sides and the absolutely convergent initial-line tail. In particular this
module does not assume an already shifted integral or a polynomial bound.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionBufferedPolynomials

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Bridge IdealMobiusReciprocal ExpansionDetectorInitial ExpansionDeletedControl
open HeckeSkeleton.HeckeBufferedReciprocal HeckeSkeleton.HeckeConductorNorm
open ExpansionInterfaces.Mellin
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- `true` selects the actual reciprocal Moebius coefficients; `false`
selects the ordinary actual deleted ideal coefficients. -/
def deletedAnnularCoefficient (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) : ℂ :=
  match reciprocal with
  | false => nonzeroIdealCoefficient (deletePrimes K E (primeCoefficient K χ)) I
  | true => coefficient K (deletePrimes K E (primeCoefficient K χ)) I

def deletedFunction (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  match reciprocal with
  | false => heckeDeletedContinuation K χ E s
  | true => (heckeDeletedContinuation K χ E s)⁻¹

theorem deletedAnnularCoefficient_norm_le (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) :
    ‖deletedAnnularCoefficient K reciprocal χ E I‖ ≤ 1 := by
  have ha := norm_deletePrimes_le_one K E (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ)
  cases reciprocal with
  | false => exact norm_nonzeroIdealCoefficient_le_one _ ha I
  | true => exact norm_coefficient_le_one K _ ha I

/-- The inverse coefficients are the literal excluded Moebius--Hecke
coefficients, including all of their actual ramified zero values. -/
theorem inverse_coefficient_eq_literal (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (I : NonzeroIdeal K) :
    deletedAnnularCoefficient K true χ E I =
      if (∀ p ∈ E, ¬p.asIdeal ∣ I.val) then
        (UniqueFactorizationMonoid.moebius I.val : ℂ) * heckeIdealCoefficient K χ I else 0 := by
  have h := term_deletePrimes K E (primeCoefficient K χ) (0 : ℂ) I
  rw [hecke_excludedTerm_eq_literal] at h
  simpa only [term, dirichletTerm, neg_zero, Complex.cpow_zero, mul_one,
    deletedAnnularCoefficient] using h

theorem deletedFunction_initial_series (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    deletedFunction K reciprocal χ E s =
      ExpansionInterfaces.Mellin.dirichletSeries
        (deletedAnnularCoefficient K reciprocal χ E) (idealNorm K) s := by
  cases reciprocal with
  | false =>
      exact heckeDeletedContinuation_eq_deleted_series K χ E hs
  | true =>
      change (heckeDeletedContinuation K χ E s)⁻¹ =
        ∑' I, term K (deletePrimes K E (primeCoefficient K χ)) s I
      rw [heckeDeletedContinuation_eq_deleted_series K χ E hs]
      exact (moebius_series_eq_inverse K _
        (norm_deletePrimes_le_one K E (primeCoefficient K χ)
          (norm_primeCoefficient_le_one K χ)) hs).symm

theorem deletedAnnularCoefficient_summable (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I => ‖deletedAnnularCoefficient K reciprocal χ E I‖ *
      idealNorm K I ^ (-σ)) := by
  apply Summable.of_nonneg_of_le
    (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (idealNorm_pos K I).le _)) _
    (summable_nonzeroIdeal_norm_rpow K hσ)
  intro I
  exact (mul_le_mul_of_nonneg_right (deletedAnnularCoefficient_norm_le K reciprocal χ E I)
    (Real.rpow_nonneg (idealNorm_pos K I).le _)).trans_eq (one_mul _)

def initialMass : ℝ := ∑' I : NonzeroIdeal K, idealNorm K I ^ (-2 : ℝ)

theorem initialMass_nonneg : 0 ≤ initialMass K :=
  tsum_nonneg (fun I => Real.rpow_nonneg (idealNorm_pos K I).le _)

theorem deleted_initial_mass_le (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑' I, ‖deletedAnnularCoefficient K reciprocal χ E I‖ * idealNorm K I ^ (-2 : ℝ)) ≤
      initialMass K := by
  apply Summable.tsum_le_tsum _
    (deletedAnnularCoefficient_summable K reciprocal χ E (by norm_num))
    (summable_nonzeroIdeal_norm_rpow K (by norm_num : (1 : ℝ) < 2))
  intro I
  exact (mul_le_mul_of_nonneg_right (deletedAnnularCoefficient_norm_le K reciprocal χ E I)
    (Real.rpow_nonneg (idealNorm_pos K I).le _)).trans_eq (one_mul _)

theorem deletedFunction_norm_le_sum (reciprocal : Bool) (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    ‖deletedFunction K reciprocal χ E s‖ ≤
      ‖heckeDeletedContinuation K χ E s‖ + ‖(heckeDeletedContinuation K χ E s)⁻¹‖ := by
  cases reciprocal with
  | false => exact le_add_of_nonneg_right (norm_nonneg _)
  | true => exact le_add_of_nonneg_left (norm_nonneg _)

theorem deletedFunction_rectangle_differentiable (reciprocal : Bool)
    (χ : HeckeCharacter K) (E : Finset (HeightOneSpectrum (𝓞 K)))
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    {a e H Hupper : ℝ} (ha : 1 / 2 ≤ a) (he : 0 < e) (s : ℂ)
    (hpadding : |s.im| + H ≤ Hupper)
    (hupper : ZeroUpperBound K χ Hupper (a + 2 * e)) :
    DifferentiableOn ℂ (fun z => deletedFunction K reciprocal χ E (s + z))
      (closedRectangle (a + 6 * e - s.re) (2 - s.re) H) := by
  have hd := (heckeDeletedContinuation_entire K χ hχ E).comp
    (differentiable_const.add differentiable_id)
  cases reciprocal with
  | false => exact hd.differentiableOn
  | true =>
      intro z hz
      apply ((hd z).inv ?_).differentiableWithinAt
      apply deleted_ne_zero_of_upper K χ hχ E ha he hupper (s + z)
      · simp only [Complex.add_re]
        linarith [hz.1]
      · calc
          |(s + z).im| = |s.im + z.im| := rfl
          _ ≤ |s.im| + |z.im| := abs_add _ _
          _ ≤ |s.im| + H := add_le_add_left hz.2.2 _
          _ ≤ Hupper := hpadding

/-- The finite-height upper bound, with all series and analytic premises
specialized to the real deleted Hecke function. The common constant depends
only on the fixed field, infinity type, and positive losses e and ε.

The annular profile is quantified after that constant; its own Mellin
constant is displayed. For the varying inverse cutoff family it is replaced
by the uniform cutoff-family constant in `AnnularCutoffFamily`.
-/
theorem exists_actual_buffered_annular_upper
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (reciprocal : Bool) (W : AnnularProfile) (order : ℕ)
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
      let CW := W.contourConstant (-2) 2 order
      ‖∑ J ∈ S, smoothedTerm W (deletedAnnularCoefficient K reciprocal χ E)
        (idealNorm K) s X J‖ ≤ (1 / (2 * Real.pi)) *
        ((B * X ^ (a + 6 * e - s.re)) * CW +
          2 * (CW / (1 + H) ^ order) * B * X ^ (2 - s.re) * (2 - a - 6 * e) +
          (initialMass K * X ^ (2 - s.re)) * (CW / H ^ order)) := by
  obtain ⟨C, hC, hbound⟩ := exists_actual_deleted_buffered_control K hcomplex τ m he he' hε
  refine ⟨C, hC, ?_⟩
  intro reciprocal W order χ I E a H Hupper X s hχ hτ hm hI hE ha ha' hH
    hpadding hupper hX hs hs' S hS
  let B := bufferedCost K χ I C ε Hupper
  let CW := W.contourConstant (-2) 2 order
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
  have hb := annular_polynomial_uniform_upper W (-2) 2 order
    (deletedAnnularCoefficient K reciprocal χ E) (idealNorm K) (idealNorm_pos K)
    (deletedFunction K reciprocal χ E) s hX (by linarith) (by linarith) (by linarith) hH
    hB hB hsum hline
    (deletedFunction_rectangle_differentiable K reciprocal χ E hχ ha he s
      (by linarith) hupper) hrect hleft S hS
  have hmass : (∑' J, ‖deletedAnnularCoefficient K reciprocal χ E J‖ *
      idealNorm K J ^ (-(s.re + (2 - s.re)))) ≤ initialMass K := by
    convert deleted_initial_mass_le K reciprocal χ E using 1 <;> ring
  have hCW : 0 ≤ CW := (W.contourConstant_spec (-2) 2 order).1
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
