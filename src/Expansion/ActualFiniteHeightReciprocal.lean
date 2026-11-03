import HeckeSkeleton.ExpansionModels.SmallRowReciprocal

/-!
# Actual deleted reciprocals in a detected finite rectangle

The physical zero detector is local in height.  It supplies nonvanishing
of the actual continuation, or of its pole-cleared numerator in the norm
branch, at every point strictly to the right of the detected boundary.
The latter branch keeps the literal reciprocal's removable value at its
norm pole.  No common global packet boundary or reciprocal bound is an
input to this local regularity result.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- The closed height bound is sufficient: differentiability follows
from genuine pointwise nonvanishing of an entire numerator. -/
theorem differentiableAt_actual_reciprocal_of_upper
    (chi : HeckeCharacter K) (H alpha : ℝ) (halpha : 1 / 2 ≤ alpha)
    (hupper : ZeroUpperBound K chi H alpha) (s : ℂ)
    (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    DifferentiableAt ℂ (fun z => (heckeContinuation K chi z)⁻¹) s := by
  by_cases hnorm : ∃ t : ℝ, chi = heckeNormTwist K t
  · obtain ⟨t, ht⟩ := hnorm
    have hu : ZeroUpperBound K (heckeNormTwist K t) H alpha := by
      simpa only [← ht] using hupper
    have heq : (fun z => (heckeContinuation K (heckeNormTwist K t) z)⁻¹) =
        fun z => (z - heckeNormPole t) / normPoleNumerator K t z := by
      funext z
      rw [heckeContinuation_normTwist_eq K t]
      exact inv_div _ _
    rw [ht, heq]
    exact (differentiableAt_id.sub_const _).div
      (normPoleNumerator_differentiable K t s)
      (normPoleNumerator_ne_zero_of_upper K t H alpha halpha hu s hs hheight)
  · have hnon : ∀ t : ℝ, chi ≠ heckeNormTwist K t := fun t ht => hnorm ⟨t, ht⟩
    exact (differentiable_heckeContinuation_of_nonNorm K chi hnon s).inv
      (continuation_ne_zero_of_upper K chi hnon H alpha halpha hupper s hs hheight)

/-- Every finite deletion factor is nonzero here since Re(s) > 1/2.
The complete physical reciprocal, including a removable norm pole, is
therefore differentiable at the selected point. -/
theorem differentiableAt_actual_deleted_reciprocal_of_upper
    (chi : HeckeCharacter K) (D : Finset (HeightOneSpectrum (𝓞 K)))
    (H alpha : ℝ) (halpha : 1 / 2 ≤ alpha)
    (hupper : ZeroUpperBound K chi H alpha) (s : ℂ)
    (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    DifferentiableAt ℂ (fun z => (heckeDeletedContinuation K chi D z)⁻¹) s := by
  have hfull := differentiableAt_actual_reciprocal_of_upper K chi H alpha halpha
    hupper s hs hheight
  have hdel : DifferentiableAt ℂ
      (fun z => (heckeEulerDeletionPolynomial K chi D z)⁻¹) s :=
    (heckeEulerDeletionPolynomial_analyticAt K chi D s).differentiableAt.inv
      (heckeEulerDeletionPolynomial_ne_zero K chi D (by linarith))
  simpa only [heckeDeletedContinuation, mul_inv] using hdel.fun_mul hfull

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The literal denominator character belongs to the original four
characters selected by the identity companion.  Its detected rectangle
therefore gives the required local physical reciprocal directly. -/
theorem differentiableAt_actual_row_reciprocal_of_rowZeroBelow
    (psi : HeckeCharacter K) (P : ProbeData K S) (E : RowEulerData K S P)
    (u : FrequencyRow K S) (H alpha : ℝ) (halpha : 1 / 2 ≤ alpha)
    (hbelow : rowZeroBelow K S psi {1} P E u H alpha)
    (s : ℂ) (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    DifferentiableAt ℂ (fun z =>
      (heckeDeletedContinuation K (psi * conjugate (E.rows.character u))
        (exceptionalPrimes K S) z)⁻¹) s := by
  have hmember := denominator_mem_physicalRowFamily K S psi {1} P E u
    (by simp : (1 : HeckeCharacter K) ∈ ({1} : Finset (HeckeCharacter K)))
  exact differentiableAt_actual_deleted_reciprocal_of_upper K
    (psi * conjugate (E.rows.character u)) (exceptionalPrimes K S) H alpha halpha
    (zeroUpperBound_of_rowZeroBelow K S psi {1} P E u H alpha hbelow _ hmember)
    s hs hheight

end Expansion.Project

#print axioms Expansion.Project.differentiableAt_actual_reciprocal_of_upper
#print axioms Expansion.Project.differentiableAt_actual_deleted_reciprocal_of_upper
#print axioms Expansion.Project.differentiableAt_actual_row_reciprocal_of_rowZeroBelow
