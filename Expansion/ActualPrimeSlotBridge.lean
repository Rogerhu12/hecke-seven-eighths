import Expansion.ActualMaskedPrimeCancellation

/-!
# The actual shared prime slot and finite-height cancellation

The finite prime window, row character, coefficient character, complete
ideal mask and square-root normalization are identified literally.  No
equality to the full compensated physical kernel is claimed here: its
marked Euler-table factorization is a separate analytic construction.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (omega ψ : HeckeCharacter K)

/-- The exact slot formula, including all original ramified and row zeros. -/
theorem shared_primePolynomial_eq_actualOriginalMaskedPrimeSum
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (V W : IdealTest K)
    (u : FrequencyRow K S) (j : Fin g.slotCount) (Z t : ℝ) :
    primePolynomial (sharedMomentData K S P R omega ψ a g c u.sector V W)
      j u.ideal.val Z t =
      (Real.sqrt (Z ^ (g.slots j).length) : ℂ)⁻¹ *
        actualOriginalMaskedPrimeSum K S (R.character u * c j) u.ideal.val
          ((g.slots j).profile t) (Z ^ (g.slots j).length)
          ((g.slots j).support t (Z ^ (g.slots j).length)) := by
  change (Real.sqrt (Z ^ (g.slots j).length) : ℂ)⁻¹ *
      (∑ p ∈ (g.slots j).support t (Z ^ (g.slots j).length),
        primeCoefficient K (completeIdealRowCharacter K S P R u.sector u.ideal.val * c j) p *
          (g.slots j).profile t ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (g.slots j).length) *
          (if completeIdealCommonMask K S u.ideal.val p.asIdeal then 1 else 0)) = _
  rw [completeIdealRowCharacter_of_frequencyRow]
  rfl

/-- All analytic constants are fixed before choosing a row and its finite
zero buffer. Support coverage comes from the actual slot definition. -/
theorem exists_shared_primePolynomial_finite_height_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (conductorRatio : ℝ) (hRatio : 0 ≤ conductorRatio)
    (a : PolynomialPresentation K ψ) (g : SlotGeometry K)
    (c : Fin g.slotCount → HeckeCharacter K) (V W : IdealTest K)
    (j : Fin g.slotCount) (t : ℝ)
    (hW : ContDiff ℝ ∞ ((g.slots j).profile t))
    (hs : Function.support ((g.slots j).profile t) ⊆ Icc (1 : ℝ) 2) (order : ℕ) :
    ∃ C A P₀ CW B M : ℝ,
      1 ≤ C ∧ 1 ≤ A ∧ 2 ≤ P₀ ∧ 0 ≤ CW ∧ 0 < B ∧ 0 < M ∧
      ∀ (u : FrequencyRow K S) (U β δ H Z Hupper : ℝ),
        (∀ v : ℝ, R.character u * c j ≠ heckeNormTwist K v) →
        (fun v => heckeRadialParameter K v (R.character u * c j)) = arch →
        heckeArchWeight K (R.character u * c j) = weight → 1 ≤ U →
        heckeConductorScale K (R.character u * c j) ≤ conductorRatio * U →
        1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
        0 < H → P₀ ≤ Z ^ (g.slots j).length → H + 3 / 2 ≤ Hupper →
        ZeroUpperBound K (R.character u * c j) Hupper β →
        ‖primePolynomial (sharedMomentData K S P R omega ψ a g c u.sector V W)
          j u.ideal.val Z t‖ ≤
          (Real.sqrt (Z ^ (g.slots j).length))⁻¹ *
            (actualPrimeCancellationEnvelope K C A CW order U β δ H
                (Z ^ (g.slots j).length) + B * Real.sqrt (Z ^ (g.slots j).length) +
              (Real.log ((Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) *
                idealNorm K u.ideal.val) / Real.log 2) * M) := by
  obtain ⟨C, A, P₀, CW, B, M, hC, hA, hP₀, hCW, hB, hM, hb⟩ :=
    exists_actual_finite_height_masked_prime_bound K S hcomplex arch weight
      conductorRatio hRatio ((g.slots j).profile t) hW hs order
  refine ⟨C, A, P₀, CW, B, M, hC, hA, hP₀, hCW, hB, hM, ?_⟩
  intro u U β δ H Z Hupper hχ harch hweight hU hQ hβ hβ' hδ hδ'
    hH hP hpadding hupper
  have h := hb (R.character u * c j) u.ideal.val U β δ H
    (Z ^ (g.slots j).length) Hupper ((g.slots j).support t (Z ^ (g.slots j).length))
    hχ harch hweight hU hQ hβ hβ' hδ hδ' hH hP hpadding hupper
    (fun p hp => ((g.slots j).support_spec t (Z ^ (g.slots j).length) p).mpr hp)
  rw [shared_primePolynomial_eq_actualOriginalMaskedPrimeSum K S P R omega ψ,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg _))

end Expansion.Project

#print axioms Expansion.Project.shared_primePolynomial_eq_actualOriginalMaskedPrimeSum
#print axioms Expansion.Project.exists_shared_primePolynomial_finite_height_bound
