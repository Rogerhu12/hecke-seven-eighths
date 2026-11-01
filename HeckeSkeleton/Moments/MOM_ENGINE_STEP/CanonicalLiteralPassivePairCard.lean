import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNonzeroMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveNormalizedFamily

/-!
# Uniform count of the actual independent passive pairs

The two sides retain their independent nonzero divisor-allocation
labels and their two rectangle choices. The original first common
ideal, and the genuine pool prime when present, pay the count. The
constant is selected before the scale, source, profiles or allocations.

This counts the actual carrier used by the passive family. It neither
adds back zero Mobius terms nor assumes a cardinality estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open CanonicalLiteralPassiveNonzero CanonicalLiteralPassiveLabelMass

namespace CanonicalLiteralPassiveNormalizedFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {k l : ℕ}
variable {leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l}

/-- The universal factor four is precisely the two rectangle choices
on each side; the two divisor-allocation counts are separate. -/
theorem pairLabel_card
    (left : leftAtoms.ProfileData) (right : rightAtoms.ProfileData)
    (BL : ActualColumnAllocation K k) (BR : ActualColumnAllocation K l)
    (ML MR : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (Fintype.card (PairLabel (A := A) left right BL BR ML MR) : ℝ) =
      4 * (((nonzeroLabels left BL A ML).card : ℝ) *
        ((nonzeroLabels right BR A MR).card : ℝ)) := by
  simp only [PairLabel, SideLabel, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The direct/main pair uses the actual radical deletion of the
original first common ideal. All occurrence counts, including the two
plain occurrences and zero live slots, are included by the label bound. -/
theorem direct_pair_card (cap : ℕ) (columnBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (A : SArithmeticData K) (D : Ideal (𝓞 K)), D ≠ 0 →
      (Ideal.absNorm D : ℝ) ≤ Z ^ columnBound →
      ∀ k l : ℕ,
      ∀ (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k)
        (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l)
        (left : leftAtoms.ProfileData) (right : rightAtoms.ProfileData)
        (BL : ActualColumnAllocation K k) (BR : ActualColumnAllocation K l),
        k ≤ cap → l ≤ cap →
        (Fintype.card (PairLabel (A := A) left right BL BR (firstMask D) (firstMask D)) : ℝ) ≤
          C * Z ^ ε := by
  obtain ⟨C, hC, hcard⟩ := direct_source_card (K := K)
    cap columnBound (ε / 2) hcolumnBound (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro Z hZ A D hD hnorm k l leftAtoms rightAtoms left right BL BR hk hl
  have hleft := hcard Z hZ A D D hD (firstMask_dvd D hD)
    hnorm k leftAtoms left BL hk
  have hright := hcard Z hZ A D D hD (firstMask_dvd D hD)
    hnorm l rightAtoms right BR hl
  have hpower : Z ^ (ε / 2) * Z ^ (ε / 2) = Z ^ ε := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  calc
    _ = 4 * (((nonzeroLabels left BL A (firstMask D)).card : ℝ) *
        ((nonzeroLabels right BR A (firstMask D)).card : ℝ)) :=
      pairLabel_card left right BL BR (firstMask D) (firstMask D)
    _ ≤ 4 * ((C * Z ^ (ε / 2)) * (C * Z ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hleft hright (Nat.cast_nonneg _) (by positivity)) (by norm_num)
    _ = (4 * C ^ 2) * Z ^ ε := by
      calc
        _ = (4 * C ^ 2) * (Z ^ (ε / 2) * Z ^ (ε / 2)) := by ring
        _ = _ := by rw [hpower]

/-- At valuation six the actual mask retains its second copy of the
pool prime. The already proved nonzero-label count pays it before the
two independent sides are multiplied. -/
theorem pool_pair_card (cap : ℕ) (columnBound primeBound ε : ℝ)
    (hcolumnBound : 0 ≤ columnBound) (hprimeBound : 0 ≤ primeBound) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (A : SArithmeticData K) (D : Ideal (𝓞 K)), D ≠ 0 →
      (Ideal.absNorm D : ℝ) ≤ Z ^ columnBound →
      ∀ (p : ExteriorPrime A), (Ideal.absNorm p.val.asIdeal : ℝ) ≤ Z ^ primeBound →
      ∀ (e : AmplifierValuation) (k l : ℕ),
      ∀ (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k)
        (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l)
        (left : leftAtoms.ProfileData) (right : rightAtoms.ProfileData)
        (BL : ActualColumnAllocation K k) (BR : ActualColumnAllocation K l),
        k ≤ cap → l ≤ cap →
        (Fintype.card (PairLabel (A := A) left right BL BR
          (poolMask D p e) (poolMask D p e)) : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hcard⟩ := pool_source_card (K := K)
    cap columnBound primeBound (ε / 2) hcolumnBound hprimeBound (by positivity)
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro Z hZ A D hD hnorm p hp e k l leftAtoms rightAtoms left right BL BR hk hl
  have hleft := hcard Z hZ A D D hD (firstMask_dvd D hD)
    hnorm p hp e k leftAtoms left BL hk
  have hright := hcard Z hZ A D D hD (firstMask_dvd D hD)
    hnorm p hp e l rightAtoms right BR hl
  have hpower : Z ^ (ε / 2) * Z ^ (ε / 2) = Z ^ ε := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  calc
    _ = 4 * (((nonzeroLabels left BL A (poolMask D p e)).card : ℝ) *
        ((nonzeroLabels right BR A (poolMask D p e)).card : ℝ)) :=
      pairLabel_card left right BL BR (poolMask D p e) (poolMask D p e)
    _ ≤ 4 * ((C * Z ^ (ε / 2)) * (C * Z ^ (ε / 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hleft hright (Nat.cast_nonneg _) (by positivity)) (by norm_num)
    _ = (4 * C ^ 2) * Z ^ ε := by
      calc
        _ = (4 * C ^ 2) * (Z ^ (ε / 2) * Z ^ (ε / 2)) := by ring
        _ = _ := by rw [hpower]

end CanonicalLiteralPassiveNormalizedFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.pairLabel_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.direct_pair_card
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveNormalizedFamily.pool_pair_card
