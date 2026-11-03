import HeckeGeneral.Analysis.TInputPrincipal
import HeckeGeneral.Analysis.SIntegerAnnularColumnFinite

/-!
# Finiteness of the actual physical-probe row

Candidate under native validation; the first source was archived before
repairing the missing Global namespace opening. Full audit remains pending.

The actual compact tensor support, rather than decay of an arbitrary Schwartz
function, supplies the required bound at infinity. Compact finite coordinates
give one common nonzero integer denominator. Its multiples lie in the actual
mixed integer lattice and in a compact set, hence form a finite set.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Compact subsets of the actual local multiplicative group contain only
finitely many diagonals of nonzero S-integers. The source is all nonzero
S-integers, not merely the global S-units. -/
theorem finite_nonzeroSIntegerDiagonal_preimage_compact
    (C : Set (sLocalMultiplicativeGroup K S)) (hC : IsCompact C) :
    Set.Finite ((sLocalNonzeroIntegerDiagonal K S) ⁻¹' C) := by
  let fin : sLocalMultiplicativeGroup K S → ((v : S) → v.val.adicCompletion K) :=
    fun x v => (x.2 v).val
  have hfin : Continuous fin := by
    apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
  let arch : sLocalMultiplicativeGroup K S → mixedEmbedding.euclidean.mixedSpace K :=
    fun x => (traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)
  have harch : Continuous arch := (traceToMixed K).symm.continuous.comp
    (Units.continuous_val.comp continuous_fst)
  have hfinite := finite_sInteger_diagonal_compact_conditions K S
    (arch '' C) (hC.image harch) (fin '' C) (hC.image hfin)
  apply hfinite.subset
  intro m hm
  constructor
  · exact ⟨sLocalNonzeroIntegerDiagonal K S m, hm, rfl⟩
  · exact ⟨sLocalNonzeroIntegerDiagonal K S m, hm, rfl⟩

/-- The original additive test has finite support on every fixed translated
nonzero S-integer diagonal. -/
theorem finite_additiveTest_nonzeroSInteger_row (W : AdditiveProbeTest K S)
    (d : sLocalMultiplicativeGroup K S) :
    Set.Finite {m : NonzeroRingElements (S.integer K) |
      additiveTest K S W (sLocalNonzeroIntegerDiagonal K S m / d) ≠ 0} := by
  have hW : HasCompactSupport (additiveTest K S W) := W.tensor_compactSupport
  have hfinite := finite_nonzeroSIntegerDiagonal_preimage_compact K S
    ((fun x : sLocalMultiplicativeGroup K S => x * d) '' tsupport (additiveTest K S W))
    (hW.isCompact.image (continuous_id.mul continuous_const))
  apply hfinite.subset
  intro m hm
  refine ⟨sLocalNonzeroIntegerDiagonal K S m / d, subset_closure hm, ?_⟩
  exact div_mul_cancel _ _

/-- Exactly the `ProbeIntegralInput.row_finite` field, with its original
quantifiers and actual summands. No convergence or arithmetic-calibration
input is used. -/
theorem probeIntegralInput_row_finite (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∀ (Q : Finset (ExteriorPrime K S)) (X Z : ℝ), 0 < X → 0 < Z →
      ∀ (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S),
        Set.Finite {m : NonzeroRingElements (S.integer K) |
          probeRowTerm K S P ψ Q X Z t I m ≠ 0} := by
  intro Q X Z _hX _hZ t I
  by_cases h : 0 < exteriorNorm K S I * X
  · apply (finite_additiveTest_nonzeroSInteger_row K S P.additive
      ((t : sLocalMultiplicativeGroup K S) *
        sLocalNormSection K S ⟨exteriorNorm K S I * X, h⟩)).subset
    intro m hm
    simp only [probeRowTerm, dif_pos h] at hm
    intro hz
    apply hm
    rw [hz, mul_zero, zero_mul]
  · have he : {m : NonzeroRingElements (S.integer K) |
        probeRowTerm K S P ψ Q X Z t I m ≠ 0} = ∅ := by
      ext m
      simp [probeRowTerm, h]
    rw [he]
    exact Set.finite_empty

end HeckeGeneral.ThetaSkeleton.Physical
