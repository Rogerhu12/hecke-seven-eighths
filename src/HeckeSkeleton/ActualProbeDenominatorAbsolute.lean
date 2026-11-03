import HeckeGeneral.Analysis.PhysicalProbeData
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
The original denominator weight occurs outside the inner row tsum. Its actual
annular support bounds the norm of every nonzero outer ideal term, for any
ProbeData and target character. Thus the outer denominator series has finite
support, including when no convergence of the inner rows has yet been proved.

This supplies precisely ProbeIntegralInput.denominator_absolute; it does not
supply theta_absolute, row_finite, Haar integrability or sixth-unit invariance.
UNCOMPILED static candidate, 2026-10-12; native_runs=0, verified_increment=0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualDenominatorAbsoluteDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A nonzero original denominator term forces a genuine ideal norm cutoff.
The upper endpoint is the one stored in this arbitrary P, not a fixed bump. -/
theorem probeDenominatorTerm_norm_le_of_ne_zero
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S)
    (hI : probeDenominatorTerm K S P ψ Q X Y Z t I ≠ 0) :
    exteriorNorm K S I ≤ P.denominator.upper * Y := by
  have hW : P.denominator.toFun (exteriorNorm K S I / Y) ≠ 0 := by
    intro hz
    apply hI
    simp only [probeDenominatorTerm, hz, mul_zero, zero_mul]
  have hupper : exteriorNorm K S I / Y ≤ P.denominator.upper :=
    (P.denominator.support hW).2
  exact (div_le_iff₀ hY).mp hupper

/-- The actual outer support is contained in the preimage of the existing
finite set of nonzero integral ideals with norm at most upper*Y. -/
theorem probeDenominatorTerm_support_subset
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Function.support (probeDenominatorTerm K S P ψ Q X Y Z t) ⊆
      (fun I : ExteriorIdeal K S => I.val) ⁻¹'
        (dyadicIdealSupport K (P.denominator.upper * Y / 2) : Set (NonzeroIdeal K)) := by
  have hu : 0 < P.denominator.upper :=
    lt_of_lt_of_le P.denominator.lower_pos P.denominator.upper_ge
  intro I hI
  apply (mem_dyadicIdealSupport_iff K
    (div_nonneg (mul_nonneg hu.le hY.le) (by norm_num)) I.val).mpr
  have hN := probeDenominatorTerm_norm_le_of_ne_zero K S P ψ Q X Y Z hY t I hI
  change exteriorNorm K S I ≤ 2 * (P.denominator.upper * Y / 2)
  linarith

theorem probeDenominatorTerm_hasFiniteSupport
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Function.HasFiniteSupport (probeDenominatorTerm K S P ψ Q X Y Z t) := by
  have hfinite : Set.Finite
      ((fun I : ExteriorIdeal K S => I.val) ⁻¹'
        (dyadicIdealSupport K (P.denominator.upper * Y / 2) : Set (NonzeroIdeal K))) :=
    (dyadicIdealSupport K (P.denominator.upper * Y / 2)).finite_toSet.preimage
      Subtype.val_injective.injOn
  exact hfinite.subset (probeDenominatorTerm_support_subset K S P ψ Q X Y Z hY t)

theorem probeDenominatorTerm_summable
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Summable (probeDenominatorTerm K S P ψ Q X Y Z t) :=
  summable_of_hasFiniteSupport
    (probeDenominatorTerm_hasFiniteSupport K S P ψ Q X Y Z hY t)

/-- Absolute summability holds as well, because taking a norm does not enlarge support. -/
theorem probeDenominatorTerm_norm_summable
    (P : ProbeData K S) (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Summable (fun I : ExteriorIdeal K S => ‖probeDenominatorTerm K S P ψ Q X Y Z t I‖) := by
  apply summable_of_hasFiniteSupport
  apply (probeDenominatorTerm_hasFiniteSupport K S P ψ Q X Y Z hY t).subset
  intro I hI
  exact norm_ne_zero_iff.mp hI

/-- The exact original field type, with all Q/X/Y/Z/t quantifiers retained.
No positivity of X or Z is needed for this finite-support argument. -/
theorem actual_probeDenominator_absolute (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
      0 < X → 0 < Y → 0 < Z → ∀ t : sLocalNormOneGroup K S,
        Summable (probeDenominatorTerm K S P ψ Q X Y Z t) := by
  intro Q X Y Z _hX hY _hZ t
  exact probeDenominatorTerm_summable K S P ψ Q X Y Z hY t

end HeckeGeneral.ThetaSkeleton.Physical.ActualDenominatorAbsoluteDraft
