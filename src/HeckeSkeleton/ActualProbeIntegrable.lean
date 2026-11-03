import HeckeSkeleton.ActualProbeRowFinite
import HeckeSkeleton.ActualProbeDenominatorAbsolute
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Haar integrability of the actual physical probe

UNCOMPILED candidate; no native invocation. Compactness gives a uniform
finite set of actual row elements on any compact set of norm-one parameters.
The original denominator then gives a uniform finite set of exterior ideals.
The completed theta value at each fixed element is a constant in this argument;
no theta convergence or reflection theorem is used to prove integrability.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open ActualDenominatorAbsoluteDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem continuous_additiveTest (W : AdditiveProbeTest K S) :
    Continuous (additiveTest K S W) := by
  unfold additiveTest
  apply continuous_sLocalTensorTestFunction K S
  apply continuous_finsetProd Finset.univ
  intro p _
  exact (W.finite_locallyConstant p).continuous.comp (continuous_apply p)

theorem continuous_probeRowTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Z : ℝ) (I : ExteriorIdeal K S)
    (m : NonzeroRingElements (S.integer K)) :
    Continuous (fun t : sLocalNormOneGroup K S => probeRowTerm K S P ψ Q X Z t I m) := by
  unfold probeRowTerm
  split_ifs with h
  · exact (continuous_const.mul ((continuous_additiveTest K S P.additive).comp
      (continuous_const.div' (continuous_subtype_val.mul continuous_const)))).mul continuous_const
  · exact continuous_const

/-- One finite row-index set works throughout the compact parameter set. -/
theorem exists_uniform_probeRowTerm_support (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Z : ℝ) (I : ExteriorIdeal K S)
    (C : Set (sLocalNormOneGroup K S)) (hC : IsCompact C) :
    ∃ M : Finset (NonzeroRingElements (S.integer K)),
      ∀ t ∈ C, ∀ m ∉ M, probeRowTerm K S P ψ Q X Z t I m = 0 := by
  by_cases h : 0 < exteriorNorm K S I * X
  · let d := sLocalNormSection K S ⟨exteriorNorm K S I * X, h⟩
    let F : sLocalMultiplicativeGroup K S × sLocalNormOneGroup K S →
        sLocalMultiplicativeGroup K S := fun p => p.1 * ((p.2 : sLocalMultiplicativeGroup K S) * d)
    have hF : Continuous F := continuous_fst.mul
      ((continuous_subtype_val.comp continuous_snd).mul continuous_const)
    have hc : IsCompact (F '' (tsupport (additiveTest K S P.additive) ×ˢ C)) :=
      (P.additive.tensor_compactSupport.isCompact.prod hC).image hF
    have hfinite := finite_nonzeroSIntegerDiagonal_preimage_compact K S _ hc
    refine ⟨hfinite.toFinset, ?_⟩
    intro t ht m hm
    by_contra hrow
    have htest : additiveTest K S P.additive
        (sLocalNonzeroIntegerDiagonal K S m / ((t : sLocalMultiplicativeGroup K S) * d)) ≠ 0 := by
      intro hz
      apply hrow
      simp only [probeRowTerm, dif_pos h]
      change _ * additiveTest K S P.additive
        (sLocalNonzeroIntegerDiagonal K S m / ((t : sLocalMultiplicativeGroup K S) * d)) * _ = 0
      rw [hz, mul_zero, zero_mul]
    apply hm
    apply hfinite.mem_toFinset.mpr
    refine ⟨(sLocalNonzeroIntegerDiagonal K S m /
      ((t : sLocalMultiplicativeGroup K S) * d), t), ⟨subset_closure htest, ht⟩, ?_⟩
    exact div_mul_cancel _ _
  · refine ⟨∅, ?_⟩
    intro t _ m _
    simp only [probeRowTerm, dif_neg h]

theorem continuousOn_probeRowSum (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Z : ℝ) (I : ExteriorIdeal K S)
    (C : Set (sLocalNormOneGroup K S)) (hC : IsCompact C) :
    ContinuousOn (fun t => ∑' m : NonzeroRingElements (S.integer K),
      probeRowTerm K S P ψ Q X Z t I m) C := by
  obtain ⟨M, hM⟩ := exists_uniform_probeRowTerm_support K S P ψ Q X Z I C hC
  apply (continuous_finsetSum M (fun m _ =>
    continuous_probeRowTerm K S P ψ Q X Z I m)).continuousOn.congr
  intro t ht
  exact tsum_eq_sum (fun m hm => hM t ht m hm)

theorem continuousOn_probeDenominatorTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ) (I : ExteriorIdeal K S)
    (C : Set (sLocalNormOneGroup K S)) (hC : IsCompact C) :
    ContinuousOn (fun t => probeDenominatorTerm K S P ψ Q X Y Z t I) C :=
  continuousOn_const.mul (continuousOn_probeRowSum K S P ψ Q X Z I C hC)

theorem continuousOn_probeIntegrand (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ) (hY : 0 < Y)
    (C : Set (sLocalNormOneGroup K S)) (hC : IsCompact C) :
    ContinuousOn (probeIntegrand K S P ψ Q X Y Z) C := by
  have hfinite : Set.Finite
      ((fun I : ExteriorIdeal K S => I.val) ⁻¹'
        (dyadicIdealSupport K (P.denominator.upper * Y / 2) : Set (NonzeroIdeal K))) :=
    (dyadicIdealSupport K (P.denominator.upper * Y / 2)).finite_toSet.preimage
      Subtype.val_injective.injOn
  apply (continuousOn_finsetSum hfinite.toFinset (fun I _ =>
    continuousOn_probeDenominatorTerm K S P ψ Q X Y Z I C hC)).congr
  intro t _
  apply tsum_eq_sum
  intro I hI
  by_contra hne
  exact hI (hfinite.mem_toFinset.mpr
    (probeDenominatorTerm_support_subset K S P ψ Q X Y Z hY t hne))

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- Exactly the original integrability field, with its original finite-index
instance and actual unnormalized Haar measure. -/
theorem probeIntegralInput_integral (P : ProbeData K S) (ψ : HeckeCharacter K) :
    ∀ (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ),
      0 < X → 0 < Y → 0 < Z →
      letI : (sixthPowerUnits K S).FiniteIndex :=
        sUnit_power_range_finiteIndex K S 6 (by decide)
      IntegrableOn (probeIntegrand K S P ψ Q X Y Z)
        (sUnitFundamentalDomain K S (sixthPowerUnits K S)) (sUnitHaarMeasure K S) := by
  intro Q X Y Z _hX hY _hZ
  letI : (sixthPowerUnits K S).FiniteIndex :=
    sUnit_power_range_finiteIndex K S 6 (by decide)
  have hC := isCompact_closure_sUnitFundamentalDomain K S (sixthPowerUnits K S)
  exact (ContinuousOn.integrableOn_compact hC
    (continuousOn_probeIntegrand K S P ψ Q X Y Z hY _ hC)).mono_set subset_closure

end HeckeGeneral.ThetaSkeleton.Physical
