import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Original first coefficients and common-class divisor gates

The first source operation acts on each of the two original rectangles
with exactly the same multiplier. A nonzero coefficient still retains
its original divisor. On an active second common class that divisor
divides both complete extracted ideals, so its gate is identically one
on the corresponding Cartesian supports. No occurrence is discarded.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

namespace OrdinaryRectangleFactors

/-- The part of `I` outside its common support with `J` is coprime to
the whole ideal `J`, including every multiplicity. -/
theorem commonResidual_coprime (I J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    IsCoprime J (supportResidual I (primeSupport I ∩ primeSupport J)) := by
  apply (primeSupport_disjoint_iff hJ (supportResidual_ne_zero _ _)).mp
  rw [supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hPJ hPI
  obtain ⟨hPI, hnot⟩ := Finset.mem_sdiff.mp hPI
  exact hnot (Finset.mem_inter.mpr ⟨hPI, hPJ⟩)

/-- A divisor of both original ideals is already contained in their
complete extracted left and right common ideals. Squarefreeness is not
needed: the full original multiplicity survives extraction. -/
theorem commonDivisor_dvd_label (I J D : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) (hDI : D ∣ I) (hDJ : D ∣ J) :
    D ∣ (commonSupportLabel I J).1 ∧ D ∣ (commonSupportLabel I J).2 := by
  have hl : IsCoprime D (supportResidual I (primeSupport I ∩ primeSupport J)) :=
    (commonResidual_coprime I J hJ).of_isCoprime_of_dvd_left hDJ
  have hr : IsCoprime D (supportResidual J (primeSupport I ∩ primeSupport J)) := by
    rw [Finset.inter_comm]
    exact (commonResidual_coprime J I hI).of_isCoprime_of_dvd_left hDI
  constructor
  · apply hl.dvd_of_dvd_mul_right
    change D ∣ supportExtract I (primeSupport I ∩ primeSupport J) * _
    rwa [support_reconstruct I hI]
  · apply hr.dvd_of_dvd_mul_right
    change D ∣ supportExtract J (primeSupport I ∩ primeSupport J) * _
    rwa [support_reconstruct J hJ]

/-- Nonzero source witnesses establish the gate once for the entire
active common class; later columns need not be assumed nonzero. -/
theorem commonDivisor_dvd_pool {ι κ : Type*}
    (left : Finset ι) (right : Finset κ)
    (I : ι → Ideal (𝓞 K)) (J : κ → Ideal (𝓞 K))
    (D : Ideal (𝓞 K)) (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
    (hI : ∀ i ∈ left, I i ≠ 0) (hJ : ∀ j ∈ right, J j ≠ 0)
    (hDI : ∀ i ∈ left, D ∣ I i) (hDJ : ∀ j ∈ right, D ∣ J j)
    (hDE : DE ∈ commonSupportPool left right I J) :
    D ∣ DE.1 ∧ D ∣ DE.2 := by
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hDE
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  exact commonDivisor_dvd_label (I i) (J j) D
    (hI i hi) (hJ j hj) (hDI i hi) (hDJ j hj)

section Gates

variable {A : SArithmeticData K} {ι κ : Type*}
variable {I : ι → A.Exterior} {J : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

theorem left_divisor_gate (b : FirstCommonCharacterBlock I J DE)
    (left : Finset ι) (D : Ideal (𝓞 K)) (hD : D ∣ DE.1)
    (f : ι → ℂ) (i : ι) (hi : i ∈ b.leftColumns left) :
    (if D ∣ (I i).val then f i else 0) = f i := by
  apply if_pos
  rw [b.left_reconstruct left i hi, b.common_left]
  exact hD.trans (dvd_mul_right _ _)

theorem right_divisor_gate (b : FirstCommonCharacterBlock I J DE)
    (right : Finset κ) (D : Ideal (𝓞 K)) (hD : D ∣ DE.2)
    (f : κ → ℂ) (i : κ) (hi : i ∈ b.rightColumns right) :
    (if D ∣ (J i).val then f i else 0) = f i := by
  apply if_pos
  rw [b.right_reconstruct right i hi, b.common_right]
  exact hD.trans (dvd_mul_right _ _)

end Gates
end OrdinaryRectangleFactors

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace FirstPresentation

variable (F : FirstPresentation call p) (hF : F.Realizes)

include hF

theorem chart_leftCoefficient (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    (F.source.charts v D).leftCoefficient i = F.coefficient i *
      (((((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i)) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) : ℂ)) := by
  have heq : (F.source.charts v D).leftCoefficient =
      (F.canonicalChart v D).leftCoefficient := by
    congr 1 <;> first | exact hF.profile | exact hF.chart v D
  rw [congrFun heq i]
  rfl

theorem chart_rightCoefficient (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    (F.source.charts v D).rightCoefficient i = F.coefficient i *
      (((((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i)) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) : ℂ)) := by
  have heq : (F.source.charts v D).rightCoefficient =
      (F.canonicalChart v D).rightCoefficient := by
    congr 1 <;> first | exact hF.profile | exact hF.chart v D
  rw [congrFun heq i]
  rfl

end FirstPresentation

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : FirstCauchyKey F)

theorem phase_eq_one : FirstCauchyKey.phase key = 1 := by
  unfold FirstCauchyKey.phase
  split_ifs
  · change (((fixedRightPhase PUnit (FirstCauchyKey.character key)) 1 : Circle) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  · change (((fixedLeftPhase PUnit (FirstCauchyKey.character key)) 1 : Circle) : ℂ) = 1
    rw [map_one, Circle.coe_one]

theorem coefficient_nonzero_divisor (i : F.source.Column)
    (hi : FirstCauchyKey.coefficient key i ≠ 0) :
    (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val := by
  by_contra hn
  exact hi (by simp only [FirstCauchyKey.coefficient, if_neg hn])

theorem multiplier_nonzero_divisor (i : F.source.Column)
    (hi : FirstCauchyKey.multiplier key i ≠ 0) :
    (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val := by
  by_contra hn
  exact hi (by simp only [FirstCauchyKey.multiplier, if_neg hn])

/-- The first transform's whole coefficient uses exactly the same
linear multiplier as each of its original comparison rectangles. -/
theorem coefficient_eq_multiplier (hF : F.Realizes) (i : F.source.Column) :
    FirstCauchyKey.coefficient key i = FirstCauchyKey.multiplier key i * F.coefficient i := by
  by_cases hdiv : (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val
  · simp only [FirstCauchyKey.coefficient, FirstCauchyKey.multiplier, if_pos hdiv]
    cases hs : FirstCauchyKey.side key
    · simp only [hs, Bool.false_eq_true, if_false, FirstBlockDirectData.originalLeftCoefficient]
      rw [F.chart_leftCoefficient hF key.1 key.2.1 i]
      simp only [FirstCauchyKey.block, FirstCauchyKey.divisor, ActualDirectFirstSource.block]
      ring
    · simp only [hs, if_true, FirstBlockDirectData.originalRightCoefficient]
      rw [F.chart_rightCoefficient hF key.1 key.2.1 i]
      simp only [FirstCauchyKey.block, FirstCauchyKey.divisor, ActualDirectFirstSource.block]
      ring
  · simp only [FirstCauchyKey.coefficient, FirstCauchyKey.multiplier, if_neg hdiv, zero_mul]

theorem data_ideal (i : F.source.Column) :
    (FirstCauchyKey.data key).ideal i =
      if FirstCauchyKey.side key then (FirstCauchyKey.block key).rightResidual i
      else (FirstCauchyKey.block key).leftResidual i := by
  unfold FirstCauchyKey.data
  split_ifs
  · exact congrFun (FirstCauchyKey.piece key).right_ideal i
  · exact congrFun (FirstCauchyKey.piece key).left_ideal i

theorem firstElement_ne_zero : FirstCauchyKey.firstElement key ≠ 0 := by
  let delta := sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (FirstCauchyKey.divisor key).val
  have hd : (Arithmetic.data c).Generates
      (firstPhysicalDivisorIdeal (A := Arithmetic.data c)
        (FirstCauchyKey.divisor key).val) delta.val :=
    originalFrequencyIdeal_generates delta.val delta.property
  unfold FirstCauchyKey.firstElement
  dsimp only
  split_ifs
  · exact (CanonicalLiteralFirstPhase.rightElement_generates (Arithmetic.context c)
      (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).leftMultiplicity
      (FirstCauchyKey.block key).rightMultiplicity _ delta.val hd).1
  · exact (CanonicalLiteralFirstPhase.leftElement_generates (Arithmetic.context c)
      (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).leftMultiplicity
      (FirstCauchyKey.block key).rightMultiplicity _ delta.val hd).1

/-- After its original gate is known, the actual first scalar is a
norm tilt divided by the same norm, times the full nonunit-preserving
fixed residue. It is uniform across both original comparison terms. -/
theorem multiplier_eq_residue (i : F.source.Column)
    (hdiv : (FirstCauchyKey.residual key).val ∣ ((FirstCauchyKey.data key).ideal i).val) :
    FirstCauchyKey.multiplier key i =
      ((((Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) ^ p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((FirstCauchyKey.data key).ideal i) : ℂ)) *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
        ((FirstCauchyKey.data key).ideal i).val (FirstCauchyKey.firstElement key) := by
  have hallowed := canonicalFirstCommonBlock_allowed (Arithmetic.context c)
    F.source.columns F.source.columns F.source.ideal F.source.ideal key.1.val key.1.property
  have hleft := allowed_mk0_of_generator (Arithmetic.context c).correction.B
    ((FirstCauchyKey.block key).leftGenerator i)
    ((FirstCauchyKey.block key).left_generates i).1 (hallowed.1 i)
  have hright := allowed_mk0_of_generator (Arithmetic.context c).correction.B
    ((FirstCauchyKey.block key).rightGenerator i)
    ((FirstCauchyKey.block key).right_generates i).1 (hallowed.2 i)
  rw [FirstCauchyKey.multiplier, if_pos hdiv, key.phase_eq_one, mul_one, key.data_ideal i]
  cases hs : FirstCauchyKey.side key
  · simp only [hs, Bool.false_eq_true, if_false, FirstCauchyKey.firstElement]
    rw [CanonicalLiteralFirstPhase.leftDivisorFactor
      (Arithmetic.units_are_sixth c) (Arithmetic.context c)
      (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).primes_injective
      (FirstCauchyKey.block key).leftMultiplicity (FirstCauchyKey.block key).rightMultiplicity
      ((FirstCauchyKey.block key).leftResidual i) ((FirstCauchyKey.block key).leftGenerator i)
      ((FirstCauchyKey.block key).left_generates i) hleft]
  · simp only [hs, if_true, FirstCauchyKey.firstElement]
    rw [CanonicalLiteralFirstPhase.rightDivisorFactor
      (Arithmetic.units_are_sixth c) (Arithmetic.context c)
      (FirstCauchyKey.block key).primes (FirstCauchyKey.block key).primes_injective
      (FirstCauchyKey.block key).leftMultiplicity (FirstCauchyKey.block key).rightMultiplicity
      ((FirstCauchyKey.block key).rightResidual i) ((FirstCauchyKey.block key).rightGenerator i)
      ((FirstCauchyKey.block key).right_generates i) hright]

end FirstCauchyKey

namespace PhysicalSource

variable (source : PhysicalSource call p)

theorem residualDivisor_dvd_activeCommon
    (hdiv : ∀ i ∈ source.source.columns, source.source.coefficient i ≠ 0 →
      source.first.residualDivisor.val ∣ (source.source.ideal i).val)
    (DE : Ideal (𝓞 K) × Ideal (𝓞 K)) (hDE : DE ∈ source.activeCommon) :
    source.first.residualDivisor.val ∣ DE.1 ∧
      source.first.residualDivisor.val ∣ DE.2 := by
  apply OrdinaryRectangleFactors.commonDivisor_dvd_pool
    (source.source.columns.filter (fun i => source.source.coefficient i ≠ 0))
    (source.source.columns.filter (fun i => source.source.coefficient i ≠ 0))
    (fun i => (source.source.ideal i).val) (fun i => (source.source.ideal i).val)
    source.first.residualDivisor.val DE
  · intro i _
    exact (source.source.ideal i).property.1
  · intro i _
    exact (source.source.ideal i).property.1
  · intro i hi
    exact hdiv i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  · intro i hi
    exact hdiv i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  · exact hDE

end PhysicalSource
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstCauchyKey.coefficient_eq_multiplier
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryRectangleFactors.commonDivisor_dvd_label
