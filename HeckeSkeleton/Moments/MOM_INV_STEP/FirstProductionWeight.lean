import HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveProduction

/-!
# The actual second production weight keeps its reconstruction zeros

The physical cost is exactly c_K N(g/d₂)/(rX). Both Moebius factors
contract in norm, while the original common and overlap zero factors
remain together as the actual reconstruction zero. The common norm cost
is displayed once, before any fixed-box numerical estimate is applied.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionWeight

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstToSecondData PositiveAssignedSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) → Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
variable (hmask : T.mask = ∅)
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J s Γ H₂

def physicalCost (i : Idx) : ℝ :=
  let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i
  ActualPoissonScale.fieldConstant K * height K Sset B.commonResidual /
    ((InverseRowMajorant.rowRadius (R i.1)).val * sourceScale K S T U)

theorem physicalCost_nonneg (i : Idx) :
    0 ≤ physicalCost K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i := by
  unfold physicalCost
  apply div_nonneg
  · exact mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K) (height_pos K Sset _).le
  · rw [sourceScale_eq K S T hbase U]
    exact (mul_pos (InverseRowMajorant.rowRadius (R i.1)).property U.property).le

theorem physicalCost_eq (i : Idx) :
    physicalCost K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i =
      ActualPoissonScale.fieldConstant K *
        height K Sset
          (FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i).commonResidual *
        (R i.1).val / U.val := by
  unfold physicalCost
  rw [sourceScale_eq K S T hbase U]
  dsimp only [InverseRowMajorant.rowRadius]
  field_simp [(R i.1).property.ne', U.property.ne']
  <;> ring

def overlapZeroNorm (i : Idx) : ℝ :=
  let Q := data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1
  ‖SecondColumnEnergy.overlapZero K S i.2.2.1.1.val Q.label
    (SecondMobiusGeometry.overlapIdeal K S (sourceScale K S T U) i.2.2.1.1.val i.2.2.2)‖

/-- The source scalar and the independently extracted overlap supply
exactly the zero required for the actual squarefree reconstruction. -/
theorem weight_overlap_eq (i : Idx) :
    SecondAdaptiveProduction.weightAt K S D Γ
      (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1) (H₂ i.1) i.2.2.1 *
      overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J s H₂ i =
    let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i
    ‖(moebius (IdealMobiusMask.primeProduct i.2.2.1.2.1.val) : ℂ)‖ *
      (physicalCost K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i *
        ‖B.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ B)‖) := by
  let Q := data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1
  let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i
  have hh := PositiveLiteralChildren.physical_scalar_with_overlap K S D Γ
    Q.columns Q.triple (SecondParentProduction.scale_pos K S Q) Q.radius B
  have hpuncture : childPuncture Q.columns.originalPuncture Q.triple =
      ActualTwoPassChildren.oldPuncture K S T.columns D Γ B := by
    change childPuncture T.columns.puncture
      (FirstColumnAssembly.firstTriple K S B.refs.1 B.refs.2 B.b₁ B.b₂ B.quotient) =
      childPuncture T.columns.puncture (PositiveLiteralChildren.priorTriple K B.outer)
    rw [PositiveLiteralChildren.priorTriple_source K S D Γ B]
  rw [hpuncture] at hh
  change (_ * ‖SecondParentRetained.sourceScalar K S Q.columns Q.triple
    (SecondParentProduction.scale_pos K S Q) Q.radius B.secondDivisor B.common B.firstLabel
      (sIntegerMaskGenerator K Sset B.firstDivisor)‖) *
      ‖SecondColumnEnergy.overlapZero K S B.common B.firstLabel B.overlap‖ = _
  rw [mul_assoc, hh]
  rfl

/-- The two actual Moebius coefficients contract without discarding
the common/overlap zero. This is the physical scalar supplied to the
finite production packet theorem. -/
theorem actual_weight_le (i : Idx) :
    SecondAdaptiveProduction.weightAt K S D Γ
      (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1) (H₂ i.1) i.2.2.1 *
      ‖(moebius i.2.2.2.val : ℂ)‖ *
      overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J s H₂ i ≤
    let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i
    physicalCost K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i *
      ‖B.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ B)‖ := by
  let B := FirstToSecondData.bare K S D T Θ ψ G hν hG hbase R U J s Γ H₂ hmask i
  let c := physicalCost K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i *
    ‖B.retainedZero (ActualTwoPassChildren.oldPuncture K S T.columns D Γ B)‖
  have hc : 0 ≤ c := mul_nonneg
    (physicalCost_nonneg K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i) (norm_nonneg _)
  have hμ : ‖(moebius i.2.2.2.val : ℂ)‖ *
      ‖(moebius (IdealMobiusMask.primeProduct i.2.2.1.2.1.val) : ℂ)‖ ≤ 1 :=
    mul_le_one₀ (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one _)
      (norm_nonneg _) (HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one _)
  calc
    _ = ‖(moebius i.2.2.2.val : ℂ)‖ *
        (SecondAdaptiveProduction.weightAt K S D Γ
          (data K S D T Θ ψ G hν hG hbase R U J s i.1 i.2.1) (H₂ i.1) i.2.2.1 *
          overlapZeroNorm K S D Γ T Θ ψ G hν hG hbase R U J s H₂ i) := by ring
    _ = (‖(moebius i.2.2.2.val : ℂ)‖ *
        ‖(moebius (IdealMobiusMask.primeProduct i.2.2.1.2.1.val) : ℂ)‖) * c := by
      rw [weight_overlap_eq K S D Γ T Θ ψ G hν hG hbase R U J s H₂ hmask i]
      dsimp only [c]
      ring
    _ ≤ 1 * c := mul_le_mul_of_nonneg_right hμ hc
    _ = _ := one_mul c

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstProductionWeight

end
