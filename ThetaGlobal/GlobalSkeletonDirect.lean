import ThetaGlobal.GlobalProjectDirectMask
import ThetaGlobal.GlobalSkeletonChoice
import ThetaGlobal.ActualAnnularTransfer
import HeckeAxiom.GaussDictionary

/-!
# The actual direct quotient series is the skeleton's completed theta sum

The same arithmetic choice supplies the allowed generator, principal
Gauss sum and target Hecke period.  The finite mask is evaluated before
using reciprocity, so all collision zeros and puncture/mark conditions
remain in the literal `completedTerm` definition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalSkeletonDirect

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton
open scoped NumberField Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

def forwardPair (j : ForwardIndex R) : ExteriorIdeal K Sf × ExteriorIdeal K Sf :=
  (HeckeAxiom.exteriorEquiv R.A j.1.val, HeckeAxiom.exteriorEquiv R.A j.2)

theorem forwardPair_injective : Function.Injective (forwardPair K c) := by
  intro i j h
  apply Prod.ext
  · apply Subtype.ext
    apply (HeckeAxiom.exteriorEquiv R.A).injective
    exact congrArg Prod.fst h
  · apply (HeckeAxiom.exteriorEquiv R.A).injective
    exact congrArg Prod.snd h

theorem forwardPair_completedIdeal (j : ForwardIndex R) :
    completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2 =
      HeckeAxiom.exteriorEquiv R.A (forwardIdeal R j.1 j.2) := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [forwardPair, completedIdeal, exteriorMul, forwardIdeal,
    HeckeAxiom.exteriorEquiv, pow_succ, pow_zero, mul_one, mul_assoc]

theorem coefficientGenerator (I : R.A.Exterior) :
    R.probe.coefficients.generator I = Adata.generator (HeckeAxiom.exteriorEquiv R.A I) := by
  apply Subtype.ext
  have hg := congrArg Units.val (thetaRecipe_generator K c (HeckeAxiom.exteriorEquiv R.A I))
  simp only [Equiv.symm_apply_apply, GlobalActualFrequency.generatorUnit] at hg
  exact (R.probe.sameGenerator I).symm.trans hg.symm

/-- Both normalized Gauss sums use the same ideal, allowed generator,
trace character and embedding. -/
theorem gammaTwo (I : ExteriorSquarefreeIdeal R.A.cS) :
    R.probe.coefficients.gammaTwo I =
      thetaGamma K Sf Adata (HeckeAxiom.exteriorEquiv R.A I.val) 2 := by
  rw [R.probe.gammaTwo_eq_idealGauss,
    (axiomChoice K c).thetaGamma_eq_gauss _ 2 (by decide) (by decide)]
  change R.A.idealGauss R.σ R.traceBad I.val (R.probe.coefficients.generator I.val) _ 2 =
    R.A.idealGauss R.σ R.traceBad
      ((HeckeAxiom.exteriorEquiv R.A).symm (HeckeAxiom.exteriorEquiv R.A I.val))
      (Adata.generator (HeckeAxiom.exteriorEquiv R.A I.val)) _ 2
  rw [Equiv.symm_apply_apply, coefficientGenerator K c]

def generatorFrequency (I : ExteriorIdeal K Sf) : ThetaReflectionData.Frequency R.A :=
  QuotientGroup.mk (GlobalActualFrequency.generatorUnit K Sf Adata I)

theorem generatorFrequency_mul (I J : ExteriorIdeal K Sf) :
    generatorFrequency K c (exteriorMul K Sf I J) =
      generatorFrequency K c I * generatorFrequency K c J := by
  obtain ⟨u, hu⟩ := (axiomChoice K c).thetaData_multiplicative I J
  have he : GlobalActualFrequency.generatorUnit K Sf Adata (exteriorMul K Sf I J) =
      u.val ^ 6 * GlobalActualFrequency.generatorUnit K Sf Adata I *
        GlobalActualFrequency.generatorUnit K Sf Adata J := by
    apply Units.ext
    exact congrArg (fun a : Sf.integer K => (a : K)) hu
  have hunit : (QuotientGroup.mk (u.val ^ 6) : ThetaReflectionData.Frequency R.A) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩
  simp only [generatorFrequency, he, QuotientGroup.mk_mul, hunit, one_mul]

theorem forwardFrequency_completed (j : ForwardIndex R) :
    forwardFrequency R j = generatorFrequency K c
      (completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2) := by
  rw [completedIdeal, generatorFrequency_mul, generatorFrequency_mul, generatorFrequency_mul]
  simp only [forwardFrequency, forwardGenerator, generatorFrequency,
    thetaRecipe_generator, forwardPair, Equiv.symm_apply_apply,
    QuotientGroup.mk_mul, QuotientGroup.mk_pow, pow_succ, pow_zero, mul_one, mul_assoc]

theorem forwardNorm_completed (j : ForwardIndex R) :
    (q R.A (forwardGenerator R j.1 j.2)).val =
      exteriorNorm K Sf (completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2) := by
  rw [forwardGenerator_norm,
    HeckeGeneral.ThetaSkeleton.Physical.ActualThetaAbsoluteDraft.exteriorNorm_completedIdeal] <;> rfl

variable (θ : HeckeCharacter K) (C : FiniteFixedSource.Source R θ)
  (L : FiniteLocalHighK.Input R θ C)

local notation "D" => C.projected.base.factorization

theorem directTest_completed (w : InfinitePlace K) (l : PositiveAxis) (j : ForwardIndex R) :
    ActualAnnularTransfer.directTest R θ C L w
      (exteriorNorm K Sf (completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2) /
        l.val⁻¹) =
      FiniteNormalizedMellin.direct R θ C L w (q R.A (forwardGenerator R j.1 j.2) * l) := by
  have he : exteriorNorm K Sf
      (completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2) / l.val⁻¹ =
      (q R.A (forwardGenerator R j.1 j.2) * l).val := by
    rw [← forwardNorm_completed K c j, div_inv_eq_mul] <;> rfl
  rw [he, ActualAnnularTransfer.directTest,
    dif_pos (q R.A (forwardGenerator R j.1 j.2) * l).property]

theorem completed_support (d : MarkedDatum K Sf) (V : ℝ → ℂ) (X : ℝ)
    (cn : ExteriorIdeal K Sf × ExteriorIdeal K Sf)
    (hcn : completedTerm K Sf Adata θ (rowElement K Sf Adata d)
      d.puncture d.marks V X cn ≠ 0) : cn ∈ Set.range (forwardPair K c) := by
  have hs : Squarefree cn.1.val.val := by
    by_contra hn
    exact hcn (by simp [completedTerm, hn])
  let i : ForwardIndex R :=
    (⟨(HeckeAxiom.exteriorEquiv R.A).symm cn.1, hs⟩,
      (HeckeAxiom.exteriorEquiv R.A).symm cn.2)
  refine ⟨i, ?_⟩
  apply Prod.ext <;> simp only [forwardPair, i, Equiv.apply_symm_apply]

theorem completed_sum_reindex (d : MarkedDatum K Sf) (V : ℝ → ℂ) (X : ℝ) :
    (∑' j : ForwardIndex R,
      completedTerm K Sf Adata θ (rowElement K Sf Adata d)
        d.puncture d.marks V X (forwardPair K c j)) =
      completedThetaSum K Sf Adata θ (rowElement K Sf Adata d) d.puncture d.marks V X :=
  (forwardPair_injective K c).tsum_eq (fun cn => completed_support K c θ d V X cn)

variable (H : GlobalProjectLocalDigitTables.Input R D Adata)
  (hS : conductorPlaces K θ ⊆ R.A.Sf)

include H hS in
/-- The literal coefficient dictionary, with the same direct high K-type
sheet and the original project's whole-index mask. -/
theorem directTerm_generator (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (l : PositiveAxis) (j : ForwardIndex R) :
    GlobalProjectOrbitEvaluation.directTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (forwardGenerator R j.1 j.2) =
      completedTerm K Sf Adata θ (rowElement K Sf Adata d) d.puncture d.marks
        (ActualAnnularTransfer.directTest R θ C L w) l.val⁻¹ (forwardPair K c j) := by
  let I := completedIdeal K Sf (forwardPair K c j).1 (forwardPair K c j).2
  let a := GlobalActualFrequency.generatorUnit K Sf Adata I
  have hfreq : (QuotientGroup.mk (forwardGenerator R j.1 j.2) :
      ThetaReflectionData.Frequency R.A) = QuotientGroup.mk a :=
    forwardFrequency_completed K c j
  have ht := GlobalProjectDirectReindex.directTerm_eq_of_frequency_eq R θ C L Adata H hS
    (QuotientGroup.mk d.rowUnit) (GlobalProjectMarkedSupport.row R d)
    (GlobalProjectMarkedSupport.digits R d) (GlobalProjectMarkedSupport.marks R d)
    w l (forwardGenerator R j.1 j.2) a hfreq
  rw [ht]
  have hext : (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p a) =
      R.probe.coefficients.gammaTwo j.1 /
        ((Real.sqrt (R.A.exteriorNorm j.1.val) : ℂ) * (R.A.exteriorNorm j.2 : ℂ)) :=
    (GlobalProjectDirectReindex.exteriorProduct_eq_of_frequency_eq R D
      C.projected.base.exterior a _ hfreq.symm).trans
      (GlobalProjectDirectReindex.exteriorProduct_generator R D C.projected.base.exterior j.1 j.2)
  have hallowed : QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal a) ∈
      R.probe.correction.B := by
    rw [show a = R.probe.allowed.generator ((HeckeAxiom.exteriorEquiv R.A).symm I) from
      thetaRecipe_generator K c I, ← R.probe.sameComplement]
    exact R.probe.allowed.allowed _
  have hq : q R.A a = q R.A (forwardGenerator R j.1 j.2) := by
    apply Subtype.ext
    exact congrArg (ThetaReflectionData.frequencyNorm R.A) hfreq.symm
  rw [GlobalProjectOrbitEvaluation.directTerm, GlobalProjectForwardCoefficients.scalar,
    GlobalProjectDirectMask.forwardCoefficient_generator R Adata d D H I,
    hext, if_pos hallowed, mul_one,
    thetaRecipe_period_generator K c θ hS d I, hq,
    ← directTest_completed K c θ C L w l j, gammaTwo K c]
  have hsf : Squarefree (forwardPair K c j).1.val.val := j.1.property
  by_cases hm : wholeIndexMask K Sf d.puncture d.marks I
  · rw [if_pos hm]
    unfold completedTerm
    dsimp only
    rw [if_pos ⟨hsf, hm⟩]
    rw [(axiomChoice K c).idealSymbol_reciprocity (GlobalProjectDirectMask.baseIdeal R d) I]
    simp only [periodValue, rowElement, GlobalProjectDirectMask.baseIdeal,
      GlobalProjectPhases.idealSymbol_mul]
    change _ = _
    ring
  · simp only [if_neg hm, zero_mul, completedTerm, hsf, true_and, hm, if_false]

include H hS in
/-- The full quotient series is the repository's literal completed theta
sum.  Neither side is assumed equal to a replacement coefficient model. -/
theorem direct_sum_eq_completed (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (l : PositiveAxis) :
    (∑' ξ : ThetaReflectionData.Frequency R.A,
      GlobalProjectOrbitEvaluation.directTerm R θ C L (QuotientGroup.mk d.rowUnit)
        (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
        w l (Quotient.out ξ)) =
      completedThetaSum K Sf Adata θ (rowElement K Sf Adata d) d.puncture d.marks
        (ActualAnnularTransfer.directTest R θ C L w) l.val⁻¹ := by
  rw [GlobalProjectDirectReindex.direct_frequency_reindex R θ C L Adata H hS
    (QuotientGroup.mk d.rowUnit) (GlobalProjectMarkedSupport.row R d)
    (GlobalProjectMarkedSupport.digits R d) (GlobalProjectMarkedSupport.marks R d)]
  simp_rw [directTerm_generator K c θ C L H hS d w l]
  exact completed_sum_reindex K c θ d _ _

include H hS in
theorem direct_sum_at_inverse (d : MarkedDatum K Sf) (w : InfinitePlace K)
    {X : ℝ} (hX : 0 < X) :
    (∑' ξ : ThetaReflectionData.Frequency R.A,
      GlobalProjectOrbitEvaluation.directTerm R θ C L (QuotientGroup.mk d.rowUnit)
        (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
        w ⟨X⁻¹, inv_pos.mpr hX⟩ (Quotient.out ξ)) =
      completedThetaSum K Sf Adata θ (rowElement K Sf Adata d) d.puncture d.marks
        (ActualAnnularTransfer.directTest R θ C L w) X := by
  simpa only [inv_inv] using direct_sum_eq_completed K c θ C L H hS d w
    ⟨X⁻¹, inv_pos.mpr hX⟩

end ThetaGlobal.GlobalSkeletonDirect
