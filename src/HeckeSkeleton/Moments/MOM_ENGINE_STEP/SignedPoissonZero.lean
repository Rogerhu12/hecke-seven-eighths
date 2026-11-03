import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstFiniteSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource

/-!
# The two additive origins with their actual signs

A fixed row-ball majorant need not vanish at the additive origin.  Its
Poisson identity therefore retains the original-origin subtraction.
The pure dual-zero term below is defined from the original Fourier
coefficient and the original dual tensor.  No test is replaced and no
zero value is imposed on a row-ball profile.

The whole Gram source will use the sign of the original-origin term
before taking absolute values of its dual-zero and nonzero parts.
-/

noncomputable section
open scoped Classical BigOperators nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]

/-- The literal original-origin contribution, before its subtraction.
Its mask dependence is exactly the original Möbius factor. -/
def ParentPeriodicPair.originZero (p : ParentPeriodicPair K S Γ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
      (p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0)

def FirstFiniteSource.originZeroTerm {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℂ :=
  ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns, ∑ D ∈ s.mask.powerset,
    (s.pairs i j).originZero h D

@[simp] theorem ParentPeriodicPair.originZero_empty (p : ParentPeriodicPair K S Γ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    p.originZero h ∅ =
      ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
        (p.residue 0 * sIntegerTensorTerm K S (traceSchwartzToMixed K p.profile) h 0) := by
  simp only [originZero, IdealMobiusMask.primeProduct, Finset.prod_empty,
    moebius_one, Int.cast_one, one_mul]

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The original dual-frequency zero.  This definition contains no
subtraction of the original additive origin and assumes no annularity. -/
def ParentPeriodicPair.dualZero (p : ParentPeriodicPair K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
    (sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero r
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D) *
      (sIntegerPeriodicDivisorFourier K (S : Set (HeightOneSpectrum (𝓞 K)))
        hDiff p.modulus p.modulus_ne_zero p.residue
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val 0 *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K p.profile) h 0))

theorem ParentPeriodicPair.gated_dualZero (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    (p.gated P).dualZero μv hDiff h r D =
      if P then p.dualZero μv hDiff h r D else 0 := by
  by_cases hP : P
  · rw [p.gated_of_true P hP, if_pos hP]
  · unfold dualZero
    simp only [ParentPeriodicPair.gated, if_neg hP, sIntegerPeriodicDivisorFourier,
      PeriodicFourier.divisorTransform, PeriodicFourier.fourier, PeriodicFourier.dilate,
      zero_mul, Finset.sum_const_zero, mul_zero]

theorem ParentPeriodicPair.gated_originZero (p : ParentPeriodicPair K S Γ)
    (P : Prop) [Decidable P]
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    (p.gated P).originZero h D = if P then p.originZero h D else 0 := by
  by_cases hP : P
  · rw [p.gated_of_true P hP, if_pos hP]
  · simp only [originZero, ParentPeriodicPair.gated, if_neg hP, zero_mul, mul_zero]

/-- The original Poisson correction is retained exactly, with its sign. -/
theorem ParentPeriodicPair.transformedZero_eq_dual_sub_origin
    (p : ParentPeriodicPair K S Γ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    p.transformedZero μv hDiff h r D = p.dualZero μv hDiff h r D - p.originZero h D := by
  unfold transformedZero dualZero originZero
  ring

def FirstFiniteSource.dualZeroTerm {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) : ℂ :=
  ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns, ∑ D ∈ s.mask.powerset,
    (s.pairs i j).dualZero μv hDiff h s.radius D

theorem FirstFiniteSource.zeroTerm_eq_dual_sub_origin {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    s.zeroTerm μv hDiff h = s.dualZeroTerm μv hDiff h - s.originZeroTerm h := by
  simp only [zeroTerm, dualZeroTerm, originZeroTerm,
    ParentPeriodicPair.transformedZero_eq_dual_sub_origin, Finset.sum_sub_distrib]

/-- The genuine finite transform retains its original-origin sign
before any nonzero row is assigned to an ordinary or exceptional class. -/
theorem FirstFiniteSource.transform_re_le_dual_rows {ι κ : Type*}
    (s : FirstFiniteSource K S Γ ι κ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    (s.transform μv hDiff h).re ≤
      ‖s.dualZeroTerm μv hDiff h‖ - (s.originZeroTerm h).re +
        ∑ D : s.mask.powerset,
          ‖∑ t ∈ s.rows, ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
            (s.pairs i j).transformedRow μv hDiff h s.radius D.val t‖ := by
  rw [s.transform_eq_common_rows μv hDiff h,
    s.zeroTerm_eq_dual_sub_origin μv hDiff h]
  simp only [Complex.add_re, Complex.sub_re]
  apply add_le_add (sub_le_sub_right (Complex.re_le_norm _) _)
  apply (Complex.re_le_norm _).trans
  calc
    _ ≤ ∑ D ∈ s.mask.powerset,
        ‖∑ t ∈ s.rows, ∑ i ∈ s.leftColumns, ∑ j ∈ s.rightColumns,
          (s.pairs i j).transformedRow μv hDiff h s.radius D t‖ := norm_sum_le _ _
    _ = _ := (Finset.sum_coe_sort _ _).symm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.transformedZero_eq_dual_sub_origin
#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.zeroTerm_eq_dual_sub_origin
#print axioms HeckeSkeleton.Moments.EngineStep.FirstFiniteSource.transform_re_le_dual_rows
