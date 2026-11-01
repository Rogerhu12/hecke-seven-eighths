import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPrimitivePooledSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFirstTerminalWindows

/-!
# Original ideal windows for the actual first normalization

The two common ideals, their active radical and the selected physical
mask divisor are bounded by the original full Cartesian columns. These
bounds apply before second-stage rows or coefficients are inspected.
The pool frozen ideal includes its full original valuation power.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {Index : Type*} {data : Index → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

variable (C : A.GeneralArithmeticContext σ η hS)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (W : NormProfileRecipe data) (ξ : Index)
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 1 < Z)
variable (hbudget : Q.FullJointBudget Z (a.m + a.q))
variable (centered : Bool) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)

local notation "internal" => Q.fullSupportParameters a Z
local notation "atoms" => (Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) internal Z t
local notation "raw" => atoms.raw Y₁ Y₂

local notation "source" => Q.literalPrimitiveFirstSource μv ν C hroot hemb W ξ
  a Z t Y₁ Y₂ hZ hbudget centered cutoff hcutoff δ₁ hδ₁ hδ₁half

/-- Every first arithmetic length is derived from a norm window on
the same original columns. The physical mask divisor is not discarded. -/
theorem literalPrimitiveFirstIdealLengths
    (normBound : ℝ)
    (hN : ∀ i ∈ source.columns, (Ideal.absNorm (source.ideal i).val : ℝ) ≤ Z ^ normBound)
    (DE : source.CommonLabel) (D : ((source.block DE).mask source.mask).powerset) :
    idealLogLength Z DE.val.1 ≤ normBound ∧
      idealLogLength Z DE.val.2 ≤ normBound ∧
      idealLogLength Z (firstActiveRadical DE.val.1 DE.val.2) ≤ normBound ∧
      idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D.val).val ≤ normBound := by
  let b := source.block DE
  have hDE := actual_common_pair_properties source.columns source.columns
    (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) DE
  have hnorm := actual_common_pair_norm source.columns source.columns
    (fun i => (source.ideal i).val) (fun i => (source.ideal i).val) (Z ^ normBound)
    (fun i _ => (source.ideal i).property.1) (fun i _ => (source.ideal i).property.1)
    hN hN DE
  have hactiveDvd : firstActiveRadical DE.val.1 DE.val.2 ∣ DE.val.1 := by
    rw [← b.activeIdeal_eq, ← b.common_left]
    exact firstActiveIdeal_dvd_common b.primes b.leftMultiplicity b.rightMultiplicity b.left_positive
  have hactiveNorm : (Ideal.absNorm (firstActiveRadical DE.val.1 DE.val.2) : ℝ) ≤
      Z ^ normBound := (norm_le_of_dvd hDE.1 hactiveDvd).trans hnorm.1
  have hsub : D.val ⊆ b.mask ∅ := Finset.mem_powerset.mp D.property
  have hdiv := original_submask_generator_dvd hsub
  have hmask := sIntegerElementNorm_le_of_dvd A.Sf
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).val
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).val
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D.val).property
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (b.mask ∅)).property hdiv
  have hphysicalNorm : A.exteriorNorm (firstPhysicalDivisorIdeal (A := A) D.val) ≤
      Z ^ normBound := by
    rw [firstPhysicalDivisorIdeal_norm]
    exact hmask.trans ((b.principal_mask_norm_le_common C).trans hnorm.1)
  have hlog (I : Ideal (𝓞 K)) (hI : I ≠ 0)
      (hIbound : (Ideal.absNorm I : ℝ) ≤ Z ^ normBound) :
      idealLogLength Z I ≤ normBound := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [rpow_idealLogLength Z hZ I hI]
    exact hIbound
  exact ⟨hlog _ hDE.1 hnorm.1, hlog _ hDE.2.1 hnorm.2,
    hlog _ (firstActiveRadical_ne_zero _ _) hactiveNorm,
    hlog _ (firstPhysicalDivisorIdeal (A := A) D.val).property.1 hphysicalNorm⟩

end CompleteMovingRowRecipe

namespace PowerScaleExteriorPool

variable {A : SArithmeticData K} {bad : Finset (HeightOneSpectrum (𝓞 K))}
variable {Z ell eps : ℝ} (pool : PowerScaleExteriorPool A bad Z ell eps)

/-- The original frozen ideal includes all of the actual prime
valuation. Its fixed box pays at most seven original pool lengths. -/
theorem original_frozen_length_le
    (D : Ideal (𝓞 K)) (hD : D ≠ 0) (bound : ℝ)
    (hDN : (Ideal.absNorm D : ℝ) ≤ Z ^ bound)
    (valuation : AmplifierValuation) (p : pool.primes) :
    idealLogLength Z (D * p.val.val.asIdeal ^ valuation.multiplicity) ≤ bound + 7 * ell := by
  have hz : 0 < Z := zero_lt_one.trans pool.base_gt_one
  have hp := pool.norm_upper p.val p.property
  have hdegree : (valuation.multiplicity : ℝ) ≤ 7 := by
    cases valuation <;> norm_num [AmplifierValuation.multiplicity]
  have hnorm : (Ideal.absNorm (D * p.val.val.asIdeal ^ valuation.multiplicity) : ℝ) ≤
      Z ^ (bound + 7 * ell) := by
    rw [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    calc
      _ ≤ Z ^ bound * (Z ^ ell) ^ valuation.multiplicity :=
        mul_le_mul hDN (pow_le_pow_left₀ (Nat.cast_nonneg _) hp _)
          (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hz.le _)
      _ = Z ^ (bound + ell * valuation.multiplicity) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le pool.base_gt_one.le
        (by nlinarith [mul_le_mul_of_nonneg_left hdegree pool.exponent_pos.le])
  apply (Real.rpow_le_rpow_left_iff pool.base_gt_one).mp
  rw [rpow_idealLogLength Z pool.base_gt_one _
    (mul_ne_zero hD (pow_ne_zero _ p.val.val.ne_bot))]
  exact hnorm

end PowerScaleExteriorPool
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalPrimitiveFirstIdealLengths
#print axioms HeckeSkeleton.Moments.EngineStep.PowerScaleExteriorPool.original_frozen_length_le
