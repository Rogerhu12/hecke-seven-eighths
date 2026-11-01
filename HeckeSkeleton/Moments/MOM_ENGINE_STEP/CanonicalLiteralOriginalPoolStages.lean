import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSectorStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstRowGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PreparedOriginalFibreRows

/-!
# The four original pool sources with their computed row endpoints

One actual pool supplies the main source and its valuation-one,
valuation-six and valuation-seven sources. The main insertion pays
its six-prime row shift through the original nominal geometry. Every
error source retains the original row subset. The finite classifiers
use the same complete original columns.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable {C : A.GeneralArithmeticContext σ η hS}


namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z step eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad Z (step / 3) eps}
variable {ι : Type*} (d : FirstGaussPoolData C pool ι) (c : ι → ℂ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (a : RealParameters) (I : OriginalNominalIdeals K)
variable (supportError : ℝ) (herr : 0 ≤ supportError) (hstep : 0 < step)
variable (hrows : ∀ h ∈ d.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ I.canonicalRetainedScale a Z supportError)

local notation "mainGeometry" => OriginalNominalGeometry.canonicalMain
  (a := a) (step := step) I supportError (zero_lt_one.trans pool.base_gt_one) herr
local notation "poolGeometry" => OriginalNominalGeometry.canonicalPoolError
  (a := a) pool

include hrows hstep in
theorem literalMainRows : ∀ h ∈ d.mainRows,
    A.exteriorNorm (originalFrequencyIdeal h) ≤
      mainGeometry.retainedScale * Z ^ mainGeometry.enlargement := by
  intro h hh
  have hw := d.main_originalFrequencyIdeal_norm_le_sharp
    (I.firstFrequency a Z + supportError) hrows h hh
  have hg : 6 * (step / 3) ≤ mainGeometry.enlargement := by
    simpa only [OriginalNominalGeometry.canonicalMain, OriginalNominalGeometry.forMain,
      OriginalNominalTag.poolLength] using mainGeometry.enlargement_ge_pool hstep.le
  calc
    A.exteriorNorm (originalFrequencyIdeal h) ≤
        Z ^ (I.firstFrequency a Z + supportError + 6 * (step / 3)) := hw
    _ = mainGeometry.retainedScale * Z ^ (6 * (step / 3)) := by
      rw [Real.rpow_add (zero_lt_one.trans pool.base_gt_one)]
      rfl
    _ ≤ mainGeometry.retainedScale * Z ^ mainGeometry.enlargement :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le pool.base_gt_one.le hg)
        mainGeometry.retainedScale_pos.le

include hrows hstep in
theorem literalPoolRows (e : AmplifierValuation) (p : pool.primes) :
    ∀ h ∈ d.errorRows p.val,
      A.exteriorNorm (originalFrequencyIdeal h) ≤
        (poolGeometry e p I supportError herr).retainedScale *
          Z ^ (poolGeometry e p I supportError herr).enlargement := by
  intro h hh
  exact (d.error_originalFrequencyIdeal_norm_le_sharp _ hrows p.val h hh).trans
    ((poolGeometry e p I supportError herr).retainedScale_le_enlarged
      pool.base_gt_one.le hstep.le)

variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)

/-- The valuation remains the original one, six or seven source. -/
def literalValuationStage (e : AmplifierValuation) (p : pool.primes) :
    ActualGaussStage (E := ℝ) hΓ μv hDiff
      (d.residualSource p.val e.multiplicity c) (rowBallFiniteFamily K A.Sf 1) :=
  ActualGaussStage.literalSectorStage
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.residualSource p.val e.multiplicity c)
    (poolGeometry e p I supportError herr).retainedScale Z
    (poolGeometry e p I supportError herr).enlargement
    (poolGeometry e p I supportError herr).retainedScale_pos
    (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalPoolRows a I supportError herr hstep hrows e p)

/-- These are the actual four sources of the original one-pool identity. -/
def literalCanonicalStages : ActualPoolStages (E := ℝ) hΓ μv hDiff d c
    (rowBallFiniteFamily K A.Sf 1) where
  main := ActualGaussStage.literalSectorStage
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.mainSource c) mainGeometry.retainedScale Z mainGeometry.enlargement
    mainGeometry.retainedScale_pos (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalMainRows a I supportError herr hstep hrows)
  one p := d.literalValuationStage (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    c P a I supportError herr hstep hrows δ hδ hδhalf cutoff hcutoff .one p
  six p := d.literalValuationStage (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    c P a I supportError herr hstep hrows δ hδ hδhalf cutoff hcutoff .six p
  seven p := d.literalValuationStage (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    c P a I supportError herr hstep hrows δ hδ hδhalf cutoff hcutoff .seven p

local notation "stages" => d.literalCanonicalStages (hΓ := hΓ) (μv := μv)
  (hDiff := hDiff) (ν := ν) c P a I supportError herr hstep hrows δ hδ hδhalf cutoff hcutoff

/-- No activity assumption is used to count the original finite row code. -/
def literalCanonicalStagesOriginalFibreRows (B : ℝ) (hB : 0 ≤ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B) :
    stages.OriginalFibreRows
      (PUnit.{1} × SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) 0 0 B Z where
  main := ActualGaussStage.literalSectorStageOriginalFibreRows
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.mainSource c) mainGeometry.retainedScale Z mainGeometry.enlargement
    mainGeometry.retainedScale_pos (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalMainRows a I supportError herr hstep hrows) B hB pool.base_gt_one.le hN
  one p := ActualGaussStage.literalSectorStageOriginalFibreRows
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.residualSource p.val 1 c)
    (poolGeometry .one p I supportError herr).retainedScale Z
    (poolGeometry .one p I supportError herr).enlargement
    (poolGeometry .one p I supportError herr).retainedScale_pos
    (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalPoolRows a I supportError herr hstep hrows .one p)
    B hB pool.base_gt_one.le
    (fun i _ => (d.residualSource_ideal_norm_le p.val 1 c i).trans
      (hN i.val (Finset.mem_filter.mp i.property).1))
  six p := ActualGaussStage.literalSectorStageOriginalFibreRows
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.residualSource p.val 6 c)
    (poolGeometry .six p I supportError herr).retainedScale Z
    (poolGeometry .six p I supportError herr).enlargement
    (poolGeometry .six p I supportError herr).retainedScale_pos
    (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalPoolRows a I supportError herr hstep hrows .six p)
    B hB pool.base_gt_one.le
    (fun i _ => (d.residualSource_ideal_norm_le p.val 6 c i).trans
      (hN i.val (Finset.mem_filter.mp i.property).1))
  seven p := ActualGaussStage.literalSectorStageOriginalFibreRows
    (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    P δ hδ hδhalf (d.residualSource p.val 7 c)
    (poolGeometry .seven p I supportError herr).retainedScale Z
    (poolGeometry .seven p I supportError herr).enlargement
    (poolGeometry .seven p I supportError herr).retainedScale_pos
    (zero_lt_one.trans pool.base_gt_one) cutoff hcutoff
    (d.literalPoolRows a I supportError herr hstep hrows .seven p)
    B hB pool.base_gt_one.le
    (fun i _ => (d.residualSource_ideal_norm_le p.val 7 c i).trans
      (hN i.val (Finset.mem_filter.mp i.property).1))

end FirstGaussPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalMainRows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalPoolRows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalCanonicalStages
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalCanonicalStagesOriginalFibreRows

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.literalValuationStage
