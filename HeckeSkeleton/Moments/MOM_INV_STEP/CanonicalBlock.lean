import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientCycle
import HeckeSkeleton.Moments.MOM_INV_STEP.MarkPriority
import Mathlib.Tactic.LinearCombination

/-!
# Actual marked canonical cube blocks

The coefficient is the literal calibrated a₀ coefficient, an actual
Hecke ideal coefficient, one fixed puncture, the fourth-power label row,
the original ideal-divisibility marks on n b³, and the original norm
cutoff. The additional weight depends only on the frozen cube and label.

Both identities below start from the squared orbital series of this
specified coefficient. They apply genuine primitive-modulus Poisson to
each pair, retaining the external, cube, label and principal zero masks.
No row identity or energy bound is an input to either theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalBlock

open NumberField IsDedekindDomain UniqueFactorizationMonoid
  HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- Input coefficient data of one fixed class. In particular, the extra
weight cannot depend on the moving squarefree column n. -/
structure ColumnData (σ : Type*) where
  lambda : HeckeCharacter K
  background : HeckeCharacter K
  puncture : Ideal (𝓞 K)
  slots : Finset σ
  primeLists : σ → Finset (Ideal (𝓞 K))
  primeWeights : σ → Ideal (𝓞 K) → ℂ
  labelWeight : Ext → Ext → ℂ
  cutoff : ℝ → ℂ
  base : ℝ
  length : ℝ

variable {σ : Type*}

def canonicalColumn (C : ColumnData K S σ) (f b n : Ext) : ℂ :=
  C.labelWeight b f * CoefficientCycle.canonicalCoefficient K Sset D C.lambda n *
    heckeIdealCoefficient K C.background n.val *
    (if IsCoprime n.val.val C.puncture then 1 else 0) *
    idealSymbol K Sset D n (D.generator f) ^ 4 *
    HeckeSkeleton.Moments.MOMInvStep.divisorMark C.slots C.primeLists C.primeWeights
      (n.val.val * b.val.val ^ 3) *
    C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)

/-- The actual inverse coefficient uses the ideal Moebius function; it
is not chosen as an inverse transform of `canonicalColumn`. -/
def inverseColumn (C : ColumnData K S σ) (f b n : Ext) : ℂ :=
  C.labelWeight b f * (moebius n.val.val : ℂ) *
    heckeIdealCoefficient K C.background n.val *
    (if IsCoprime n.val.val C.puncture then 1 else 0) *
    idealSymbol K Sset D n (D.generator f) ^ 4 *
    HeckeSkeleton.Moments.MOMInvStep.divisorMark C.slots C.primeLists C.primeWeights
      (n.val.val * b.val.val ^ 3) *
    C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length)

theorem generator_contraction (f : Ext) :
    sIntegerModulusContraction K Sset (D.generator f) = f.val.val := by
  unfold sIntegerModulusContraction
  rw [D.generator_span]
  exact under_map_coprime_sIntegerIdeal K Sset f.val.val
    (sexticIdeal_coprime_S K Sset f.val.val f.property)

/-- The literal ideal row still carries its coprimality zero. -/
theorem idealSymbol_sixth_mask (I : Ext) (a : OS) :
    idealSymbol K Sset D I a ^ 6 =
      if IsCoprime I.val.val (sIntegerModulusContraction K Sset a) then 1 else 0 := by
  rw [← CanonicalPoissonSource.idealSymbol_pow]
  exact sIntegerSexticIdealEvaluation_sixth_power_coprime_mask
    K Sset D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem idealSymbol_eq_zero_of_not_coprime (I : Ext) (a : OS)
    (hbad : ¬ IsCoprime I.val.val (sIntegerModulusContraction K Sset a)) :
    idealSymbol K Sset D I a = 0 := by
  have h := idealSymbol_sixth_mask K S D I a
  rw [if_neg hbad] at h
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp h

theorem cube_factor_mask (b : Ext) (a : OS) :
    idealSymbol K Sset D b a ^ 3 =
      (if IsCoprime b.val.val (sIntegerModulusContraction K Sset a) then 1 else 0) *
        idealSymbol K Sset D b a ^ 3 := by
  by_cases hc : IsCoprime b.val.val (sIntegerModulusContraction K Sset a)
  · simp only [if_pos hc, one_mul]
  · rw [idealSymbol_eq_zero_of_not_coprime K S D b a hc]
    norm_num

theorem label_factor_mask (n f : Ext) :
    idealSymbol K Sset D n (D.generator f) ^ 4 =
      (if IsCoprime n.val.val f.val.val then 1 else 0) *
        idealSymbol K Sset D n (D.generator f) ^ 4 := by
  by_cases hc : IsCoprime n.val.val f.val.val
  · simp only [if_pos hc, one_mul]
  · have hz := idealSymbol_eq_zero_of_not_coprime K S D n (D.generator f)
      (by simpa only [generator_contraction] using hc)
    rw [hz]
    norm_num

theorem canonicalColumn_puncture_zero (C : ColumnData K S σ) (f b n : Ext)
    (hn : ¬ IsCoprime n.val.val C.puncture) :
    canonicalColumn K S D C f b n = 0 := by
  simp [canonicalColumn, hn]

theorem inverseColumn_puncture_zero (C : ColumnData K S σ) (f b n : Ext)
    (hn : ¬ IsCoprime n.val.val C.puncture) :
    inverseColumn K S D C f b n = 0 := by
  simp [inverseColumn, hn]

/-- Calibration acts on the genuine decorated coefficient while its
common puncture, label, original marks, and cutoff remain in place. -/
theorem canonicalColumn_first_cycle (C : ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (f b n : Ext) (hn : Squarefree n.val.val) :
    canonicalColumn K S D C f b n * thetaGamma K Sset D n 1 =
      inverseColumn K S D C f b n * heckeIdealCoefficient K G n.val := by
  unfold canonicalColumn inverseColumn
  have h := CoefficientCycle.first_cycle hcal n hn
  linear_combination
    C.labelWeight b f * heckeIdealCoefficient K C.background n.val *
      (if IsCoprime n.val.val C.puncture then 1 else 0) *
      idealSymbol K Sset D n (D.generator f) ^ 4 *
      HeckeSkeleton.Moments.MOMInvStep.divisorMark C.slots C.primeLists C.primeWeights
        (n.val.val * b.val.val ^ 3) *
      C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length) * h

theorem inverseColumn_second_cycle (C : ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (f b n : Ext) (hn : Squarefree n.val.val) :
    inverseColumn K S D C f b n * conj (thetaGamma K Sset D n 1) =
      canonicalColumn K S D C f b n * conj (heckeIdealCoefficient K G n.val) := by
  unfold canonicalColumn inverseColumn
  have h := CoefficientCycle.second_cycle hcal n hn
  linear_combination
    C.labelWeight b f * heckeIdealCoefficient K C.background n.val *
      (if IsCoprime n.val.val C.puncture then 1 else 0) *
      idealSymbol K Sset D n (D.generator f) ^ 4 *
      HeckeSkeleton.Moments.MOMInvStep.divisorMark C.slots C.primeLists C.primeWeights
        (n.val.val * b.val.val ^ 3) *
      C.cutoff ((n.val.val.absNorm : ℝ) / C.base ^ C.length) * h

variable (Γ : Subgroup (((S : Set (HeightOneSpectrum (𝓞 K)))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 : ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K →* ((S : Set (HeightOneSpectrum (𝓞 K)))).unit K).range)

def primitivePairBlock (x y : Ext × Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {R : ℝ // 0 < R}) :
    ActualMaskedPoissonBlock K S Γ :=
  PrimitivePoissonSource.block K S D Γ hΓ
    (PrimitivePoissonSource.pairSupport K S D x.2 y.2 x.1 y.1)
    (PrimitivePoissonSource.pairExponent K S x.2 y.2 x.1 y.1)
    φ h hlc hcs M R

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K Sset)] [Γ.FiniteIndex]
  [IsPrincipalIdealRing OS]

/-- The actual squared forward row over a finite cube-by-column support. -/
def canonicalCubeEnergy (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (R : {R : ℝ // 0 < R}) : ℂ :=
  CanonicalPoissonSource.squaredRowOrbitalSeries K S D Γ (B ×ˢ N)
    Prod.snd Prod.fst (fun x => canonicalColumn K S D C f x.1 x.2) φ h M R

/-- The actual squared inverse row with the independently defined Moebius
coefficient and the same class-wide puncture. -/
def inverseCubeEnergy (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum OS)) (R : {R : ℝ // 0 < R}) : ℂ :=
  CanonicalPoissonSource.inverseSquaredRowOrbitalSeries K S D Γ (B ×ˢ N)
    Prod.snd Prod.fst (fun x => inverseColumn K S D C f x.1 x.2) φ h M R

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem canonicalCubeEnergy_primitive_poisson (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {R : ℝ // 0 < R}) :
    canonicalCubeEnergy K S D Γ C f B N φ h M R =
      ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N),
        canonicalColumn K S D C f p.1.1 p.1.2 *
          conj (canonicalColumn K S D C f p.2.1 p.2.2) *
          (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R).transformed
            μv D.different_outside := by
  exact PrimitivePoissonSource.squaredRowOrbitalSeries_primitive_poisson
    K S D Γ hΓ μv ν μ (B ×ˢ N) Prod.snd Prod.fst
    (fun x => canonicalColumn K S D C f x.1 x.2)
    (fun x hx => hN x.2 (Finset.mem_product.mp hx).2) φ h hlc hcs M R

include ν μ in
theorem inverseCubeEnergy_primitive_poisson (C : ColumnData K S σ) (f : Ext)
    (B N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (R : {R : ℝ // 0 < R}) :
    inverseCubeEnergy K S D Γ C f B N φ h M R =
      ∑ p ∈ (B ×ˢ N) ×ˢ (B ×ˢ N),
        conj (inverseColumn K S D C f p.1.1 p.1.2) *
          inverseColumn K S D C f p.2.1 p.2.2 *
          (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M R).transformed
            μv D.different_outside := by
  exact PrimitivePoissonSource.inverseSquaredRowOrbitalSeries_primitive_poisson
    K S D Γ hΓ μv ν μ (B ×ˢ N) Prod.snd Prod.fst
    (fun x => inverseColumn K S D C f x.1 x.2)
    (fun x hx => hN x.2 (Finset.mem_product.mp hx).2) φ h hlc hcs M R

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalBlock

end
