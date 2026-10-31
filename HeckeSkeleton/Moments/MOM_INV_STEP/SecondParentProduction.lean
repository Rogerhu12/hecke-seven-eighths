import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCommonEnvelope

/-!
# Whole retained second source and its genuine positive child energies

Every fresh common ideal, actual mask divisor and original sector is
summed here. The signed scalar remains intact until the positive
energies have been formed. The common Fourier envelope is derived from
the actual Haar profile. No source equality or energy estimate is a
premise of the production theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentProduction

open NumberField IsDedekindDomain MeasureTheory UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CanonicalFirstEnergy
  CommonKernel SecondSourceColumns SecondParentRetained ActualDivisorSectors
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

structure Data (σ : Type*) (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K) where
  columns : ColumnFamily K Sset σ Θ ψ
  triple : OuterTriple K
  label : Ext
  divisor : NonzeroRingElements OS
  archTest : SchwartzMap V ℂ
  localTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ
  locallyConstant : ∀ v ∈ S, IsLocallyConstant (localTest v)
  compactSupport : ∀ v ∈ S, HasCompactSupport (localTest v)
  radius : {r : ℝ // 0 < r}
  frequencyBound : ℝ
  base_gt_one : 1 < columns.base
  cutoffSupport : tsupport (columns.cutoff triple) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8)
  fullPool : columns.columns triple =
    squarefreePool K Sset (2 * columns.base ^ columns.columnLength triple)

variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def scale (T : Data K S σ Θ ψ) : ℝ := T.columns.base ^ T.columns.columnLength T.triple

theorem scale_pos (T : Data K S σ Θ ψ) : 0 < scale K S T :=
  Real.rpow_pos_of_pos (zero_lt_one.trans T.base_gt_one) _

def test (T : Data K S σ Θ ψ) : SchwartzMap ℝ ℂ :=
  FinalMellinTests.powerTest (T.columns.cutoff T.triple) (-1 / 2)

theorem test_support (T : Data K S σ Θ ψ) :
    tsupport (test K S T) ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8) :=
  (FinalMellinTests.powerTest_support _ _).trans T.cutoffSupport

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

abbrev Index (T : Data K S σ Θ ψ) :=
  Σ g : squarefreePool K Sset (2 * scale K S T),
    Σ δ : (SecondSourceMasks.commonMask K S D g.val).powerset,
      FirstDualTruncation.sectorCutoff K S D Γ T.frequencyBound

def selectedDivisor (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    NonzeroRingElements OS := sIntegerMaskGenerator K Sset i.2.1.val

def selectedRow (T : Data K S σ Θ ψ) (i : Index K S D Γ T) : Ext :=
  newRowIdeal K S i.2.2.val.1 T.divisor (selectedDivisor K S D Γ T i)

def selectedSector (T : Data K S σ Θ ψ) (i : Index K S D Γ T) : Sector :=
  newSector K S Γ D T.divisor (selectedDivisor K S D Γ T i) i.2.2.val.2

def weight (T : Data K S σ Θ ψ) (i : Index K S D Γ T) : ℝ :=
  ‖(moebius (IdealMobiusMask.primeProduct i.2.1.val) : ℂ)‖ *
    ‖sourceScalar K S T.columns T.triple (scale_pos K S T) T.radius
      i.2.1.val i.1.val T.label T.divisor‖

theorem weight_nonneg (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    0 ≤ weight K S D Γ T i := mul_nonneg (norm_nonneg _) (norm_nonneg _)

def radialScale (T : Data K S σ Θ ψ) (i : Index K S D Γ T) : ℝ :=
  SecondCommonEnvelope.radialScale K S T.radius (selectedDivisor K S D Γ T i)
    (residualScale K S T.columns T.triple (scale_pos K S T) i.1.val)
    (residualScale K S T.columns T.triple (scale_pos K S T) i.1.val)

theorem radialScale_pos (T : Data K S σ Θ ψ) (i : Index K S D Γ T) :
    0 < radialScale K S D Γ T i :=
  SecondCommonEnvelope.radialScale_pos K S _ _ _ _

def coordinate (side : Bool) : LogPlane →L[ℝ] ℝ :=
  if side then (ContinuousLinearMap.snd ℝ ℝ ℝ).comp logCoordinates.toContinuousLinearMap
  else -((ContinuousLinearMap.fst ℝ ℝ ℝ).comp logCoordinates.toContinuousLinearMap)

@[simp] theorem coordinate_false (ξ : LogPlane) : coordinate false ξ = -ξ.fst := rfl
@[simp] theorem coordinate_true (ξ : LogPlane) : coordinate true ξ = ξ.snd := rfl

def centeredEnergy (T : Data K S σ Θ ψ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) (i : Index K S D Γ T) : ℝ :=
  radialScale K S D Γ T i ^ ε *
    SecondPositiveChildren.centeredEnergy K S D Γ T.columns T.triple G hG
      i.1.val T.label (divisorIdeal K S (selectedDivisor K S D Γ T i))
      (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
      (test K S T) (test_support K S T) (scale K S T)
      (FirstCommonEnvelope.frequencyEnvelope m) (coordinate side)

theorem centeredEnergy_nonneg (T : Data K S σ Θ ψ) (G : HeckeCharacter K)
    (hG : G ∈ Θ) (ε : ℝ) (m : ℕ) (side : Bool) (i : Index K S D Γ T) :
    0 ≤ centeredEnergy K S D Γ T G hG ε m side i := by
  apply mul_nonneg (Real.rpow_nonneg (radialScale_pos K S D Γ T i).le ε)
  apply Finset.sum_nonneg
  intro b hb
  apply Finset.sum_nonneg
  intro v hv
  apply mul_nonneg (norm_nonneg _)
  apply integral_nonneg
  intro τ
  exact mul_nonneg (FirstCommonEnvelope.frequencyEnvelope_nonneg m τ)
    (SecondPositiveChildren.branchEnergy_nonneg K S D Γ T.columns T.triple G hG
      i.1.val T.label (divisorIdeal K S (selectedDivisor K S D Γ T i))
      (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
      (test K S T) (test_support K S T) (scale K S T) b v (coordinate side τ))

def total (T : Data K S σ Θ ψ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (ε : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  ∑ i : Index K S D Γ T, weight K S D Γ T i * centeredEnergy K S D Γ T G hG ε m side i

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def selectedProfile (T : Data K S σ Θ ψ) (i : Index K S D Γ T) : Profile K S :=
  sourceProfile K S μv ν T.columns T.triple (scale_pos K S T)
    T.archTest T.localTest T.locallyConstant T.compactSupport T.radius
    i.2.1.val i.2.2.val.1 i.1.val

def term (T : Data K S σ Θ ψ) (G : HeckeCharacter K) (i : Index K S D Γ T) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct i.2.1.val) : ℂ) *
    sourceScalar K S T.columns T.triple (scale_pos K S T) T.radius
      i.2.1.val i.1.val T.label T.divisor *
    SecondPhysicalEnergy.source K S D Γ T.columns T.triple G i.1.val T.label
      (divisorIdeal K S (selectedDivisor K S D Γ T i))
      (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
      (test K S T) (scale K S T) (selectedProfile K S D Γ μv ν T i)

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem retained_eq_sum (T : Data K S σ Θ ψ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
      UnramifiedAt K (T.columns.background T.triple) p) :
    SecondPoissonSplit.retainedSource K S D Γ hΓ μv
      (DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val)
      (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
      T.archTest T.localTest T.locallyConstant T.compactSupport T.radius T.frequencyBound =
      ∑ i : Index K S D Γ T, term K S D Γ μv ν T G i := by
  rw [T.fullPool]
  rw [retainedSource_eq_fixed_common K S D Γ hΓ μv ν hallowed T.columns T.triple G hcal hbg
    (scale_pos K S T) T.cutoffSupport T.label T.divisor (2 * scale K S T)
    (by positivity) T.archTest T.localTest T.locallyConstant T.compactSupport T.radius
    T.frequencyBound]
  simp only [Index, Fintype.sum_sigma, term, selectedDivisor, selectedRow, selectedSector,
    selectedProfile, SecondPhysicalEnergy.source, SecondPhysicalEnergy.sourcePool,
    SecondPhysicalEnergy.sourceCoefficient, forwardColumn, poweredFamily,
    SecondSourceAssembly.slicedColumn, test, scale, Finset.sum_coe_sort]

include hallowed in
theorem term_bound (T : Data K S σ Θ ψ) (G : HeckeCharacter K) (hG : G ∈ Θ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hprime : ∀ i ∈ T.columns.survivors T.triple,
      ∀ p ∈ T.columns.primeLists i, Prime p)
    (ε : ℝ) (m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ i : Index K S D Γ T, ∀ ξ : LogPlane,
      ‖SecondPhysicalEnergy.density K S Γ (selectedProfile K S D Γ μv ν T i) ξ‖ ≤
        (M * radialScale K S D Γ T i ^ ε) * FirstCommonEnvelope.frequencyEnvelope m ξ)
    (i : Index K S D Γ T) :
    ‖term K S D Γ μv ν T G i‖ ≤
      M * (weight K S D Γ T i *
        (Real.sqrt (centeredEnergy K S D Γ T G hG ε m false i) *
          Real.sqrt (centeredEnergy K S D Γ T G hG ε m true i))) := by
  have hg := squarefreePool_squarefree K Sset i.1.property
  have hd := SecondSourceMasks.actual_divisor_dvd K S D i.1.val hg i.2.1.val
    (Finset.mem_powerset.mp i.2.1.property)
  have he (side : Bool) :
      SecondPhysicalEnergy.positiveEnergy K S D Γ T.columns T.triple G i.1.val T.label
        (divisorIdeal K S (selectedDivisor K S D Γ T i))
        (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
        (test K S T) (scale K S T) (selectedProfile K S D Γ μv ν T i) (coordinate side) ≤
      M * centeredEnergy K S D Γ T G hG ε m side i := by
    have h := SecondPositiveChildren.sourceEnergy_le_of_density_bound
      K S D Γ T.columns T.triple G hG i.1.val T.label
      (divisorIdeal K S (selectedDivisor K S D Γ T i))
      (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
      (test K S T) (test_support K S T) (scale K S T) hallowed hcal hg hd
      (scale_pos K S T) T.base_gt_one hprime (selectedProfile K S D Γ μv ν T i)
      (coordinate side) (FirstCommonEnvelope.frequencyEnvelope m)
      (FirstCommonEnvelope.frequencyEnvelope_integrable m)
      (FirstCommonEnvelope.frequencyEnvelope_continuous m)
      (FirstCommonEnvelope.frequencyEnvelope_nonneg m)
      (M * radialScale K S D Γ T i ^ ε)
      (mul_nonneg hM (Real.rpow_nonneg (radialScale_pos K S D Γ T i).le ε)) (hP i)
    exact h.trans_eq (mul_assoc _ _ _)
  have hb := SecondPhysicalEnergy.full_source_energy K S D Γ T.columns T.triple G
    i.1.val T.label (divisorIdeal K S (selectedDivisor K S D Γ T i))
    (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
    (test K S T) (scale K S T) (selectedProfile K S D Γ μv ν T i)
    rfl rfl (test_support K S T)
  have hs : ‖SecondPhysicalEnergy.source K S D Γ T.columns T.triple G i.1.val T.label
        (divisorIdeal K S (selectedDivisor K S D Γ T i))
        (selectedRow K S D Γ T i) (selectedSector K S D Γ T i)
        (test K S T) (scale K S T) (selectedProfile K S D Γ μv ν T i)‖ ≤
      M * (Real.sqrt (centeredEnergy K S D Γ T G hG ε m false i) *
        Real.sqrt (centeredEnergy K S D Γ T G hG ε m true i)) := by
    apply hb.trans
    calc
      _ ≤ Real.sqrt (M * centeredEnergy K S D Γ T G hG ε m false i) *
          Real.sqrt (M * centeredEnergy K S D Γ T G hG ε m true i) :=
        mul_le_mul (Real.sqrt_le_sqrt (he false)) (Real.sqrt_le_sqrt (he true))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul hM, Real.sqrt_mul hM]
        have hMM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
        calc
          _ = (Real.sqrt M * Real.sqrt M) *
            (Real.sqrt (centeredEnergy K S D Γ T G hG ε m false i) *
              Real.sqrt (centeredEnergy K S D Γ T G hG ε m true i)) := by ring
          _ = _ := by rw [hMM]
  rw [term, norm_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_left hs (weight_nonneg K S D Γ T i)).trans_eq (by
    dsimp only [weight]
    ring)

include hΓ hallowed ν in
/-- Uniform production estimate for the entire second retained source.
Constants precede every inverse family, original prime list, source
ideal, physical radius, frequency cutoff and test function. -/
theorem exists_retained_centered_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ₀ : Type*} [DecidableEq σ₀] {Θ₀ : Subgroup (HeckeCharacter K)} {ψ₀ : HeckeCharacter K},
      ∀ (T : Data K S σ₀ Θ₀ ψ₀), T.localTest = h →
      ∀ (G : HeckeCharacter K) (hG : G ∈ Θ₀),
      ThetaCalibrationInput K Sset D T.columns.lambda G →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
        UnramifiedAt K (T.columns.background T.triple) p) →
      (∀ i ∈ T.columns.survivors T.triple, ∀ p ∈ T.columns.primeLists i, Prime p) →
      ‖SecondPoissonSplit.retainedSource K S D Γ hΓ μv
        (DivisorInverseColumn.coefficient K S D T.columns T.triple T.label.val.val T.divisor.val)
        (T.columns.columns T.triple ×ˢ T.columns.columns T.triple)
        T.archTest T.localTest T.locallyConstant T.compactSupport T.radius T.frequencyBound‖ ≤
      (A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest) *
        (Real.sqrt (total K S D Γ T G hG ε m false) *
          Real.sqrt (total K S D Γ T G hG ε m true)) := by
  obtain ⟨s, A, hA, hb⟩ := SecondCommonEnvelope.exists_second_density_common_envelope
    K S D Γ μv ν h hlc hcs ε hε m
  refine ⟨s, A, hA, ?_⟩
  intro σ₀ _ Θ₀ ψ₀ T hlocal G hG hcal hbg hprime
  subst h
  let M := A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest
  have hM : 0 ≤ M := mul_nonneg hA (apply_nonneg _ _)
  have hP (i : Index K S D Γ T) (ξ : LogPlane) :
      ‖SecondPhysicalEnergy.density K S Γ (selectedProfile K S D Γ μv ν T i) ξ‖ ≤
        (M * radialScale K S D Γ T i ^ ε) * FirstCommonEnvelope.frequencyEnvelope m ξ :=
    hb T.archTest T.radius (selectedDivisor K S D Γ T i) i.2.2.val.1
      (residualScale K S T.columns T.triple (scale_pos K S T) i.1.val)
      (residualScale K S T.columns T.triple (scale_pos K S T) i.1.val) ξ
  rw [retained_eq_sum K S D Γ μv ν hΓ hallowed T G hcal hbg]
  calc
    _ ≤ ∑ i : Index K S D Γ T, ‖term K S D Γ μv ν T G i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Index K S D Γ T, M * (weight K S D Γ T i *
        (Real.sqrt (centeredEnergy K S D Γ T G hG ε m false i) *
          Real.sqrt (centeredEnergy K S D Γ T G hG ε m true i))) :=
      Finset.sum_le_sum (fun i _ =>
        term_bound K S D Γ μv ν hallowed T G hG hcal hprime ε m M hM hP i)
    _ = M * ∑ i : Index K S D Γ T, weight K S D Γ T i *
        (Real.sqrt (centeredEnergy K S D Γ T G hG ε m false i) *
          Real.sqrt (centeredEnergy K S D Γ T G hG ε m true i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (FullMobius.common_weighted_cauchy Finset.univ (weight K S D Γ T)
        (centeredEnergy K S D Γ T G hG ε m false)
        (centeredEnergy K S D Γ T G hG ε m true)
        (fun i _ => weight_nonneg K S D Γ T i)
        (fun i _ => centeredEnergy_nonneg K S D Γ T G hG ε m false i)
        (fun i _ => centeredEnergy_nonneg K S D Γ T G hG ε m true i)) hM

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentProduction

end

