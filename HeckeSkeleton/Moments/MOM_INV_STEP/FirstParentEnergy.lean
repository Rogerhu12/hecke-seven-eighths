import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormPoolEnergy

/-!
# Two positive energies for the entire literal retained first parent

The source is the full original squarefree dyadic pool. The common
positive outer measure includes the actual mask-divisor coefficient,
the physical prefactor, and only the old cube-label weights. The source
factorization and both applications of finite Cauchy are proved.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open FirstSourceColumns FirstSourceFrozen CanonicalFirstEnergy FirstNormPoolEnergy
  FirstPoissonNormalization FirstSourcePartition FirstDualTruncation
  CanonicalNormPools
open HeckeSkeleton.Moments.MOMInvStep.FullMobius
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ : Type*}

structure Data where
  columns : CanonicalBlock.ColumnData K S σ
  label : Ext
  cubes : Finset Ext
  scale : {r : ℝ // 0 < r}
  archTest : SchwartzMap V ℂ
  localTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ
  locallyConstant : ∀ v ∈ S, IsLocallyConstant (localTest v)
  compactSupport : ∀ v ∈ S, HasCompactSupport (localTest v)
  mask : Finset (HeightOneSpectrum OS)
  radius : {r : ℝ // 0 < r}
  frequencyBound : ℝ

def columnPool (T : Data K S (σ := σ)) : Finset Ext := dyadicPool K Sset T.scale.val

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- Every old cube pair, actual extraction key, mask divisor and original sector. -/
abbrev Index (T : Data K S (σ := σ)) :=
  Σ b₁ : T.cubes, Σ b₂ : T.cubes,
    Σ κ : keys K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val,
      Σ δ : (FirstParentRetained.actualMask K S D T.mask
        (anchor K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val κ).1
        (anchor K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val κ).2
        b₁.val b₂.val).powerset, sectorCutoff K S D Γ T.frequencyBound

def selectedAnchor (T : Data K S (σ := σ)) (i : Index K S D Γ T) : Ext × Ext :=
  anchor K S (columnPool K S T) (columnPool K S T) i.1.val i.2.1.val i.2.2.1

def selectedDivisor (T : Data K S (σ := σ)) (i : Index K S D Γ T) :
    NonzeroRingElements OS := sIntegerMaskGenerator K Sset i.2.2.2.1.val

theorem selectedAnchor_squarefree (T : Data K S (σ := σ)) (i : Index K S D Γ T) :
    Squarefree (selectedAnchor K S D Γ T i).1.val.val ∧
      Squarefree (selectedAnchor K S D Γ T i).2.val.val := by
  obtain ⟨h₁,h₂⟩ := anchor_mem K S (columnPool K S T) (columnPool K S T)
    i.1.val i.2.1.val i.2.2.1
  exact ⟨dyadicPool_squarefree K Sset h₁, dyadicPool_squarefree K Sset h₂⟩

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def selectedProfile (T : Data K S (σ := σ)) (i : Index K S D Γ T) : Profile K S :=
  FirstParentRetained.profile K S D μv ν T.archTest T.localTest T.locallyConstant
    T.compactSupport T.radius (selectedDivisor K S D Γ T i)
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
    i.1.val i.2.1.val i.2.2.2.2.val.1
    (residualScale K S T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false)
    (residualScale K S T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val true)

def sourceTerm (T : Data K S (σ := σ)) (i : Index K S D Γ T) : ℂ :=
  (moebius (IdealMobiusMask.primeProduct i.2.2.2.1.val) : ℂ) *
    (outerFactor K S D T.radius (selectedDivisor K S D Γ T i)
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val : ℂ) *
    originalSource K S D Γ T.columns (columnPool K S T) (columnPool K S T)
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val (CanonicalIdealRow.ofExterior K S T.label)
      (CanonicalIdealRow.ofExterior K S T.label)
      (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 (selectedProfile K S D Γ μv ν T i)

def outerWeight (T : Data K S (σ := σ)) (i : Index K S D Γ T) : ℝ :=
  ‖(moebius (IdealMobiusMask.primeProduct i.2.2.2.1.val) : ℂ)‖ *
    outerFactor K S D T.radius (selectedDivisor K S D Γ T i)
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val *
    (‖T.columns.labelWeight i.1.val T.label‖ * ‖T.columns.labelWeight i.2.1.val T.label‖)

def leftEnergy (G : HeckeCharacter K) (T : Data K S (σ := σ)) (i : Index K S D Γ T) : ℝ :=
  positiveEnergy K S Γ (selectedProfile K S D Γ μv ν T i)
    (leftDomain K S (columnPool K S T) (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val)
    (leftDomain K S (columnPool K S T) (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val)
    (selectedProfile K S D Γ μv ν T i).leftScale (fun η : CommonKernel.LogPlane => η.fst)
    (movingColumn K S D Γ T.columns G (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false
      (CanonicalIdealRow.ofExterior K S T.label) (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2)

def rightEnergy (G : HeckeCharacter K) (T : Data K S (σ := σ)) (i : Index K S D Γ T) : ℝ :=
  positiveEnergy K S Γ (selectedProfile K S D Γ μv ν T i)
    (leftDomain K S (columnPool K S T) (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val)
    (rightDomain K S (columnPool K S T) (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val)
    (selectedProfile K S D Γ μv ν T i).rightScale (fun η : CommonKernel.LogPlane => η.snd)
    (fun u => conj (movingColumn K S D Γ T.columns G (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val true
      (CanonicalIdealRow.ofExterior K S T.label) (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 u))

def totalLeft (G : HeckeCharacter K) (T : Data K S (σ := σ)) : ℝ :=
  ∑ i : Index K S D Γ T, outerWeight K S D Γ T i * leftEnergy K S D Γ μv ν G T i

def totalRight (G : HeckeCharacter K) (T : Data K S (σ := σ)) : ℝ :=
  ∑ i : Index K S D Γ T, outerWeight K S D Γ T i * rightEnergy K S D Γ μv ν G T i

theorem positiveEnergy_nonneg (P : Profile K S)
    (T U : Finset (Finset (HeightOneSpectrum (𝓞 K))))
    (X : {r : ℝ // 0 < r}) (coordinate : CommonKernel.LogPlane → ℝ)
    (a : (Ideal (𝓞 K))⁰ → ℂ) :
    0 ≤ positiveEnergy K S Γ P T U X coordinate a := by
  apply Finset.sum_nonneg
  intro e he
  apply mul_nonneg (norm_nonneg _)
  exact integral_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem outerWeight_nonneg (T : Data K S (σ := σ)) (i : Index K S D Γ T) :
    0 ≤ outerWeight K S D Γ T i := by
  exact mul_nonneg
    (mul_nonneg (norm_nonneg _) (outerFactor_nonneg K S D T.radius
      (selectedDivisor K S D Γ T i) _ _ _ _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem outerScalar_norm_le (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (r₁ r₂ b₁ b₂ f z : Ext) (hr₁ : Squarefree r₁.val.val) (hr₂ : Squarefree r₂.val.val)
    (d : OS) (ξ : CanonicalSectors.UnitClasses K Sset Γ) :
    ‖outerScalar K S D Γ C r₁ r₂ b₁ b₂
      (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S f)
      (CanonicalIdealRow.ofExterior K S z) d ξ‖ ≤
        ‖C.labelWeight b₁ f‖ * ‖C.labelWeight b₂ f‖ := by
  simp only [outerScalar, norm_mul, Complex.norm_conj]
  have h₁ := outerCoefficient_norm_le_one K S D hcal C.background r₁ r₂ b₁ b₂
    hr₁ hr₂ false (CanonicalIdealRow.ofExterior K S f)
  have h₂ := outerCoefficient_norm_le_one K S D hcal C.background r₁ r₂ b₁ b₂
    hr₁ hr₂ true (CanonicalIdealRow.ofExterior K S f)
  have hc := cubeFourierScalar_norm_le_one K S D r₁ r₂ b₁ b₂ d
    (CanonicalSectors.rowElement K Sset Γ D (z,ξ)).val
  calc
    _ ≤ 1 * (‖C.labelWeight b₁ f‖ * 1) * (‖C.labelWeight b₂ f‖ * 1) := by
      gcongr <;> assumption
    _ = _ := by ring

theorem sourceTerm_norm_le (hallowed : AllowedGeneratorInput K Sset D)
    (G : HeckeCharacter K) (T : Data K S (σ := σ))
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G) (i : Index K S D Γ T) :
    ‖sourceTerm K S D Γ μv ν T i‖ ≤
      outerWeight K S D Γ T i *
        (Real.sqrt (leftEnergy K S D Γ μv ν G T i) *
          Real.sqrt (rightEnergy K S D Γ μv ν G T i)) := by
  have hsf := selectedAnchor_squarefree K S D Γ T i
  have he := literal_first_source_energy K S D Γ hallowed T.columns G hcal
    (columnPool K S T) (columnPool K S T)
    (fun n hn => dyadicPool_squarefree K Sset hn)
    (fun n hn => dyadicPool_squarefree K Sset hn)
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val
    (CanonicalIdealRow.ofExterior K S T.label) (CanonicalIdealRow.ofExterior K S T.label)
    (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1) (selectedDivisor K S D Γ T i).val
    i.2.2.2.2.val.2 (selectedProfile K S D Γ μv ν T i)
    (fun U hU => leftDomain_height_window K S D T.scale _ _ _ _ U hU)
    (fun U hU => rightDomain_height_window K S D T.scale _ _ _ _ U hU)
  have ho := outerScalar_norm_le K S D Γ T.columns G hcal
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
    i.1.val i.2.1.val T.label i.2.2.2.2.val.1 hsf.1 hsf.2
    (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2
  have hP := outerFactor_nonneg K S D T.radius (selectedDivisor K S D Γ T i)
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val
  rw [sourceTerm, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hP]
  change _ ≤ _ * (_ * _)
  calc
    _ ≤ (‖(moebius (IdealMobiusMask.primeProduct i.2.2.2.1.val) : ℂ)‖ *
      outerFactor K S D T.radius (selectedDivisor K S D Γ T i)
        (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val) *
      (‖outerScalar K S D Γ T.columns (selectedAnchor K S D Γ T i).1
        (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val
        (CanonicalIdealRow.ofExterior K S T.label) (CanonicalIdealRow.ofExterior K S T.label)
        (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
        (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2‖ *
        (Real.sqrt (leftEnergy K S D Γ μv ν G T i) *
          Real.sqrt (rightEnergy K S D Γ μv ν G T i))) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg _) hP)
    _ ≤ _ := by
      dsimp only [outerWeight]
      have hs : 0 ≤ Real.sqrt (leftEnergy K S D Γ μv ν G T i) *
          Real.sqrt (rightEnergy K S D Γ μv ν G T i) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ho hs)
        (mul_nonneg (norm_nonneg
          (moebius (IdealMobiusMask.primeProduct i.2.2.2.1.val) : ℂ)) hP)
      convert hh using 1 <;> ring

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

theorem canonicalRetained_eq_sum (T : Data K S (σ := σ)) :
    canonicalRetained K S D Γ hΓ μv T.columns T.label T.cubes (columnPool K S T)
      T.archTest T.localTest T.locallyConstant T.compactSupport T.mask T.radius T.frequencyBound =
      ∑ i : Index K S D Γ T, sourceTerm K S D Γ μv ν T i := by
  rw [FirstParentRetained.canonicalRetained_eq_slices K S D Γ hΓ μv ν
    T.columns T.label T.cubes (columnPool K S T) T.archTest T.localTest
    T.locallyConstant T.compactSupport T.mask T.radius T.frequencyBound
    (fun r₁ r₂ b₁ b₂ => residualScale K S T.scale r₁ r₂ b₁ b₂ false)
    (fun r₁ r₂ b₁ b₂ => residualScale K S T.scale r₁ r₂ b₁ b₂ true)]
  simp only [Index, Fintype.sum_sigma, sourceTerm, selectedAnchor, selectedDivisor,
    selectedProfile, FirstParentRetained.sliceValue, Finset.sum_coe_sort]

/-- One whole-parent Cauchy inequality over the same complete positive measure. -/
theorem canonicalRetained_norm_le (hallowed : AllowedGeneratorInput K Sset D)
    (G : HeckeCharacter K) (T : Data K S (σ := σ))
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G) :
    ‖canonicalRetained K S D Γ hΓ μv T.columns T.label T.cubes (columnPool K S T)
      T.archTest T.localTest T.locallyConstant T.compactSupport T.mask T.radius T.frequencyBound‖ ≤
      Real.sqrt (totalLeft K S D Γ μv ν G T) *
        Real.sqrt (totalRight K S D Γ μv ν G T) := by
  rw [canonicalRetained_eq_sum K S D Γ μv ν hΓ T]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i hi => sourceTerm_norm_le K S D Γ μv ν hallowed G T hcal i)).trans
  exact common_weighted_cauchy Finset.univ (outerWeight K S D Γ T)
    (leftEnergy K S D Γ μv ν G T) (rightEnergy K S D Γ μv ν G T)
    (fun i hi => outerWeight_nonneg K S D Γ T i)
    (fun i hi => positiveEnergy_nonneg K S Γ _ _ _ _ _ _)
    (fun i hi => positiveEnergy_nonneg K S Γ _ _ _ _ _ _)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentEnergy

end

