import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNormalizedImageFibres
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentOriginalArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassivePairCard

/-!
# The original physical fibres with their actual passive allocations

The original source classifier still counts the same physical leaves.
Each such leaf now has its own two independent passive allocations.
Their cardinality is proved from the original first common ideal and,
for an error leaf, its actual pool prime. The two estimates use half
of the fibre loss each. No cardinality bound is supplied as input.

All numerical constants below are functions only of the original cap,
fixed classifier dimensions, norm box and requested loss. They precede
the scale, source, profile tables and chosen normalized family.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass ActualNormalizedPairFamily
open CanonicalLiteralPassiveNormalizedFamily CanonicalLiteralPassiveLabelMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

namespace CanonicalLiteralPassiveLabelMass

/-- The mask is read from the original four-way pool tag. At valuation
six it retains the second copy of the pool prime. -/
def poolTagMask {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    {P : PowerScaleExteriorPool A bad Z ell eps} (D : Ideal (𝓞 K)) :
    PoolSourceTag P → HeckeGeneral.Analysis.NonzeroIdeal K
  | .inl _ => firstMask D
  | .inr (.inl p) => poolMask D p.val .one
  | .inr (.inr (.inl p)) => poolMask D p.val .six
  | .inr (.inr (.inr p)) => poolMask D p.val .seven

/-- One constant controls the genuine main tag and all three original
valuation tags. Prime norm bounds come from the original pool. -/
theorem pool_tag_pair_card (cap : ℕ) (B ell ε : ℝ)
    (hB : 0 ≤ B) (hell : 0 ≤ ell) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (A : SArithmeticData K) (bad : Finset (HeightOneSpectrum (𝓞 K)))
        (eps : ℝ) (P : PowerScaleExteriorPool A bad Z ell eps)
        (D : Ideal (𝓞 K)), D ≠ 0 → (Ideal.absNorm D : ℝ) ≤ Z ^ B →
      ∀ (tag : PoolSourceTag P) (k l : ℕ)
        (ld : CanonicalLiteralRectangles.Atoms (K := K) k)
        (rd : CanonicalLiteralRectangles.Atoms (K := K) l)
        (lw : ld.ProfileData) (rw : rd.ProfileData)
        (BL : ActualColumnAllocation K k) (BR : ActualColumnAllocation K l),
        k ≤ cap → l ≤ cap →
        (Fintype.card (PairLabel (A := A) lw rw BL BR
          (poolTagMask D tag) (poolTagMask D tag)) : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨CD, hCD, hd⟩ := direct_pair_card (K := K) cap B ε hB hε
  obtain ⟨CP, hCP, hp⟩ := pool_pair_card (K := K) cap B ell ε hB hell hε
  refine ⟨CD + CP, add_pos hCD hCP, ?_⟩
  intro Z hZ A bad eps P D hD hDN tag k l ld rd lw rw BL BR hk hl
  have hCD' : CD * Z ^ ε ≤ (CD + CP) * Z ^ ε :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCP.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hCP' : CP * Z ^ ε ≤ (CD + CP) * Z ^ ε :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCD.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  rcases tag with u | (p | (p | p))
  · exact (hd Z hZ A D hD hDN k l ld rd lw rw BL BR hk hl).trans hCD'
  · exact (hp Z hZ A D hD hDN p.val (P.norm_upper p.val p.property)
      .one k l ld rd lw rw BL BR hk hl).trans hCP'
  · exact (hp Z hZ A D hD hDN p.val (P.norm_upper p.val p.property)
      .six k l ld rd lw rw BL BR hk hl).trans hCP'
  · exact (hp Z hZ A D hD hDN p.val (P.norm_upper p.val p.property)
      .seven k l ld rd lw rw BL BR hk hl).trans hCP'

end CanonicalLiteralPassiveLabelMass

/-- Chosen before any moving data; the pair count uses one eighth of
the requested loss. The physical count supplies the other eighth. -/
def directPassivePairConstant (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  Classical.choose (direct_pair_card (K := K) cap B (ε / 8) hB (by positivity))

theorem directPassivePairConstant_pos (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < directPassivePairConstant K cap B ε hB hε :=
  (Classical.choose_spec
    (direct_pair_card (K := K) cap B (ε / 8) hB (by positivity))).1

def amplifiedPassivePairConstant (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (B ell ε : ℝ) (hB : 0 ≤ B) (hell : 0 ≤ ell) (hε : 0 < ε) : ℝ :=
  Classical.choose (pool_tag_pair_card (K := K) cap B ell (ε / 8) hB hell (by positivity))

theorem amplifiedPassivePairConstant_pos (K : Type) [Field K] [NumberField K]
    (cap : ℕ) (B ell ε : ℝ) (hB : 0 ≤ B) (hell : 0 ≤ ell) (hε : 0 < ε) :
    0 < amplifiedPassivePairConstant K cap B ell ε hB hell hε :=
  (Classical.choose_spec
    (pool_tag_pair_card (K := K) cap B ell (ε / 8) hB hell (by positivity))).1

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ] {cap dimension width : ℕ} {B Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}

section Direct

variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)

/-- The new mask reads the original first common ideal, without
reconstructing or reselecting a source label. -/
def passiveMaskAt (j : R.CoveredLeafKey L) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  firstMask j.1.val.1

variable (kl kr : R.liveLeaves L exceptional N → ℕ)
variable (ld : ∀ j : R.liveLeaves L exceptional N,
  CanonicalLiteralRectangles.Atoms (K := K) (kl j))
variable (rd : ∀ j : R.liveLeaves L exceptional N,
  CanonicalLiteralRectangles.Atoms (K := K) (kr j))
variable (lw : ∀ j, (ld j).ProfileData) (rw : ∀ j, (rd j).ProfileData)
variable (BL : ∀ j, ActualColumnAllocation K (kl j))
variable (BR : ∀ j, ActualColumnAllocation K (kr j))
variable (families : ∀ j : R.liveLeaves L exceptional N,
  ActualNormalizedPairFamily A σ V
    (PairLabel (A := A) (lw j) (rw j) (BL j) (BR j)
      (R.passiveMaskAt L j.val) (R.passiveMaskAt L j.val)) ω ψ Z)
variable (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 < Z)
variable (rows : R.OriginalFibreRows Θ dimension width B Z)
variable (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
variable (mask : OriginalMaskPrimeData s.mask maskIdeal)
variable (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
variable (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B)
variable (hkl : ∀ j, kl j ≤ cap) (hkr : ∀ j, kr j ≤ cap)

include hZ rows hmask0 mask hmaskN hN hkl hkr

/-- The new allocations cost their proved original-mask subpower
count. The old physical classifier still supplies the source fibre. -/
theorem passive_index_fibre :
    ∀ i, ((Finset.univ.filter
      (fun b : (sigmaCombine families).active Finset.univ =>
        (R.arithmeticLabels L hcap exceptional N).dependentIndex families
          Finset.univ (fun _ => Finset.univ) b = i)).card : ℝ) ≤
      (directPassivePairConstant K cap B ε hB hε *
        kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B
          (ε / 2) hB (by positivity)) * Z ^ (ε / 4) := by
  have hpair := (Classical.choose_spec
    (direct_pair_card (K := K) cap B (ε / 8) hB (by positivity))).2
  have hinner (j : R.liveLeaves L exceptional N) :
      (Fintype.card (PairLabel (A := A) (lw j) (rw j) (BL j) (BR j)
        (R.passiveMaskAt L j.val) (R.passiveMaskAt L j.val)) : ℝ) ≤
      directPassivePairConstant K cap B ε hB hε * Z ^ (ε / 8) := by
    have hp := actual_common_pair_properties s.columns s.columns
      (fun i => (s.ideal i).val) (fun i => (s.ideal i).val) j.val.1
    have hn := actual_common_pair_norm s.columns s.columns
      (fun i => (s.ideal i).val) (fun i => (s.ideal i).val) (Z ^ B)
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      hN hN j.val.1
    exact hpair Z hZ A j.val.1.val.1 hp.1 hn.1
      (kl j) (kr j) (ld j) (rd j) (lw j) (rw j) (BL j) (BR j) (hkl j) (hkr j)
  have hsource := R.original_image_kernel_source_fibre L hcap (ε / 2)
    hB (by positivity) hZ.le rows maskIdeal hmask0 mask hmaskN hN exceptional N
  have h := activeSigma_index_fibre_subpower
    (directPassivePairConstant K cap B ε hB hε)
    (kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B
      (ε / 2) hB (by positivity)) Z (ε / 8) ((ε / 2) / 4)
    (zero_lt_one.trans hZ) (directPassivePairConstant_pos K cap B ε hB hε).le
    families (R.arithmeticLabels L hcap exceptional N).index hinner hsource
  have he : ε / 8 + (ε / 2) / 4 = ε / 4 := by ring
  simpa only [OriginalArithmeticLabels.dependentIndex, he] using h

end ActualDirectFirstSource.SecondStages
end Direct

section Amplified

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

/-- The tag comes from the original selected left or right pool stage. -/
def passivePoolTagAt (j : R.CoveredLeafKey L) : PoolSourceTag P :=
  match j.2.2.2.2 with
  | .inl k =>
      ((R j.1 j.2.1).left j.2.2.1 j.2.2.2.1).leafTag
        ((s.pools j.1 j.2.1).leftSourceCovers L j.2.2.1 j.2.2.2.1) k
  | .inr k =>
      ((R j.1 j.2.1).right j.2.2.1 j.2.2.2.1).leafTag
        ((s.pools j.1 j.2.1).rightSourceCovers L j.2.2.1 j.2.2.2.1) k

def passiveMaskAt (j : R.CoveredLeafKey L) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  poolTagMask j.1.val.1 (R.passivePoolTagAt L j)

variable (hcap : L.slotCount ≤ cap)
variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
variable (kl kr : R.liveLeaves L exceptional N → ℕ)
variable (ld : ∀ j : R.liveLeaves L exceptional N,
  CanonicalLiteralRectangles.Atoms (K := K) (kl j))
variable (rd : ∀ j : R.liveLeaves L exceptional N,
  CanonicalLiteralRectangles.Atoms (K := K) (kr j))
variable (lw : ∀ j, (ld j).ProfileData) (rw : ∀ j, (rd j).ProfileData)
variable (BL : ∀ j, ActualColumnAllocation K (kl j))
variable (BR : ∀ j, ActualColumnAllocation K (kr j))
variable (families : ∀ j : R.liveLeaves L exceptional N,
  ActualNormalizedPairFamily A σ V
    (PairLabel (A := A) (lw j) (rw j) (BL j) (BR j)
      (R.passiveMaskAt L j.val) (R.passiveMaskAt L j.val)) ω ψ Z)
variable (ε B₀ : ℝ) (hB : 0 ≤ B) (hell : 0 ≤ ell) (hε : 0 < ε)
variable (hbox : B₀ + 7 * ell ≤ B)
variable (rows : R.OriginalFibreRows Θ dimension width B Z)
variable (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
variable (mask : OriginalMaskPrimeData s.mask maskIdeal)
variable (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
variable (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
variable (hkl : ∀ j, kl j ≤ cap) (hkr : ∀ j, kr j ≤ cap)

include hbox rows hmask0 mask hmaskN hN hkl hkr

/-- The original pool prime and valuation are kept in the arithmetic
index. Their actual passive masks are paid inside the label count. -/
theorem passive_index_fibre :
    ∀ i, ((Finset.univ.filter
      (fun b : (sigmaCombine families).active Finset.univ =>
        (R.arithmeticLabels L hcap exceptional N).dependentAmplifiedIndex families
          Finset.univ (fun _ => Finset.univ) P (R.arithmeticTag L exceptional N)
          (R.arithmeticTag_mem L exceptional N) b = i)).card : ℝ) ≤
      (amplifiedPassivePairConstant K cap B ell ε hB hell hε *
        kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B
          (ε / 2) hB (by positivity)) * Z ^ (ε / 4) := by
  have hZ : 1 < Z := P.base_gt_one
  have hB₀ : B₀ ≤ B := by linarith
  have hN' : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B := by
    intro i hi
    exact (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le hZ.le hB₀)
  have hpair := (Classical.choose_spec
    (pool_tag_pair_card (K := K) cap B ell (ε / 8) hB hell (by positivity))).2
  have hinner (j : R.liveLeaves L exceptional N) :
      (Fintype.card (PairLabel (A := A) (lw j) (rw j) (BL j) (BR j)
        (R.passiveMaskAt L j.val) (R.passiveMaskAt L j.val)) : ℝ) ≤
      amplifiedPassivePairConstant K cap B ell ε hB hell hε * Z ^ (ε / 8) := by
    have hp := actual_common_pair_properties s.columns s.columns
      (fun i => (s.ideal i).val) (fun i => (s.ideal i).val) j.val.1
    have hn := actual_common_pair_norm s.columns s.columns
      (fun i => (s.ideal i).val) (fun i => (s.ideal i).val) (Z ^ B)
      (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1)
      hN' hN' j.val.1
    exact hpair Z hZ A bad eps P j.val.1.val.1 hp.1 hn.1
      (R.passivePoolTagAt L j.val) (kl j) (kr j) (ld j) (rd j)
      (lw j) (rw j) (BL j) (BR j) (hkl j) (hkr j)
  have hsource := R.original_image_kernel_source_fibre L hcap (ε / 2) B₀
    hB (by positivity) hbox rows maskIdeal hmask0 mask hmaskN hN exceptional N
  have h := activeSigma_index_fibre_subpower
    (amplifiedPassivePairConstant K cap B ell ε hB hell hε)
    (kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B
      (ε / 2) hB (by positivity)) Z (ε / 8) ((ε / 2) / 4)
    (zero_lt_one.trans hZ)
    (amplifiedPassivePairConstant_pos K cap B ell ε hB hell hε).le
    families ((R.arithmeticLabels L hcap exceptional N).amplifiedIndex
      (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N)) hinner hsource
  have he : ε / 8 + (ε / 2) / 4 = ε / 4 := by ring
  simpa only [OriginalArithmeticLabels.dependentAmplifiedIndex, he] using h

end ActualFirstSource.SecondStages
end Amplified
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveLabelMass.pool_tag_pair_card
#print axioms HeckeSkeleton.Moments.EngineStep.directPassivePairConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.amplifiedPassivePairConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.passive_index_fibre
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.passive_index_fibre
