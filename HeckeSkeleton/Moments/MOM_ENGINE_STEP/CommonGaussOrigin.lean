import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeGramOrigin

/-!
# The original origin after the complete common-support partition

At additive frequency zero a generated Gauss column depends only on
its original ideal. Changing the generator transports the complete
quotient sum exactly and requires no allowed-generator condition.

Consequently the original-origin terms of the actual second common
blocks reassemble the same whole Gauss Gram source. For the empty
Poisson mask their sum is the original polynomial square times its
actual tensor and Haar covolume. Its real part is nonnegative for the
canonical row-ball tensor. This is proved before any blockwise norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)

/-- The complete zero Gauss sum is independent of the chosen generator
of the same original ideal. The entire quotient is retained. -/
theorem generatedColumn_residue_zero_generator_change
    (I : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates I b) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).residue hDiff 0 =
      (generatedOriginalColumn (σ := σ) hΓ I b hb).residue hDiff 0 := by
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) a ha.1
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) b hb.1
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {a})
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {b})
  change completeResidueGauss
      (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff)
      a (generatedIdealCharacter (σ := σ) I a ha) 0 =
    completeResidueGauss
      (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff)
      b (generatedIdealCharacter (σ := σ) I b hb) 0
  exact generated_zero_gauss_generator_change (σ := σ)
    (actualSIntegerTrace K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) hDiff) I a b ha hb

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]

/-- Both original Gauss residues and the original profile are unchanged
at the primal origin, for every original Möbius divisor. -/
theorem generated_gauss_pair_originZero_generator_change
    (I J : A.Exterior) (a b a' b' : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b)
    (ha' : A.Generates I a') (hb' : A.Generates J b')
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum A.R)) :
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).originZero finiteTest D =
    ((generatedOriginalColumn (σ := σ) hΓ I a' ha').pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b' hb') φ).originZero finiteTest D := by
  simp only [ParentPeriodicPair.originZero, OrbitalGaussColumn.pair_residue_zero]
  rw [generatedColumn_residue_zero_generator_change (σ := σ) hΓ hDiff I a a' ha ha',
    generatedColumn_residue_zero_generator_change (σ := σ) hΓ hDiff J b b' hb hb']
  rfl

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- The actual common block has the same original-origin contribution
at its unique residual-coprime label. No source identity is assumed. -/
theorem FirstCommonCharacterBlock.secondPair_originZero
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (left : Finset ι) (right : Finset κ)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum A.R))
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right) :
    (b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D =
      if IsCoprime (b.leftResidual i).val (b.rightResidual j).val then
        ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).pair hDiff
          (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
          (profiles i j)).originZero finiteTest D else 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_originZero]
  congr 1
  have ha := b.secondLeft_generates C i
  have hb := b.secondRight_generates C j
  rw [b.secondLeftIdeal_eq left i hi] at ha
  rw [b.secondRightIdeal_eq right j hj] at hb
  have he := generated_gauss_pair_originZero_generator_change (σ := σ) hΓ hDiff
    (fullI i) (fullJ j)
    (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (afull i) (bfull j) ha hb (hafull i) (hbfull j) (profiles i j) finiteTest D
  simpa only [b.secondLeftIdeal_eq left i hi, b.secondRightIdeal_eq right j hj] using he

/-- The exact original-origin identity across all actual common blocks.
The empty mask contributes its single original divisor, and each full
column pair is counted at its literal common-support label. -/
theorem common_support_gauss_origins
    (C : A.GeneralArithmeticContext σ η htrace)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (afull : ι → A.R) (bfull : κ → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (hbfull : ∀ j, A.Generates (fullJ j) (bfull j))
    (profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    (∑ i ∈ left, ∑ j ∈ right,
      ((generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).pair hDiff
        (generatedOriginalColumn (σ := σ) hΓ (fullJ j) (bfull j) (hbfull j))
        (profiles i j)).originZero finiteTest ∅) =
      ∑ DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val),
        let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
        (b.secondFiniteSource hΓ hDiff C left right profiles ∅ radius X hX).originZeroTerm
          finiteTest := by
  simp only [FirstFiniteSource.originZeroTerm, FirstCommonCharacterBlock.secondFiniteSource,
    Finset.powerset_empty, Finset.sum_singleton]
  rw [sum_common_support_blocks left right (fun i => (fullI i).val) (fun j => (fullJ j).val)]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro DE _
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
  change (∑ i ∈ b.leftColumns left, ∑ j ∈ b.rightColumns right, _) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← b.left_residual i, ← b.right_residual j]
  exact (b.secondPair_originZero hΓ hDiff C left right afull bfull hafull hbfull
    profiles finiteTest ∅ i hi j hj).symm

/-- Whole-source nonnegativity follows from its original tensor value
and its exact Gram square; no total-origin bound is an input. -/
theorem common_support_gauss_origin_nonneg
    (C : A.GeneralArithmeticContext σ η htrace)
    (columns : Finset ι) (coefficient : ι → ℂ)
    (fullI : ι → A.Exterior) (afull : ι → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hpositive : 0 ≤ (sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0).re)
    (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ (∑ DE : commonSupportPool columns columns
        (fun i => (fullI i).val) (fun j => (fullI j).val),
      let b := canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
      (b.secondFiniteSource hΓ hDiff C columns columns
        (fun i j => (coefficient i * star (coefficient j)) • φ)
        ∅ radius X hX).originZeroTerm finiteTest).re := by
  rw [← common_support_gauss_origins hΓ hDiff C columns columns fullI fullI afull afull
    hafull hafull (fun i j => (coefficient i * star (coefficient j)) • φ)
    finiteTest radius X hX]
  exact gauss_originZero_sum_nonneg columns coefficient
    (fun i => generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i))
    hDiff φ finiteTest hpositive

/-- The fixed canonical row-ball test supplies the positive original
tensor internally, including its finite-place factors and Haar mass. -/
theorem common_support_canonical_gauss_origin_nonneg
    (C : A.GeneralArithmeticContext σ η htrace)
    (columns : Finset ι) (coefficient : ι → ℂ)
    (fullI : ι → A.Exterior) (afull : ι → A.R)
    (hafull : ∀ i, A.Generates (fullI i) (afull i))
    (B : ℝ) (radius : {r : ℝ // 0 < r}) (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ (∑ DE : commonSupportPool columns columns
        (fun i => (fullI i).val) (fun j => (fullI j).val),
      let b := canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
      (b.secondFiniteSource hΓ hDiff C columns columns
        (fun i j => (coefficient i * star (coefficient j)) • CanonicalRowBall.archTest K A.Sf B)
        ∅ radius X hX).originZeroTerm (rowBallFiniteFamily K A.Sf B)).re := by
  apply common_support_gauss_origin_nonneg hΓ hDiff C columns coefficient fullI afull hafull
    (CanonicalRowBall.archTest K A.Sf B) (rowBallFiniteFamily K A.Sf B) ?_ radius X hX
  rw [CanonicalRowBall.originalTensor_zero, Complex.ofReal_re]
  exact inv_nonneg.mpr (CanonicalRowBall.mass_pos K A.Sf).le

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generatedColumn_residue_zero_generator_change
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondPair_originZero
#print axioms HeckeSkeleton.Moments.EngineStep.common_support_gauss_origins
#print axioms HeckeSkeleton.Moments.EngineStep.common_support_gauss_origin_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.common_support_canonical_gauss_origin_nonneg
