import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondActiveDualZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.WholeGramOrigin
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The two terms in the literal second zero frequency

The V2 source retains `transformedZero`, including its primal-origin
subtraction. Its row-ball test has a nonzero value at zero. Accordingly,
the pure dual Euler diagonal and the original Gauss origin are treated
separately here. The latter is supported on powerful original ideals on
both sides; it is not asserted to have equal-ideal support.

These are local ingredients for T2. The finite source, its common label,
the complete correlation and its original profile are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- A nonzero Gauss origin forces the complete original ideal to be
powerful, independently of the chosen generator. -/
theorem generated_residue_zero_powerful
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (hnonzero : (generatedOriginalColumn (σ := σ) hΓ I a ha).residue hDiff 0 ≠ 0) :
    Powerful I.val := by
  apply actual_sInteger_zero_gauss_nonzero_powerful C hDiff I a ha
  simpa only [OrbitalGaussColumn.residue, generatedOriginalColumn,
    actualSIntegerGauss, map_zero] using hnonzero

/-- The origin of a genuine generated pair is zero away from the
powerful-product support. No annularity of its Schwartz test is used. -/
theorem generated_originZero_of_not_powerful
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (φ : SchwartzMap V ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (D : Finset (HeightOneSpectrum A.R))
    (hbad : ¬ Powerful (I.val * J.val)) :
    ((generatedOriginalColumn (σ := σ) hΓ I a ha).pair hDiff
      (generatedOriginalColumn (σ := σ) hΓ J b hb) φ).originZero finiteTest D = 0 := by
  by_contra hn
  have hres :
      (generatedOriginalColumn (σ := σ) hΓ I a ha).residue hDiff 0 *
        star ((generatedOriginalColumn (σ := σ) hΓ J b hb).residue hDiff 0) ≠ 0 := by
    intro hz
    apply hn
    rw [ParentPeriodicPair.originZero, OrbitalGaussColumn.pair_residue_zero,
      hz, zero_mul, mul_zero]
  have hI := generated_residue_zero_powerful hΓ C hDiff I a ha
    (mul_ne_zero_iff.mp hres).1
  have hJ := generated_residue_zero_powerful hΓ C hDiff J b hb
    (fun hz => (mul_ne_zero_iff.mp hres).2 (by rw [hz, star_zero]))
  exact hbad (powerful_mul I.property.1 J.property.1 hI hJ)

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

/-- Common-support extraction preserves the same original powerful
support of the Gauss origin. The residual coprimality remains a gate. -/
theorem second_originZero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (D : Finset (HeightOneSpectrum A.R))
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) :
    (b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D = 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_originZero]
  split_ifs with hcop
  · apply generated_originZero_of_not_powerful hΓ C hDiff
      (b.secondLeftIdeal i) (b.secondRightIdeal j) _ _
      (b.secondLeft_generates C i) (b.secondRight_generates C j)
      (profiles i j) finiteTest D
    simpa only [b.secondLeftIdeal_eq left i hi,
      b.secondRightIdeal_eq right j hj] using hbad
  · rfl

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- Both genuine terms vanish away from the original powerful product.
The dual term uses equality of full ideals; the origin uses its two
individual zero-frequency Gauss sums. -/
theorem second_signedZero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (b.secondPair hΓ hDiff C profiles i j).transformedZero
      μv hDiff finiteTest radius D = 0 := by
  rw [ParentPeriodicPair.transformedZero_eq_dual_sub_origin,
    b.secondDualZero_of_not_powerful hΓ μv C hDiff finiteTest left right profiles
      i hi j hj hbad radius D haδ hbδ,
    second_originZero_of_not_powerful hΓ b C hDiff finiteTest
      left right profiles i hi j hj D hbad, sub_self]

/-- The original tensor at zero is bounded by the zeroth original
Schwartz seminorm and the fixed finite-place tensor. -/
theorem original_tensor_zero_norm_le
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (seminorms : Finset (ℕ × ℕ)) (hzero : (0, 0) ∈ seminorms)
    (φ : SchwartzMap V ℂ) :
    ‖sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0‖ ≤
      ‖∏ v ∈ A.Sf, finiteTest v 0‖ *
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ := by
  have he : sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K φ) finiteTest 0 =
      φ 0 * ∏ v ∈ A.Sf, finiteTest v 0 := by
    simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply]
  rw [he, norm_mul]
  have hp : ‖φ 0‖ ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ :=
    (SchwartzMap.norm_le_seminorm ℂ φ 0).trans
      (Seminorm.le_finset_sup_apply hzero)
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The origin amplitude retains both complete original ideal norms.
Those are the two norms cancelled by the actual first Poisson columns. -/
theorem second_originZero_amplitude
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (seminorms : Finset (ℕ × ℕ)) (hzero : (0, 0) ∈ seminorms)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (D : Finset (HeightOneSpectrum A.R)) :
    ‖(b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D‖ ≤
      (‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖ *
        ‖∏ v ∈ A.Sf, finiteTest v 0‖) *
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
        (‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
          A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j)) := by
  have hres := (b.second_residue_norm_le_modulus hΓ hDiff C profiles i j 0).trans_eq
    (b.second_modulus_norm hΓ hDiff C left right profiles i hi j hj)
  have hres' : ‖(b.secondPair hΓ hDiff C profiles i j).residue 0‖ ≤
      A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j) := by
    simpa only [map_mul, Nat.cast_mul, SArithmeticData.exteriorNorm] using hres
  have ht := original_tensor_zero_norm_le (A := A) finiteTest seminorms hzero (profiles i j)
  change ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ) *
      ((b.secondPair hΓ hDiff C profiles i j).residue 0 *
        sIntegerTensorTerm K A.Sf (traceSchwartzToMixed K (profiles i j)) finiteTest 0)‖ ≤ _
  simp only [norm_mul]
  calc
    _ ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
        ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖ *
        ((A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j)) *
          (‖∏ v ∈ A.Sf, finiteTest v 0‖ *
            seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      exact mul_le_mul hres' ht (norm_nonneg _)
        (mul_nonneg (A.exteriorNorm_pos _).le (A.exteriorNorm_pos _).le)
    _ = _ := by ring

/-- One fixed original seminorm set controls the actual signed zero.
The full Euler diagonal and the extra origin weight remain separate in
the displayed scalar, so neither term can be silently discarded. -/
theorem second_signedZero_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
      (DE : Ideal (𝓞 K) × Ideal (𝓞 K))
      (b : FirstCommonCharacterBlock fullI fullJ DE)
      (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
      (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)),
      IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
      IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val →
      ‖(b.secondPair hΓ hDiff C profiles i j).transformedZero
        μv hDiff finiteTest radius D‖ ≤
      Cbound * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
        (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI i) +
          ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
            A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j)) := by
  obtain ⟨s, Cdual, hCdual, hdual⟩ :=
    second_dualZero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  let seminorms := insert (0, 0) s
  let Corigin : ℝ :=
    ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖ *
      ‖∏ v ∈ A.Sf, finiteTest v 0‖
  have hCorigin : 0 ≤ Corigin := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨seminorms, Cdual + Corigin, add_nonneg hCdual hCorigin, ?_⟩
  intro C ι κ fullI fullJ DE b left right profiles hDiff i hi j hj radius D haδ hbδ
  have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) :=
    apply_nonneg _ _
  have hsmono : s.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) ≤
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) :=
    Seminorm.finset_sup_apply_le hs
      (fun a ha => Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem ha))
  have hd : ‖(b.secondPair hΓ hDiff C profiles i j).dualZero
        μv hDiff finiteTest radius D‖ ≤
      Cdual * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
        (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI i)) := by
    unfold FirstCommonCharacterBlock.secondPair
    rw [ParentPeriodicPair.gated_dualZero]
    split_ifs with hcop
    · have hp := hdual (b.secondLeftIdeal i) (b.secondRightIdeal j) _ _
        (b.secondLeft_generates C i) (b.secondRight_generates C j)
        (profiles i j) hDiff radius D haδ hbδ
      have hnorm : (if b.secondLeftIdeal i = b.secondRightIdeal j then
          A.exteriorNorm (b.secondLeftIdeal i) else 0) ≤ A.exteriorNorm (fullI i) := by
        rw [b.secondLeftIdeal_eq left i hi]
        split_ifs
        · exact le_rfl
        · exact (A.exteriorNorm_pos _).le
      calc
        _ ≤ Cdual * s.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI i) :=
          hp.trans (mul_le_mul_of_nonneg_left hnorm
            (mul_nonneg (mul_nonneg hCdual (apply_nonneg _ _))
              (firstZeroDivisorWeight_nonneg radius D)))
        _ ≤ Cdual * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmono hCdual)
              (firstZeroDivisorWeight_nonneg radius D)) (A.exteriorNorm_pos _).le
        _ = _ := by ring
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg hCdual hs)
        (mul_nonneg (firstZeroDivisorWeight_nonneg radius D) (A.exteriorNorm_pos _).le)
  have ho := second_originZero_amplitude hΓ b C hDiff finiteTest seminorms
    (Finset.mem_insert_self _ _) left right profiles i hi j hj D
  change ‖(b.secondPair hΓ hDiff C profiles i j).originZero finiteTest D‖ ≤
    Corigin * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles i j) *
      (‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
        A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j)) at ho
  rw [ParentPeriodicPair.transformedZero_eq_dual_sub_origin]
  apply (norm_sub_le _ _).trans ((add_le_add hd ho).trans _)
  have hx : 0 ≤ firstZeroDivisorWeight radius D * A.exteriorNorm (fullI i) :=
    mul_nonneg (firstZeroDivisorWeight_nonneg radius D) (A.exteriorNorm_pos _).le
  have hy : 0 ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
      A.exteriorNorm (fullI i) * A.exteriorNorm (fullJ j) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (A.exteriorNorm_pos _).le)
      (A.exteriorNorm_pos _).le
  nlinarith [mul_nonneg (mul_nonneg hCorigin hs) hx,
    mul_nonneg (mul_nonneg hCdual hs) hy]

/-- The actual signed second zero has a uniform whole-index bound.
Only genuinely nonzero original profiles enter the powerful count;
the common labels and all original tuple fibres are preserved. -/
theorem second_signedZero_diagonal_supported_of_fibers
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ M.powerset,
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
            ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
              A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2)) ≤
          Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * multiplicity * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_signedZero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    PowerfulDiagonal.powerful_whole_index_normalized_sum_of_fibers (K := K) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors multiplicity hfiber hfactor N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  let allPairs := firstZeroPairs left right fullI fullJ
  let pairs := allPairs.filter (fun v => profiles v.2.1 v.2.2 ≠ 0)
  let amp := secondZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v := norm_nonneg _
  have hmem (v) (hv : v ∈ allPairs) := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hblock (v) (hv : v ∈ allPairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hpoint (v) (hv : v ∈ allPairs) : amp v ≤
      C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ M.powerset,
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
            ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
              A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2))) := by
    change ‖∑ D ∈ M.powerset,
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            (firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
              ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
                A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2)) := by
        apply Finset.sum_le_sum
        intro D hD
        exact hzero C fullI fullJ v.1.val (blocks v.1) left right profiles hDiff
          v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 radius D
          (hleftmask v.1 _ (hblock v hv).1 D hD)
          (hrightmask v.1 _ (hblock v hv).2.1 D hD)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hall (v) (hv : v ∈ pairs) : v ∈ allPairs := (Finset.mem_filter.mp hv).1
  have hij (v) (hv : v ∈ allPairs) : v.2 ∈ left ×ˢ right :=
    Finset.mem_product.mpr ⟨(hmem v hv).1, (hmem v hv).2.1⟩
  have hfiber' (w : Fin k → Ideal (𝓞 K)) :
      (pairs.filter (fun v => factors v.2 = w)).card ≤ multiplicity := by
    let T := pairs.filter (fun v => factors v.2 = w)
    have hi : Set.InjOn
        (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => v.2)
        (T : Set (FirstZeroLabel left right fullI fullJ × (ι × κ))) := by
      intro v hv u hu he
      exact firstZeroPairs_projection_injective left right fullI fullJ
        (hall v (Finset.mem_filter.mp hv).1)
        (hall u (Finset.mem_filter.mp hu).1) he
    have hs : T.image Prod.snd ⊆ (left ×ˢ right).filter (fun ij => factors ij = w) := by
      intro ij hij'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hij'
      exact Finset.mem_filter.mpr
        ⟨hij v (hall v (Finset.mem_filter.mp hv).1), (Finset.mem_filter.mp hv).2⟩
    have hc := (Finset.card_le_card hs).trans (hfiber w)
    rw [Finset.card_image_of_injOn hi] at hc
    exact hc
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    calc
      _ ≤ C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          (∑ D ∈ M.powerset,
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) +
              ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ *
                A.exteriorNorm (fullI v.2.1) * A.exteriorNorm (fullJ v.2.2))) :=
          hpoint v (hall v hv)
      _ ≤ C₀ * (Amp / Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (hprofile v (hall v hv)) hC₀
      _ = _ := by ring
  have hc := hdiag pairs (fun v => factors v.2) multiplicity hfiber' N (C₀ * Amp)
    (fun v => (amp v : ℂ)) hN (mul_nonneg hC₀ hAmp)
    (by
      intro v hv
      rw [hfactor v.2 (hij v (hall v hv))]
      exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1)
    (by
      intro v hv
      rw [hfactor v.2 (hij v (hall v hv))]
      exact hnorm v.2 (hij v (hall v hv)) (Finset.mem_filter.mp hv).2)
    (by
      intro v hv hbad
      have hav := hall v hv
      have hbad' : ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) := by
        simpa only [hfactor v.2 (hij v hav)] using hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D hD =>
            second_signedZero_of_not_powerful hΓ μv (blocks v.1) C hDiff finiteTest left right profiles
              v.2.1 (hblock v hav).1 v.2.2 (hblock v hav).2.1 hbad'
              radius D
              (hleftmask v.1 _ (hblock v hav).1 D hD)
              (hrightmask v.1 _ (hblock v hav).2.1 D hD))
        rw [he, norm_zero]
      rw [hz, Complex.ofReal_zero])
    (by
      intro v hv
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hampnonneg v)]
        using hcoef v hv)
  have hvanish (v) (hv : v ∈ allPairs) (hφ : profiles v.2.1 v.2.2 = 0) : amp v = 0 := by
    have hp : amp v ≤ 0 := by
      simpa only [hφ, map_zero, zero_mul, mul_zero] using hpoint v hv
    exact le_antisymm hp (hampnonneg v)
  have hrestrict : (∑ v ∈ allPairs, amp v) = ∑ v ∈ pairs, amp v := by
    dsimp only [pairs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hφ : profiles v.2.1 v.2.2 = 0
    · rw [if_neg (fun hne => hne hφ)]
      exact hvanish v hv hφ
    · rw [if_pos hφ]
  have hreal : ‖∑ v ∈ pairs, (amp v : ℂ)‖ = ∑ v ∈ pairs, amp v := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun v _ => hampnonneg v))
  rw [hreal] at hc
  calc
    _ ≤ ∑ v ∈ allPairs, amp v :=
      second_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ = ∑ v ∈ pairs, amp v := hrestrict
    _ ≤ Cdiag * multiplicity * (C₀ * Amp) * N ^ ε := hc
    _ = (Cdiag * C₀) * ((multiplicity : ℝ) * Amp * N ^ ε) := by ring
    _ ≤ (Cdiag * (1 + C₀)) * ((multiplicity : ℝ) * Amp * N ^ ε) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCdiag.le)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAmp)
        (Real.rpow_nonneg (zero_le_one.trans hN) _)
    _ = (Cdiag * (1 + C₀)) * multiplicity * Amp * N ^ ε := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
