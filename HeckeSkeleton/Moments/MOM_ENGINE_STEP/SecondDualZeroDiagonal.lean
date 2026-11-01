import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondDualZeroAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualTupleCount
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroDiagonal

/-!
# The complete pure dual-zero diagonal on the original source

The original pair has one actual common-support label. Its pure second
Poisson dual zero is supported on equality of the complete original
ideals, for arbitrary original Schwartz profiles. Equality forces the
original ideal product to be powerful. The global tuple count is applied
once to these original pairs, before any sum over common labels.

The finite-fibre version preserves a literal original tuple encoding.
For genuine prime-power residual columns the fibre is proved from the
original whole factors and their actual quotient presentations. Only
pointwise original profile seminorm normalization and ideal windows are
inputs; there is no profile-zero assumption and no given zero-term bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

theorem FirstCommonCharacterBlock.secondDualZero_of_not_coprime
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hcop : ¬ IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    (b.secondPair hΓ hDiff C profiles i j).dualZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_dualZero, if_neg hcop]

/-- The equal-ideal support is for the complete original column ideals,
independently of their blockwise chosen generators. -/
theorem FirstCommonCharacterBlock.secondDualZero_of_ne
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hneq : fullI i ≠ fullJ j)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (b.secondPair hΓ hDiff C profiles i j).dualZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_dualZero]
  split_ifs with hcop
  · apply generated_second_dualZero_of_ne hΓ μv hDiff
      (b.secondLeftIdeal i) (b.secondRightIdeal j) _ _
      (b.secondLeft_generates C i) (b.secondRight_generates C j)
      _ (profiles i j) finiteTest radius D haδ hbδ
    simpa only [b.secondLeftIdeal_eq left i hi, b.secondRightIdeal_eq right j hj] using hneq
  · rfl

theorem FirstCommonCharacterBlock.secondDualZero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val))
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (b.secondPair hΓ hDiff C profiles i j).dualZero μv hDiff finiteTest radius D = 0 := by
  apply b.secondDualZero_of_ne hΓ μv C hDiff finiteTest left right profiles i hi j hj
    _ radius D haδ hbδ
  intro he
  apply hbad
  rw [he]
  simpa only [pow_two] using powerful_pow (fullJ j).val 2 (Or.inr (by norm_num))

def secondDualZeroPairAmplitude
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : ℝ :=
  ‖∑ D ∈ M.powerset,
    ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
      μv hDiff finiteTest radius D‖

/-- The second zero terms also use the unique original pair label. -/
theorem second_dualZero_blocks_le_pair_sum
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (cutoff : ℝ) (hcutoff : 1 ≤ cutoff) :
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤
    ∑ v ∈ firstZeroPairs left right fullI fullJ,
      secondDualZeroPairAmplitude hΓ μv C left right fullI fullJ blocks profiles hDiff finiteTest radius M v := by
  let amp := secondDualZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  change _ ≤ ∑ v ∈ firstZeroPairs left right fullI fullJ, amp v
  calc
    _ ≤ ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        amp (DE, (i, j)) := by
      apply Finset.sum_le_sum
      intro DE _
      change ‖∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        ∑ D ∈ M.powerset, ((blocks DE).secondPair hΓ hDiff C profiles i j).dualZero
          μv hDiff finiteTest radius D‖ ≤ _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ = _ := by
      unfold firstZeroPairs
      rw [Finset.sum_filter, Finset.sum_product]
      simp only [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro DE _
      have hDE := commonSupportPool_support_eq left right
        (fun i => (fullI i).val) (fun j => (fullJ j).val) DE.val DE.property
      simp_rw [commonSupportLabel_eq_iff _ _ DE.val.1 DE.val.2 hDE]
      simp only [FirstCommonCharacterBlock.leftColumns,
        FirstCommonCharacterBlock.rightColumns, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hleft : supportExtract (fullI i).val (primeSupport DE.val.1) = DE.val.1
      · simp only [hleft, if_true, true_and]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hright : supportExtract (fullJ j).val (primeSupport DE.val.1) = DE.val.2
        · simp only [hright, if_true, true_and]
          by_cases hc : IsCoprime (supportResidual (fullI i).val (primeSupport DE.val.1))
              (supportResidual (fullJ j).val (primeSupport DE.val.1))
          · simp only [if_pos hc]
          · simp only [if_neg hc]
            have hc' : ¬ IsCoprime ((blocks DE).leftResidual i).val
                ((blocks DE).rightResidual j).val := by
              simpa only [(blocks DE).left_residual, (blocks DE).right_residual] using hc
            change ‖∑ D ∈ M.powerset,
              ((blocks DE).secondPair hΓ hDiff C profiles i j).dualZero
                μv hDiff finiteTest radius D‖ = 0
            have hz : (∑ D ∈ M.powerset,
                ((blocks DE).secondPair hΓ hDiff C profiles i j).dualZero
                  μv hDiff finiteTest radius D) = 0 :=
              Finset.sum_eq_zero (fun D _ =>
                (blocks DE).secondDualZero_of_not_coprime hΓ μv C hDiff finiteTest
                  profiles i j radius D hc')
            rw [hz, norm_zero]
        · simp only [hright, if_false, false_and, Finset.sum_const_zero]
      · simp only [hleft, if_false, false_and, Finset.sum_const_zero]

/-- The full second source zero bound, allowing a finite tuple fibre. -/
theorem second_dualZero_diagonal_normalized_of_fibers
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
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * multiplicity * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_dualZero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    common_label_powerful_normalized_sum_of_fibers (A := A) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors multiplicity hfiber hfactor N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  let pairs := firstZeroPairs left right fullI fullJ
  let amp := secondDualZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v := norm_nonneg _
  have hmem (v) (hv : v ∈ pairs) := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hblock (v) (hv : v ∈ pairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
        (profiles v.2.1 v.2.2) := apply_nonneg _ _
    have hb (D) (hD : D ∈ M.powerset) :
        ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
          μv hDiff finiteTest radius D‖ ≤
        C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) := by
      unfold FirstCommonCharacterBlock.secondPair
      rw [ParentPeriodicPair.gated_dualZero, if_pos (hblock v hv).2.2]
      have he := hzero ((blocks v.1).secondLeftIdeal v.2.1) ((blocks v.1).secondRightIdeal v.2.2)
        _ _ ((blocks v.1).secondLeft_generates C _) ((blocks v.1).secondRight_generates C _)
        (profiles v.2.1 v.2.2) hDiff radius D
        (hleftmask v.1 _ (hblock v hv).1 D hD) (hrightmask v.1 _ (hblock v hv).2.1 D hD)
      apply he.trans
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hC₀ hs) (firstZeroDivisorWeight_nonneg radius D))
      rw [(blocks v.1).secondLeftIdeal_eq left _ (hblock v hv).1,
        (blocks v.1).secondRightIdeal_eq right _ (hblock v hv).2.1]
      split_ifs
      · exact le_rfl
      · exact (A.exteriorNorm_pos _).le
    change ‖∑ D ∈ M.powerset,
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) :=
        Finset.sum_le_sum (fun D hD => hb D hD)
      _ = C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          A.exteriorNorm (fullI v.2.1) * ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        ring
      _ ≤ C₀ * (Amp / Real.sqrt N) := mul_le_mul_of_nonneg_left (hprofile v hv) hC₀
      _ = _ := by ring
  have hc := hdiag left right fullI fullJ factors multiplicity hfiber hfactor N (C₀ * Amp)
    hN (mul_nonneg hC₀ hAmp) hnorm (fun v => (amp v : ℂ))
    (by
      intro v hv hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D hD =>
            (blocks v.1).secondDualZero_of_not_powerful hΓ μv C hDiff finiteTest left right profiles
              v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 hbad
              radius D
              (hleftmask v.1 _ (hblock v hv).1 D hD)
              (hrightmask v.1 _ (hblock v hv).2.1 D hD))
        rw [he, norm_zero]
      rw [hz, Complex.ofReal_zero])
    (by
      intro v hv
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hampnonneg v)] using hcoef v hv)
  have hreal : ‖∑ v ∈ pairs, (amp v : ℂ)‖ = ∑ v ∈ pairs, amp v := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun v _ => hampnonneg v))
  rw [hreal] at hc
  calc
    _ ≤ ∑ v ∈ pairs, amp v :=
      second_dualZero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ ≤ Cdiag * multiplicity * (C₀ * Amp) * N ^ ε := hc
    _ = (Cdiag * C₀) * ((multiplicity : ℝ) * Amp * N ^ ε) := by ring
    _ ≤ (Cdiag * (1 + C₀)) * ((multiplicity : ℝ) * Amp * N ^ ε) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCdiag.le)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAmp)
        (Real.rpow_nonneg (zero_le_one.trans hN) _)
    _ = (Cdiag * (1 + C₀)) * multiplicity * Amp * N ^ ε := by ring


/-- With the original whole-factor injection, the tuple multiplicity is
proved to be one. No extra fibre-count assumption is required. -/
theorem second_dualZero_diagonal_normalized
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
      (factors : ι × κ → Fin k → Ideal (𝓞 K)),
    Set.InjOn factors (left ×ˢ right : Set (ι × κ)) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨seminorms, Cbound, hCbound, hbound⟩ :=
    second_dualZero_diagonal_normalized_of_fibers (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨seminorms, Cbound, hCbound, ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors hinj hfactor N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  have hfiber (v) : ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro ij hij uv huv
    exact hinj (Finset.mem_product.mp (Finset.mem_filter.mp hij).1)
      (Finset.mem_product.mp (Finset.mem_filter.mp huv).1)
      ((Finset.mem_filter.mp hij).2.trans (Finset.mem_filter.mp huv).2.symm)
  simpa only [Nat.cast_one, mul_one] using
    hbound C left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
      factors 1 hfiber hfactor N Amp hN hAmp hnorm hleftmask hrightmask hprofile

/-- Actual prime-power residual columns.  The only injection is that of
the original whole tuple; the residual tuple and its finite multiplicity
are constructed in the proof.  The constant and original seminorms are
chosen before the prime, the valuation, all columns and all profiles. -/
theorem actual_residual_second_dualZero_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
      (nLeft nRight : ℕ) {ι κ : Type*} (left : Finset ι) (right : Finset κ)
      (originalI : ι → A.Exterior) (originalJ : κ → A.Exterior)
      (RI : ∀ i, AmplifierResidualPresentation C p nLeft (originalI i))
      (RJ : ∀ j, AmplifierResidualPresentation C p nRight (originalJ j)),
    let fullI := fun i => (RI i).residual
    let fullJ := fun j => (RJ j).residual
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (originalFactors : ι × κ → Fin k → A.Exterior),
    Set.InjOn (fun ij t => (originalFactors ij t).val) (left ×ˢ right : Set (ι × κ)) →
    (∀ ij ∈ left ×ˢ right,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (originalI ij.1).val * (originalJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * ((nLeft + nRight + 1) ^ k : ℕ) * Amp * N ^ ε := by
  obtain ⟨seminorms, Cbound, hCbound, hz⟩ :=
    second_dualZero_diagonal_normalized_of_fibers (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨seminorms, Cbound, hCbound, ?_⟩
  intro C p nLeft nRight ι κ left right originalI originalJ RI RJ
  dsimp only
  intro blocks profiles hDiff radius M cutoff hcutoff originalFactors hinj hproduct
    N Amp hN hAmp hnorm hleftmask hrightmask hprofile
  let factors := fun ij => actualResidualFactorTuple C p (originalFactors ij)
  have hfiber (v) : ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤
      (nLeft + nRight + 1) ^ k := by
    apply actual_residual_tuple_fiber_card C p (left ×ˢ right) originalFactors
      (fun ij hij uv huv he => hinj (Finset.mem_product.mp hij)
        (Finset.mem_product.mp huv) he)
    intro ij hij
    have hs := actual_factor_valuation_sum p (originalFactors ij)
      (ExteriorIdealEuler.mul (originalI ij.1) (originalJ ij.2)) (hproduct ij hij)
    rw [primeExponent_exterior_mul, (RI ij.1).original_valuation,
      (RJ ij.2).original_valuation] at hs
    exact hs
  exact hz C left right (fun i => (RI i).residual) (fun j => (RJ j).residual)
    blocks profiles hDiff radius M cutoff hcutoff factors ((nLeft + nRight + 1) ^ k)
    hfiber (fun ij hij => actual_residual_pair_tuple_product C p (originalFactors ij)
      (originalI ij.1) (originalJ ij.2) (hproduct ij hij) (RI ij.1) (RJ ij.2))
    N Amp hN hAmp hnorm hleftmask hrightmask hprofile

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondDualZero_of_ne
#print axioms HeckeSkeleton.Moments.EngineStep.second_dualZero_blocks_le_pair_sum
#print axioms HeckeSkeleton.Moments.EngineStep.second_dualZero_diagonal_normalized_of_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.second_dualZero_diagonal_normalized
#print axioms HeckeSkeleton.Moments.EngineStep.actual_residual_second_dualZero_bound
