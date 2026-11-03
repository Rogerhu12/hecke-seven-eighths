import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroDiagonal

/-!
# One global normalized second Euler diagonal

Each original pair has one actual common-support label. Its literal
second zero term vanishes off equality of the complete original ideals.
Equality forces their product to be powerful; the genuine global tuple
count is therefore applied once, before any sum over labels. The profile
normalization uses only fixed original seminorms, the original ideal
norm, and the explicit inverse-norm divisor weights.
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

theorem FirstCommonCharacterBlock.secondZero_of_not_coprime
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hcop : ¬ IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    (b.secondPair hΓ hDiff C profiles i j).transformedZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_transformedZero (A := A), if_neg hcop]

/-- The equal-ideal support is for the complete original column ideals,
independently of their blockwise chosen generators. -/
theorem FirstCommonCharacterBlock.secondZero_of_ne
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hneq : fullI i ≠ fullJ j) (hφ : profiles i j 0 = 0)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (b.secondPair hΓ hDiff C profiles i j).transformedZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.secondPair
  rw [ParentPeriodicPair.gated_transformedZero (A := A)]
  split_ifs with hcop
  · apply generated_second_zero_of_ne hΓ μv hDiff
      (b.secondLeftIdeal i) (b.secondRightIdeal j) _ _
      (b.secondLeft_generates C i) (b.secondRight_generates C j)
      _ (profiles i j) hφ finiteTest radius D haδ hbδ
    simpa only [b.secondLeftIdeal_eq left i hi, b.secondRightIdeal_eq right j hj] using hneq
  · rfl

theorem FirstCommonCharacterBlock.secondZero_of_not_powerful
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) (hφ : profiles i j 0 = 0)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (haδ : IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
    (hbδ : IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) :
    (b.secondPair hΓ hDiff C profiles i j).transformedZero μv hDiff finiteTest radius D = 0 := by
  apply b.secondZero_of_ne hΓ μv C hDiff finiteTest left right profiles i hi j hj
    _ hφ radius D haδ hbδ
  intro he
  apply hbad
  rw [he]
  simpa only [pow_two] using powerful_pow (fullJ j).val 2 (Or.inr (by norm_num))

def secondZeroPairAmplitude
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
    ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
      μv hDiff finiteTest radius D‖

/-- The second zero terms also use the unique original pair label. -/
theorem second_zero_blocks_le_pair_sum
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
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤
    ∑ v ∈ firstZeroPairs left right fullI fullJ,
      secondZeroPairAmplitude hΓ μv C left right fullI fullJ blocks profiles hDiff finiteTest radius M v := by
  let amp := secondZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  change _ ≤ ∑ v ∈ firstZeroPairs left right fullI fullJ, amp v
  calc
    _ ≤ ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        amp (DE, (i, j)) := by
      apply Finset.sum_le_sum
      intro DE _
      change ‖∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        ∑ D ∈ M.powerset, ((blocks DE).secondPair hΓ hDiff C profiles i j).transformedZero
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
              ((blocks DE).secondPair hΓ hDiff C profiles i j).transformedZero
                μv hDiff finiteTest radius D‖ = 0
            have hz : (∑ D ∈ M.powerset,
                ((blocks DE).secondPair hΓ hDiff C profiles i j).transformedZero
                  μv hDiff finiteTest radius D) = 0 :=
              Finset.sum_eq_zero (fun D _ =>
                (blocks DE).secondZero_of_not_coprime hΓ μv C hDiff finiteTest
                  profiles i j radius D hc')
            rw [hz, norm_zero]
        · simp only [hright, if_false, false_and, Finset.sum_const_zero]
      · simp only [hleft, if_false, false_and, Finset.sum_const_zero]

/-- A uniform normalized bound for the actual second Euler diagonal.
All constants and original seminorms precede every moving source datum. -/
theorem second_zero_diagonal_normalized
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
    (∀ i ∈ left, ∀ j ∈ right, profiles i j 0 = 0) →
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
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_zero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    common_label_powerful_normalized_sum (A := A) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors hinj hfactor N Amp hN hAmp hnorm hannular hleftmask hrightmask hprofile
  let pairs := firstZeroPairs left right fullI fullJ
  let amp := secondZeroPairAmplitude hΓ μv C left right fullI fullJ
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
        ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
          μv hDiff finiteTest radius D‖ ≤
        C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) := by
      unfold FirstCommonCharacterBlock.secondPair
      rw [ParentPeriodicPair.gated_transformedZero (A := A), if_pos (hblock v hv).2.2]
      have he := hzero ((blocks v.1).secondLeftIdeal v.2.1) ((blocks v.1).secondRightIdeal v.2.2)
        _ _ ((blocks v.1).secondLeft_generates C _) ((blocks v.1).secondRight_generates C _)
        (profiles v.2.1 v.2.2) (hannular _ (hmem v hv).1 _ (hmem v hv).2.1) hDiff radius D
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
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
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
  have hc := hdiag left right fullI fullJ factors hinj hfactor N (C₀ * Amp)
    hN (mul_nonneg hC₀ hAmp) hnorm (fun v => (amp v : ℂ))
    (by
      intro v hv hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D hD =>
            (blocks v.1).secondZero_of_not_powerful hΓ μv C hDiff finiteTest left right profiles
              v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 hbad
              (hannular _ (hmem v hv).1 _ (hmem v hv).2.1) radius D
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
      second_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ ≤ Cdiag * (C₀ * Amp) * N ^ ε := hc
    _ ≤ (Cdiag * (1 + C₀)) * Amp * N ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hN) _)
      nlinarith [mul_nonneg hCdiag.le hAmp]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondZero_of_ne
#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_blocks_le_pair_sum
#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_diagonal_normalized
