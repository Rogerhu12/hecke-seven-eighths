import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PowerfulDiagonal

/-!
# One global powerful diagonal for the actual first zero terms

The active label is recovered from the original pair itself. Therefore
forgetting the label is injective on the finite set used for the zero
terms, even though each common-support block is presented as a rectangle.
The powerful tuple count is applied once to the original complete factor
encoding. The only normalization premise concerns fixed seminorms of
individual original profiles and the explicitly computed divisor weight.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {ι κ : Type*}

abbrev FirstZeroLabel (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior) :=
  ↥(commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))

def firstZeroPairs (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior) :
    Finset (FirstZeroLabel left right fullI fullJ × (ι × κ)) :=
  (Finset.univ ×ˢ (left ×ˢ right)).filter
    (fun v => commonSupportLabel (fullI v.2.1).val (fullJ v.2.2).val = v.1.val)

theorem mem_firstZeroPairs (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) :
    v ∈ firstZeroPairs left right fullI fullJ ↔
      v.2.1 ∈ left ∧ v.2.2 ∈ right ∧
        commonSupportLabel (fullI v.2.1).val (fullJ v.2.2).val = v.1.val := by
  simp only [firstZeroPairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and]
  tauto

theorem firstZeroPairs_projection_injective
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior) :
    Set.InjOn (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => v.2)
      (firstZeroPairs left right fullI fullJ : Set _) := by
  intro v hv w hw he
  have hv' := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hw' := (mem_firstZeroPairs left right fullI fullJ w).mp hw
  apply Prod.ext
  · apply Subtype.ext
    calc
      v.1.val = commonSupportLabel (fullI v.2.1).val (fullJ v.2.2).val := hv'.2.2.symm
      _ = commonSupportLabel (fullI w.2.1).val (fullJ w.2.2).val := by rw [he]
      _ = w.1.val := hw'.2.2
  · exact he

theorem FirstCommonCharacterBlock.mem_iff_label
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) (right : Finset κ)
    (hDE : primeSupport DE.1 = primeSupport DE.2) (i : ι) (j : κ) :
    (i ∈ b.leftColumns left ∧ j ∈ b.rightColumns right ∧
      IsCoprime (b.leftResidual i).val (b.rightResidual j).val) ↔
    (i ∈ left ∧ j ∈ right ∧ commonSupportLabel (fullI i).val (fullJ j).val = DE) := by
  rw [commonSupportLabel_eq_iff _ _ DE.1 DE.2 hDE]
  simp only [FirstCommonCharacterBlock.leftColumns, FirstCommonCharacterBlock.rightColumns,
    Finset.mem_filter, b.left_residual, b.right_residual]
  tauto

/-- The normalized powerful count on the genuine common-support labels.
Forgetting the label is injective because the label is calculated from
the original pair. This wrapper applies to either transform. -/
theorem common_label_powerful_normalized_sum
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ {ι κ : Type*} (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)),
    Set.InjOn factors (left ×ˢ right : Set (ι × κ)) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    ∀ coeff : FirstZeroLabel left right fullI fullJ × (ι × κ) → ℂ,
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) → coeff v = 0) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ, ‖coeff v‖ ≤ Amp / Real.sqrt N) →
    ‖∑ v ∈ firstZeroPairs left right fullI fullJ, coeff v‖ ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨Cbound, hCbound, hcount⟩ :=
    PowerfulDiagonal.powerful_whole_index_normalized_sum (K := K) k ε hε
  refine ⟨Cbound, hCbound, ?_⟩
  intro ι κ left right fullI fullJ factors hinj hfactor N Amp hN hAmp hnorm coeff hzero hcoef
  have hij (v) (hv : v ∈ firstZeroPairs left right fullI fullJ) : v.2 ∈ left ×ˢ right := by
    have hv' := (mem_firstZeroPairs left right fullI fullJ v).mp hv
    exact Finset.mem_product.mpr ⟨hv'.1, hv'.2.1⟩
  apply hcount (firstZeroPairs left right fullI fullJ) (fun v => factors v.2)
    (fun v hv w hw he => firstZeroPairs_projection_injective left right fullI fullJ
      hv hw (hinj (hij v hv) (hij w hw) he)) N Amp coeff hN hAmp
  · intro v hv
    rw [hfactor v.2 (hij v hv)]
    exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1
  · intro v hv
    rw [hfactor v.2 (hij v hv)]
    exact hnorm v.2 (hij v hv)
  · intro v hv hbad
    apply hzero v hv
    simpa only [hfactor v.2 (hij v hv)] using hbad
  · exact hcoef

variable {σ : K →+* ℂ}
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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def firstZeroPairAmplitude
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : ℝ :=
  ‖∑ D ∈ ((blocks v.1).mask M).powerset,
    ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero μv hDiff finiteTest radius D‖

/-- Each original pair is counted at its unique complete common-support label. -/
theorem first_zero_blocks_le_pair_sum
    (C : A.GeneralArithmeticContext σ η hS)
    (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val)
    (profiles : ι → κ → SchwartzMap V ℂ)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
    (cutoff : ℝ) (hcutoff : 1 ≤ cutoff) :
    (∑ DE, ‖((blocks DE).finiteSource hΓ C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤
    ∑ v ∈ firstZeroPairs left right fullI fullJ,
      firstZeroPairAmplitude hΓ μv C left right fullI fullJ blocks profiles hDiff finiteTest radius M v := by
  let amp := firstZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  change _ ≤ ∑ v ∈ firstZeroPairs left right fullI fullJ, amp v
  calc
    _ ≤ ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        amp (DE, (i, j)) := by
      apply Finset.sum_le_sum
      intro DE _
      change ‖∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        ∑ D ∈ ((blocks DE).mask M).powerset,
          ((blocks DE).pair hΓ C profiles i j).transformedZero μv hDiff finiteTest radius D‖ ≤ _
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
            change ‖∑ D ∈ ((blocks DE).mask M).powerset,
              ((blocks DE).pair hΓ C profiles i j).transformedZero μv hDiff finiteTest radius D‖ = 0
            have hz : (∑ D ∈ ((blocks DE).mask M).powerset,
                ((blocks DE).pair hΓ C profiles i j).transformedZero μv hDiff finiteTest radius D) = 0 :=
              Finset.sum_eq_zero (fun D _ =>
                (blocks DE).transformedZero_eq_zero_of_not_coprime hΓ μv C hDiff finiteTest
                  profiles i j radius D hc')
            rw [hz, norm_zero]
        · simp only [hright, if_false, false_and, Finset.sum_const_zero]
      · simp only [hleft, if_false, false_and, Finset.sum_const_zero]

/-- A global normalized first-zero bound. Fixed original seminorms are
selected before all indices and scales. The normalization premise is
pointwise in the original pair and contains only those profile seminorms
and the explicit inverse-norm divisor weight; no Fourier or diagonal
energy inequality is an input. -/
theorem first_zero_diagonal_normalized
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
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
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).finiteSource hΓ C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    first_zero_amplitude_uniform (K := K) (S := A.Sf) (Γ := Γ) μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ := PowerfulDiagonal.powerful_whole_index_normalized_sum
    (K := K) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors hinj hfactor N Amp hN hAmp hnorm hannular hprofile
  let pairs := firstZeroPairs left right fullI fullJ
  let amp := firstZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v :=
    norm_nonneg _
  have hmem (v) (hv : v ∈ pairs) :=
    (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hij (v) (hv : v ∈ pairs) : v.2 ∈ left ×ˢ right :=
    Finset.mem_product.mpr ⟨(hmem v hv).1, (hmem v hv).2.1⟩
  have hblock (v) (hv : v ∈ pairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hfactorinj : Set.InjOn (fun v => factors v.2) (pairs : Set _) := by
    intro v hv w hw he
    exact firstZeroPairs_projection_injective left right fullI fullJ hv hw
      (hinj (hij v hv) (hij w hw) he)
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    change ‖∑ D ∈ ((blocks v.1).mask M).powerset,
      ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ ((blocks v.1).mask M).powerset,
          ‖((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ ((blocks v.1).mask M).powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            firstZeroDivisorWeight radius D := by
        apply Finset.sum_le_sum
        intro D hD
        exact hzero ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2)
          ((blocks v.1).residue_norm_le_one hΓ C profiles _ _)
          (hannular _ (hmem v hv).1 _ (hmem v hv).2.1) hDiff radius D
      _ = C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          ∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ C₀ * (Amp / Real.sqrt N) := mul_le_mul_of_nonneg_left (hprofile v hv) hC₀
      _ = _ := by ring
  have hc := hdiag pairs (fun v => factors v.2) hfactorinj N (C₀ * Amp)
    (fun v => (amp v : ℂ)) hN (mul_nonneg hC₀ hAmp)
    (by intro v hv; rw [hfactor v.2 (hij v hv)]; exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1)
    (by intro v hv; rw [hfactor v.2 (hij v hv)]; exact hnorm v.2 (hij v hv))
    (by
      intro v hv hbad
      have hbad' : ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) := by
        simpa only [hfactor v.2 (hij v hv)] using hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ ((blocks v.1).mask M).powerset,
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ ((blocks v.1).mask M).powerset,
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D _ =>
            (blocks v.1).transformedZero_eq_zero_of_not_powerful hΓ μv C hDiff finiteTest
              left right profiles v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 radius D hbad')
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
      first_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ ≤ Cdiag * (C₀ * Amp) * N ^ ε := hc
    _ ≤ (Cdiag * (1 + C₀)) * Amp * N ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hN) _)
      nlinarith [mul_nonneg hCdiag.le hAmp]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstZeroPairs_projection_injective
#print axioms HeckeSkeleton.Moments.EngineStep.common_label_powerful_normalized_sum
#print axioms HeckeSkeleton.Moments.EngineStep.first_zero_diagonal_normalized

