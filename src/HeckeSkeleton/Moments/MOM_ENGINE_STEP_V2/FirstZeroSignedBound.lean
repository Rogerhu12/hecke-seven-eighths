module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDualZeroSupport
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonFirstOrigin

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: the supported powerful bound for the actual signed first zero

The first source uses its literal `transformedZero`, including the
original-origin subtraction. The complete mask sum is performed before
bounding that origin: it is either the unmasked origin or zero. Thus the
origin needs its point-evaluation seminorm but no mask-cardinality loss.

The original powerful-product count and unique common-support labels are
unchanged. Its norm window is required only for nonzero profiles, so the
actual Cartesian union of the two centered rectangles is retained. Both
normalization premises concern individual original profiles; neither is
an assumed Fourier estimate or a terminal bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis UniqueFactorizationMonoid MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
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

/-- The finite orders and both constants precede the original pair,
its modulus, radius and mask. The origin is summed exactly first. -/
private theorem first_signed_zero_pair_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cdual Corigin : ℝ,
      0 ≤ Cdual ∧ 0 ≤ Corigin ∧
    ∀ p : ParentPeriodicPair K A.Sf Γ,
      (∀ x, ‖p.residue x‖ ≤ 1) →
    ∀ hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0,
    ∀ (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)),
      ‖∑ D ∈ M.powerset, p.transformedZero μv hDiff finiteTest radius D‖ ≤
        Cdual * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
          ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) +
        Corigin * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile := by
  obtain ⟨s, Cdual, hCdual, hdual⟩ :=
    first_dual_zero_amplitude_uniform (K := K) (S := A.Sf) (Γ := Γ) μv finiteTest
  let seminorms := insert (0, 0) s
  let H : ℝ :=
    ‖((sUnitHaarCovolume K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖
  let B : ℝ := ‖∏ v ∈ A.Sf, finiteTest v 0‖
  have hH : 0 ≤ H := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hs (φ : SchwartzMap V ℂ) :
      s.sup (schwartzSeminormFamily ℂ V ℂ) φ ≤
        seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert (0, 0) s)) φ
  have heval (φ : SchwartzMap V ℂ) :
      ‖φ 0‖ ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ) φ :=
    (SchwartzMap.norm_le_seminorm ℂ φ 0).trans
      (by
        simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily ℂ V ℂ) (x := φ)
            (Finset.mem_insert_self (0, 0) s)))
  refine ⟨seminorms, Cdual, H * B, hCdual, mul_nonneg hH hB, ?_⟩
  intro p hres hDiff radius M
  have hpoint (D : Finset (HeightOneSpectrum A.R)) :
      ‖p.dualZero μv hDiff finiteTest radius D‖ ≤
        Cdual * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
          firstZeroDivisorWeight radius D :=
    (hdual p hres hDiff radius D).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hs p.profile) hCdual)
        (firstZeroDivisorWeight_nonneg radius D))
  have hdualsum :
      ‖∑ D ∈ M.powerset, p.dualZero μv hDiff finiteTest radius D‖ ≤
        Cdual * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
          ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := by
    calc
      _ ≤ ∑ D ∈ M.powerset, ‖p.dualZero μv hDiff finiteTest radius D‖ :=
        norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          Cdual * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile *
            firstZeroDivisorWeight radius D :=
        Finset.sum_le_sum (fun D _ => hpoint D)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have horiginEmpty : ‖p.originZero finiteTest ∅‖ ≤
      (H * B) * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile := by
    rw [p.originZero_empty]
    simp only [sIntegerTensorTerm, map_zero, traceSchwartzToMixed_apply, norm_mul]
    change H * (‖p.residue 0‖ * (‖p.profile 0‖ * B)) ≤ _
    calc
      _ ≤ H * (1 * (‖p.profile 0‖ * B)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hres 0) (mul_nonneg (norm_nonneg _) hB)) hH
      _ = H * (‖p.profile 0‖ * B) := by rw [one_mul]
      _ ≤ H * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (heval p.profile) hB) hH
      _ = _ := by ring
  have horigin : ‖∑ D ∈ M.powerset, p.originZero finiteTest D‖ ≤
      (H * B) * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) p.profile := by
    rw [p.sum_originZero_powerset, origin_mask_zero]
    by_cases hM : M = ∅
    · simpa only [if_pos hM, one_mul] using horiginEmpty
    · simp only [if_neg hM, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hH hB) (apply_nonneg _ _)
  have hsplit :
      (∑ D ∈ M.powerset, p.transformedZero μv hDiff finiteTest radius D) =
        (∑ D ∈ M.powerset, p.dualZero μv hDiff finiteTest radius D) -
          ∑ D ∈ M.powerset, p.originZero finiteTest D := by
    simp only [ParentPeriodicPair.transformedZero_eq_dual_sub_origin,
      Finset.sum_sub_distrib]
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add hdualsum horigin)

/-- The actual first signed zero has a uniform powerful-diagonal bound.
The same scalar amplitude separately controls the dual divisor-weighted
profile and the original-origin profile. All fixed data are selected
before the moving source, and zero profiles need no product-norm bound. -/
theorem first_signed_zero_diagonal_supported
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)),
    Set.InjOn factors (left ×ˢ right : Set (ι × κ)) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 →
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          Amp / Real.sqrt N) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) ≤
        Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).finiteSource hΓ C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨seminorms, Cdual, Corigin, hCdual, hCorigin, hpair⟩ :=
    first_signed_zero_pair_amplitude_uniform (A := A) (Γ := Γ) μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    PowerfulDiagonal.powerful_whole_index_normalized_sum (K := K) k ε hε
  let Camp := Cdual + Corigin
  have hCamp : 0 ≤ Camp := add_nonneg hCdual hCorigin
  refine ⟨seminorms, Cdiag * (1 + Camp), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors hinj hfactor N Amp hN hAmp hnorm hprofile horigin
  let allPairs := firstZeroPairs left right fullI fullJ
  let pairs := allPairs.filter (fun v => profiles v.2.1 v.2.2 ≠ 0)
  let amp := firstZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v :=
    norm_nonneg _
  have hall (v) (hv : v ∈ pairs) : v ∈ firstZeroPairs left right fullI fullJ :=
    (Finset.mem_filter.mp hv).1
  have hmem (v) (hv : v ∈ pairs) :=
    (mem_firstZeroPairs left right fullI fullJ v).mp (hall v hv)
  have hij (v) (hv : v ∈ pairs) : v.2 ∈ left ×ˢ right :=
    Finset.mem_product.mpr ⟨(hmem v hv).1, (hmem v hv).2.1⟩
  have hblock (v) (hv : v ∈ pairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hfactorinj : Set.InjOn
      (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => factors v.2)
      (pairs : Set (FirstZeroLabel left right fullI fullJ × (ι × κ))) := by
    intro v hv w hw he
    exact firstZeroPairs_projection_injective left right fullI fullJ (hall v hv) (hall w hw)
      (hinj (Finset.mem_product.mp (hij v hv))
        (Finset.mem_product.mp (hij w hw)) he)
  have hpoint (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) :
      amp v ≤
        Cdual * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          ∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) +
        Corigin * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) :=
    hpair ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2)
      ((blocks v.1).residue_norm_le_one hΓ C profiles _ _)
      hDiff radius ((blocks v.1).mask M)
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (Camp * Amp) / Real.sqrt N := by
    calc
      _ ≤ Cdual *
          (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            ∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) +
          Corigin * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) :=
        hpoint v
      _ ≤ Cdual * (Amp / Real.sqrt N) + Corigin * (Amp / Real.sqrt N) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hprofile v (hall v hv)) hCdual)
          (mul_le_mul_of_nonneg_left (horigin v (hall v hv)) hCorigin)
      _ = _ := by dsimp only [Camp]; ring
  have hc := hdiag pairs (fun v => factors v.2) hfactorinj N (Camp * Amp)
    (fun v => (amp v : ℂ)) hN (mul_nonneg hCamp hAmp)
    (by
      intro v hv
      rw [hfactor v.2 (hij v hv)]
      exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1)
    (by
      intro v hv
      rw [hfactor v.2 (hij v hv)]
      exact hnorm v.2 (hij v hv) (Finset.mem_filter.mp hv).2)
    (by
      intro v hv hbad
      have hbad' : ¬ Powerful ((fullI v.2.1).val * (fullJ v.2.2).val) := by
        simpa only [hfactor v.2 (hij v hv)] using hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ ((blocks v.1).mask M).powerset,
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ ((blocks v.1).mask M).powerset,
            ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).transformedZero
              μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D _ =>
            (blocks v.1).transformedZero_eq_zero_of_not_powerful hΓ μv C hDiff finiteTest
              left right profiles v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 radius D hbad')
        rw [he, norm_zero]
      rw [hz, Complex.ofReal_zero])
    (by
      intro v hv
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hampnonneg v)] using
        hcoef v hv)
  have hvanish (v : FirstZeroLabel left right fullI fullJ × (ι × κ))
      (hφ : profiles v.2.1 v.2.2 = 0) : amp v = 0 := by
    have hb := hpoint v
    simp only [hφ, map_zero, zero_mul, mul_zero, add_zero] at hb
    exact le_antisymm hb (hampnonneg v)
  have hrestrict : (∑ v ∈ allPairs, amp v) = ∑ v ∈ pairs, amp v := by
    dsimp only [pairs]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hφ : profiles v.2.1 v.2.2 = 0
    · rw [if_neg (fun hne => hne hφ)]
      exact hvanish v hφ
    · rw [if_pos hφ]
  have hreal : ‖∑ v ∈ pairs, (amp v : ℂ)‖ = ∑ v ∈ pairs, amp v := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun v _ => hampnonneg v))
  rw [hreal] at hc
  calc
    _ ≤ ∑ v ∈ allPairs, amp v :=
      first_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ = ∑ v ∈ pairs, amp v := hrestrict
    _ ≤ Cdiag * (Camp * Amp) * N ^ ε := hc
    _ ≤ (Cdiag * (1 + Camp)) * Amp * N ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hN) _)
      nlinarith [mul_nonneg hCdiag.le hAmp]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.first_signed_zero_diagonal_supported
