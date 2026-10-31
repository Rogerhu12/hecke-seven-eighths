import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedPoissonZero
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroDiagonal

/-!
# The actual first dual origin without a vanishing-profile assumption

The pure dual-frequency zero has the original complete divisor Fourier
coefficient. Its arithmetic support is therefore the same powerful
product diagonal, independently of the value of the original profile at
zero. Its amplitude is controlled by fixed original Schwartz seminorms
and the genuine norm-dilated divisor radius.

The finite diagonal estimate below counts each original column pair at
its unique common-support label. It retains the same full factor tuple,
mask divisors, profile, and field normalization. The primal-origin term
is kept separately by the signed Poisson identity.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis UniqueFactorizationMonoid MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section Amplitude

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The modulus, original profile, radius and divisor are all chosen
after the fixed seminorms and amplitude constant. No original-origin
vanishing is needed for the pure dual-frequency zero. -/
theorem first_dual_zero_amplitude_uniform
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ p : ParentPeriodicPair K S Γ,
      (∀ x, ‖p.residue x‖ ≤ 1) →
    ∀ hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → HeckeGeneral.Characters.localDifferentExponent K v = 0,
    ∀ (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))),
      ‖p.dualZero μv hDiff finiteTest radius D‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile *
          firstZeroDivisorWeight radius D := by
  obtain ⟨s, C₀, hC₀, hzero⟩ :=
    dual_tensor_zero_seminorm_bound (K := K) (S := S) μv finiteTest
  let H : ℝ := ‖((sUnitHaarCovolume K (S : Set (HeightOneSpectrum (𝓞 K))) Γ).toReal : ℂ)‖
  let J : ℝ := ‖(((2 : ℝ) ^ InfinitePlace.nrComplexPlaces K /
    Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ)‖
  refine ⟨s, H * J * C₀, mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC₀.le, ?_⟩
  intro p hres hDiff radius D
  have hfourier := p.divisorFourier_norm_le_card hres hDiff
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D).val 0
  have hdual := hzero p.profile
  unfold ParentPeriodicPair.dualZero
  simp only [norm_mul]
  calc
    _ ≤ ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * H *
        (‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
          ((Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ) *
            (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul hfourier hdual (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * H *
        ((‖sIntegerMaskPoissonFactor K S p.modulus p.modulus_ne_zero radius
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)‖ *
          (Nat.card ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸ Ideal.span {p.modulus}) : ℝ)) *
          (C₀ * s.sup (schwartzSeminormFamily ℂ (mixedEmbedding.euclidean.mixedSpace K) ℂ) p.profile)) := by ring
    _ = _ := by
      rw [p.poissonFactor_mul_card radius D]
      unfold firstZeroDivisorWeight
      dsimp only [H, J]
      ring

end Amplitude

section Diagonal

variable {A : SArithmeticData K} {ι κ : Type*}

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

/-- A forbidden residual pair remains zero in the pure dual term. -/
theorem FirstCommonCharacterBlock.dualZero_eq_zero_of_not_coprime
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (profiles : ι → κ → SchwartzMap V ℂ) (i : ι) (j : κ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hcop : ¬ IsCoprime (b.leftResidual i).val (b.rightResidual j).val) :
    (b.pair hΓ C profiles i j).dualZero μv hDiff finiteTest radius D = 0 := by
  unfold FirstCommonCharacterBlock.pair
  rw [ParentPeriodicPair.gated_dualZero, if_neg hcop]

/-- The complete divisor Fourier coefficient at zero forces the
original full product to be powerful. This retains every unit sector. -/
theorem FirstCommonCharacterBlock.dualZero_eq_zero_of_not_powerful
    {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (left : Finset ι) (right : Finset κ) (profiles : ι → κ → SchwartzMap V ℂ)
    (i : ι) (hi : i ∈ b.leftColumns left) (j : κ) (hj : j ∈ b.rightColumns right)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hbad : ¬ Powerful ((fullI i).val * (fullJ j).val)) :
    (b.pair hΓ C profiles i j).dualZero μv hDiff finiteTest radius D = 0 := by
  unfold ParentPeriodicPair.dualZero
  rw [b.zeroFourier_eq_zero_of_not_powerful hΓ C hDiff left right profiles i hi j hj
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val hbad]
  simp only [zero_mul, mul_zero]

def firstDualZeroPairAmplitude
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
  ‖∑ D ∈ ((blocks v.1).mask M).powerset,
    ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero μv hDiff finiteTest radius D‖

/-- Each original pair is counted at its unique complete common-support label. -/
theorem first_dual_zero_blocks_le_pair_sum
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
    (∑ DE, ‖((blocks DE).finiteSource hΓ C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤
    ∑ v ∈ firstZeroPairs left right fullI fullJ,
      firstDualZeroPairAmplitude hΓ μv C left right fullI fullJ blocks profiles hDiff finiteTest radius M v := by
  let amp := firstDualZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  change _ ≤ ∑ v ∈ firstZeroPairs left right fullI fullJ, amp v
  calc
    _ ≤ ∑ DE, ∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        amp (DE, (i, j)) := by
      apply Finset.sum_le_sum
      intro DE _
      change ‖∑ i ∈ (blocks DE).leftColumns left, ∑ j ∈ (blocks DE).rightColumns right,
        ∑ D ∈ ((blocks DE).mask M).powerset,
          ((blocks DE).pair hΓ C profiles i j).dualZero μv hDiff finiteTest radius D‖ ≤ _
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
              ((blocks DE).pair hΓ C profiles i j).dualZero μv hDiff finiteTest radius D‖ = 0
            have hz : (∑ D ∈ ((blocks DE).mask M).powerset,
                ((blocks DE).pair hΓ C profiles i j).dualZero μv hDiff finiteTest radius D) = 0 :=
              Finset.sum_eq_zero (fun D _ =>
                (blocks DE).dualZero_eq_zero_of_not_coprime hΓ μv C hDiff finiteTest
                  profiles i j radius D hc')
            rw [hz, norm_zero]
        · simp only [hright, if_false, false_and, Finset.sum_const_zero]
      · simp only [hleft, if_false, false_and, Finset.sum_const_zero]

/-- A global normalized first-zero bound. Fixed original seminorms are
selected before all indices and scales. The normalization premise is
pointwise in the original pair and contains only those profile seminorms
and the explicit inverse-norm divisor weight; no Fourier or diagonal
energy inequality is an input. -/
theorem first_dual_zero_diagonal_normalized
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
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        (∑ D ∈ ((blocks v.1).mask M).powerset, firstZeroDivisorWeight radius D) ≤
          Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).finiteSource hΓ C left right profiles M radius cutoff hcutoff).dualZeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    first_dual_zero_amplitude_uniform (K := K) (S := A.Sf) (Γ := Γ) μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ := PowerfulDiagonal.powerful_whole_index_normalized_sum
    (K := K) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors hinj hfactor N Amp hN hAmp hnorm hprofile
  let pairs := firstZeroPairs left right fullI fullJ
  let amp := firstDualZeroPairAmplitude hΓ μv C left right fullI fullJ
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
  have hfactorinj : Set.InjOn
      (fun v : FirstZeroLabel left right fullI fullJ × (ι × κ) => factors v.2)
      (pairs : Set (FirstZeroLabel left right fullI fullJ × (ι × κ))) := by
    intro v hv w hw he
    exact firstZeroPairs_projection_injective left right fullI fullJ hv hw
      (hinj (Finset.mem_product.mp (hij v hv))
        (Finset.mem_product.mp (hij w hw)) he)
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    change ‖∑ D ∈ ((blocks v.1).mask M).powerset,
      ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ ((blocks v.1).mask M).powerset,
          ‖((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ ((blocks v.1).mask M).powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            firstZeroDivisorWeight radius D := by
        apply Finset.sum_le_sum
        intro D hD
        exact hzero ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2)
          ((blocks v.1).residue_norm_le_one hΓ C profiles _ _)
          hDiff radius D
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
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ ((blocks v.1).mask M).powerset,
          ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D _ =>
            (blocks v.1).dualZero_eq_zero_of_not_powerful hΓ μv C hDiff finiteTest
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
      first_dual_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ ≤ Cdiag * (C₀ * Amp) * N ^ ε := hc
    _ ≤ (Cdiag * (1 + C₀)) * Amp * N ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hN) _)
      nlinarith [mul_nonneg hCdiag.le hAmp]

end Diagonal
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.dualZero_eq_zero_of_not_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.first_dual_zero_amplitude_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.dualZero_eq_zero_of_not_powerful
#print axioms HeckeSkeleton.Moments.EngineStep.first_dual_zero_diagonal_normalized
