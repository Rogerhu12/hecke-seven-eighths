import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualZeroSupport

/-!
# The first pure-dual zero counts only nonzero original profiles

The whole original source, common blocks and column carrier are retained.
Only the finite powerful-product count is restricted internally to the
pairs whose actual original profile is nonzero. The discarded dual-zero
amplitudes vanish by their fixed seminorm bound, so the original full
terminal sum is recovered exactly.

This separates the sharp zero product window from the coarse Cartesian
union window used by the tail. In a centered coefficient the two original
comparison rectangles have the same total scale, whereas the Cartesian
union also contains cross combinations whose coefficient is zero. No
change to the source, first divisors or chosen child family is needed.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

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

/-- A sharp product-norm window is required only when the original
profile is nonzero. All source and normalization arguments, and the
placement of the fixed constants, agree with the unrestricted theorem. -/
theorem first_dual_zero_diagonal_supported
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
    (∀ ij ∈ left ×ˢ right, profiles ij.1 ij.2 ≠ 0 →
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
  let allPairs := firstZeroPairs left right fullI fullJ
  let pairs := allPairs.filter (fun v => profiles v.2.1 v.2.2 ≠ 0)
  let amp := firstDualZeroPairAmplitude hΓ μv C left right fullI fullJ
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
      _ ≤ C₀ * (Amp / Real.sqrt N) := mul_le_mul_of_nonneg_left (hprofile v (hall v hv)) hC₀
      _ = _ := by ring
  have hc := hdiag pairs (fun v => factors v.2) hfactorinj N (C₀ * Amp)
    (fun v => (amp v : ℂ)) hN (mul_nonneg hC₀ hAmp)
    (by intro v hv; rw [hfactor v.2 (hij v hv)]; exact mul_ne_zero (fullI v.2.1).property.1 (fullJ v.2.2).property.1)
    (by intro v hv; rw [hfactor v.2 (hij v hv)]; exact hnorm v.2 (hij v hv) (Finset.mem_filter.mp hv).2)
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
  have hvanish (v : FirstZeroLabel left right fullI fullJ × (ι × κ))
      (hφ : profiles v.2.1 v.2.2 = 0) : amp v = 0 := by
    change ‖∑ D ∈ ((blocks v.1).mask M).powerset,
      ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero μv hDiff finiteTest radius D‖ = 0
    apply norm_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro D _
    have hb := hzero ((blocks v.1).pair hΓ C profiles v.2.1 v.2.2)
      ((blocks v.1).residue_norm_le_one hΓ C profiles _ _) hDiff radius D
    change ‖((blocks v.1).pair hΓ C profiles v.2.1 v.2.2).dualZero
      μv hDiff finiteTest radius D‖ ≤
        C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          firstZeroDivisorWeight radius D at hb
    rw [hφ, map_zero, mul_zero, zero_mul] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
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
      first_dual_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ = ∑ v ∈ pairs, amp v := hrestrict
    _ ≤ Cdiag * (C₀ * Amp) * N ^ ε := hc
    _ ≤ (Cdiag * (1 + C₀)) * Amp * N ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hN) _)
      nlinarith [mul_nonneg hCdiag.le hAmp]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_dual_zero_diagonal_supported
