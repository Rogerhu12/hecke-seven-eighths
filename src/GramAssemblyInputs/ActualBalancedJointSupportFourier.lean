import ActualBalancedJointSeminorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Linarith

/-!
UNCOMPILED / native 0. The support and Fourier bounds concern the same
balanced joint profile used by the literal periodic sum. Constants precede
its compact divisor parameter, frequency, finite S coordinates and radius.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeGeneral.Analysis.ActualBalancedJointSupportFourierDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open ActualBalancedClearedJointDraft ActualBalancedJointSeminormDraft
open ActualJointAnnularAllScaleDraft
open scoped Classical BigOperators ContDiff FourierTransform
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "Z" => SFiniteLocalGroup K S

theorem schwartzSeminorm_le_finset_sup (s : Finset (ℕ × ℕ)) (i : ℕ × ℕ) (hi : i ∈ s)
    (f : SchwartzMap (V × V) ℂ) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f := by
  have h := Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ (V × V) ℂ) hi (x := f)
  exact h

/-- Finite aggregation of the already proved actual composition bounds. -/
theorem exists_balancedJoint_finite_seminorm_bound (M : ℕ) (s : Finset (ℕ × ℕ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ f : SchwartzMap (V × V) ℂ,
        s.sup (schwartzSeminormFamily ℝ W ℂ)
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (balancedJointCoordinateEquiv K S M y) f) ≤
          B * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f := by
  have hb (i : ℕ × ℕ) := exists_balancedJoint_comp_seminorm_bound K S Γ M i.1 i.2
  choose b hbpos hbound using hb
  let B : ℝ := 1 + ∑ i ∈ s, b i
  have hsum : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i _ => (hbpos i).le)
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, hB, fun y hy f => ?_⟩
  have hsup : 0 ≤ s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f := apply_nonneg _ _
  apply Seminorm.finset_sup_apply_le (mul_nonneg hB.le hsup)
  intro i hi
  have hbi : b i ≤ B := by
    have hle : b i ≤ ∑ j ∈ s, b j :=
      Finset.single_le_sum (fun j _ => (hbpos j).le) hi
    dsimp [B]
    linarith
  change SchwartzMap.seminorm ℂ i.1 i.2 _ ≤ _
  calc
    _ ≤ b i * SchwartzMap.seminorm ℂ i.1 i.2 f := hbound i y hy f
    _ ≤ B * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f :=
      mul_le_mul hbi (schwartzSeminorm_le_finset_sup K s i hi f)
        (apply_nonneg _ _) hB.le

/-- The fixed standard Fourier CLM is applied after the actual compact
precomposition. This is not a frequency-dependent Fourier comparison. -/
theorem exists_balancedJoint_fourier_seminorm_bound (M k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ, ∀ f : SchwartzMap (V × V) ℂ,
        SchwartzMap.seminorm ℂ k n
          (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (balancedJointCoordinateEquiv K S M y) f)) ≤
          C * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f := by
  let T : SchwartzMap W ℂ →L[ℝ] SchwartzMap W ℂ := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ (SchwartzMap W ℂ) :=
    (SchwartzMap.seminorm ℝ k n).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ W ℂ).continuous_seminorm (k, n)).comp T.continuous
  obtain ⟨s, D, hD, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ W ℂ) q hq
  obtain ⟨B, hB, hb⟩ := exists_balancedJoint_finite_seminorm_bound K S Γ M s
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hD)
  refine ⟨s, (D : ℝ) * B, mul_pos hDpos hB, fun y hy f => ?_⟩
  have hF0 : ∀ g : SchwartzMap W ℂ, SchwartzMap.seminorm ℂ k n (𝓕 g) ≤
      (D : ℝ) * s.sup (schwartzSeminormFamily ℝ W ℂ) g :=
    fun g => Seminorm.le_def.mp hbound g
  calc
    _ ≤ (D : ℝ) * s.sup (schwartzSeminormFamily ℝ W ℂ) _ := hF0 _
    _ ≤ (D : ℝ) * (B * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f) :=
      mul_le_mul_of_nonneg_left (hb y hy f) hDpos.le
    _ = _ := by ring

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
local notation:max "F" M:max y:max ν:max z₁:max z₂:max φ:max R:max =>
  balancedClearedJointTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport
    M y ν z₁ z₂ φ R

/-- The actual inverse family is bounded on the fixed compact divisor set;
the support radius is chosen before all moving profile parameters. -/
theorem exists_balancedJoint_support_radius (M : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (x : W),
        F M y ν z₁ z₂ φ R x ≠ 0 → ‖x‖ ≤ B := by
  obtain ⟨B₀, hB₀, hsupp⟩ := exists_actualJointAnnularTraceSchwartz_support_radius K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport
  obtain ⟨D, hD, hd⟩ := ((isCompact_sUnitCompactRepresentativeSet K S Γ).image
    (continuous_balancedJointCoordinate_inverseCLM K S M)).isBounded.exists_pos_norm_le
  let T : ℝ := max 1 ‖(traceProductEquiv K).toContinuousLinearMap‖
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D * (T * B₀), by positivity, fun y hy ν z₁ z₂ φ R x hx => ?_⟩
  let e := balancedJointCoordinateEquiv K S M y
  let z : W := (traceProductEquiv K).symm (e x)
  change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R (e x) ≠ 0 at hx
  have hz : actualJointAnnularTraceSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R z ≠ 0 := by
    change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν z₁ z₂ φ R ((traceProductEquiv K) z) ≠ 0
    simpa only [z, ContinuousLinearEquiv.apply_symm_apply] using hx
  have hez : (traceProductEquiv K) z = e x := (traceProductEquiv K).apply_symm_apply _
  have he : ‖e x‖ ≤ T * B₀ := by
    rw [← hez]
    exact ((traceProductEquiv K).toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul (le_max_right _ _) (hsupp ν z₁ z₂ φ R z hz) (norm_nonneg _) hT.le)
  have hinv : ‖e.symm.toContinuousLinearMap‖ ≤ D :=
    hd _ (Set.mem_image_of_mem _ hy)
  calc
    ‖x‖ = ‖e.symm (e x)‖ := by rw [e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ D * (T * B₀) := mul_le_mul hinv he (norm_nonneg _) hD.le

@[simp] theorem balancedJoint_zero (M : ℕ) (y : G) (ν : ℝ) (z₁ z₂ : Z)
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : F M y ν z₁ z₂ φ R 0 = 0 := by
  change sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R ((balancedJointCoordinateEquiv K S M y) 0) = 0
  rw [map_zero]
  have hz := actualJointAnnularTraceSchwartz_zero K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R
  simpa only [actualJointAnnularTraceSchwartz_apply, map_zero] using hz

/-- Actual-profile specialization of the fixed Fourier and compact
composition bounds; no finite-coordinate or frequency is discarded. -/
theorem exists_balancedJoint_profile_fourier_bound (M k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}),
        SchwartzMap.seminorm ℂ k n (𝓕 (F M y ν z₁ z₂ φ R)) ≤
          C * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
            (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
              ψ hψ hψsupport ν z₁ z₂ φ R) := by
  obtain ⟨s, C, hC, hb⟩ := exists_balancedJoint_fourier_seminorm_bound K S Γ M k n
  exact ⟨s, C, hC, fun y hy ν z₁ z₂ φ R => hb y hy _⟩
/-- Both seminorms appearing in the actual min-Poisson bound are
controlled by one finite collection of original unsplit joint seminorms. -/
theorem exists_balancedJoint_Poisson_seminorm_bound (M k : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ y ∈ sUnitCompactRepresentativeSet K S Γ,
      ∀ (ν : ℝ) (z₁ z₂ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}),
        SchwartzMap.seminorm ℂ 0 0 (F M y ν z₁ z₂ φ R) +
          SchwartzMap.seminorm ℂ k 0 (𝓕 (F M y ν z₁ z₂ φ R)) ≤
          C * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
            (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
              ψ hψ hψsupport ν z₁ z₂ φ R) := by
  obtain ⟨B, hB, hb⟩ := exists_balancedJoint_profile_seminorm_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport M 0 0
  obtain ⟨s, D, hD, hd⟩ := exists_balancedJoint_profile_fourier_bound K S Γ
    a ha a0 b0 ha0 haSupport ψ hψ hψsupport M k 0
  refine ⟨insert (0, 0) s, B + D, add_pos hB hD, fun y hy ν z₁ z₂ φ R => ?_⟩
  let f := sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ν z₁ z₂ φ R
  have h0 : SchwartzMap.seminorm ℂ 0 0 f ≤
      (insert (0, 0) s).sup (schwartzSeminormFamily ℝ (V × V) ℂ) f :=
    schwartzSeminorm_le_finset_sup K (insert (0, 0) s) (0, 0) (Finset.mem_insert_self _ _) f
  have hs : s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f ≤
      (insert (0, 0) s).sup (schwartzSeminormFamily ℝ (V × V) ℂ) f :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun i hi => Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hi))
  calc
    _ ≤ B * SchwartzMap.seminorm ℂ 0 0 f +
        D * s.sup (schwartzSeminormFamily ℝ (V × V) ℂ) f :=
      add_le_add (hb y hy ν z₁ z₂ φ R) (hd y hy ν z₁ z₂ φ R)
    _ ≤ B * (insert (0, 0) s).sup (schwartzSeminormFamily ℝ (V × V) ℂ) f +
        D * (insert (0, 0) s).sup (schwartzSeminormFamily ℝ (V × V) ℂ) f :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hB.le) (mul_le_mul_of_nonneg_left hs hD.le)
    _ = _ := by ring
end HeckeGeneral.Analysis.ActualBalancedJointSupportFourierDraft
