import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily
import HeckeSkeleton.Moments.MOM_INV_STEP.CenteredMellin

/-!
# First inverse columns at one fixed annular center

A is the actual residual scale; U is a fixed center for the whole
extracted-product box. The literal source at A is expressed through a
family whose pool, column length and Schwartz test all use U. None of
those fields can vary with an actual extracted ideal, row or label.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredFamily

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools CommonKernel
open FirstCompleteFamily
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

def family (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) : ColumnFamily K Sset σ Θ ψ :=
  { FirstCompleteFamily.family K S C Θ ψ G hν hG J U a t with
    cutoff := fun _ => WideMellinTests.weightedTest a t }

theorem family_squarefree (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) (γ : OuterTriple K) (n : Ext)
    (hn : n ∈ (family K S C Θ ψ G hν hG J U a t).columns γ) :
    Squarefree n.val.val ∧ height K Sset n ≤ 4 * U :=
  FirstCompleteFamily.family_squarefree K S C Θ ψ G hν hG J U a t γ n hn

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem column_eq_complete_sum (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) (hZ : 1 < C.base) (hU : 0 < U)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (y : Ideal (𝓞 K) × Sector) :
    DivisorInverseColumn.column K S Γ D
      (family K S C Θ ψ G hν hG J U a t) γ j d y =
    ∑ n ∈ squarefreePool K Sset (2 * U),
      bareCoefficient K S D Γ C G J γ j d y n *
        WideMellinTests.weightedTest a t (height K Sset n / U) := by
  unfold DivisorInverseColumn.column
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [DivisorInverseColumn.coefficient, FirstCanonicalLabel.inverseCoefficient,
    family, FirstCompleteFamily.family, bareCoefficient, height]
  rw [norm_scale C.base U hZ hU]
  ring

/-- The original W is still present when the actual dyadic pool is
enlarged to the complete pool attached to the fixed center. -/
theorem residualBranch_eq_centered_pool (C : ColumnData K S σ) (G : HeckeCharacter K)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (a τ v X A U : ℝ) (hv : 0 < v) (hA : 0 < A) (hU : 0 < U)
    (hAU : A ≤ U) (hactual : X = v * A) :
    residualBranch K S D Γ C G J γ j d y W a τ v X A =
    ∑ n ∈ squarefreePool K Sset (2 * U),
      bareCoefficient K S D Γ C G J γ j d y n *
        (W (v * height K Sset n / X) * ((height K Sset n ^ a : ℝ) : ℂ) *
          columnPhase τ (Real.log (height K Sset n))) := by
  unfold residualBranch
  apply Finset.sum_subset
  · intro n hn
    have hh := (mem_dyadicPool K Sset A n).mp hn
    exact (mem_squarefreePool K Sset (2 * U) n).mpr ⟨hh.1, by linarith [hh.2.2]⟩
  · intro n hn hnot
    have hh := (mem_squarefreePool K Sset (2 * U) n).mp hn
    have hz : W (v * height K Sset n / X) = 0 := by
      by_contra hz
      have hs := hW (subset_closure (Function.mem_support.mpr hz))
      have he : v * height K Sset n / X = height K Sset n / A := by
        rw [hactual]
        field_simp [hv.ne', hA.ne']
      rw [he] at hs
      apply hnot
      exact (mem_dyadicPool K Sset A n).mpr ⟨hh.1,
        (by simpa only [one_mul] using (le_div_iff₀ hA).mp hs.1),
        (div_le_iff₀ hA).mp hs.2⟩
    rw [hz, zero_mul, zero_mul, mul_zero]

/-- The complete production family uses U, fixed over the whole
v-box. Only unit phases retain the actual extracted product v. -/
theorem first_residual_branch_centered (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (a τ vcenter v X A U : ℝ) (hZ : 1 < C.base)
    (hc : 0 < vcenter) (hA : 0 < A) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ 2 * vcenter)
    (hactual : X = v * A) (hcenter : X = vcenter * U) :
    residualBranch K S D Γ C G J γ j d y W a τ v X A =
      ∫ t : ℝ, MellinSeparation.density W hW t *
        columnPhase t (Real.log v) * columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) *
        DivisorInverseColumn.column K S Γ D
          (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d y := by
  have hv : 0 < v := hc.trans_le hvlo
  have hX : 0 < X := by rw [hcenter]; exact mul_pos hc hU
  have hAU : A ≤ U := by
    have hh := mul_le_mul_of_nonneg_right hvlo hA.le
    rw [← hactual, hcenter] at hh
    exact (mul_le_mul_left hc).mp hh
  rw [residualBranch_eq_centered_pool K S D Γ C G J γ j d y W hW
    a τ v X A U hv hA hU hAU hactual]
  have hm := CenteredMellin.finite_source_centered 1 2 (by norm_num) (by norm_num)
    W hW CenteredMellin.firstWindow (squarefreePool K Sset (2 * U))
    (bareCoefficient K S D Γ C G J γ j d y) (height K Sset)
    a τ v X U hv hX hU (fun n _ => height_pos K Sset n)
    (fun n _ => CenteredMellin.first_cutoff_source W hW vcenter v (height K Sset n) X U
      hc (height_pos K Sset n) hU hvlo hvhi hcenter)
  rw [CenteredMellin.density_eq_standard] at hm
  refine hm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [column_eq_complete_sum K S D Γ C Θ ψ G hν hG J U a (t + τ) hZ hU γ j d y]
    rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredFamily

end

