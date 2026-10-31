import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalBlock
import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn
import HeckeSkeleton.Moments.MOM_INV_STEP.MellinCompleteTests

/-!
# Literal complete intermediate inverse families

The original norm test is retained while its dyadic pool is enlarged.
Only its genuine Mellin integral is then separated. The resulting
family has the original prime lists and individual weights, a fixed
surviving subset, a genuine admissible background, the actual puncture,
and one fixed Schwartz test independent of its row and label.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily

open NumberField IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalBlock CanonicalNormPools
  MellinSchwartz MellinWeightedTests MellinSeparation MellinCompleteTests CommonKernel
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

variable {σ : Type*}

def family (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) : ColumnFamily K Sset σ Θ ψ where
  lambda := C.lambda
  background := fun _ => C.background * G
  background_admissible := fun _ =>
    BackgroundCycle.admissible_mul K Θ ψ C.background G hν hG
  originalPuncture := C.puncture
  originalSlots := C.slots
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  survivors := fun _ => C.slots \ J
  survivors_subset := fun _ => Finset.sdiff_subset
  columns := fun _ => squarefreePool K Sset (2 * U)
  columns_squarefree := fun _ _ hn => squarefreePool_squarefree K Sset hn
  cutoff := fun _ => weightedTest a t
  base := C.base
  columnLength := fun _ => Real.log U / Real.log C.base

theorem norm_scale (Z U : ℝ) (hZ : 1 < Z) (hU : 0 < U) :
    Z ^ (Real.log U / Real.log Z) = U := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hlog : Real.log Z ≠ 0 := (Real.log_pos hZ).ne'
  rw [Real.rpow_def_of_pos hZ0]
  have he : Real.log Z * (Real.log U / Real.log Z) = Real.log U := by
    field_simp [hlog]
  rw [he, Real.exp_log hU]

theorem family_squarefree (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) (γ : OuterTriple K) (n : Ext)
    (hn : n ∈ (family K S C Θ ψ G hν hG J U a t).columns γ) :
    Squarefree n.val.val ∧ height K Sset n ≤ 4 * U := by
  have hh := (mem_squarefreePool K Sset (2 * U) n).mp hn
  exact ⟨hh.1, by linarith [hh.2]⟩

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- All original arithmetic factors, with no Mellin test or norm power
and with the literal first mask divisor still inside the column. -/
def bareCoefficient (C : ColumnData K S σ) (G : HeckeCharacter K)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (n : Ext) : ℂ :=
  (moebius n.val.val : ℂ) * heckeIdealCoefficient K (C.background * G) n.val *
    (if IsCoprime n.val.val (childPuncture C.puncture γ) then 1 else 0) *
    labelRow K Sset D n j ^ 4 *
    divisorMark (C.slots \ J) C.primeLists C.primeWeights n.val.val *
    idealSymbol K Sset D n d *
    star (sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) n y)

theorem column_eq_complete_sum (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (U a t : ℝ) (hZ : 1 < C.base) (hU : 0 < U)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS) (y : Ideal (𝓞 K) × Sector) :
    DivisorInverseColumn.column K S Γ D
      (family K S C Θ ψ G hν hG J U a t) γ j d y =
    ∑ n ∈ squarefreePool K Sset (2 * U),
      bareCoefficient K S D Γ C G J γ j d y n * weightedTest a t (height K Sset n / U) := by
  unfold DivisorInverseColumn.column
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [DivisorInverseColumn.coefficient, FirstCanonicalLabel.inverseCoefficient,
    family, bareCoefficient, height]
  rw [norm_scale C.base U hZ hU]
  ring

def residualBranch (C : ColumnData K S σ) (G : HeckeCharacter K)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (W : SchwartzMap ℝ ℂ)
    (a τ v X U : ℝ) : ℂ :=
  ∑ n ∈ dyadicPool K Sset U, bareCoefficient K S D Γ C G J γ j d y n *
    (W (v * height K Sset n / X) * ((height K Sset n ^ a : ℝ) : ℂ) *
      columnPhase τ (Real.log (height K Sset n)))

/-- Extend the original source before applying Mellin, retaining W.
This is an equality of complete finite sources, not of frequency slices. -/
theorem residualBranch_eq_complete (C : ColumnData K S σ) (G : HeckeCharacter K)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (a τ v X U : ℝ) (hv : 0 < v) (hU : 0 < U) (hscale : X = v * U) :
    residualBranch K S D Γ C G J γ j d y W a τ v X U =
    ∑ n ∈ squarefreePool K Sset (2 * U),
      bareCoefficient K S D Γ C G J γ j d y n *
        (W (v * height K Sset n / X) * ((height K Sset n ^ a : ℝ) : ℂ) *
          columnPhase τ (Real.log (height K Sset n))) := by
  unfold residualBranch
  apply Finset.sum_subset
  · intro n hn
    have hh := (mem_dyadicPool K Sset U n).mp hn
    exact (mem_squarefreePool K Sset (2 * U) n).mpr ⟨hh.1, by linarith [hh.2.2]⟩
  · intro n hn hnot
    have hh := (mem_squarefreePool K Sset (2 * U) n).mp hn
    have hzero : W (v * height K Sset n / X) = 0 := by
      by_contra hz
      have hs := hW (subset_closure (Function.mem_support.mpr hz))
      have hratio : v * height K Sset n / X = height K Sset n / U := by
        rw [hscale]
        field_simp [hv.ne', hU.ne']
      rw [hratio] at hs
      apply hnot
      exact (mem_dyadicPool K Sset U n).mpr ⟨hh.1,
        (by simpa only [one_mul] using (le_div_iff₀ hU).mp hs.1),
        (div_le_iff₀ hU).mp hs.2⟩
    rw [hzero, zero_mul, zero_mul, mul_zero]

/-- The actual first residual branch is the genuine Mellin integral of
a literal retained-divisor inverse column with a complete sf pool. -/
theorem first_residual_branch_complete (C : ColumnData K S σ)
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ C.background) (hG : G ∈ Θ)
    (J : Finset σ) (γ : OuterTriple K) (j : Ideal (𝓞 K)) (d : OS)
    (y : Ideal (𝓞 K) × Sector) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (a τ v X U : ℝ) (hZ : 1 < C.base) (hv : 0 < v) (hU : 0 < U)
    (hscale : X = v * U) :
    residualBranch K S D Γ C G J γ j d y W a τ v X U =
      ∫ t : ℝ, density W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) *
        (((U ^ a : ℝ) : ℂ) * columnPhase (t + τ) (Real.log U)) *
        DivisorInverseColumn.column K S Γ D
          (family K S C Θ ψ G hν hG J U a (t + τ)) γ j d y := by
  rw [residualBranch_eq_complete K S D Γ C G J γ j d y W hW a τ v X U hv hU hscale]
  have hm := finite_source_complete (squarefreePool K Sset (2 * U))
    (bareCoefficient K S D Γ C G J γ j d y) (height K Sset)
    W hW a τ v X U hv hU hscale (fun n _ => height_pos K Sset n)
  refine hm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [column_eq_complete_sum K S D Γ C Θ ψ G hν hG J U a (t + τ) hZ hU γ j d y]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily

end

