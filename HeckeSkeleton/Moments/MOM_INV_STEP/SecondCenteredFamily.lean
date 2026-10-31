import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCompleteColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompleteFamily
import HeckeSkeleton.Moments.MOM_INV_STEP.CenteredMellin

/-!
# Literal second child families at fixed annular centers

The physical source is first restored to a complete sf pool while the
original powered norm test is present. A genuine Mellin integral then
separates the actual product of the fixed common norm and the overlap
norm. The final family uses one center U for every row and label in
the whole product box. Its length, pool and Schwartz cutoff therefore
have no hidden dependence on those moving reconstruction data.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondCenteredFamily

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel SecondCompleteColumns
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def appendResidual (γ : OuterTriple K) (I : Ideal (𝓞 K)) : OuterTriple K :=
  ⟨γ.q0, γ.quotient, γ.residual * I⟩

theorem appendResidual_mask (R n I : Ideal (𝓞 K)) (γ : OuterTriple K) :
    idealCoprimeMask (childPuncture R γ * I) n =
      idealCoprimeMask (childPuncture R (appendResidual K γ I)) n := by
  simp only [idealCoprimeMask, childPuncture, appendResidual, IsCoprime.mul_right_iff,
    isCoprime_radical_right_iff]
  congr 1
  tauto

/-- Every moving label and row uses the same original family, surviving
slot set, background, complete sf pool and fixed-center norm test. -/
def family (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ) :
    ColumnFamily K Sset σ Θ ψ where
  lambda := C.lambda
  background := fun _ => C.background γ₀ * G⁻¹
  background_admissible := fun _ => BackgroundCycle.admissible_mul_inv K Θ ψ
    (C.background γ₀) G (C.background_admissible γ₀) hG
  originalPuncture := C.originalPuncture
  originalSlots := C.originalSlots
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  survivors := fun _ => C.survivors γ₀ \ J
  survivors_subset := fun _ => Finset.sdiff_subset.trans (C.survivors_subset γ₀)
  columns := fun _ => squarefreePool K Sset (2 * U)
  columns_squarefree := fun _ _ hn => squarefreePool_squarefree K Sset hn
  cutoff := fun _ => FinalMellinTests.weightedTest 0 t
  base := C.base
  columnLength := fun _ => Real.log U / Real.log C.base

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def bareCoefficient (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (J : Finset σ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) (n : Ext) : ℂ :=
  CoefficientCycle.canonicalCoefficient K Sset D C.lambda n *
    heckeIdealCoefficient K (C.background γ₀ * G⁻¹) n.val *
    idealCoprimeMask (childPuncture C.originalPuncture γ) n.val.val *
    sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) n y *
    labelRow K Sset D n f ^ 4 *
    divisorMark (C.survivors γ₀ \ J) C.primeLists C.primeWeights n.val.val

theorem column_eq_complete_sum (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (U t : ℝ)
    (hZ : 1 < C.base) (hU : 0 < U) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) :
    column K Sset D (family K S C γ₀ G hG J U t)
      (CanonicalSectors.sectorUnit K Sset Γ) γ f y =
      ∑ n ∈ squarefreePool K Sset (2 * U),
        bareCoefficient K S D Γ C γ₀ G J γ f y n *
          FinalMellinTests.weightedTest 0 t (height K Sset n / U) := by
  unfold column
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [family, bareCoefficient, height, idealCoprimeMask]
  rw [FirstCompleteFamily.norm_scale C.base U hZ hU]

/-- The actual complete second summand is already the literal child
coefficient. Its new row and sector were computed by the two divisors. -/
theorem childTerm_eq (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (J : Finset σ) (g j d₂ v I n : Ext) (ξ : Sector)
    (W : ℝ → ℂ) (X : ℝ) :
    childTerm K S Γ D C.lambda (C.background γ₀ * G⁻¹) g j d₂ v I ξ
      (childPuncture C.originalPuncture γ₀) (C.survivors γ₀) J C.primeLists C.primeWeights
      W X n =
      bareCoefficient K S D Γ C γ₀ G J
        (appendResidual K γ₀ (SecondOverlapColumns.residual K S g d₂).val.val)
        (finalLabel K S j d₂ v).val.val (I.val.val, ξ) n *
          W (height K Sset v * height K Sset n / X) := by
  unfold childTerm bareCoefficient
  rw [appendResidual_mask K, labelRow_exterior, sectorRow_exterior]
  unfold SecondOverlapColumns.forwardCoefficient CanonicalSectorRows.sectorCharacter
  ring

def branch (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (J : Finset σ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector)
    (W : SchwartzMap ℝ ℂ) (τ v X A : ℝ) : ℂ :=
  ∑ n ∈ squarefreePool K Sset (2 * A), bareCoefficient K S D Γ C γ₀ G J γ f y n *
    (W (v * height K Sset n / X) * columnPhase τ (Real.log (height K Sset n)))

/-- The original powered test remains present during pool enlargement.
The numerical factor four is the complete-pool margin, not a hard
window attached to the new Mellin frequency. -/
theorem branch_eq_centered_pool (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (J : Finset σ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (τ v X A U : ℝ) (hv : 0 < v) (hA : 0 < A) (hU : 0 < U)
    (hAU : A ≤ U) (hactual : X = v * A) :
    branch K S D Γ C γ₀ G J γ f y W τ v X A =
      ∑ n ∈ squarefreePool K Sset (2 * U),
        bareCoefficient K S D Γ C γ₀ G J γ f y n *
          (W (v * height K Sset n / X) * columnPhase τ (Real.log (height K Sset n))) := by
  unfold branch
  apply Finset.sum_subset
  · intro n hn
    have hh := (mem_squarefreePool K Sset (2 * A) n).mp hn
    exact (mem_squarefreePool K Sset (2 * U) n).mpr ⟨hh.1, by linarith [hh.2]⟩
  · intro n hn hnot
    have hh := (mem_squarefreePool K Sset (2 * U) n).mp hn
    have hz : W (v * height K Sset n / X) = 0 := by
      by_contra hz
      have hs := hW (subset_closure (Function.mem_support.mpr hz))
      have he : v * height K Sset n / X = height K Sset n / A := by
        rw [hactual]
        field_simp [hv.ne', hA.ne']
      rw [he] at hs
      have hb := (div_le_iff₀ hA).mp hs.2
      apply hnot
      exact (mem_squarefreePool K Sset (2 * A) n).mpr ⟨hh.1, by nlinarith⟩
    rw [hz, zero_mul, mul_zero]

/-- The final child family has one fixed scale and test throughout the
actual g*v box. Only unit scalar phases retain its true norm product. -/
theorem second_branch_centered (C : ColumnFamily K Sset σ Θ ψ) (γ₀ : OuterTriple K)
    (G : HeckeCharacter K) (hG : G ∈ Θ) (J : Finset σ) (γ : OuterTriple K)
    (f : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 / 8 : ℝ) (21 / 8))
    (τ vcenter v X A U : ℝ) (hZ : 1 < C.base)
    (hc : 0 < vcenter) (hA : 0 < A) (hU : 0 < U)
    (hvlo : vcenter ≤ v) (hvhi : v ≤ 4 * vcenter)
    (hactual : X = v * A) (hcenter : X = vcenter * U) :
    branch K S D Γ C γ₀ G J γ f y W τ v X A =
      ∫ t : ℝ, PositiveIntervalMellin.density (1 / 8) (21 / 8)
        (by norm_num) (by norm_num) W hW t * columnPhase t (Real.log v) *
        columnPhase t (-Real.log X) * columnPhase (t + τ) (Real.log U) *
        column K Sset D (family K S C γ₀ G hG J U (t + τ))
          (CanonicalSectors.sectorUnit K Sset Γ) γ f y := by
  have hv : 0 < v := hc.trans_le hvlo
  have hX : 0 < X := by rw [hcenter]; exact mul_pos hc hU
  have hAU : A ≤ U := by
    have hh := mul_le_mul_of_nonneg_right hvlo hA.le
    rw [← hactual, hcenter] at hh
    exact (mul_le_mul_left hc).mp hh
  rw [branch_eq_centered_pool K S D Γ C γ₀ G J γ f y W hW
    τ v X A U hv hA hU hAU hactual]
  have hm := CenteredMellin.finite_source_centered (1 / 8) (21 / 8)
    (by norm_num) (by norm_num) W hW CenteredMellin.finalWindow
    (squarefreePool K Sset (2 * U)) (bareCoefficient K S D Γ C γ₀ G J γ f y)
    (height K Sset) 0 τ v X U hv hX hU (fun n _ => height_pos K Sset n)
    (fun n _ => CenteredMellin.final_cutoff_source W hW vcenter v (height K Sset n) X U
      hc (height_pos K Sset n) hU hvlo hvhi hcenter)
  simp only [Real.rpow_zero, Complex.ofReal_one, one_mul, mul_one] at hm
  refine hm.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [column_eq_complete_sum K S D Γ C γ₀ G hG J U (t + τ) hZ hU γ f y]
    rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondCenteredFamily

end
