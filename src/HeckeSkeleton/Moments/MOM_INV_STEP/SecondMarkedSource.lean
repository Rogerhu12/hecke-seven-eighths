import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSourceColumns
import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorInverseColumn
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Original weights on the fresh inverse source

This is the literal norm cutoff and original prime-mark product from
the first positive inverse column. Computing the fresh common factor
rescales the cutoff exactly and retains its common puncture zero.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondMarkedSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools SecondSourceColumns
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem mask_mul (R A B : Ideal (𝓞 K)) :
    idealCoprimeMask R (A * B) = idealCoprimeMask R A * idealCoprimeMask R B := by
  simp only [idealCoprimeMask, IsCoprime.mul_left_iff]
  by_cases hA : IsCoprime A R <;> by_cases hB : IsCoprime B R <;> simp [hA, hB]

theorem mask_star_self (R A : Ideal (𝓞 K)) :
    star (idealCoprimeMask R A) * idealCoprimeMask R A = idealCoprimeMask R A := by
  unfold idealCoprimeMask
  split_ifs <;> simp

def originalWeight (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K) (x : Ext) : ℂ :=
  idealCoprimeMask (childPuncture C.originalPuncture γ) x.val.val *
    divisorMark (C.survivors γ) C.primeLists C.primeWeights x.val.val *
    C.cutoff γ (height K Sset x / C.base ^ C.columnLength γ)

def residualWeight (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K) (g z : Ext) : ℂ :=
  idealCoprimeMask (childPuncture C.originalPuncture γ * g.val.val) z.val.val *
    divisorMark (C.survivors γ) C.primeLists C.primeWeights (g.val.val * z.val.val) *
    C.cutoff γ (height K Sset z / (C.base ^ C.columnLength γ / height K Sset g))

theorem coefficient_eq (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (j x : Ext) (dk : OS) :
    DivisorInverseColumn.coefficient K S D C γ j.val.val dk x =
      sourceCoefficient K S D (C.background γ) x j dk * originalWeight K S C γ x := by
  unfold DivisorInverseColumn.coefficient FirstCanonicalLabel.inverseCoefficient
  rw [labelRow_exterior]
  unfold sourceCoefficient SecondSourceCharacters.decoration originalWeight
    idealCoprimeMask height
  ring

theorem weight_at_factor (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (g z : Ext) (hc : IsCoprime g.val.val z.val.val) :
    originalWeight K S C γ (exteriorMul K Sset g z) =
      idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val *
        residualWeight K S C γ g z := by
  have hm : idealCoprimeMask
      (childPuncture C.originalPuncture γ * g.val.val) z.val.val =
        idealCoprimeMask (childPuncture C.originalPuncture γ) z.val.val := by
    simp only [idealCoprimeMask, IsCoprime.mul_right_iff, hc.symm, and_true]
  unfold originalWeight residualWeight
  rw [hm, height_mul]
  change idealCoprimeMask (childPuncture C.originalPuncture γ) (g.val.val * z.val.val) *
    divisorMark (C.survivors γ) C.primeLists C.primeWeights (g.val.val * z.val.val) *
    C.cutoff γ (height K Sset g * height K Sset z / C.base ^ C.columnLength γ) = _
  rw [mask_mul]
  have hn : height K Sset g * height K Sset z / C.base ^ C.columnLength γ =
      height K Sset z / (C.base ^ C.columnLength γ / height K Sset g) := by
    rw [div_div_eq_mul_div]
    ring
  rw [hn]
  ring

theorem actual_weight_pair (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (x₁ x₂ : Ext) (hx₁ : Squarefree x₁.val.val) (hx₂ : Squarefree x₂.val.val) :
    star (originalWeight K S C γ x₁) * originalWeight K S C γ x₂ =
      idealCoprimeMask (childPuncture C.originalPuncture γ)
        (ActualInverseFactors.common K Sset x₁ x₂).val.val *
      star (residualWeight K S C γ (ActualInverseFactors.common K Sset x₁ x₂)
        (ActualInverseFactors.residual K Sset x₁ x₂)) *
      residualWeight K S C γ (ActualInverseFactors.common K Sset x₁ x₂)
        (ActualInverseFactors.residual K Sset x₂ x₁) := by
  let g := ActualInverseFactors.common K Sset x₁ x₂
  let z₁ := ActualInverseFactors.residual K Sset x₁ x₂
  let z₂ := ActualInverseFactors.residual K Sset x₂ x₁
  have h₁ : originalWeight K S C γ x₁ =
      idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val *
        residualWeight K S C γ g z₁ := by
    calc
      _ = originalWeight K S C γ (exteriorMul K Sset g z₁) :=
        congrArg (originalWeight K S C γ)
          (ActualInverseFactors.common_mul_residual K Sset x₁ x₂ hx₁).symm
      _ = _ := weight_at_factor K S C γ g z₁
        (ActualInverseFactors.common_residual_coprime K Sset x₁ x₂)
  have h₂ : originalWeight K S C γ x₂ =
      idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val *
        residualWeight K S C γ g z₂ := by
    have he := weight_at_factor K S C γ (ActualInverseFactors.common K Sset x₂ x₁) z₂
      (ActualInverseFactors.common_residual_coprime K Sset x₂ x₁)
    rw [ActualInverseFactors.common_mul_residual K Sset x₂ x₁ hx₂,
      ActualInverseFactors.common_comm K Sset x₂ x₁] at he
    exact he
  rw [h₁, h₂, star_mul]
  calc
    _ = (star (idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val) *
        idealCoprimeMask (childPuncture C.originalPuncture γ) g.val.val) *
      star (residualWeight K S C γ g z₁) * residualWeight K S C γ g z₂ := by ring
    _ = _ := by rw [mask_star_self]

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondMarkedSource

end
