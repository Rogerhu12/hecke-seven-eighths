import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds
import HeckeGeneral.Analysis.IdealMobiusReciprocal

/-!
# The first actual overlap divisor is extracted from the inverse column

The first common-divisor expansion still uses the original marked
canonical source.  This file factors its actual squarefree column
`e * u`, keeping the literal first mask divisor, the old row sector,
the original prime weights and the original norm cutoff.  No identity
of source energies is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstOverlapColumns

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FirstSourceColumns FirstSourceFrozen CanonicalFirstSource CanonicalFirstEnergy
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem normWeight_mul (e u : Ext) :
    normWeight K (exteriorMul K Sset e u).val =
      normWeight K e.val * normWeight K u.val := by
  change (Real.sqrt (((e.val.val * u.val.val).absNorm : ℕ) : ℝ) : ℂ)⁻¹ = _
  rw [Ideal.absNorm_mul, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  simp only [normWeight, Complex.ofReal_mul, mul_inv]

theorem mask_mul (R A B : Ideal (𝓞 K)) :
    (if IsCoprime (A * B) R then (1 : ℂ) else 0) =
      (if IsCoprime A R then 1 else 0) * (if IsCoprime B R then 1 else 0) := by
  rw [IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

/-- This uses the genuine denominator multiplicativity of the ideal
symbol.  The retained first divisor and the original sector stay fixed. -/
theorem fixedSectorCoefficient_mul (ν G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (f z : E) (d : OS) (ξ : Sector)
    (e u : Ext) (hcop : IsCoprime e.val.val u.val.val) :
    fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ
        (exteriorMul K Sset e u) =
      fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ e *
        fixedSectorCoefficient K S D Γ ν G r₁ r₂ b₁ b₂ f z d ξ u := by
  unfold fixedSectorCoefficient fixedMultiplierCoefficient fixedInverseCoefficient
  simp only [ThetaGaussCRT.idealSymbol_mul_denominator, mul_pow, map_mul]
  change _ * (((moebius (e.val.val * u.val.val) : ℂ) *
    heckeIdealCoefficient K ν (e.val * u.val) * heckeIdealCoefficient K G (e.val * u.val)) *
      (_ * (if IsCoprime (e.val.val * u.val.val) _ then 1 else 0)) * _) * _ = _
  rw [hcop.isRelPrime.moebius_mul, Int.cast_mul, heckeIdealCoefficient_mul,
    heckeIdealCoefficient_mul, mask_mul]
  ring

variable {σ : Type*} [DecidableEq σ]

/-- The entire frozen product seen by the original marks. -/
def markBase (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (e : Ext) : Ideal (𝓞 K) :=
  (sourceIdeal K S b₁ b₂ side).val.val ^ 3 *
    (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * e.val.val

def assignedMark (C : CanonicalBlock.ColumnData K S σ)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (e : Ext) (J : Finset σ) : ℂ :=
  divisorMark J C.primeLists C.primeWeights (markBase K S r₁ r₂ b₁ b₂ side e)

/-- The factor extracted before the remaining moving column.  Its
row dependence will be bounded pointwise by its norm. -/
def extractedScalar (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) : ℂ :=
  normWeight K e.val * fixedSectorCoefficient K S D Γ C.background G
    r₁ r₂ b₁ b₂ f z d ξ e *
    (if IsCoprime ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * e.val.val)
      C.puncture then 1 else 0)

/-- Before complete-pool restoration the lists retain their literal
priority deletion.  The cutoff still evaluates the original source norm. -/
def residualTerm (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e : Ext) (J : Finset σ) (u : Ext) : ℂ :=
  normWeight K u.val * fixedSectorCoefficient K S D Γ C.background G
    r₁ r₂ b₁ b₂ f z d ξ u *
    (if IsCoprime u.val.val C.puncture then 1 else 0) *
    divisorMark (C.slots \ J)
      (residualDivisorLists (markBase K S r₁ r₂ b₁ b₂ side e) C.primeLists)
      C.primeWeights u.val.val *
    C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
      (e.val.val.absNorm : ℝ) * (u.val.val.absNorm : ℝ) / C.base ^ C.length)

/-- An exact equality for the actual first positive column, before
any Cauchy inequality or enlargement of its residual domain. -/
theorem movingColumn_mul (C : CanonicalBlock.ColumnData K S σ) (G : HeckeCharacter K)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (f z : E) (d : OS) (ξ : Sector)
    (e u : Ext) (hcop : IsCoprime e.val.val u.val.val)
    (hprime : ∀ i ∈ C.slots, ∀ p ∈ C.primeLists i, Prime p) :
    movingColumn K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ
        (exteriorMul K Sset e u).val =
      extractedScalar K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e *
        ∑ J ∈ C.slots.powerset,
          assignedMark K S C r₁ r₂ b₁ b₂ side e J *
            residualTerm K S D Γ C G r₁ r₂ b₁ b₂ side f z d ξ e J u := by
  have hm : ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val *
      (e.val.val * u.val.val)) * (sourceIdeal K S b₁ b₂ side).val.val ^ 3 =
      markBase K S r₁ r₂ b₁ b₂ side e * u.val.val := by
    unfold markBase
    ring
  have hp : (if IsCoprime ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val *
      (e.val.val * u.val.val)) C.puncture then (1 : ℂ) else 0) =
      (if IsCoprime ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * e.val.val)
        C.puncture then 1 else 0) *
      (if IsCoprime u.val.val C.puncture then 1 else 0) := by
    rw [← mul_assoc, mask_mul]
  rw [movingColumn, extendExterior_val, fixedMarkedInverse,
    normWeight_mul, fixedSectorCoefficient_mul K S D Γ _ _ _ _ _ _ _ _ _ _ e u hcop]
  unfold decoration frozenOriginal
  change _ * (_ * ((if IsCoprime
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * (e.val.val * u.val.val))
      C.puncture then 1 else 0) *
      divisorMark C.slots C.primeLists C.primeWeights
        (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * (e.val.val * u.val.val)) *
          (sourceIdeal K S b₁ b₂ side).val.val ^ 3) *
      C.cutoff (((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val *
        (e.val.val * u.val.val)).absNorm / C.base ^ C.length))) = _
  rw [hp, hm, mark_priority _ _ _ _ _ hprime]
  simp only [Ideal.absNorm_mul, Nat.cast_mul]
  unfold extractedScalar assignedMark residualTerm
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1 <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstOverlapColumns

end
