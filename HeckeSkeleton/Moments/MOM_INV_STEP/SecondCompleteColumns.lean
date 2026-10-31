import HeckeSkeleton.Moments.MOM_INV_STEP.SecondCanonicalEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.MellinWeightedTests

/-!
# Complete literal second columns with the original common factor fixed

The actual new Moebius divisor is extracted from each fully extended
residual separately. Its prime marks retain their original weights.
The original common ideal g is not recomputed. The new fourth-power
label kills both the removed divisor and the overlap, so the original
mark lists and complete squarefree quotient pool are restored by exact
equalities before the second positive estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondCompleteColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers SecondOverlapColumns SecondCanonicalEnergy CanonicalNormPools
  CanonicalMarkRestoration CanonicalSectorRows CommonKernel
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
theorem forwardCoefficient_mul (Λ ν : HeckeCharacter K) (v u f I : Ext) (ξ : Sector)
    (hcp : IsCoprime v.val.val u.val.val) :
    forwardCoefficient K S Γ D Λ ν (exteriorMul K Sset v u) f I ξ =
      forwardCoefficient K S Γ D Λ ν v f I ξ *
        forwardCoefficient K S Γ D Λ ν u (exteriorMul K Sset f v) I ξ := by
  have ha := CanonicalGaussCalibration.canonicalCoefficient_mul K S D hallowed Λ v u hcp
  rw [hallowed.reciprocity v u] at ha
  have hν : heckeIdealCoefficient K ν (exteriorMul K Sset v u).val =
      heckeIdealCoefficient K ν v.val * heckeIdealCoefficient K ν u.val :=
    heckeIdealCoefficient_mul K ν v.val u.val
  unfold forwardCoefficient
  rw [ha, hν, generator_mul_character K S D hallowed]
  simp only [sectorCharacter, ThetaGaussCRT.idealSymbol_mul_denominator, mul_pow]
  ring

theorem mask_product (R A B : Ideal (𝓞 K)) :
    idealCoprimeMask R (A * B) = idealCoprimeMask R A * idealCoprimeMask R B := by
  unfold idealCoprimeMask
  rw [IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

def finalLabel (j d₂ v : Ext) : Ext := exteriorMul K Sset (exteriorMul K Sset j d₂) v

/-- The second divisor is removed from the fixed common puncture only
because it is present in the actual new label. -/
theorem remove_divisor_mask (Λ ν : HeckeCharacter K) (g j d₂ v u I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (R : Ideal (𝓞 K)) :
    forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ *
        idealCoprimeMask (R * g.val.val) u.val.val =
      forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ *
        idealCoprimeMask (R * (residual K S g d₂).val.val) u.val.val := by
  by_cases hz : forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ = 0
  · simp only [hz, zero_mul]
  have hc := live_forward_label_coprime K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ hz
  change IsCoprime u.val.val ((j.val.val * d₂.val.val) * v.val.val) at hc
  have hd : IsCoprime u.val.val d₂.val.val := hc.of_mul_right_left.of_mul_right_right
  have hf : g.val.val = d₂.val.val * (residual K S g d₂).val.val :=
    (FirstSourceDecomposition.squarefree_divisor_decomposition g.val d₂.val hg hd₂).1
  rw [hf]
  simp only [idealCoprimeMask, IsCoprime.mul_right_iff, hd, true_and]

theorem extracted_dvd_final (g j d₂ v : Ext) (hg : Squarefree g.val.val)
    (hd₂ : d₂.val.val ∣ g.val.val) (R : Ideal (𝓞 K)) :
    g.val.val * v.val.val ∣
      (R * (residual K S g d₂).val.val) * (finalLabel K S j d₂ v).val.val := by
  have hf : g.val.val = d₂.val.val * (residual K S g d₂).val.val :=
    (FirstSourceDecomposition.squarefree_divisor_decomposition g.val d₂.val hg hd₂).1
  refine ⟨R * j.val.val, ?_⟩
  change R * (residual K S g d₂).val.val * ((j.val.val * d₂.val.val) * v.val.val) =
    (g.val.val * v.val.val) * (R * j.val.val)
  rw [hf]
  ring

variable {σ : Type*} [DecidableEq σ]

theorem restore_mask_and_marks (Λ ν : HeckeCharacter K)
    (g j d₂ v u I : Ext) (ξ : Sector) (hg : Squarefree g.val.val)
    (hd₂ : d₂.val.val ∣ g.val.val) (R : Ideal (𝓞 K))
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p) :
    forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ *
        idealCoprimeMask (R * g.val.val) u.val.val *
        divisorMark slots (residualDivisorLists (g.val.val * v.val.val) lists) a u.val.val =
      forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ *
        idealCoprimeMask (R * (residual K S g d₂).val.val) u.val.val *
        divisorMark slots lists a u.val.val := by
  rw [remove_divisor_mask K S Γ D Λ ν g j d₂ v u I ξ hg hd₂ R]
  exact restore_original_lists K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ _ _
    (extracted_dvd_final K S g j d₂ v hg hd₂ R) slots lists a hprime

def extractedScalar (Λ ν : HeckeCharacter K) (g j d₂ v I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) : ℂ :=
  forwardCoefficient K S Γ D Λ ν v (exteriorMul K Sset j d₂) I ξ *
    idealCoprimeMask (R * g.val.val) v.val.val

def assignedMark (g v : Ext) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (J : Finset σ) : ℂ :=
  divisorMark J lists a (g.val.val * v.val.val)

/-- This is already a literal canonical forward summand: the original
weights and lists, the actual new label, row and common puncture. -/
def childTerm (Λ ν : HeckeCharacter K) (g j d₂ v I : Ext) (ξ : Sector)
    (R : Ideal (𝓞 K)) (slots J : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ) (u : Ext) : ℂ :=
  forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ *
    idealCoprimeMask (R * (residual K S g d₂).val.val) u.val.val *
    divisorMark (slots \ J) lists a u.val.val *
    W (height K Sset v * height K Sset u / X)

include hallowed in
theorem sourceTerm_mul (Λ ν : HeckeCharacter K) (g j d₂ v u I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val)
    (hcp : IsCoprime v.val.val u.val.val) (R : Ideal (𝓞 K))
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (W : ℝ → ℂ) (X : ℝ) :
    sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X (exteriorMul K Sset v u) =
      extractedScalar K S Γ D Λ ν g j d₂ v I ξ R *
        ∑ J ∈ slots.powerset, assignedMark K S g v lists a J *
          childTerm K S Γ D Λ ν g j d₂ v I ξ R slots J lists a W X u := by
  unfold sourceTerm
  rw [forwardCoefficient_mul K S Γ D hallowed Λ ν v u _ I ξ hcp]
  change _ * idealCoprimeMask (R * g.val.val) (v.val.val * u.val.val) *
    divisorMark slots lists a (g.val.val * (v.val.val * u.val.val)) *
    W (((v.val.val * u.val.val).absNorm : ℝ) / X) = _
  rw [mask_product, ← mul_assoc g.val.val, mark_priority _ _ _ _ _ hprime,
    map_mul, Nat.cast_mul]
  unfold extractedScalar assignedMark childTerm height finalLabel
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hh := restore_mask_and_marks K S Γ D Λ ν g j d₂ v u I ξ hg hd₂ R
    (slots \ J) lists a (fun i hi p hp => hprime i (Finset.mem_sdiff.mp hi).1 p hp)
  dsimp only [finalLabel] at hh
  have he := congrArg (fun w : ℂ =>
    (forwardCoefficient K S Γ D Λ ν v (exteriorMul K Sset j d₂) I ξ *
      idealCoprimeMask (R * g.val.val) v.val.val) *
      divisorMark J lists a (g.val.val * v.val.val) *
      (w * W ((v.val.val.absNorm : ℝ) * (u.val.val.absNorm : ℝ) / X))) hh
  convert he using 1 <;> ring

theorem childTerm_zero_non_coprime (Λ ν : HeckeCharacter K)
    (g j d₂ v u I : Ext) (ξ : Sector) (R : Ideal (𝓞 K))
    (slots J : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (W : ℝ → ℂ) (X : ℝ)
    (hbad : ¬IsCoprime v.val.val u.val.val) :
    childTerm K S Γ D Λ ν g j d₂ v I ξ R slots J lists a W X u = 0 := by
  have hz : forwardCoefficient K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ = 0 := by
    by_contra h
    have hc := live_forward_label_coprime K S Γ D Λ ν u (finalLabel K S j d₂ v) I ξ h
    exact hbad hc.of_mul_right_right.symm
  simp only [childTerm, hz, zero_mul]

include hallowed in
/-- The complete quotient expression already vanishes on every
forbidden overlap; no moving coprimality indicator remains. -/
theorem sourceTerm_complete (Λ ν : HeckeCharacter K) (g j d₂ v u I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (R : Ideal (𝓞 K))
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (W : ℝ → ℂ) (X : ℝ) :
    (if IsCoprime v.val.val u.val.val then
      sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X (exteriorMul K Sset v u)
      else 0) =
      extractedScalar K S Γ D Λ ν g j d₂ v I ξ R *
        ∑ J ∈ slots.powerset, assignedMark K S g v lists a J *
          childTerm K S Γ D Λ ν g j d₂ v I ξ R slots J lists a W X u := by
  by_cases hc : IsCoprime v.val.val u.val.val
  · rw [if_pos hc]
    exact sourceTerm_mul K S Γ D hallowed Λ ν g j d₂ v u I ξ hg hd₂ hc R
      slots lists a hprime W X
  · rw [if_neg hc]
    simp only [childTerm_zero_non_coprime K S Γ D Λ ν g j d₂ v u I ξ R
      slots _ lists a W X hc, mul_zero, Finset.sum_const_zero]

include hallowed in
/-- Exact finite reindexing of the actual second positive column,
including all mutual-divisor choices and the complete sf quotient pool. -/
theorem quotient_column_eq (Λ ν : HeckeCharacter K) (g j d₂ v I : Ext) (ξ : Sector)
    (hg : Squarefree g.val.val) (hd₂ : d₂.val.val ∣ g.val.val) (hv : Squarefree v.val.val)
    (R : Ideal (𝓞 K)) (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hprime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p)
    (W : ℝ → ℂ) (X N : ℝ) (P : Ext → ℂ) :
    (∑ z ∈ squarefreePool K Sset N with v.val.val ∣ z.val.val,
      sourceTerm K S Γ D Λ ν g j d₂ I ξ R slots lists a W X z * P z) =
      extractedScalar K S Γ D Λ ν g j d₂ v I ξ R *
        ∑ J ∈ slots.powerset, assignedMark K S g v lists a J *
          ∑ u ∈ squarefreePool K Sset (N / height K Sset v),
            childTerm K S Γ D Λ ν g j d₂ v I ξ R slots J lists a W X u *
              P (exteriorMul K Sset v u) := by
  rw [sum_multiples K Sset v N hv]
  unfold quotientPool
  rw [Finset.sum_filter]
  calc
    _ = ∑ u ∈ squarefreePool K Sset (N / height K Sset v),
        (extractedScalar K S Γ D Λ ν g j d₂ v I ξ R *
          ∑ J ∈ slots.powerset, assignedMark K S g v lists a J *
            childTerm K S Γ D Λ ν g j d₂ v I ξ R slots J lists a W X u) *
          P (exteriorMul K Sset v u) := by
      apply Finset.sum_congr rfl
      intro u hu
      have he := congrArg (fun w : ℂ => w * P (exteriorMul K Sset v u))
        (sourceTerm_complete K S Γ D hallowed Λ ν g j d₂ v u I ξ hg hd₂ R
          slots lists a hprime W X)
      simpa only [ite_mul, zero_mul] using he
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      apply Finset.sum_congr rfl
      intro u hu
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondCompleteColumns

end
