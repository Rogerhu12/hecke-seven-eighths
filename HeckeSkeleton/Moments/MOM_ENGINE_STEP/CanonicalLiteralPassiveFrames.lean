import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveSource

/-!
# Actual side frames for the passive allocations

The complete smooth carrier already filters each original occurrence
against the fixed bad-prime ideal.  Its product is therefore a genuine
exterior ideal.  The total ideal map below uses that exact product on
the carrier and the unit only outside it.

Each frame uses the allocation already stored in the live passive
label, including its original witness.  The paid characters, individual
weights, quotient scales, Gauss factors and residual log locations are
read from the same table.  No new source identity, nonempty witness or
energy estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveFrames

open CanonicalLiteralProfileCarrier CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)

def smoothColumns : Finset (AllocationColumn K B.keep.card) :=
  childCartesianColumns (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)

theorem columnIdeal_ne_zero (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) : allocationColumnIdeal i ≠ 0 := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hi).1
  exact mul_ne_zero
    (mul_ne_zero (idealCarrier_nonzero _ _ hp.1) (idealCarrier_nonzero _ _ hp.2))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => (i.2 j).ne_bot))

private theorem idealCarrier_coprime
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (hS : ∀ I ∈ S, IsCoprime I.val A.cS)
    (I : Ideal (𝓞 K)) (hI : I ∈ idealCarrier S) : IsCoprime I A.cS := by
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
  exact hS J hJ

theorem columnIdeal_coprime (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) : IsCoprime (allocationColumnIdeal i) A.cS := by
  have hm := Finset.mem_product.mp hi
  have hp := Finset.mem_product.mp hm.1
  have hs := Fintype.mem_piFinset.mp hm.2
  have hleft := idealCarrier_coprime A (W.exteriorSmoothPlain₁ B A)
    (W.exteriorSmoothPlain₁_coprime B A) _ hp.1
  have hright := idealCarrier_coprime A (W.exteriorSmoothPlain₂ B A)
    (W.exteriorSmoothPlain₂_coprime B A) _ hp.2
  simp only [allocationColumnIdeal, IsCoprime.mul_left_iff, IsCoprime.prod_left_iff,
    Finset.mem_univ, forall_const]
  exact ⟨⟨hleft, hright⟩, fun j => W.exteriorSmoothSlots_coprime B A j (i.2 j) (hs j)⟩

/-- The unit outside the finite carrier only makes the map total. -/
def columnExterior (i : AllocationColumn K B.keep.card) : A.Exterior :=
  if hi : i ∈ smoothColumns W B A then
    ⟨allocationColumnIdeal i, columnIdeal_ne_zero W B A i hi,
      Ideal.isCoprime_iff_sup_eq.mp (columnIdeal_coprime W B A i hi)⟩
  else unitExterior A

theorem columnExterior_val_of_mem (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) :
    (columnExterior W B A i).val = allocationColumnIdeal i := by
  simp only [columnExterior, dif_pos hi]

variable (paid : FixedChildCharacters K B.keep.card)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- The frame stores the existing passive allocation verbatim. -/
def frame (firstSign : ℝ) (rectangle : Bool) :
    SecondSideFrame (V := WithLp 2 (ℝ × ℝ)) C R PUnit.{1} side B.keep.card where
  allocation := branch W B A M a
  characters := paid
  phaseCharacter := 1
  dictionary := (table W B A paid).dictionary
    (side.phase PUnit.{1} (1 : (PUnit.{1} × PUnit.{1}) →* Circle)) rectangle
  base_gt_one := (table W B A paid).base_gt_one
  length_pos := (table W B A paid).length_pos
  ideal := columnExterior W B A
  ideal_product i hi := columnExterior_val_of_mem W B A i hi
  gaussScale₁ := (table W B A paid).gauss₁
  gaussScale₂ := (table W B A paid).gauss₂
  gaussSlotScale := (table W B A paid).gaussSlot
  gaussScale₁_pos := (table W B A paid).gauss₁_pos
  gaussScale₂_pos := (table W B A paid).gauss₂_pos
  gaussSlotScale_pos := (table W B A paid).gaussSlot_pos
  leftLocation _ := CanonicalLiteralLocations.plain firstSign
  rightLocation _ := CanonicalLiteralLocations.plain firstSign
  slotLocation _ := CanonicalLiteralLocations.prime firstSign

variable (firstSign : ℝ) (rectangle : Bool)

@[simp] theorem frame_allocation :
    (frame W B A paid C R side M a firstSign rectangle).allocation = branch W B A M a := rfl

@[simp] theorem frame_witness :
    (frame W B A paid C R side M a firstSign rectangle).allocation.witness =
      (branch W B A M a).witness := rfl

@[simp] theorem frame_characters :
    (frame W B A paid C R side M a firstSign rectangle).characters = paid := rfl

@[simp] theorem frame_normalizationScale :
    (frame W B A paid C R side M a firstSign rectangle).normalizationScale =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot :=
  d.allocate_gaussScale B

@[simp] theorem frame_normalizer :
    (frame W B A paid C R side M a firstSign rectangle).normalizer = d.normalizer :=
  table_normalizer W B A paid

@[simp] theorem frame_source_allocation :
    (frame W B A paid C R side M a firstSign rectangle).source.allocation =
      branch W B A M a := by
  cases side <;> rfl

@[simp] theorem frame_source_characters (h : R.live) :
    (frame W B A paid C R side M a firstSign rectangle).source.characters h = paid := by
  cases side <;> rfl

@[simp] theorem frame_source_scale₁ :
    (frame W B A paid C R side M a firstSign rectangle).source.scale₁ =
      d.scale₁ rectangle / idealNorm K (B.plainDivisor 0) := by
  cases side <;> rfl

@[simp] theorem frame_source_scale₂ :
    (frame W B A paid C R side M a firstSign rectangle).source.scale₂ =
      d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)) := by
  cases side <;> rfl

@[simp] theorem frame_source_base :
    (frame W B A paid C R side M a firstSign rectangle).source.base = d.base := by
  cases side <;> rfl

@[simp] theorem frame_source_length (j : Fin B.keep.card) :
    (frame W B A paid C R side M a firstSign rectangle).source.length j =
      d.length (SlotRestriction.index B.keep j) := by
  cases side <;> rfl

@[simp] theorem frame_leftLocation (h : H) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (frame W B A paid C R side M a firstSign rectangle).leftLocation h I =
      CanonicalLiteralLocations.plain firstSign I := rfl

@[simp] theorem frame_rightLocation (h : H) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (frame W B A paid C R side M a firstSign rectangle).rightLocation h I =
      CanonicalLiteralLocations.plain firstSign I := rfl

@[simp] theorem frame_slotLocation (h : H) (j : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (frame W B A paid C R side M a firstSign rectangle).slotLocation h j p =
      CanonicalLiteralLocations.prime firstSign j p := rfl

end CanonicalLiteralPassiveFrames
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.columnIdeal_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.columnIdeal_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame_normalizationScale
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveFrames.frame_source_allocation
