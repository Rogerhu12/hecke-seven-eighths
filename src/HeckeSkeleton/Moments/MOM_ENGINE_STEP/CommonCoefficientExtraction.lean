import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CommonScalarReweight
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorIdentification

/-!
# The original factor dictionaries extract the actual common atoms

The complete common character has already entered the genuine local
correlation.  Thus the common coefficient is extracted from the bare
original atoms, while the residual ideal alone is evaluated at the
actual frequency.  In particular a common ramification zero is never
multiplied into the column a second time.

Every reconstruction below is the actual occurrence-support branch.
Both rectangles of a centered coefficient have the same extracted
scalar.  The extra original Gauss normalizer is retained separately.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.Support

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {k : ℕ}

/-- Evaluation at one is used only for an actual exterior ideal. -/
theorem actualIdealResidue_frequency_one (I : A.Exterior) :
    actualIdealResidue (A := A) (σ := σ) I.val (1 : A.R) = 1 := by
  rw [actualIdealResidue_exterior]
  change σ ((MulChar.ofUnitHom _) (Ideal.Quotient.mk _ (1 : A.R))) = 1
  rw [map_one, map_one, map_one]

private theorem bare_plain_extract
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (N : ℝ)
    (B I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    (Real.sqrt N : ℂ)⁻¹ * (sourcePlainCoefficient χ θ M (B * I) * w (B * I)) =
      ((Real.sqrt (idealNorm F B) : ℂ)⁻¹ * sourcePlainCoefficient χ θ M B) *
        ((Real.sqrt (N / idealNorm F B) : ℂ)⁻¹ *
          (sourcePlainCoefficient χ θ M I * w (B * I))) := by
  have hB : (Real.sqrt (idealNorm F B) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (idealNorm_pos F B)).ne'
  have hn : (Real.sqrt N : ℂ)⁻¹ =
      (Real.sqrt (idealNorm F B) : ℂ)⁻¹ *
        (Real.sqrt (N / idealNorm F B) : ℂ)⁻¹ := by
    rw [Real.sqrt_div' N (idealNorm_pos F B).le, Complex.ofReal_div,
      inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  rw [sourcePlainCoefficient_mul, hn]
  ring

namespace FixedChildCharacters

/-- The actual frozen Hecke coefficients and their original central
factors.  The already extracted common character does not occur here. -/
def bareFrozenScalar (T : FixedChildCharacters F k)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) : ℂ :=
  ((Real.sqrt (idealNorm F B₁) : ℂ)⁻¹ *
      sourcePlainCoefficient T.plain T.plainTwist T.mask B₁) *
    ((Real.sqrt (idealNorm F B₂) : ℂ)⁻¹ *
      sourcePlainCoefficient T.plain T.plainTwist T.mask B₂) *
    ∏ i ∈ Finset.univ.filter (fun i => i ∉ keep),
      (Real.sqrt (Z ^ length i) : ℂ)⁻¹ *
        (sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (frozen i) *
          w i (frozen i))

theorem frozenScalar_eq_bare_mul_residue (T : FixedChildCharacters F k)
    (g h : A.R) (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) :
    T.frozenScalar (σ := σ) g h B₁ B₂ Z length keep frozen w =
      T.bareFrozenScalar B₁ B₂ Z length keep frozen w *
        actualIdealResidue (A := A) (σ := σ)
          (frozenSourceIdeal B₁ B₂ keep frozen) (g * h) := by
  simp only [frozenScalar, bareFrozenScalar, sourcePlainFrozen, sourcePrimeTerm,
    frozenSourceIdeal, actualIdealResidue_ideal_mul, actualIdealResidue_prod,
    Finset.sdiff_eq_filter, Finset.mem_univ, true_and, Finset.prod_mul_distrib]
  ring

theorem frozenScalar_one_eq_bare (T : FixedChildCharacters F k)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (I : A.Exterior) (hI : frozenSourceIdeal B₁ B₂ keep frozen = I.val) :
    T.frozenScalar (σ := σ) (1 : A.R) 1 B₁ B₂ Z length keep frozen w =
      T.bareFrozenScalar B₁ B₂ Z length keep frozen w := by
  rw [frozenScalar_eq_bare_mul_residue, one_mul, hI,
    actualIdealResidue_frequency_one, mul_one]

/-- This is a coefficient identity from individual multiplicativity,
before any Fourier transform or absolute value. -/
theorem bareCoefficient_extract (T : FixedChildCharacters F k)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) ×
      (Fin keep.card → HeightOneSpectrum (𝓞 F))) :
    T.bareCoefficient N₁ N₂ Z length w₁ w₂ w
      ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2) =
      T.bareFrozenScalar B₁ B₂ Z length keep frozen w *
        (T.restrictSlots keep).bareCoefficient
          (N₁ / idealNorm F B₁) (N₂ / idealNorm F B₂) Z
          (fun j => length (SlotRestriction.index keep j))
          (fun I => w₁ (B₁ * I)) (fun I => w₂ (B₂ * I))
          (fun j => w (SlotRestriction.index keep j)) y := by
  simp only [bareCoefficient, childCartesianCoefficient]
  rw [bare_plain_extract, bare_plain_extract,
    SlotRestriction.product_extend keep frozen y.2
      (fun i p => (Real.sqrt (Z ^ length i) : ℂ)⁻¹ *
        (sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p * w i p))]
  simp only [bareFrozenScalar, restrictSlots]
  ring

end FixedChildCharacters

namespace SupportCartesianBranch

variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {P : Finset (Ideal (𝓞 F))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

private theorem residual_plain_nonzero
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns) :
    y.1.1 ≠ 0 ∧ y.1.2 ≠ 0 := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hy).1
  constructor
  · obtain ⟨I, _, he⟩ := Finset.mem_image.mp hp.1
    exact he ▸ supportResidual_ne_zero I P
  · obtain ⟨I, _, he⟩ := Finset.mem_image.mp hp.2
    exact he ▸ supportResidual_ne_zero I P

def bareCommonScalar (T : FixedChildCharacters F k)
    (Z : ℝ) (length : Fin k → ℝ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) : ℂ :=
  T.bareFrozenScalar b.plainDivisor₁ b.plainDivisor₂
    Z length b.keep b.witness.2 w

def bareResidualCoefficient (T : FixedChildCharacters F k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) :
    AllocationColumn F b.keep.card → ℂ :=
  rawBareSourceCoefficient (T.restrictSlots b.keep)
    (N₁ / idealNorm F b.plainDivisor₁) (N₂ / idealNorm F b.plainDivisor₂)
    Z (fun j => length (SlotRestriction.index b.keep j))
    (fun I => w₁ (b.plainDivisor₁ * I)) (fun I => w₂ (b.plainDivisor₂ * I))
    (fun j => w (SlotRestriction.index b.keep j))

def residualCoefficient (T : FixedChildCharacters F k) (frequency : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) :
    AllocationColumn F b.keep.card → ℂ :=
  rawSourceCoefficient (σ := σ) (T.restrictSlots b.keep) 1 frequency
    (N₁ / idealNorm F b.plainDivisor₁) (N₂ / idealNorm F b.plainDivisor₂)
    Z (fun j => length (SlotRestriction.index b.keep j))
    (fun I => w₁ (b.plainDivisor₁ * I)) (fun I => w₂ (b.plainDivisor₂ * I))
    (fun j => w (SlotRestriction.index b.keep j))

theorem raw_bare_extract (T : FixedChildCharacters F k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns) :
    rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w (b.reconstruct y) =
      b.bareCommonScalar T Z length w *
        b.bareResidualCoefficient T N₁ N₂ Z length w₁ w₂ w y := by
  have hn := b.residual_plain_nonzero y hy
  have h₁ : sourceMomentIdeal (b.plainExtract₁ * y.1.1) =
      b.plainDivisor₁ * sourceMomentIdeal y.1.1 := by
    change sourceMomentIdeal (b.plainDivisor₁.val * y.1.1) =
      b.plainDivisor₁ * sourceMomentIdeal y.1.1
    simpa only [sourceMomentIdeal_val_of_ne_zero y.1.1 hn.1] using
      sourceMomentIdeal_mul_val b.plainDivisor₁ (sourceMomentIdeal y.1.1)
  have h₂ : sourceMomentIdeal (b.plainExtract₂ * y.1.2) =
      b.plainDivisor₂ * sourceMomentIdeal y.1.2 := by
    change sourceMomentIdeal (b.plainDivisor₂.val * y.1.2) =
      b.plainDivisor₂ * sourceMomentIdeal y.1.2
    simpa only [sourceMomentIdeal_val_of_ne_zero y.1.2 hn.2] using
      sourceMomentIdeal_mul_val b.plainDivisor₂ (sourceMomentIdeal y.1.2)
  simp only [rawBareSourceCoefficient, reconstruct, h₁, h₂, bareCommonScalar,
    bareResidualCoefficient]
  exact T.bareCoefficient_extract b.plainDivisor₁ b.plainDivisor₂
    N₁ N₂ Z length b.keep b.witness.2 w₁ w₂ w
    ((sourceMomentIdeal y.1.1, sourceMomentIdeal y.1.2), y.2)

/-- Only the residual exterior ideal is evaluated at the actual
frequency.  The common residue is already in the full correlation. -/
theorem raw_coefficient_residue_extract (T : FixedChildCharacters F k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns)
    (J : A.Exterior) (hJ : J.val = allocationColumnIdeal y) (frequency : A.R) :
    rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w (b.reconstruct y) *
        σ (A.sexticResidue J frequency) =
      b.bareCommonScalar T Z length w *
        b.residualCoefficient (σ := σ) T frequency N₁ N₂ Z length w₁ w₂ w y := by
  rw [b.raw_bare_extract T N₁ N₂ Z length w₁ w₂ w y hy]
  unfold residualCoefficient
  rw [raw_source_coefficient_eq_bare_mul_residue _ 1 frequency _ _ _ _ _ _ _ y J hJ,
    one_mul]
  unfold bareResidualCoefficient
  ring

/-- The subtraction is retained until after the same common scalar has
been extracted from both actual rectangles. -/
theorem raw_centered_residue_extract (T : FixedChildCharacters F k)
    (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns)
    (J : A.Exterior) (hJ : J.val = allocationColumnIdeal y) (frequency : A.R) :
    (rawBareSourceCoefficient T X₁ X₂ Z length w₁ w₂ w (b.reconstruct y) -
      rawBareSourceCoefficient T Y₁ Y₂ Z length v₁ v₂ w (b.reconstruct y)) *
        σ (A.sexticResidue J frequency) =
      b.bareCommonScalar T Z length w *
        (b.residualCoefficient (σ := σ) T frequency X₁ X₂ Z length w₁ w₂ w y -
          b.residualCoefficient (σ := σ) T frequency Y₁ Y₂ Z length v₁ v₂ w y) := by
  rw [sub_mul, b.raw_coefficient_residue_extract T X₁ X₂ Z length w₁ w₂ w y hy J hJ,
    b.raw_coefficient_residue_extract T Y₁ Y₂ Z length v₁ v₂ w y hy J hJ, mul_sub]

section OriginalFactors

variable {Ray : Type*} [CommGroup Ray]
variable {T : FixedChildCharacters F k} {phase : Ray →* Circle}
variable (D : SecondCoefficientTermDictionary T phase S₁ S₂ S)
variable (atoms : SecondColumnFactors F Ray k)

/-- The actual original factor table, not a whole-column calibration
premise, reaches the computed common scalar and actual residual column.
Its additional Gauss normalizer appears exactly once. -/
theorem identified_coefficient_residue_extract
    (hid : D.FactorIdentification atoms)
    (y : AllocationColumn F b.keep.card) (hy : y ∈ b.residualColumns)
    (J : A.Exterior) (hJ : J.val = allocationColumnIdeal y) (frequency : A.R) :
    atoms.coefficient (b.reconstruct y) *
        (phase (atoms.ray (b.reconstruct y)) : ℂ) *
        σ (A.sexticResidue J frequency) =
      b.bareCommonScalar T D.base D.length D.slotWeight *
        (atoms.normalizer *
          b.residualCoefficient (σ := σ) T frequency D.scale₁ D.scale₂
            D.base D.length D.leftWeight D.rightWeight D.slotWeight y) := by
  have hcoefficient (i : AllocationColumn F k)
      (hi : i ∈ childCartesianColumns S₁ S₂ S) :
      D.normalizedCoefficient atoms.leftNormalizer atoms.rightNormalizer atoms.slotNormalizer i =
        atoms.coefficient i := by
    have hm := hi
    simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
      Fintype.mem_piFinset] at hm
    unfold SecondCoefficientTermDictionary.normalizedCoefficient
      SecondColumnFactors.coefficient childCartesianCoefficient
    dsimp only
    rw [hid.left_atom _ hm.1.1, hid.right_atom _ hm.1.2]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hid.slot_atom j _ (hm.2 j)]
  have hray (i : AllocationColumn F k)
      (hi : i ∈ childCartesianColumns S₁ S₂ S) : D.ray i = atoms.ray i := by
    have hm := hi
    simp only [childCartesianColumns, Finset.product_eq_sprod, Finset.mem_product,
      Fintype.mem_piFinset] at hm
    unfold SecondCoefficientTermDictionary.ray SecondColumnFactors.ray
    rw [hid.left_ray _ hm.1.1, hid.right_ray _ hm.1.2]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact hid.slot_ray j _ (hm.2 j)
  have hm := b.original_subset (b.reconstruct_mem y hy)
  rw [← hcoefficient _ hm, ← hray _ hm,
    D.normalizedCoefficient_eq]
  calc
    _ = atoms.normalizer *
        (D.coefficient (b.reconstruct y) *
          (phase (D.ray (b.reconstruct y)) : ℂ)) *
        σ (A.sexticResidue J frequency) := by
      unfold SecondColumnFactors.normalizer
      ring
    _ = atoms.normalizer *
        (rawBareSourceCoefficient T D.scale₁ D.scale₂ D.base D.length
          D.leftWeight D.rightWeight D.slotWeight (b.reconstruct y) *
            σ (A.sexticResidue J frequency)) := by
      rw [D.coefficient_phase _ hm]
      ring
    _ = _ := by
      rw [b.raw_coefficient_residue_extract T D.scale₁ D.scale₂ D.base D.length
        D.leftWeight D.rightWeight D.slotWeight y hy J hJ]
      ring

end OriginalFactors
end SupportCartesianBranch

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.frozenScalar_one_eq_bare
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.raw_centered_residue_extract
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.identified_coefficient_residue_extract

