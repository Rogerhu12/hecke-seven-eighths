import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FixedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NonzeroQuotientSupport

/-!
# Exact source factors after quotient and slot extraction

A plain quotient is normalized at N/N(B), with the actual frozen
character, common mask and residue value retained in its scalar.  The
same scalar works for both rectangles of a centered coefficient.
Selected slots keep their original characters and lengths.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}

theorem sourcePlainCoefficient_mul
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ) (B I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    sourcePlainCoefficient χ θ M (B * I) =
      sourcePlainCoefficient χ θ M B * sourcePlainCoefficient χ θ M I := by
  simp only [sourcePlainCoefficient, heckeIdealCoefficient_mul,
    show (B * I).val = B.val * I.val from rfl, map_mul]
  ring

def sourcePlainFrozen (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (B : HeckeGeneral.Analysis.NonzeroIdeal F) : ℂ :=
  (Real.sqrt (idealNorm F B) : ℂ)⁻¹ *
    (sourcePlainCoefficient χ θ M B *
      actualIdealResidue (A := A) (σ := σ) B.val (g * h'))

theorem sourcePlainTerm_extract
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ)
    (g h' : A.R) (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (N : ℝ) (B I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    sourcePlainTerm (σ := σ) χ θ M g h' w N (B * I) =
      sourcePlainFrozen (σ := σ) χ θ M g h' B *
        sourcePlainTerm (σ := σ) χ θ M g h' (fun J => w (B * J))
          (N / idealNorm F B) I := by
  have hB : (Real.sqrt (idealNorm F B) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (idealNorm_pos F B)).ne'
  have hnorm : (Real.sqrt N : ℂ)⁻¹ =
      (Real.sqrt (idealNorm F B) : ℂ)⁻¹ *
        (Real.sqrt (N / idealNorm F B) : ℂ)⁻¹ := by
    rw [Real.sqrt_div' N (idealNorm_pos F B).le, Complex.ofReal_div,
      inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
  simp only [sourcePlainTerm, sourcePlainFrozen, sourcePlainCoefficient_mul,
    show (B * I).val = B.val * I.val from rfl, actualIdealResidue_ideal_mul]
  rw [hnorm]
  ring

namespace FixedChildCharacters

variable {k : ℕ}

def restrictSlots (T : FixedChildCharacters F k) (keep : Finset (Fin k)) :
    FixedChildCharacters F keep.card where
  plain := T.plain
  slot j := T.slot (SlotRestriction.index keep j)
  plainTwist := T.plainTwist
  slotTwist j := T.slotTwist (SlotRestriction.index keep j)
  mask := T.mask
  fixedRay := T.fixedRay
  plainTwist_mem := T.plainTwist_mem
  slotTwist_mem j := T.slotTwist_mem (SlotRestriction.index keep j)

def frozenScalar (T : FixedChildCharacters F k) (g h' : A.R)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F) (Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) : ℂ :=
  sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h' B₁ *
    sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h' B₂ *
      ∏ i ∈ Finset.univ.filter (fun i => i ∉ keep),
        sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
          g h' (w i) (Z ^ length i) (frozen i)

theorem coefficient_extract (T : FixedChildCharacters F k) (g h' : A.R)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) × (Fin keep.card → HeightOneSpectrum (𝓞 F))) :
    T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w
      ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2) =
      T.frozenScalar (σ := σ) g h' B₁ B₂ Z length keep frozen w *
        (T.restrictSlots keep).coefficient (σ := σ) g h'
          (N₁ / idealNorm F B₁) (N₂ / idealNorm F B₂) Z
          (fun j => length (SlotRestriction.index keep j))
          (fun I => w₁ (B₁ * I)) (fun J => w₂ (B₂ * J))
          (fun j => w (SlotRestriction.index keep j)) y := by
  simp only [coefficient, childCartesianCoefficient]
  rw [sourcePlainTerm_extract, sourcePlainTerm_extract, SlotRestriction.product_extend]
  simp only [frozenScalar, restrictSlots]
  ring

/-- Both rectangles are transported by the same exact frozen scalar. -/
theorem centered_coefficient_extract (T : FixedChildCharacters F k) (g h' : A.R)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F) (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (y : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) × (Fin keep.card → HeightOneSpectrum (𝓞 F))) :
    (T.coefficient (σ := σ) g h' X₁ X₂ Z length w₁ w₂ w
        ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2) -
      T.coefficient (σ := σ) g h' Y₁ Y₂ Z length v₁ v₂ w
        ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2)) =
      T.frozenScalar (σ := σ) g h' B₁ B₂ Z length keep frozen w *
        ((T.restrictSlots keep).coefficient (σ := σ) g h'
          (X₁ / idealNorm F B₁) (X₂ / idealNorm F B₂) Z
          (fun j => length (SlotRestriction.index keep j))
          (fun I => w₁ (B₁ * I)) (fun J => w₂ (B₂ * J))
          (fun j => w (SlotRestriction.index keep j)) y -
        (T.restrictSlots keep).coefficient (σ := σ) g h'
          (Y₁ / idealNorm F B₁) (Y₂ / idealNorm F B₂) Z
          (fun j => length (SlotRestriction.index keep j))
          (fun I => v₁ (B₁ * I)) (fun J => v₂ (B₂ * J))
          (fun j => w (SlotRestriction.index keep j)) y) := by
  rw [coefficient_extract, coefficient_extract, mul_sub]

end FixedChildCharacters

namespace SlotRestriction

variable {k : ℕ} {P V : Type*} [AddCommMonoid V]

theorem sum_extend (keep : Finset (Fin k)) (frozen : Fin k → P)
    (y : Fin keep.card → P) (f : Fin k → P → V) :
    (∑ i, f i (extend keep frozen y i)) =
      (∑ i ∈ Finset.univ.filter (fun i => i ∉ keep), f i (frozen i)) +
        ∑ j, f (index keep j) (y j) := by
  have hk : (∑ i ∈ keep, f i (extend keep frozen y i)) =
      ∑ j, f (index keep j) (y j) := by
    rw [← Finset.sum_coe_sort keep (fun i => f i (extend keep frozen y i))]
    calc
      _ = ∑ j : Fin keep.card,
          f (index keep j) (extend keep frozen y (index keep j)) :=
        (keep.equivFin.symm.sum_comp
          (fun i : keep => f i.val (extend keep frozen y i.val))).symm
      _ = _ := by simp only [extend_index]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i => i ∈ keep) (fun i => f i (extend keep frozen y i))]
  have hf : Finset.univ.filter (fun i : Fin k => i ∈ keep) = keep := by ext i; simp
  rw [hf, hk, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [extend, dif_neg (Finset.mem_filter.mp hi).2]

end SlotRestriction

section Locations

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}

def frozenSourceLocation (keep : Finset (Fin k))
    (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (x : Fin k → HeightOneSpectrum (𝓞 F) → V) : V :=
  ∑ i ∈ Finset.univ.filter (fun i => i ∉ keep), x i (frozen i)

theorem source_location_extract (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V) (x : Fin k → HeightOneSpectrum (𝓞 F) → V)
    (y : (HeckeGeneral.Analysis.NonzeroIdeal F × HeckeGeneral.Analysis.NonzeroIdeal F) × (Fin keep.card → HeightOneSpectrum (𝓞 F))) :
    childCartesianLocation x₁ x₂ x
      ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2) =
      frozenSourceLocation keep frozen x +
        childCartesianLocation (fun I => x₁ (B₁ * I)) (fun J => x₂ (B₂ * J))
          (fun j => x (SlotRestriction.index keep j)) y := by
  simp only [childCartesianLocation, frozenSourceLocation, SlotRestriction.sum_extend]
  ac_rfl

/-- Exact whole-column identity, still before every absolute value. -/
theorem extracted_source_joint_polynomial
    (T : FixedChildCharacters F k) (g h' : A.R)
    (B₁ B₂ : HeckeGeneral.Analysis.NonzeroIdeal F) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (frozen : Fin k → HeightOneSpectrum (𝓞 F))
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal F))
    (S : Fin keep.card → Finset (HeightOneSpectrum (𝓞 F)))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal F → V) (x : Fin k → HeightOneSpectrum (𝓞 F) → V) (ξ : V) :
    (∑ y ∈ childCartesianColumns S₁ S₂ S,
      T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w
          ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2) *
        jointPhase ξ (childCartesianLocation x₁ x₂ x
          ((B₁ * y.1.1, B₂ * y.1.2), SlotRestriction.extend keep frozen y.2))) =
      T.frozenScalar (σ := σ) g h' B₁ B₂ Z length keep frozen w *
        jointPhase ξ (frozenSourceLocation keep frozen x) *
          jointFourierColumn (childCartesianColumns S₁ S₂ S)
            ((T.restrictSlots keep).coefficient (σ := σ) g h'
              (N₁ / idealNorm F B₁) (N₂ / idealNorm F B₂) Z
              (fun j => length (SlotRestriction.index keep j))
              (fun I => w₁ (B₁ * I)) (fun J => w₂ (B₂ * J))
              (fun j => w (SlotRestriction.index keep j)))
            (childCartesianLocation (fun I => x₁ (B₁ * I)) (fun J => x₂ (B₂ * J))
              (fun j => x (SlotRestriction.index keep j))) ξ := by
  unfold jointFourierColumn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [FixedChildCharacters.coefficient_extract, source_location_extract, jointPhase_add]
  ring

end Locations

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.sourcePlainTerm_extract
#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.centered_coefficient_extract
#print axioms HeckeSkeleton.Moments.EngineStep.extracted_source_joint_polynomial

