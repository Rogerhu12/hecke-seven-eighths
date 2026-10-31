import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryExceptionalAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondExceptionalBinding

/-!
# Ordinary exceptional values of the actual second columns

The single original rectangle is transported through its actual source
dictionary. The right column retains conjugation and negative Fourier
locations, and the two original Gauss normalizers are used once.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ActualAllocatedSource

variable {H : Type*} {k : ℕ}

def ordinaryColumn (s : ActualAllocatedSource A V H k) (ξ : V) (h : H) : ℂ :=
  jointFourierColumn s.allocation.columns
    (rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
      s.scale₁ s.scale₂ s.base s.length (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
    (rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ

theorem OrdinaryExceptionalAt.value_eq_ordinaryColumn
    {s : ActualAllocatedSource A V H k}
    {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V} {h : H}
    (T : s.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h) :
    T.source.ordinaryValue = s.ordinaryColumn (σ := σ) ξ h := rfl

end ActualAllocatedSource

private theorem ordinary_exceptional_column_mem_source {k : ℕ}
    (B : ActualColumnAllocation F k) (i : AllocationColumn F k) (hi : i ∈ B.columns) :
    i ∈ childCartesianColumns B.plain₁ B.plain₂ B.slots := by
  rw [ActualColumnAllocation.columns, paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

namespace SecondSideFrame

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}

/-- Pointwise binding of the original ordinary Fourier column.  This
uses only the original per-factor arithmetic dictionaries. -/
theorem ordinary_column_norm_eq_source
    (f : SecondSideFrame (V := V) C R Ray side k)
    (h : R.live) (ξ : V) :
    ‖jointFourierColumn f.allocation.columns (f.coefficient h.val)
        (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
          (f.slotLocation h.val)) ξ‖ =
      ‖f.normalizer‖ *
        ‖f.source.ordinaryColumn (σ := σ) ξ h‖ := by
  cases side with
  | left =>
    let c : AllocationColumn F k → ℂ := fun i =>
      rawSourceCoefficient (σ := σ) f.characters (R.factor C h.val) (R.extractedRow C h).element
          f.dictionary.scale₁ f.dictionary.scale₂ f.dictionary.base f.dictionary.length
          f.dictionary.leftWeight f.dictionary.rightWeight f.dictionary.slotWeight i
    let x := rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val) (f.slotLocation h.val)
    have hc (i : AllocationColumn F k) (hi : i ∈ f.allocation.columns) :
        f.coefficient h.val i = f.normalizer * c i := by
      exact f.dictionary.normalized_coefficient_residue
        (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
        i (ordinary_exceptional_column_mem_source f.allocation i hi)
        (f.ideal i) (f.ideal_product i (ordinary_exceptional_column_mem_source f.allocation i hi))
        (R.frequency h.val) (R.factor C h.val) (R.extractedRow C h).element
        (R.extractedRow C h).frequency
    have hp : jointFourierColumn f.allocation.columns (f.coefficient h.val) x ξ =
        f.normalizer * jointFourierColumn f.allocation.columns c x ξ := by
      simp only [jointFourierColumn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i hi]
      ring
    change ‖jointFourierColumn f.allocation.columns (f.coefficient h.val) x ξ‖ =
      ‖f.normalizer‖ * ‖jointFourierColumn f.allocation.columns c x ξ‖
    rw [hp, norm_mul]
  | right =>
    let c : AllocationColumn F k → ℂ := fun i =>
      rawSourceCoefficient (σ := σ) f.characters (-R.factor C h.val) (R.extractedRow C h).element
          f.dictionary.scale₁ f.dictionary.scale₂ f.dictionary.base f.dictionary.length
          f.dictionary.leftWeight f.dictionary.rightWeight f.dictionary.slotWeight i
    let x := rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val) (f.slotLocation h.val)
    have hc (i : AllocationColumn F k) (hi : i ∈ f.allocation.columns) :
        f.coefficient h.val i = star f.normalizer * star (c i) := by
      have he := f.dictionary.normalized_coefficient_residue
        (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
        i (ordinary_exceptional_column_mem_source f.allocation i hi)
        (f.ideal i) (f.ideal_product i (ordinary_exceptional_column_mem_source f.allocation i hi))
        (-R.frequency h.val) (-R.factor C h.val) (R.extractedRow C h).element
        (by rw [(R.extractedRow C h).frequency, neg_mul])
      exact (congrArg star he).trans (star_mul' _ _)
    have hphase (z : V) : jointPhase ξ (-z) = star (jointPhase ξ z) := by
      simp only [jointPhase, inner_neg_right, AddChar.map_neg_eq_inv,
        Circle.coe_inv_eq_conj, starRingEnd_apply]
    have hp : jointFourierColumn f.allocation.columns (f.coefficient h.val) x ξ =
        star f.normalizer * star (jointFourierColumn f.allocation.columns c (fun i => -x i) ξ) := by
      simp only [jointFourierColumn, star_sum, star_mul', hphase, star_star, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i hi]
      ring
    have hs : f.source.ordinaryColumn (σ := σ) ξ h =
        jointFourierColumn f.allocation.columns c (fun i => -x i) ξ := by
      simp only [ActualAllocatedSource.ordinaryColumn, source, rawSource,
        ActualSecondCorrelationRows.source, ActualAllocatedSource.negativeSide,
        ActualChildRow.negative, rawSourceLocation_neg] <;> rfl
    rw [hs]
    change ‖jointFourierColumn f.allocation.columns (f.coefficient h.val) x ξ‖ = _
    rw [hp, norm_mul, norm_star, norm_star]

/-- The normalization is computed from the original positive factor
scales and is independent of the row and both Fourier parameters. -/
theorem ordinary_column_norm_eq_div_scale
    (f : SecondSideFrame (V := V) C R Ray side k)
    (h : R.live) (ξ : V) :
    ‖jointFourierColumn f.allocation.columns (f.coefficient h.val)
        (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
          (f.slotLocation h.val)) ξ‖ =
      ‖f.source.ordinaryColumn (σ := σ) ξ h‖ /
          Real.sqrt f.normalizationScale := by
  rw [f.ordinary_column_norm_eq_source h ξ]
  change ‖extraGaussNormalizer f.gaussScale₁ f.gaussScale₂ f.gaussSlotScale‖ * _ = _
  rw [extraGaussNormalizer_norm _ _ _ f.gaussScale₁_pos f.gaussScale₂_pos f.gaussSlotScale_pos]
  simp only [normalizationScale, div_eq_mul_inv] <;> ring

/-- Exact same-row pairing with actual exceptional charts.  Charts are
required only on the selected exceptional rows, and both original ordinary columns remain intact. -/
theorem ordinary_pair_magnitude_eq_exceptionalValues
    {l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (rows : Finset R.live) (ξ : V)
    {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
    (TL : ∀ h : rows, left.source.OrdinaryExceptionalAt (σ := σ) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : rows, right.source.OrdinaryExceptionalAt (σ := σ) ΨR WR₁ WR₂ ξ h.val) :
    jointColumnPairMagnitude rows left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.coefficient h.val)
      (fun h => right.coefficient h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
        (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
        (right.slotLocation h.val)) ξ =
      (‖left.normalizer‖ * ‖right.normalizer‖) *
        ∑ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ *
          ‖(TL h).source.ordinaryValue‖ * ‖(TR h).source.ordinaryValue‖ := by
  let term : R.live → ℝ := fun h =>
    ‖R.weight h.val * R.correlation h.val‖ *
      ‖jointFourierColumn left.allocation.columns (left.coefficient h.val)
        (rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val)) ξ‖ *
      ‖jointFourierColumn right.allocation.columns (right.coefficient h.val)
        (rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) ξ‖
  change (∑ h ∈ rows, term h) = _
  calc
    _ = ∑ h : rows, term h.val := (Finset.sum_coe_sort rows term).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [term]
      rw [left.ordinary_column_norm_eq_source h.val ξ,
        right.ordinary_column_norm_eq_source h.val ξ,
        ← (TL h).value_eq_ordinaryColumn, ← (TR h).value_eq_ordinaryColumn]
      ring

/-- Only the pointwise original row weight is bounded here.  The
exceptional amplitudes and their later actual row count remain literal,
and the two original Gauss scales supply one common denominator. -/
theorem ordinary_pair_magnitude_le_exceptionalValues
    {l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (rows : Finset R.live) (ξ : V)
    {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
    (TL : ∀ h : rows, left.source.OrdinaryExceptionalAt (σ := σ) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : rows, right.source.OrdinaryExceptionalAt (σ := σ) ΨR WR₁ WR₂ ξ h.val)
    (W : ℝ) (hW : ∀ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ ≤ W) :
    jointColumnPairMagnitude rows left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.coefficient h.val)
      (fun h => right.coefficient h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
        (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
        (right.slotLocation h.val)) ξ ≤
      (W / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
        ∑ h : rows, ‖(TL h).source.ordinaryValue‖ * ‖(TR h).source.ordinaryValue‖ := by
  rw [left.ordinary_pair_magnitude_eq_exceptionalValues right rows ξ TL TR]
  have hn : ‖left.normalizer‖ * ‖right.normalizer‖ =
      1 / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) :=
    extraGaussNormalizer_pair_norm _ _ _ _ _ _
      left.gaussScale₁_pos left.gaussScale₂_pos left.gaussSlotScale_pos
      right.gaussScale₁_pos right.gaussScale₂_pos right.gaussSlotScale_pos
  have hs : (∑ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ *
      ‖(TL h).source.ordinaryValue‖ * ‖(TR h).source.ordinaryValue‖) ≤
      W * ∑ h : rows, ‖(TL h).source.ordinaryValue‖ * ‖(TR h).source.ordinaryValue‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hW h)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply (mul_le_mul_of_nonneg_left hs
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
  rw [hn]
  ring

end SecondSideFrame

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinary_column_norm_eq_source
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinary_pair_magnitude_le_exceptionalValues

