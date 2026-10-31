import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointKernelExceptionalSplit

/-!
# Literal second-column magnitudes on exceptional rows

The complete centered coefficient is transported to its actual allocated
source before its norm is taken.  The right column keeps its full star
and therefore uses the same residual row with all Fourier locations
negated.  The two original Gauss normalizers appear exactly once.
The final identities apply to the rowwise exceptional part of the
common-kernel estimate, before paired Cauchy on the other rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

set_option maxHeartbeats 2000000

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ActualAllocatedSource

variable {H : Type*} {k : ℕ}

def centeredColumn (s : ActualAllocatedSource A V H k) (Y₁ Y₂ : ℝ)
    (v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (ξ : V) (h : H) : ℂ :=
  jointFourierColumn s.allocation.columns
    (fun y =>
      rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
        s.scale₁ s.scale₂ s.base s.length (s.leftWeight h) (s.rightWeight h) (s.slotWeight h) y -
      rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h) (s.row h).element
        Y₁ Y₂ s.base s.length (v₁ h) (v₂ h) (s.slotWeight h) y)
    (rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ

theorem ExceptionalAt.value_eq_centeredColumn
    {s : ActualAllocatedSource A V H k} {Y₁ Y₂ : ℝ}
    {v₁ v₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ}
    {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V} {h : H}
    (T : s.ExceptionalAt (σ := σ) Y₁ Y₂ v₁ v₂ Ψ W₁ W₂ ξ h) :
    T.source.value = s.centeredColumn (σ := σ) Y₁ Y₂ v₁ v₂ ξ h := rfl

end ActualAllocatedSource

private theorem exceptional_column_mem_source {k : ℕ}
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

/-- Pointwise binding of the complete centered Fourier column.  This
uses only the original per-factor arithmetic dictionaries. -/
theorem centered_column_norm_eq_source
    (f : SecondSideFrame (V := V) C R Ray side k)
    (E : SecondCoefficientComparison f.dictionary) (h : R.live) (ξ : V) :
    ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val)
        (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
          (f.slotLocation h.val)) ξ‖ =
      ‖f.normalizer‖ *
        ‖f.source.centeredColumn (σ := σ) E.scale₁ E.scale₂
          (fun _ => E.leftWeight) (fun _ => E.rightWeight) ξ h‖ := by
  cases side with
  | left =>
    let c : AllocationColumn F k → ℂ := fun i =>
      rawSourceCoefficient (σ := σ) f.characters (R.factor C h.val) (R.extractedRow C h).element
          f.dictionary.scale₁ f.dictionary.scale₂ f.dictionary.base f.dictionary.length
          f.dictionary.leftWeight f.dictionary.rightWeight f.dictionary.slotWeight i -
        rawSourceCoefficient (σ := σ) f.characters (R.factor C h.val) (R.extractedRow C h).element
          E.scale₁ E.scale₂ f.dictionary.base f.dictionary.length
          E.leftWeight E.rightWeight f.dictionary.slotWeight i
    let x := rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val) (f.slotLocation h.val)
    have hc (i : AllocationColumn F k) (hi : i ∈ f.allocation.columns) :
        f.centeredCoefficient E h.val i = f.normalizer * c i := by
      exact E.centered_coefficient_residue
        (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
        i (exceptional_column_mem_source f.allocation i hi)
        (f.ideal i) (f.ideal_product i (exceptional_column_mem_source f.allocation i hi))
        (R.frequency h.val) (R.factor C h.val) (R.extractedRow C h).element
        (R.extractedRow C h).frequency
    have hp : jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val) x ξ =
        f.normalizer * jointFourierColumn f.allocation.columns c x ξ := by
      simp only [jointFourierColumn, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i hi]
      ring
    change ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val) x ξ‖ =
      ‖f.normalizer‖ * ‖jointFourierColumn f.allocation.columns c x ξ‖
    rw [hp, norm_mul]
  | right =>
    let c : AllocationColumn F k → ℂ := fun i =>
      rawSourceCoefficient (σ := σ) f.characters (-R.factor C h.val) (R.extractedRow C h).element
          f.dictionary.scale₁ f.dictionary.scale₂ f.dictionary.base f.dictionary.length
          f.dictionary.leftWeight f.dictionary.rightWeight f.dictionary.slotWeight i -
        rawSourceCoefficient (σ := σ) f.characters (-R.factor C h.val) (R.extractedRow C h).element
          E.scale₁ E.scale₂ f.dictionary.base f.dictionary.length
          E.leftWeight E.rightWeight f.dictionary.slotWeight i
    let x := rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val) (f.slotLocation h.val)
    have hc (i : AllocationColumn F k) (hi : i ∈ f.allocation.columns) :
        f.centeredCoefficient E h.val i = star f.normalizer * star (c i) := by
      have he := E.centered_coefficient_residue
        (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹)
        i (exceptional_column_mem_source f.allocation i hi)
        (f.ideal i) (f.ideal_product i (exceptional_column_mem_source f.allocation i hi))
        (-R.frequency h.val) (-R.factor C h.val) (R.extractedRow C h).element
        (by rw [(R.extractedRow C h).frequency, neg_mul])
      exact (congrArg star he).trans (star_mul' _ _)
    have hphase (z : V) : jointPhase ξ (-z) = star (jointPhase ξ z) := by
      simp only [jointPhase, inner_neg_right, AddChar.map_neg_eq_inv,
        Circle.coe_inv_eq_conj, starRingEnd_apply]
    have hp : jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val) x ξ =
        star f.normalizer * star (jointFourierColumn f.allocation.columns c (fun i => -x i) ξ) := by
      simp only [jointFourierColumn, star_sum, star_mul', hphase, star_star, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i hi]
      ring
    have hs : f.source.centeredColumn (σ := σ) E.scale₁ E.scale₂
        (fun _ => E.leftWeight) (fun _ => E.rightWeight) ξ h =
        jointFourierColumn f.allocation.columns c (fun i => -x i) ξ := by
      simp only [ActualAllocatedSource.centeredColumn, source, rawSource,
        ActualSecondCorrelationRows.source, ActualAllocatedSource.negativeSide,
        ActualChildRow.negative, rawSourceLocation_neg] <;> rfl
    rw [hs]
    change ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val) x ξ‖ = _
    rw [hp, norm_mul, norm_star, norm_star]

/-- The normalization is computed from the original positive factor
scales and is independent of the row and both Fourier parameters. -/
theorem centered_column_norm_eq_div_scale
    (f : SecondSideFrame (V := V) C R Ray side k)
    (E : SecondCoefficientComparison f.dictionary) (h : R.live) (ξ : V) :
    ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient E h.val)
        (rawSourceLocation (f.leftLocation h.val) (f.rightLocation h.val)
          (f.slotLocation h.val)) ξ‖ =
      ‖f.source.centeredColumn (σ := σ) E.scale₁ E.scale₂
        (fun _ => E.leftWeight) (fun _ => E.rightWeight) ξ h‖ /
          Real.sqrt f.normalizationScale := by
  rw [f.centered_column_norm_eq_source E h ξ]
  change ‖extraGaussNormalizer f.gaussScale₁ f.gaussScale₂ f.gaussSlotScale‖ * _ = _
  rw [extraGaussNormalizer_norm _ _ _ f.gaussScale₁_pos f.gaussScale₂_pos f.gaussSlotScale_pos]
  simp only [normalizationScale, div_eq_mul_inv] <;> ring

/-- Exact same-row pairing with actual exceptional charts.  Charts are
required only on the selected exceptional rows, and the centered
subtraction is kept inside both complete column norms. -/
theorem centered_pair_magnitude_eq_exceptionalValues
    {l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    (rows : Finset R.live) (ξ : V)
    {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
    (TL : ∀ h : rows, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : rows, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val) :
    jointColumnPairMagnitude rows left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.centeredCoefficient EL h.val)
      (fun h => right.centeredCoefficient ER h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
        (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
        (right.slotLocation h.val)) ξ =
      (‖left.normalizer‖ * ‖right.normalizer‖) *
        ∑ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ *
          ‖(TL h).source.value‖ * ‖(TR h).source.value‖ := by
  let term : R.live → ℝ := fun h =>
    ‖R.weight h.val * R.correlation h.val‖ *
      ‖jointFourierColumn left.allocation.columns (left.centeredCoefficient EL h.val)
        (rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val)) ξ‖ *
      ‖jointFourierColumn right.allocation.columns (right.centeredCoefficient ER h.val)
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
      rw [left.centered_column_norm_eq_source EL h.val ξ,
        right.centered_column_norm_eq_source ER h.val ξ,
        ← (TL h).value_eq_centeredColumn, ← (TR h).value_eq_centeredColumn]
      ring

/-- Only the pointwise original row weight is bounded here.  The
exceptional amplitudes and their later actual row count remain literal,
and the two original Gauss scales supply one common denominator. -/
theorem centered_pair_magnitude_le_exceptionalValues
    {l : ℕ}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    (rows : Finset R.live) (ξ : V)
    {ΨL ΨR : Ideal (𝓞 F) →* ℂ} {WL₁ WL₂ WR₁ WR₂ : ℝ → ℂ}
    (TL : ∀ h : rows, left.source.ExceptionalAt (σ := σ) EL.scale₁ EL.scale₂
      (fun _ => EL.leftWeight) (fun _ => EL.rightWeight) ΨL WL₁ WL₂ ξ h.val)
    (TR : ∀ h : rows, right.source.ExceptionalAt (σ := σ) ER.scale₁ ER.scale₂
      (fun _ => ER.leftWeight) (fun _ => ER.rightWeight) ΨR WR₁ WR₂ ξ h.val)
    (W : ℝ) (hW : ∀ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ ≤ W) :
    jointColumnPairMagnitude rows left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.centeredCoefficient EL h.val)
      (fun h => right.centeredCoefficient ER h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
        (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
        (right.slotLocation h.val)) ξ ≤
      (W / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
        ∑ h : rows, ‖(TL h).source.value‖ * ‖(TR h).source.value‖ := by
  rw [left.centered_pair_magnitude_eq_exceptionalValues right EL ER rows ξ TL TR]
  have hn : ‖left.normalizer‖ * ‖right.normalizer‖ =
      1 / (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale) :=
    extraGaussNormalizer_pair_norm _ _ _ _ _ _
      left.gaussScale₁_pos left.gaussScale₂_pos left.gaussSlotScale_pos
      right.gaussScale₁_pos right.gaussScale₂_pos right.gaussSlotScale_pos
  have hs : (∑ h : rows, ‖R.weight h.val.val * R.correlation h.val.val‖ *
      ‖(TL h).source.value‖ * ‖(TR h).source.value‖) ≤
      W * ∑ h : rows, ‖(TL h).source.value‖ * ‖(TR h).source.value‖ := by
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

namespace ActualSecondCorrelationRows

variable {H ι J K : Type*} [Fintype ι] [DecidableEq ι]
variable (R : ActualSecondCorrelationRows A σ H ι)

/-- The local weight used by the exceptional source is the actual
complete correlation, with its original generators and unit radical. -/
theorem correlation_norm_le_actual_radical
    (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < R.leftMultiplicity i) (h : H) :
    ‖R.correlation h‖ ≤
      (Ideal.absNorm (gcd (primePowerProduct R.primes R.leftMultiplicity).val
        (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) /
        A.exteriorNorm (unitFrequencyRadical C R.primes R.leftMultiplicity
          R.rightMultiplicity (R.frequency h)) :=
  actual_complete_correlation_gcd_radical_bound_of_generates C R.primes R.primes_injective
    R.leftMultiplicity R.rightMultiplicity hm R.leftGenerator R.rightGenerator
    R.leftGenerates R.rightGenerates (R.frequency h)

/-- Raw row windows imply the complete correlation weight bound.
Neither a class total nor an exceptional energy bound is assumed. -/
theorem weighted_correlation_norm_le_of_windows
    (C : A.GeneralArithmeticContext σ η hS)
    (hm : ∀ i, 0 < R.leftMultiplicity i) (rows : Finset H)
    (Z g₂ p₂ B : ℝ) (hZ : 0 < Z) (hB : 0 ≤ B)
    (hgcd : (Ideal.absNorm (gcd (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) ≤ Z ^ g₂)
    (hunit : ∀ h ∈ rows, Z ^ p₂ ≤
      A.exteriorNorm (unitFrequencyRadical C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h)))
    (hweight : ∀ h ∈ rows, ‖R.weight h‖ ≤ B) :
    ∀ h ∈ rows, ‖R.weight h * R.correlation h‖ ≤ B * Z ^ (g₂ - p₂) := by
  intro h hh
  have hc := R.correlation_norm_le_actual_radical C hm h
  have hd := div_le_div_of_nonneg_left
    (show (0 : ℝ) ≤ (Ideal.absNorm (gcd
      (primePowerProduct R.primes R.leftMultiplicity).val
      (primePowerProduct R.primes R.rightMultiplicity).val) : ℝ) from Nat.cast_nonneg _)
    (Real.rpow_pos_of_pos hZ p₂) (hunit h hh)
  have hn := div_le_div_of_nonneg_right hgcd (Real.rpow_nonneg hZ.le p₂)
  rw [norm_mul, Real.rpow_sub hZ]
  exact mul_le_mul (hweight h hh) (hc.trans (hd.trans hn)) (norm_nonneg _) hB

/-- Correlation-zero rows disappear before the exceptional rowwise sum.
The exceptional predicate can depend on all fixed finite branch labels. -/
theorem pair_magnitude_live
    (leftColumns : Finset J) (rightColumns : Finset K)
    (c : H → J → ℂ) (d : H → K → ℂ)
    (x : H → J → V) (y : H → K → V) (exceptional : H → Prop) (ξ : V) :
    jointColumnPairMagnitude (R.rows.filter exceptional) leftColumns rightColumns
      (fun h => R.weight h * R.correlation h) c d x y ξ =
      jointColumnPairMagnitude (Finset.univ.filter (fun h : R.live => exceptional h.val))
        leftColumns rightColumns (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => c h.val) (fun h => d h.val) (fun h => x h.val) (fun h => y h.val) ξ := by
  let term : H → ℝ := fun h => ‖R.weight h * R.correlation h‖ *
    ‖jointFourierColumn leftColumns (c h) (x h) ξ‖ *
    ‖jointFourierColumn rightColumns (d h) (y h) ξ‖
  change (∑ h ∈ R.rows.filter exceptional, term h) = _
  calc
    _ = ∑ h ∈ R.live, if exceptional h then term h else 0 := by
      simp only [live, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      by_cases hc : R.correlation h = 0 <;> by_cases he : exceptional h <;>
        simp [hc, he, term]
    _ = ∑ h : R.live, if exceptional h.val then term h.val else 0 :=
      (Finset.sum_coe_sort R.live (fun h => if exceptional h then term h else 0)).symm
    _ = _ := by simp only [jointColumnPairMagnitude, Finset.sum_filter, Finset.sum_univ, term]

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.centered_column_norm_eq_source
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.centered_pair_magnitude_le_exceptionalValues
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.pair_magnitude_live

