import HeckeSkeleton.HighBin
import HeckeSkeleton.HighBinSupport.FinitePieceGauge

/-!
The original `ActualHighPresentation` records aggregate piece identities.
This module checks their exact logical scope against the real data type.
Rebalancing two rows inside each original label leaves every field of
the presentation valid, preserves all three hypotheses of the norm-form
theorem and preserves the whole-bin boundary. Nevertheless one new piece
in every label with at least two rows can have an arbitrary value.

Consequently a proof for the named `actualHighPresentation` must use its
canonical construction and its individual restricted-integral identities.
The results below do not refute that named theorem: no claim is made that
the named construction equals one of the modified presentations.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinPresentationGauge

open NumberField
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HighBinVerified.FinitePieceGauge
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- A prescribed new value for one genuine row in each original label. -/
abbrev PieceValues (c : TargetContext K) :=
  ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) → HighLabel K c Z T b → ℂ

/-- Keep every original row, label, height, Euler datum and block identity;
only rebalance the individual contributions inside each label. -/
def withPrescribedPieces (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) : ActualHighPresentation K c :=
  { P with
    shiftedPiece := fun Z T b label =>
      prescribePiece ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows
        (P.shiftedPiece Z T b label) (z Z T b label)
    block_identification := by
      intro Z T hZ hT b
      simpa only [sum_prescribePiece] using P.block_identification Z T hZ hT b
    shifted_identification := by
      intro Z T hZ hT b
      simpa only [sum_prescribePiece] using P.shifted_identification Z T hZ hT b }

theorem sum_withPrescribedPieces (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) (Z T : ℝ) (b : HighBlockIndex K c Z T)
    (label : HighLabel K c Z T b) :
    (∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
      (withPrescribedPieces K c P z).shiftedPiece Z T b label u) =
    ∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
      P.shiftedPiece Z T b label u :=
  sum_prescribePiece _ _ _

theorem fullEuler_iff (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) :
    FullHighEulerControl K c (withPrescribedPieces K c P z) ↔
      FullHighEulerControl K c P := Iff.rfl

theorem pureNormPoleExclusion_iff (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) :
    HighPureNormPoleExclusion K c (withPrescribedPieces K c P z) ↔
      HighPureNormPoleExclusion K c P := Iff.rfl

theorem conductorDeficit_iff (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) :
    HighConductorDeficit K c (withPrescribedPieces K c P z) ↔
      HighConductorDeficit K c P := Iff.rfl

theorem labelUniformity_iff (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) :
    HighLabelUniformity K c (withPrescribedPieces K c P z) ↔
      HighLabelUniformity K c P := Iff.rfl

theorem wholeBinBoundary_eq (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) :
    wholeBinBoundary K c (withPrescribedPieces K c P z) = wholeBinBoundary K c P := rfl

/-- The original finite row set supports a piece at least as large as
the prescribed value, while its signed total is exactly unchanged. -/
theorem prescribed_norm_le (c : TargetContext K) (P : ActualHighPresentation K c)
    (z : PieceValues K c) (Z T : ℝ) (b : HighBlockIndex K c Z T)
    (label : HighLabel K c Z T b)
    (hrows : 2 ≤ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows.card) :
    ‖z Z T b label‖ ≤
      ∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
        ‖(withPrescribedPieces K c P z).shiftedPiece Z T b label u‖ :=
  norm_le_sum_norm_prescribePiece _ _ _ hrows

/-- At a label with two actual rows, all recorded data and all aggregate
identities are compatible with an arbitrarily large sum of piece norms.
This local statement does not assert the failure of a particular global
asymptotic estimate for the named presentation. -/
theorem exists_presentation_preserving_inputs_with_large_piece_norm
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b)
    (hrows : 2 ≤ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows.card)
    (M : ℝ) :
    ∃ P' : ActualHighPresentation K c,
      P'.euler = P.euler ∧ P'.labels = P.labels ∧
      (FullHighEulerControl K c P' ↔ FullHighEulerControl K c P) ∧
      (HighPureNormPoleExclusion K c P' ↔ HighPureNormPoleExclusion K c P) ∧
      (HighConductorDeficit K c P' ↔ HighConductorDeficit K c P) ∧
      (HighLabelUniformity K c P' ↔ HighLabelUniformity K c P) ∧
      wholeBinBoundary K c P' = wholeBinBoundary K c P ∧
      M < ∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
        ‖P'.shiftedPiece Z T b label u‖ := by
  let z : PieceValues K c := fun _ _ _ _ => ((max M 0 + 1 : ℝ) : ℂ)
  refine ⟨withPrescribedPieces K c P z, rfl, rfl, fullEuler_iff K c P z,
    pureNormPoleExclusion_iff K c P z, conductorDeficit_iff K c P z,
    labelUniformity_iff K c P z, wholeBinBoundary_eq K c P z, ?_⟩
  have hz : ‖z Z T b label‖ = max M 0 + 1 := by
    change ‖((max M 0 + 1 : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    linarith [le_max_right M 0]
  have hM : M < ‖z Z T b label‖ := by
    rw [hz]
    linarith [le_max_left M 0]
  exact hM.trans_le (prescribed_norm_le K c P z Z T b label hrows)

end HeckeSkeleton.HighBinPresentationGauge

#print axioms HeckeSkeleton.HighBinPresentationGauge.withPrescribedPieces
#print axioms HeckeSkeleton.HighBinPresentationGauge.sum_withPrescribedPieces
#print axioms HeckeSkeleton.HighBinPresentationGauge.prescribed_norm_le
#print axioms HeckeSkeleton.HighBinPresentationGauge.exists_presentation_preserving_inputs_with_large_piece_norm
