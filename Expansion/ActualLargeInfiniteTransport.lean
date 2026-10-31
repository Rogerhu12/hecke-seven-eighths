import Expansion.ActualOuterComponents
import Expansion.ActualLargeRowBound

/-!
# Genuine infinite large-row transport

Both endpoint box series are absolutely summable on the original strict
row tail.  The finite rectangle identity may therefore be summed, and
its difference is exactly the literal large horizontal face sum.  The
target sum is bounded by the already proved original absolute large-row
input, with no convergence or contour equality supplied as a premise.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.LargeRows
open Expansion.PhysicalInitialMellin Expansion.PhysicalRapidTruncation
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

def actualLargeInitialBoxes
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H zeta : ℝ) : ℂ :=
  ∑' u : {u : FrequencyRow K Sset // Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u},
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u.val Z H 5 5 3

def actualLargeTargetBoxes
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (Z H zeta : ℝ) : ℂ :=
  ∑' u : {u : FrequencyRow K Sset // Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u},
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u.val Z H 2 2 (1 + 3 / zeta)

include nu in
theorem summable_norm_actualLargeTargetBoxes
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    {zeta Z H : ℝ} (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Summable (fun u : {u : FrequencyRow K Sset //
        Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u} =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖) := by
  have hsigma : 1 < 1 + 3 / zeta := by
    have hq : 0 < 3 / zeta := div_pos (by norm_num) hzeta
    linarith
  have h := (summable_actual_absoluteLargeRowTerm K S mu nu hcomplex P psi g ∅
    hsigma zeta Z H hZ hH).subtype
      (fun u => Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u)
  apply h.congr
  intro u
  simp only [Function.comp_apply, absoluteLargeRowTerm, if_pos u.property]

include nu in
/-- Actual absolute convergence at both endpoints permits the complete
strict large tail to be moved term by term.  No infinite-sum convention
for divergent terms is used. -/
theorem actual_large_initial_boxes_transport
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e zeta Z H : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 1 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    Summable (fun u : {u : FrequencyRow K Sset //
        Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u} =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u.val Z H 5 5 3‖) ∧
    Summable (fun u : {u : FrequencyRow K Sset //
        Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u} =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u.val Z H 2 2 (1 + 3 / zeta)‖) ∧
    actualLargeInitialBoxes K S mu P psi g Z H zeta -
      actualLargeTargetBoxes K S mu P psi g Z H zeta =
      actualLargeHorizontalFaces K S mu P psi g Z H zeta := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let rows := {u : FrequencyRow K Sset // Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u}
  have hi := (actualInitialProductRows_absolute K S mu nu P hAllowed psi hcal hunram
    g ∅ hZpos).1
  have hnormInitial : Summable (fun u : FrequencyRow K Sset =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u Z H 5 5 3‖) := by
    apply (summable_norm_actualInitialRestriction K S mu nu P hAllowed psi hcal hunram
      g ∅ hZpos (heightCube H)).congr
    intro u
    exact (congrArg norm (actual_initial_rowContourBox_eq_cube_integral K S mu P psi
      g ∅ Z H u (hi u))).symm
  have hI : Summable (fun u : rows =>
      ‖rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ u.val Z H 5 5 3‖) := hnormInitial.subtype _
  have hT := summable_norm_actualLargeTargetBoxes K S mu nu hcomplex P psi g hzeta hZ hH
  refine ⟨hI, hT, ?_⟩
  unfold actualLargeInitialBoxes actualLargeTargetBoxes actualLargeHorizontalFaces
  rw [← hI.of_norm.tsum_sub hT.of_norm]
  apply tsum_congr
  intro u
  exact actual_large_row_initial_finite_transport K S mu nu P omega psi hpsi hAllowed g ∅ u.val
    hB hB1 he he1 hzeta hZ (zero_le_one.trans hH) u.property hboundary

include nu in
/-- The complex target sum is controlled by the original literal absolute
large-row sum, including its strict norm cutoff. -/
theorem norm_actualLargeTargetBoxes_le_absolute
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    {zeta Z H : ℝ} (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    ‖actualLargeTargetBoxes K S mu P psi g Z H zeta‖ ≤
      ∑' u : FrequencyRow K Sset,
        absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
          g ∅ Z H zeta (1 + 3 / zeta) u := by
  have hs := summable_norm_actualLargeTargetBoxes K S mu nu hcomplex P psi g hzeta hZ hH
  unfold actualLargeTargetBoxes
  apply (norm_tsum_le_tsum_norm hs).trans_eq
  rw [tsum_subtype]
  rfl

include nu in
/-- The exact complex large destination has the proved half-power saving.
The constant and threshold precede Z and H. -/
theorem exists_actual_large_target_sum_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      ‖actualLargeTargetBoxes K S mu P psi g Z H zeta‖ ≤
        C * Z ^ (-(1 / 2 : ℝ)) * (1 + H) ^ (3 : ℕ) := by
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_large_tail_bound K S mu nu hcomplex
    P psi hcal hunram g hzeta
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z H hZ hH
  exact (norm_actualLargeTargetBoxes_le_absolute K S mu nu hcomplex P psi g hzeta
    (hZ0.trans hZ) hH).trans (hb Z H hZ hH)

end Expansion.Project

#print axioms Expansion.Project.actual_large_initial_boxes_transport
#print axioms Expansion.Project.exists_actual_large_target_sum_bound
