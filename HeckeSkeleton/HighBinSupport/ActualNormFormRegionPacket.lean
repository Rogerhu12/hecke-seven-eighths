import HeckeSkeleton.HighBinSupport.ActualNormFormRegionIntegral
import HeckeGeneral.Analysis.TIPSources

/-!
Finite packets of actual restricted-height pieces, with the repository's
original `AmplitudeSet` and `ModerateBlock` data types.

Rows are retained exactly when their computed label region is nonempty.
The amplitude and mean are the computed grid values, and all slot values
are evaluated at one chosen point of that actual region. No estimate is
an input to the packet norm theorem. Witness subdivision recipes remain
explicit constructor arguments; no empty or fabricated subdivision is
used to claim the independent `WitnessCover` obligation.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.NormFormRegionPacket

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormAmplitudes NormFormRegions NormFormRegionIntegral
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))

def actualRegionRows (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1)) :
    Finset (FrequencyRow K S₀) :=
  F.filter fun u => (actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty

theorem mem_actualRegionRows_iff (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (u : FrequencyRow K S₀) :
    u ∈ actualRegionRows K S P psi g F Z a e H theta N label ↔
      u ∈ F ∧ (actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty := by
  simp only [actualRegionRows, Finset.mem_filter]

theorem actualRegionRows_subset (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1)) :
    actualRegionRows K S P psi g F Z a e H theta N label ⊆ F := by
  intro u hu
  exact (Finset.mem_filter.mp hu).1

/-- The construction retains every original row whenever the height box
is nonempty; row sets are allowed to overlap across different labels. -/
theorem exists_mem_actualRegionRows (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (hH : 0 ≤ H)
    (u : FrequencyRow K S₀) (hu : u ∈ F) :
    ∃ label : Fin g.slots → Fin (N + 1),
      u ∈ actualRegionRows K S P psi g F Z a e H theta N label := by
  have hzero : (0, 0, 0) ∈ heightBox H := by
    change (-H ≤ 0 ∧ 0 ≤ H) ∧ (-H ≤ 0 ∧ 0 ≤ H) ∧ (-H ≤ 0 ∧ 0 ≤ H)
    exact ⟨⟨by linarith, hH⟩, ⟨by linarith, hH⟩, ⟨by linarith, hH⟩⟩
  have hcover : (0, 0, 0) ∈
      ⋃ label, actualSlotRegion K S₀ P psi g u Z a e H theta N label := by
    rw [iUnion_actualSlotRegion]
    exact hzero
  obtain ⟨label, hlabel⟩ := Set.mem_iUnion.mp hcover
  exact ⟨label, Finset.mem_filter.mpr ⟨hu, ⟨(0, 0, 0), hlabel⟩⟩⟩

/-- A single height triple for all slot witnesses of a nonempty region.
The default point is used only outside the retained row set. -/
def actualRegionPoint (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1)) :
    ℝ × (ℝ × ℝ) :=
  if h : (actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty
  then Classical.choose h else (0, 0, 0)

theorem actualRegionPoint_mem (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (h : (actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty) :
    actualRegionPoint K S P psi g u Z a e H theta N label ∈
      actualSlotRegion K S₀ P psi g u Z a e H theta N label := by
  simp only [actualRegionPoint, dif_pos h]
  exact Classical.choose_spec h

def actualRegionSlotValue (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z a e H theta : ℝ) (N : ℕ)
    (label : Fin g.slots → Fin (N + 1)) (i : Fin g.slots) (u : FrequencyRow K S₀) : ℂ :=
  ((primeScale g Z ^ (4 / 25 : ℝ) : ℝ) : ℂ) *
    actualSlotHeightProfile K S₀ P psi g ∅ u Z a e i
      (actualRegionPoint K S P psi g u Z a e H theta N label)

/-- The original amplitude-set data type, populated with actual region
rows, amplitudes and simultaneous slot values. Subdivisions are supplied
as a separate recipe; this definition asserts no `WitnessCover`. -/
def actualRegionAmplitudeSet (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (subdivisionCount : ℝ → ℕ)
    (subdivision : (t : ℝ) → Fin (subdivisionCount t) → WitnessSubdivision (FrequencyRow K S₀)) :
    AmplitudeSet (FrequencyRow K S₀) g.slots where
  rows := actualRegionRows K S P psi g F Z a e H theta N label
  amplitude := actualRegionAmplitude g a theta N label
  slotValue := actualRegionSlotValue K S P psi g Z a e H theta N label
  subdivisionCount := subdivisionCount
  subdivision := subdivision

theorem actualRegionAmplitudeSet_mean (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (subdivisionCount : ℝ → ℕ)
    (subdivision : (t : ℝ) → Fin (subdivisionCount t) → WitnessSubdivision (FrequencyRow K S₀)) :
    (actualRegionAmplitudeSet K S P psi g F Z a e H theta N label
      subdivisionCount subdivision).mean = actualRegionMean g a theta N label := rfl

/-- The range required by the original `BlockSource` includes the closed
upper endpoint a=1. It holds even for labels with no retained rows. -/
theorem actualRegionAmplitude_range (g : PrimeWindowGeometry) (a theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) (ha : 1 / 2 ≤ a)
    (htheta : 0 ≤ theta) (i : Fin g.slots) :
    0 ≤ actualRegionAmplitude g a theta N label i ∧
      actualRegionAmplitude g a theta N label i ≤ (2 * a - 1) / 2 := by
  unfold actualRegionAmplitude
  constructor
  · exact le_min (mul_nonneg (Nat.cast_nonneg _) htheta) (by linarith)
  · linarith [min_le_right (((label i).val : ℝ) * theta) (a - 1 / 2)]

/-- The actual slot value satisfies the original base-Z lower-witness
formula, with no independently chosen complex witness. -/
theorem actualRegionSlotValue_lower (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H theta : ℝ) (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (hZ : 0 < Z) (u : FrequencyRow K S₀)
    (hu : u ∈ actualRegionRows K S P psi g F Z a e H theta N label)
    (hB : ActualRegionSlotBounds K S₀ P psi g u Z a e H theta N label)
    (i : Fin g.slots) (hi : 0 < actualRegionAmplitude g a theta N label i) :
    Z ^ (((1 / 6 : ℝ) / g.slots) * actualRegionAmplitude g a theta N label i) ≤
      ‖actualRegionSlotValue K S P psi g Z a e H theta N label i u‖ := by
  have hnonempty := (mem_actualRegionRows_iff K S P psi g F Z a e H theta N label u).mp hu
  have hx := actualRegionPoint_mem K S P psi g u Z a e H theta N label hnonempty.2
  have hb := ((hB _ hx i).2.2.2 hi).le
  simpa only [actualRegionSlotValue, primeScale, ← Real.rpow_mul hZ.le] using hb

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The block value remains the complete fixed-bin row contour sum. -/
def actualRegionModerateBlock (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z d a e H theta : ℝ) (N : ℕ)
    (subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (subdivision : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    ModerateBlock (FrequencyRow K S₀) g.slots where
  shell := d
  bin := a
  value := ∑ u ∈ F, rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi)
    g ∅ u Z H (a + 16 * e) (1 - a - 6 * e) (17 / 50)
  Label := Fin g.slots → Fin (N + 1)
  amplitudeSet := fun label => actualRegionAmplitudeSet K S P psi g F Z a e H theta N label
    (subdivisionCount label) (subdivision label)

theorem actualRegionPiece_eq_zero_of_empty (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1))
    (h : ¬(actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty) :
    actualRegionPiece K S μ P psi g u Z a e H theta N label = 0 := by
  have hR := Set.not_nonempty_iff_eq_empty.mp h
  simp only [actualRegionPiece, hR, setIntegral_empty, mul_zero]

/-- Removing rows with empty regions changes no label contribution. -/
theorem sum_actualRegionRows_eq_sum (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀)) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) :
    (∑ u ∈ actualRegionRows K S P psi g F Z a e H theta N label,
      actualRegionPiece K S μ P psi g u Z a e H theta N label) =
      ∑ u ∈ F, actualRegionPiece K S μ P psi g u Z a e H theta N label := by
  simp only [actualRegionRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hR : (actualSlotRegion K S₀ P psi g u Z a e H theta N label).Nonempty
  · simp only [if_pos hR]
  · rw [if_neg hR]
    exact (actualRegionPiece_eq_zero_of_empty K S μ P psi g u Z a e H theta N label hR).symm

/-- A finite family of original rows gives a genuine finite packet of
restricted pieces. Row sets may overlap; the per-row height partition
proves the exact total identity. No row-cardinality estimate is assumed. -/
theorem exists_actual_region_packet_normForm_quarter_loss
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e lam : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ F : Finset (FrequencyRow K S₀),
      (∀ u ∈ F, Z ^ d ≤ frequencyRowNorm K S₀ u ∧
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d ∧
        rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
          (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e)) →
      (∀ label : Fin g.slots → Fin (N + 1),
        (∀ u ∈ actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label,
          ActualRegionSlotBounds K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label) ∧
        (∑ u ∈ actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label,
          ‖actualRegionPiece K S μ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label‖) ≤
          C * ((actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label).card : ℝ) *
            Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4)) ∧
      (∑ label : Fin g.slots → Fin (N + 1),
        ∑ u ∈ actualRegionRows K S P psi g F Z a e
          (NormForm.internalHeight Z T kappa) theta N label,
        actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) =
        ∑ u ∈ F, rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hrow⟩ :=
    exists_actual_region_normForm_quarter_loss K S μ psi companions hcomp
      P g hcal hpsi he he1 hlam heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTcap d hd hd1 a ha ha1 F hF
  have hrows (u : FrequencyRow K S₀) (hu : u ∈ F) :=
    hrow Z T hZ hT hTcap d hd hd1 u (hF u hu).1 (hF u hu).2.1 a ha ha1 (hF u hu).2.2
  constructor
  · intro label
    constructor
    · intro u hu
      have huF := (mem_actualRegionRows_iff K S P psi g F Z a e _ theta N label u).mp hu
      exact ((hrows u huF.1).1 label).2.1
    · calc
        _ ≤ ∑ _u ∈ actualRegionRows K S P psi g F Z a e
            (NormForm.internalHeight Z T kappa) theta N label,
            C * Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4) := by
          apply Finset.sum_le_sum
          intro u hu
          have huF := (mem_actualRegionRows_iff K S P psi g F Z a e _ theta N label u).mp hu
          exact ((hrows u huF.1).1 label).2.2.2
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  · simp_rw [sum_actualRegionRows_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    exact (hrows u hu).2

end HighBinVerified.NormFormRegionPacket

#print axioms HighBinVerified.NormFormRegionPacket.actualRegionAmplitudeSet_mean
#print axioms HighBinVerified.NormFormRegionPacket.actualRegionSlotValue_lower
#print axioms HighBinVerified.NormFormRegionPacket.exists_actual_region_packet_normForm_quarter_loss
