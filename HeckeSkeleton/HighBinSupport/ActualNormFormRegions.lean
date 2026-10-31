import HeckeSkeleton.HighBinSupport.ActualNormFormAmplitudeGrid
import HeckeSkeleton.HighBinSupport.HighNormFormPointwisePartition

/-!
Measurable amplitude regions for the actual complete correction slots.
The label is computed from the literal slot value at the current triple
of contour heights. The regions therefore partition each row's height
box, while different label row sets may overlap.

The existing arithmetic prime cap proves all upper bounds used below.
Every positive amplitude has its lower witness at the same point of its
region, rather than at separately chosen maxima in different slots.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.NormFormRegions

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormAmplitudes NormFormAmplitudeGrid
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The norm of the original full slot with its geometric normalization. -/
def actualNormalizedSlotProfile (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e : ℝ)
    (i : Fin g.slots) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  (primeScale g Z) ^ (4 / 25 : ℝ) *
    ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖

/-- This is a concrete height fiber, not a supplied presentation region. -/
def actualSlotRegion (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) : Set (ℝ × (ℝ × ℝ)) :=
  NormForm.amplitudeRegion g.slots N (primeScale g Z) theta
    (actualNormalizedSlotProfile K S P psi g u Z a e) (heightBox H) label

/-- The vector and mean depend on the label, not on a later integration point. -/
def actualRegionAmplitude (g : PrimeWindowGeometry) (a theta : ℝ) (N : ℕ)
    (label : Fin g.slots → Fin (N + 1)) (i : Fin g.slots) : ℝ :=
  min (((label i).val : ℝ) * theta) (a - 1 / 2)

def actualRegionMean (g : PrimeWindowGeometry) (a theta : ℝ) (N : ℕ)
    (label : Fin g.slots → Fin (N + 1)) : ℝ :=
  (∑ i, actualRegionAmplitude g a theta N label i) / g.slots

/-- The concrete upper bound and lower-witness statement returned for
one actual region. This proposition is proved below, never assumed by
the complete region-integral theorem. -/
def ActualRegionSlotBounds (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) : Prop :=
  ∀ x ∈ actualSlotRegion K S P psi g u Z a e H theta N label, ∀ i,
    0 ≤ actualRegionAmplitude g a theta N label i ∧
    actualRegionAmplitude g a theta N label i ≤ a - 1 / 2 ∧
    ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
      (primeScale g Z) ^ (-(4 / 25 : ℝ) + actualRegionAmplitude g a theta N label i + theta) ∧
    (0 < actualRegionAmplitude g a theta N label i →
      (primeScale g Z) ^ actualRegionAmplitude g a theta N label i <
        ‖((primeScale g Z ^ (4 / 25 : ℝ) : ℝ) : ℂ) *
          actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖)

theorem actualSlotRegion_subset (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) :
    actualSlotRegion K S P psi g u Z a e H theta N label ⊆ heightBox H :=
  NormForm.amplitudeRegion_subset _ _ _ _ _ _ _

theorem actualSlotRegion_disjoint (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ) (N : ℕ) :
    Pairwise (fun label₁ label₂ => Disjoint
      (actualSlotRegion K S P psi g u Z a e H theta N label₁)
      (actualSlotRegion K S P psi g u Z a e H theta N label₂)) :=
  NormForm.amplitudeRegion_disjoint _ _ _ _ _ _

theorem iUnion_actualSlotRegion (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z a e H theta : ℝ) (N : ℕ) :
    (⋃ label, actualSlotRegion K S P psi g u Z a e H theta N label) = heightBox H :=
  NormForm.iUnion_amplitudeRegion _ _ _ _ _ _

/-- One arithmetic cutoff gives measurable regions for all rows and labels. -/
theorem exists_actualSlotRegion_measurable (g : PrimeWindowGeometry)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (u : FrequencyRow K S)
        (a : ℝ), 51 / 100 ≤ a → a ≤ 1 → ∀ H theta : ℝ, ∀ N : ℕ,
      ∀ label : Fin g.slots → Fin (N + 1),
        MeasurableSet (actualSlotRegion K S P psi g u Z a e H theta N label) := by
  obtain ⟨Z0, hZ0, hcontinuous⟩ := exists_actualSlotHeightProfile_continuous K S g he he1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ P psi u a ha ha1 H theta N label
  apply NormForm.amplitudeRegion_measurable
  · intro i
    exact ((hcontinuous Z hZ P psi ∅ u a ha ha1 i).norm.const_mul _).measurable
  · exact measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

/-- All upper bounds and all positive lower witnesses are obtained from
the real full correction. No desired slot or kernel estimate is an input. -/
theorem exists_actualSlotRegion_bounds
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val)
    {e eps eta kappa theta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
        frequencyRowNorm K S u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S psi companions P (arithmeticHighEulerData K S P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∀ label : Fin g.slots → Fin (N + 1),
        ActualRegionSlotBounds K S P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label := by
  obtain ⟨ZA, hZA, hamp⟩ := exists_actualFullSlotAmplitude K S psi companions hcomp P g
    hcal hpsi he he1 heps heta hkappa htheta hbudget N hN
  obtain ⟨ZX, hZX, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  refine ⟨max ZA ZX, hZA.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow label x hx i
  obtain ⟨A⟩ := hamp Z T ((le_max_left _ _).trans hZ) hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
  have hP1 : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans
    (hscale Z ((le_max_right _ _).trans hZ))
  have hP0 : 0 < primeScale g Z := zero_lt_one.trans_le hP1
  have hxbox := actualSlotRegion_subset K S P psi g u Z a e _ theta N label hx
  have hcap : actualNormalizedSlotProfile K S P psi g u Z a e i x ≤
      (primeScale g Z) ^ (a - 1 / 2 + theta) := by
    unfold actualNormalizedSlotProfile
    calc
      _ ≤ (primeScale g Z) ^ (4 / 25 : ℝ) *
          (primeScale g Z) ^ (-(4 / 25 : ℝ) + ActualFullSlotAmplitude.amplitude K S A i + theta) :=
        mul_le_mul_of_nonneg_left (A.upper i x hxbox) (Real.rpow_nonneg hP0.le _)
      _ = (primeScale g Z) ^ (ActualFullSlotAmplitude.amplitude K S A i + theta) := by
        rw [← Real.rpow_add hP0]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (add_le_add_right (A.range i).2 theta)
  have hb := NormForm.pointwiseBucket_spec (primeScale g Z) theta (a - 1 / 2)
    (actualNormalizedSlotProfile K S P psi g u Z a e i x) N hP1 htheta
    (by linarith) (by linarith) hcap
  have hlabel : (NormForm.pointwiseBucket (primeScale g Z) theta N
      (actualNormalizedSlotProfile K S P psi g u Z a e i x)).val = (label i).val := hx.2 i
  dsimp only at hb
  rw [hlabel] at hb
  refine ⟨hb.1, hb.2.1, ?_, ?_⟩
  · calc
      _ = (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
          actualNormalizedSlotProfile K S P psi g u Z a e i x := by
        unfold actualNormalizedSlotProfile
        rw [← mul_assoc, ← Real.rpow_add hP0]
        norm_num
      _ ≤ (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
          (primeScale g Z) ^ (actualRegionAmplitude g a theta N label i + theta) :=
        mul_le_mul_of_nonneg_left hb.2.2.1 (Real.rpow_nonneg hP0.le _)
      _ = _ := by rw [← Real.rpow_add hP0]; congr 1; ring
  · intro hg
    have h := hb.2.2.2 hg
    simpa only [actualNormalizedSlotProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hP0.le (4 / 25 : ℝ))] using h

end HighBinVerified.NormFormRegions

#print axioms HighBinVerified.NormFormRegions.actualSlotRegion_disjoint
#print axioms HighBinVerified.NormFormRegions.iUnion_actualSlotRegion
#print axioms HighBinVerified.NormFormRegions.exists_actualSlotRegion_measurable
#print axioms HighBinVerified.NormFormRegions.exists_actualSlotRegion_bounds
