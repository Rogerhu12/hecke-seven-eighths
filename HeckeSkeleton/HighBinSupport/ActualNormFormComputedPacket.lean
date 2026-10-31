import HeckeSkeleton.HighBinSupport.ActualNormFormRegionPacket

/-!
A concrete finite HIGHBIN packet at every scale.

The row gate is the integrability predicate for the literal compensated
kernel. It makes the finite partition identity valid even outside the
eventual analytic range. The actual norm-form theorem proves that every
input row passes this gate in that range; no row is discarded there.

Amplitude vectors, means, row sets and pieces are computed from the
actual height regions. The witness subdivisions remain explicit data
arguments. No witness-cover assertion or default empty recipe is added.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.NormFormComputedPacket

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormRegions NormFormRegionIntegral NormFormRegionPacket
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The gate tests the original kernel on the original complete height box. -/
def integrableRows (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H : ℝ) : Finset (FrequencyRow K S₀) :=
  F.filter fun u => IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H)

theorem mem_integrableRows_iff (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z a e H : ℝ) (u : FrequencyRow K S₀) :
    u ∈ integrableRows K S μ P psi g F Z a e H ↔
      u ∈ F ∧ IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H) := by
  simp only [integrableRows, Finset.mem_filter]

theorem integrableRows_subset (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀)) (Z a e H : ℝ) :
    integrableRows K S μ P psi g F Z a e H ⊆ F := by
  intro u hu
  exact (Finset.mem_filter.mp hu).1

theorem integrableRows_eq (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀)) (Z a e H : ℝ)
    (hi : ∀ u ∈ F,
      IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H)) :
    integrableRows K S μ P psi g F Z a e H = F := by
  ext u
  simp only [mem_integrableRows_iff]
  exact ⟨And.left, fun hu => ⟨hu, hi u hu⟩⟩

/-- A finite family of integrable regions gives integrability on the
whole box by the actual partition identity. -/
theorem integrableOn_heightBox_of_regions (P : ProbeData K S₀)
    (psi : HeckeCharacter K) (g : PrimeWindowGeometry) (u : FrequencyRow K S₀)
    (Z a e H theta : ℝ) (N : ℕ)
    (hi : ∀ label : Fin g.slots → Fin (N + 1),
      IntegrableOn (actualRegionKernel K S μ P psi g u Z a e)
        (actualSlotRegion K S₀ P psi g u Z a e H theta N label)) :
    IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H) := by
  rw [← iUnion_actualSlotRegion K S₀ P psi g u Z a e H theta N]
  exact integrableOn_finite_iUnion.mpr hi

/-- Every block field is computed from the actual row kernel and regions.
The supplied subdivisions are data recipes; their saturation is a separate
source theorem. -/
def computedRegionBlock (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z d a e H theta : ℝ) (N : ℕ)
    (subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (subdivision : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀)) :
    ModerateBlock (FrequencyRow K S₀) g.slots :=
  actualRegionModerateBlock K S μ P psi g
    (integrableRows K S μ P psi g F Z a e H) Z d a e H theta N
    subdivisionCount subdivision

/-- Literal finite-label decomposition at every scale. Only the numerical
contour range is required; integrability is provided by the row gate. -/
theorem computedRegionBlock_value_eq_pieces
    (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z d a e H theta : ℝ) (N : ℕ)
    (subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (subdivision : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀))
    (ha : 51 / 100 ≤ a) (he : 0 < e) :
    (computedRegionBlock K S μ P psi g F Z d a e H theta N
      subdivisionCount subdivision).value =
      ∑ label : Fin g.slots → Fin (N + 1),
        ∑ u ∈ ((computedRegionBlock K S μ P psi g F Z d a e H theta N
          subdivisionCount subdivision).amplitudeSet label).rows,
          actualRegionPiece K S μ P psi g u Z a e H theta N label := by
  symm
  change (∑ label : Fin g.slots → Fin (N + 1),
    ∑ u ∈ actualRegionRows K S P psi g
      (integrableRows K S μ P psi g F Z a e H) Z a e H theta N label,
      actualRegionPiece K S μ P psi g u Z a e H theta N label) = _
  simp_rw [sum_actualRegionRows_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact sum_actualRegionPiece_eq_rowContourBox K S μ P psi g u Z a e H theta N ha he
    ((mem_integrableRows_iff K S μ P psi g F Z a e H u).mp hu).2

/-- Fixed finite label cardinality, independent of scales, heights and rows. -/
theorem computedRegionLabel_card (g : PrimeWindowGeometry) (N : ℕ) :
    (Finset.univ : Finset (Fin g.slots → Fin (N + 1))).card = (N + 1) ^ g.slots := by
  simp

/-- The fixed label count has height degree zero and consumes any
nonnegative prescribed scale loss. -/
theorem computedRegionLabel_count_bound (g : PrimeWindowGeometry) (N : ℕ)
    {Z loss : ℝ} (hZ : 1 ≤ Z) (hloss : 0 ≤ loss) :
    (((Finset.univ : Finset (Fin g.slots → Fin (N + 1))).card : ℕ) : ℝ) ≤
      (((N + 1) ^ g.slots : ℕ) : ℝ) * Z ^ loss := by
  rw [computedRegionLabel_card]
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow hZ hloss)

/-- The original mean is the computed full-slot mean by definition. -/
theorem computedRegionBlock_mean
    (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (F : Finset (FrequencyRow K S₀))
    (Z d a e H theta : ℝ) (N : ℕ)
    (subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ)
    (subdivision : (label : Fin g.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀))
    (label : Fin g.slots → Fin (N + 1)) :
    ((computedRegionBlock K S μ P psi g F Z d a e H theta N
      subdivisionCount subdivision).amplitudeSet label).mean =
      actualRegionMean g a theta N label := rfl

/-- The genuine analytic theorem removes the gate in the eventual range
and supplies the original norm-form exponent for every computed label.
No piece identity, amplitude value or desired estimate is a caller input. -/
theorem exists_computedRegionBlock_normForm
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
      integrableRows K S μ P psi g F Z a e (NormForm.internalHeight Z T kappa) = F ∧
      ∀ subdivisionCount : (Fin g.slots → Fin (N + 1)) → ℝ → ℕ,
      ∀ subdivision : (label : Fin g.slots → Fin (N + 1)) →
        (t : ℝ) → Fin (subdivisionCount label t) → WitnessSubdivision (FrequencyRow K S₀),
      ∀ label : Fin g.slots → Fin (N + 1),
      let block := computedRegionBlock K S μ P psi g F Z d a e
        (NormForm.internalHeight Z T kappa) theta N subdivisionCount subdivision
      (∀ u ∈ (block.amplitudeSet label).rows,
        ActualRegionSlotBounds K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) ∧
      (∑ u ∈ (block.amplitudeSet label).rows,
        ‖actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label‖) ≤
        C * ((block.amplitudeSet label).rows.card : ℝ) *
          Z ^ (NormForm.rowExponent d a (block.amplitudeSet label).mean + lam / 4) := by
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hrow⟩ :=
    exists_actual_region_normForm_quarter_loss K S μ psi companions hcomp
      P g hcal hpsi he he1 hlam heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTcap d hd hd1 a ha ha1 F hF
  have hrows (u : FrequencyRow K S₀) (hu : u ∈ F) :=
    hrow Z T hZ hT hTcap d hd hd1 u (hF u hu).1 (hF u hu).2.1 a ha ha1 (hF u hu).2.2
  have hi (u : FrequencyRow K S₀) (hu : u ∈ F) :
      IntegrableOn (actualRegionKernel K S μ P psi g u Z a e)
        (heightBox (NormForm.internalHeight Z T kappa)) :=
    integrableOn_heightBox_of_regions K S μ P psi g u Z a e
      (NormForm.internalHeight Z T kappa) theta N
      (fun label => ((hrows u hu).1 label).2.2.1)
  have hgate := integrableRows_eq K S μ P psi g F Z a e
    (NormForm.internalHeight Z T kappa) hi
  refine ⟨hgate, ?_⟩
  intro subdivisionCount subdivision label
  dsimp only [computedRegionBlock, actualRegionModerateBlock,
    actualRegionAmplitudeSet]
  rw [hgate]
  constructor
  · intro u hu
    have huF := (mem_actualRegionRows_iff K S P psi g F Z a e
      (NormForm.internalHeight Z T kappa) theta N label u).mp hu
    exact ((hrows u huF.1).1 label).2.1
  · calc
      (∑ u ∈ actualRegionRows K S P psi g F Z a e
          (NormForm.internalHeight Z T kappa) theta N label,
        ‖actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label‖) ≤
        ∑ _u ∈ actualRegionRows K S P psi g F Z a e
          (NormForm.internalHeight Z T kappa) theta N label,
          C * Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4) := by
        apply Finset.sum_le_sum
        intro u hu
        have huF := (mem_actualRegionRows_iff K S P psi g F Z a e
          (NormForm.internalHeight Z T kappa) theta N label u).mp hu
        exact ((hrows u huF.1).1 label).2.2.2
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, AmplitudeSet.mean, actualRegionMean]
        ring

end HighBinVerified.NormFormComputedPacket

#print axioms HighBinVerified.NormFormComputedPacket.computedRegionBlock_value_eq_pieces
#print axioms HighBinVerified.NormFormComputedPacket.computedRegionLabel_card
#print axioms HighBinVerified.NormFormComputedPacket.computedRegionLabel_count_bound
#print axioms HighBinVerified.NormFormComputedPacket.exists_computedRegionBlock_normForm
