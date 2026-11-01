import HeckeSkeleton.HighBinSupport.ActualNormFormRegions
import HeckeSkeleton.HighBinSupport.ActualNormFormIntegral

/-!
Literal restricted-height pieces of the actual compensated row contour.
Each piece uses its own computed pointwise label mean. The sum over all
finite labels is the original row contour, proved by genuine integrability
and the exact measurable partition. The complete theorem constructs the
slot bounds; no piece estimate or supplied region is a hypothesis.

As in the whole-box sharp norm form, the original prime normalizer is
bounded by the proved actual prime-window theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HighBinVerified.NormFormRegionIntegral

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormRegions
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

/-- The original kernel on the three final contour lines. -/
def actualRegionKernel (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀) (Z a e : ℝ)
    (x : ℝ × (ℝ × ℝ)) : ℂ :=
  compensatedRowMellinKernel K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
    (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)

/-- The piece is a restricted integral, with the original normalization. -/
def actualRegionPiece (P : ProbeData K S₀) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S₀) (Z a e H theta : ℝ)
    (N : ℕ) (label : Fin g.slots → Fin (N + 1)) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    ∫ x in actualSlotRegion K S₀ P psi g u Z a e H theta N label,
      actualRegionKernel K S μ P psi g u Z a e x

/-- At every scale and height, genuine integrability of the literal
kernel suffices for the exact finite-label decomposition. Measurability
of the computed regions is proved without a cutoff. This statement does
not assert all-scale integrability or require a norm-form bound. -/
theorem sum_actualRegionPiece_eq_rowContourBox
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (u : FrequencyRow K S₀) (Z a e H theta : ℝ) (N : ℕ)
    (ha : 51 / 100 ≤ a) (he : 0 < e)
    (hi : IntegrableOn (actualRegionKernel K S μ P psi g u Z a e) (heightBox H)) :
    (∑ label : Fin g.slots → Fin (N + 1),
      actualRegionPiece K S μ P psi g u Z a e H theta N label) =
      rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z H
        (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  let f := actualRegionKernel K S μ P psi g u Z a e
  let region := actualSlotRegion K S₀ P psi g u Z a e H theta N
  have hRegion (label : Fin g.slots → Fin (N + 1)) : MeasurableSet (region label) :=
    actualSlotRegion_measurable K S₀ P psi g u Z a e H theta N label ha he
  have hsubset (label : Fin g.slots → Fin (N + 1)) : region label ⊆ heightBox H :=
    actualSlotRegion_subset K S₀ P psi g u Z a e H theta N label
  have hsum : (∑ label : Fin g.slots → Fin (N + 1), ∫ x in region label, f x) =
      ∫ x in heightBox H, f x := by
    rw [← integral_iUnion_fintype hRegion
      (actualSlotRegion_disjoint K S₀ P psi g u Z a e H theta N)
      (fun label => hi.mono_set (hsubset label))]
    rw [iUnion_actualSlotRegion]
  have hiProd : Integrable f
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)) := by
    simpa only [IntegrableOn, ← NormFormIntegral.heightBoxMeasure_eq] using hi
  change (∑ label : Fin g.slots → Fin (N + 1),
    (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) * ∫ x in region label, f x) = _
  rw [← Finset.mul_sum, hsum]
  exact (NormFormIntegral.rowContourBox_eq_heightBox_integral K S μ P psi
    (arithmeticHighEulerData K S₀ P psi) g ∅ u Z H (a + 16 * e) (1 - a - 6 * e) hiProd).symm

/-- The exact measurable pieces, their slot witnesses and their individual
norm forms are simultaneous conclusions for the actual arithmetic data. -/
theorem exists_actual_region_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e eps eta kappa theta nu : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hnu : 0 < nu)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      (∀ label : Fin g.slots → Fin (N + 1),
        MeasurableSet (actualSlotRegion K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) ∧
        ActualRegionSlotBounds K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label ∧
        IntegrableOn (actualRegionKernel K S μ P psi g u Z a e)
          (actualSlotRegion K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label) ∧
        ‖actualRegionPiece K S μ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label‖ ≤
          C * Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) +
            (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
            kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
              2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps + 3))) ∧
      (∑ label : Fin g.slots → Fin (N + 1),
        actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) =
        rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  obtain ⟨ZB, hZB, hbounds⟩ := exists_actualSlotRegion_bounds K S₀ psi companions hcomp P g
    hcal hpsi he he1 heps heta hkappa htheta hbudget N hN
  obtain ⟨C, ZK, hC, hZK, hkernel⟩ := NormFormKernel.exists_actual_kernel_normForm_of_slot_bounds
    K S μ psi companions hcomp P g he he1 heps heta hkappa htheta hnu
  obtain ⟨CI, ZI, hCI, hZI, hint⟩ := NormFormIntegral.exists_actual_rowContour_normForm
    K S μ psi companions hcomp P g hcal hpsi he he1 heps heta hkappa htheta hnu hbudget N hN
  let cpi : ℂ := (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))
  refine ⟨8 * (‖cpi‖ + 1) * C, max ZB (max ZK ZI), by positivity,
    hZB.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
  have hZZB : ZB ≤ Z := (le_max_left _ _).trans hZ
  have hZZK : ZK ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZI : ZI ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 ≤ Z := hZB.trans hZZB
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let H : ℝ := NormForm.internalHeight Z T kappa
  let f := actualRegionKernel K S μ P psi g u Z a e
  let region := actualSlotRegion K S₀ P psi g u Z a e H theta N
  have hHid : H = Z ^ kappa := max_eq_right hTcap
  have hH1 : 1 ≤ H := by rw [hHid]; exact Real.one_le_rpow hZ1 hkappa.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  obtain ⟨A, hi, hwhole⟩ := hint Z T hZZI hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
  have hiBox : IntegrableOn f (heightBox H) := by
    simpa only [IntegrableOn, f, actualRegionKernel, H,
      ← NormFormIntegral.heightBoxMeasure_eq] using hi
  have hRegion (label : Fin g.slots → Fin (N + 1)) : MeasurableSet (region label) :=
    actualSlotRegion_measurable K S₀ P psi g u Z a e H theta N label ha he
  have hsubset (label : Fin g.slots → Fin (N + 1)) : region label ⊆ heightBox H :=
    actualSlotRegion_subset K S₀ P psi g u Z a e H theta N label
  have hB (label : Fin g.slots → Fin (N + 1)) :=
    hbounds Z T hZZB hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow label
  have hHpower : H ^ 3 = Z ^ (3 * kappa) := by
    rw [hHid, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    congr 1
    ring
  constructor
  · intro label
    refine ⟨hRegion label, hB label, hiBox.mono_set (hsubset label), ?_⟩
    let b : ℝ := NormForm.rowExponent d a (actualRegionMean g a theta N label) +
      (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
      kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
        2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)
    have hpoint : ∀ x ∈ region label, ‖f x‖ ≤ C * Z ^ b := by
      intro x hx
      exact hkernel Z T hZZK hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
        (actualRegionAmplitude g a theta N label) x (hsubset label hx)
        (fun i => (hB label x hx i).2.2.1)
    have hfinite : (volume : Measure (ℝ × (ℝ × ℝ))) (heightBox H) < ∞ :=
      (heightBox_isCompact H).measure_lt_top
    have hb : ‖∫ x in region label, f x‖ ≤
        (C * Z ^ b) * (volume : Measure (ℝ × (ℝ × ℝ))).real (heightBox H) :=
      (norm_setIntegral_le_of_norm_le_const
        (lt_of_le_of_lt (measure_mono (hsubset label)) hfinite) hpoint).trans
        (mul_le_mul_of_nonneg_left (measureReal_mono (hsubset label) hfinite.ne)
          (mul_nonneg hC.le (Real.rpow_nonneg hZ0.le _)))
    change ‖cpi * ∫ x in region label, f x‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (‖cpi‖ + 1) * ((C * Z ^ b) *
          (volume : Measure (ℝ × (ℝ × ℝ))).real (heightBox H)) :=
        mul_le_mul (by linarith : ‖cpi‖ ≤ ‖cpi‖ + 1) hb (norm_nonneg _) (by positivity)
      _ = (8 * (‖cpi‖ + 1) * C) * (Z ^ b * Z ^ (3 * kappa)) := by
        rw [NormFormIntegral.heightBox_volume_real H hH0, hHpower]
        ring
      _ = (8 * (‖cpi‖ + 1) * C) * Z ^ (b + 3 * kappa) := by
        rw [← Real.rpow_add hZ0]
      _ = _ := by
        congr 2
        dsimp only [b]
        ring
  · exact sum_actualRegionPiece_eq_rowContourBox K S μ P psi g u Z a e H theta N ha he hiBox

/-- The exact pieces, witnesses and decomposition with the original
quarter-lambda loss. All small parameters precede scales, rows and labels. -/
theorem exists_actual_region_normForm_quarter_loss
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
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      (∀ label : Fin g.slots → Fin (N + 1),
        MeasurableSet (actualSlotRegion K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) ∧
        ActualRegionSlotBounds K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label ∧
        IntegrableOn (actualRegionKernel K S μ P psi g u Z a e)
          (actualSlotRegion K S₀ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label) ∧
        ‖actualRegionPiece K S μ P psi g u Z a e
            (NormForm.internalHeight Z T kappa) theta N label‖ ≤
          C * Z ^ (NormForm.rowExponent d a (actualRegionMean g a theta N label) + lam / 4)) ∧
      (∑ label : Fin g.slots → Fin (N + 1),
        actualRegionPiece K S μ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N label) =
        rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
          (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50) := by
  obtain ⟨eps, eta, kappa, theta, nu, N, heps, heta, hkappa, htheta, hnu, hN, hbudget, hloss⟩ :=
    NormForm.exists_full_normForm_parameter_budget g.slots g.slots_pos
      (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)) lam e
      (Nat.cast_nonneg _) hlam he.le heLam
  obtain ⟨C, Z0, hC, hZ0, hrow⟩ := exists_actual_region_normForm K S μ psi companions hcomp
    P g hcal hpsi he he1 heps heta hkappa htheta hnu hbudget N hN
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
  obtain ⟨hlabel, hsum⟩ := hrow Z T hZ hT hTcap d hd hd1 u hu hu1 a ha ha1 hbelow
  refine ⟨?_, hsum⟩
  intro label
  obtain ⟨hmeas, hbounds, hint, hb⟩ := hlabel label
  refine ⟨hmeas, hbounds, hint, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (hZ0.trans hZ)
  have h := hloss d (by linarith) hd1
  linarith

end HighBinVerified.NormFormRegionIntegral

#print axioms HighBinVerified.NormFormRegionIntegral.sum_actualRegionPiece_eq_rowContourBox
#print axioms HighBinVerified.NormFormRegionIntegral.exists_actual_region_normForm
#print axioms HighBinVerified.NormFormRegionIntegral.exists_actual_region_normForm_quarter_loss
