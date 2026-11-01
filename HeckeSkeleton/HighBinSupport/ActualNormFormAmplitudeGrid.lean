import HeckeSkeleton.HighBinSupport.ActualNormFormAmplitudes

/-!
A finite amplitude grid for the actual complete correction slots.

The analytic cap and maximizing points are constructed in the imported
actual modules. The only additional budget below is a scalar inequality
for the chosen positive small parameters. The fixed threshold absorbs
the fixed constants, and the resulting slot bounds have constant one.
The values used for the lower witnesses are the actual complete slots,
multiplied only by their prescribed prime-scale power P^(4/25).
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormAmplitudeGrid

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormActual NormFormFullCorrection NormFormAmplitudes
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The finite label and its actual complete-slot witnesses. This
structure is constructed by the theorem below from the genuine detector
and local corrections; no caller supplies any of its analytic fields. -/
structure ActualFullSlotAmplitude (P : ProbeData K S) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S)
    (Z a e H theta : ℝ) (N : ℕ) where
  label : Fin g.slots → Fin (N + 1)
  point : Fin g.slots → ℝ × (ℝ × ℝ)
  point_mem : ∀ i, point i ∈ heightBox H
  range : ∀ i, 0 ≤ min (((label i).val : ℝ) * theta) (a - 1 / 2) ∧
    min (((label i).val : ℝ) * theta) (a - 1 / 2) ≤ a - 1 / 2
  upper : ∀ i, ∀ x ∈ heightBox H,
    ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
      (primeScale g Z) ^ (-(4 / 25 : ℝ) +
        min (((label i).val : ℝ) * theta) (a - 1 / 2) + theta)
  lower : ∀ i, 0 < min (((label i).val : ℝ) * theta) (a - 1 / 2) →
    (primeScale g Z) ^ (min (((label i).val : ℝ) * theta) (a - 1 / 2)) <
      ‖((primeScale g Z ^ (4 / 25 : ℝ) : ℝ) : ℂ) *
        actualSlotHeightProfile K S P psi g ∅ u Z a e i (point i)‖

def ActualFullSlotAmplitude.amplitude
    {P : ProbeData K S} {psi : HeckeCharacter K} {g : PrimeWindowGeometry}
    {u : FrequencyRow K S} {Z a e H theta : ℝ} {N : ℕ}
    (A : ActualFullSlotAmplitude K S P psi g u Z a e H theta N) (i : Fin g.slots) : ℝ :=
  min (((A.label i).val : ℝ) * theta) (a - 1 / 2)

def ActualFullSlotAmplitude.mean
    {P : ProbeData K S} {psi : HeckeCharacter K} {g : PrimeWindowGeometry}
    {u : FrequencyRow K S} {Z a e H theta : ℝ} {N : ℕ}
    (A : ActualFullSlotAmplitude K S P psi g u Z a e H theta N) : ℝ :=
  (∑ i, ActualFullSlotAmplitude.amplitude K S A i) / g.slots

/-- A genuine finite amplitude vector for one actual row. It is chosen
from the full-slot maxima and is fixed over the entire integration box.
The number of possible vectors is (N+1)^slots, independent of the row
family and the scale. -/
theorem exists_actual_fullSlot_amplitude_grid
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
      ∃ q : Fin g.slots → ℝ × (ℝ × ℝ), ∃ label : Fin g.slots → Fin (N + 1),
        (∀ i, q i ∈ heightBox (NormForm.internalHeight Z T kappa)) ∧
        ∀ i, let amplitude := min (((label i).val : ℝ) * theta) (a - 1 / 2)
          0 ≤ amplitude ∧ amplitude ≤ a - 1 / 2 ∧
          (∀ x ∈ heightBox (NormForm.internalHeight Z T kappa),
            ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
              (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude + theta)) ∧
          (0 < amplitude → (primeScale g Z) ^ amplitude <
            ‖((primeScale g Z ^ (4 / 25 : ℝ) : ℝ) : ℂ) *
              actualSlotHeightProfile K S P psi g ∅ u Z a e i (q i)‖) := by
  obtain ⟨C, ZM, hC, hZM, hmax⟩ := exists_actual_fullSlot_maximizers_with_cap
    K S psi companions hcomp P g hcal hpsi he he1 heps heta hkappa
  obtain ⟨ZX, hZX, hscale⟩ := NormFormPrimeCap.exists_primeScale_cutoff g
  let ell : ℝ := (1 / 6 : ℝ) / g.slots
  let r : ℝ := eps + eta
  let t : ℝ := ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps
  let E : ℝ := r + kappa * t
  let A : ℝ := C * (2 : ℝ) ^ r * (6 : ℝ) ^ t
  have hr : 0 < r := add_pos heps heta
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) heps.le
  have hell : 0 < ell := div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  have hA : 0 < A := mul_pos (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hhalf : 0 < ell * theta / 2 := div_pos (mul_pos hell htheta) (by norm_num)
  obtain ⟨ZA, hZA⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop hhalf)) A
  refine ⟨max ZM (max ZX ZA), hZM.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  have hZZM : ZM ≤ Z := (le_max_left _ _).trans hZ
  have hZZX : ZX ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZA : ZA ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 ≤ Z := hZM.trans hZZM
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hP1 : 1 ≤ primeScale g Z := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZZX)
  have hP0 : 0 < primeScale g Z := zero_lt_one.trans_le hP1
  have hHid : NormForm.internalHeight Z T kappa = Z ^ kappa := max_eq_right hTceiling
  have hH1 : 1 ≤ NormForm.internalHeight Z T kappa := by
    rw [hHid]
    exact Real.one_le_rpow hZ1 hkappa.le
  obtain ⟨q, hq, hqmax, hqcap⟩ := hmax Z T hZZM d hd u hu a
    (NormForm.internalHeight Z T kappa) (2 * NormForm.internalHeight Z T kappa + 2)
    ha ha1 (zero_le_one.trans hH1) (by linarith) hbelow
  let M : Fin g.slots → ℝ := fun i => (primeScale g Z) ^ (4 / 25 : ℝ) *
    ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i (q i)‖
  have hNu : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hNuZ : frequencyRowNorm K S u ≤ 2 * Z := hu1.trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1 hd1) (by norm_num))
  have hheight : 2 + (2 * NormForm.internalHeight Z T kappa + 2) ≤ 6 * Z ^ kappa := by
    rw [hHid] at hH1 ⊢
    linarith
  have hcommon : C * frequencyRowNorm K S u ^ r *
      (2 + (2 * NormForm.internalHeight Z T kappa + 2)) ^ t ≤ A * Z ^ E := by
    calc
      _ ≤ C * (2 * Z) ^ r * (6 * Z ^ kappa) ^ t :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hNu.le hNuZ hr.le) hC.le)
          (Real.rpow_le_rpow (by linarith) hheight ht)
          (Real.rpow_nonneg (by linarith) _) (by positivity)
      _ = A * Z ^ E := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hZ0.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hZ0.le kappa),
          ← Real.rpow_mul hZ0.le]
        dsimp only [A, E]
        rw [Real.rpow_add hZ0 r (kappa * t)]
        ring
  have hPscale (b : ℝ) : (primeScale g Z) ^ b = Z ^ (ell * b) :=
    (Real.rpow_mul hZ0.le ell b).symm
  have hMupper : ∀ i, M i ≤ (primeScale g Z) ^ (a - 1 / 2 + theta) := by
    intro i
    calc
      M i ≤ (primeScale g Z) ^ (4 / 25 : ℝ) *
          (C * frequencyRowNorm K S u ^ r *
            (2 + (2 * NormForm.internalHeight Z T kappa + 2)) ^ t *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e + eta)) :=
        mul_le_mul_of_nonneg_left (hqcap i) (Real.rpow_nonneg hP0.le _)
      _ ≤ (primeScale g Z) ^ (4 / 25 : ℝ) *
          (A * Z ^ E * (primeScale g Z) ^ (a - 33 / 50 + 8 * e + eta)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcommon (Real.rpow_nonneg hP0.le _))
          (Real.rpow_nonneg hP0.le _)
      _ = A * Z ^ E * (primeScale g Z) ^ (a - 1 / 2 + 8 * e + eta) := by
        rw [show a - 1 / 2 + 8 * e + eta =
          (4 / 25 : ℝ) + (a - 33 / 50 + 8 * e + eta) by ring,
          Real.rpow_add hP0 (4 / 25 : ℝ) (a - 33 / 50 + 8 * e + eta)]
        ring
      _ = A * Z ^ (E + ell * (a - 1 / 2 + 8 * e + eta)) := by
        rw [hPscale, mul_assoc, ← Real.rpow_add hZ0]
      _ ≤ Z ^ (ell * theta / 2) * Z ^ (E + ell * (a - 1 / 2 + 8 * e + eta)) :=
        mul_le_mul_of_nonneg_right (hZA Z hZZA) (Real.rpow_nonneg hZ0.le _)
      _ = Z ^ (ell * theta / 2 + E + ell * (a - 1 / 2 + 8 * e + eta)) := by
        rw [← Real.rpow_add hZ0]
        congr 1
        ring
      _ ≤ Z ^ (ell * (a - 1 / 2 + theta)) := by
        apply Real.rpow_le_rpow_of_exponent_le hZ1
        change E + ell * (8 * e + eta) ≤ ell * theta / 2 at hbudget
        nlinarith
      _ = (primeScale g Z) ^ (a - 1 / 2 + theta) := (hPscale _).symm
  have hlabel (i : Fin g.slots) := NormForm.exists_amplitude_bucket
    (primeScale g Z) theta (a - 1 / 2) (M i) N hP1 htheta (by linarith)
      (by linarith) (hMupper i)
  choose label hlabel using hlabel
  refine ⟨q, label, hq, ?_⟩
  intro i
  obtain ⟨hg0, hg1, hupper, hlower⟩ := hlabel i
  refine ⟨hg0, hg1, ?_, ?_⟩
  · intro x hx
    have hscaled : (primeScale g Z) ^ (4 / 25 : ℝ) *
        ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖ ≤
        (primeScale g Z) ^ (min (((label i).val : ℝ) * theta) (a - 1 / 2) + theta) :=
      (mul_le_mul_of_nonneg_left (hqmax i x hx) (Real.rpow_nonneg hP0.le _)).trans hupper
    calc
      _ = (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
          ((primeScale g Z) ^ (4 / 25 : ℝ) *
            ‖actualSlotHeightProfile K S P psi g ∅ u Z a e i x‖) := by
        rw [← mul_assoc, ← Real.rpow_add hP0]
        norm_num
      _ ≤ (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
          (primeScale g Z) ^ (min (((label i).val : ℝ) * theta) (a - 1 / 2) + theta) :=
        mul_le_mul_of_nonneg_left hscaled (Real.rpow_nonneg hP0.le _)
      _ = _ := by rw [← Real.rpow_add hP0]; congr 1; ring
  · intro hg
    have h := hlower hg
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hP0.le (4 / 25 : ℝ)), M] using h

/-- The concrete amplitude object is populated by the actual full-slot
grid, rather than postulated as presentation data. -/
theorem exists_actualFullSlotAmplitude
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
      Nonempty (ActualFullSlotAmplitude K S P psi g u Z a e
        (NormForm.internalHeight Z T kappa) theta N) := by
  obtain ⟨Z0, hZ0, hgrid⟩ := exists_actual_fullSlot_amplitude_grid
    K S psi companions hcomp P g hcal hpsi he he1 heps heta hkappa htheta hbudget N hN
  refine ⟨Z0, hZ0, ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  obtain ⟨q, label, hq, hgrid⟩ := hgrid Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  exact ⟨{
    label := label
    point := q
    point_mem := hq
    range := fun i => ⟨(hgrid i).1, (hgrid i).2.1⟩
    upper := fun i => (hgrid i).2.2.1
    lower := fun i => (hgrid i).2.2.2 }⟩

end HighBinVerified.NormFormAmplitudeGrid

#print axioms HighBinVerified.NormFormAmplitudeGrid.exists_actual_fullSlot_amplitude_grid
#print axioms HighBinVerified.NormFormAmplitudeGrid.exists_actualFullSlotAmplitude
