import HeckeSkeleton.HighBin
import HeckeSkeleton.HighBinSupport.ActualBoundaryEstimate

/-!
# The actual whole-bin boundary and its remaining geometric data

This module applies the proved arithmetic fixed-row contour estimate to
the literal `wholeBinBoundary` in `HeckeSkeleton.HighBin`. The fixed bins,
all retained blocks, the original contour heights and the original
subtraction are retained.

The first bound leaves the finite sum of upper-height powers visible. The
second theorem absorbs explicit height and block-count polynomials into
the repository's `HighBoundaryControl`. Its premises concern the choices
in the presentation, not contour estimates, Euler regularity or a boundary
conclusion. The named `actualHighPresentation` is still an upstream
construction obligation, so this consumer does not assert that obligation
has been solved.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinBoundaryPresentation

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HighBinBoundary.ActualEstimate
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

local instance presentationNormOneMeasurable (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneSpace

local instance presentationNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneBorel

local instance presentationLocalMeasurable (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    MeasurableSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localSpace p

local instance presentationLocalBorel (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    BorelSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localBorel p

local instance presentationLocalHaar (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    ((targetData K c).measures.haar p).IsAddHaarMeasure :=
  (targetData K c).measures.haar_isAddHaar p

/-- Both branches of the original fixed bin have the same actual norm
envelope, strict lower shell bound, and buffered upper-zero detector. -/
theorem highFixedRowBin_member_data (c : TargetContext K)
    (P : ProbeData K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (E : RowEulerData K _ P) (Θ : Finset (HeckeCharacter K))
    (selectedHeight upperHeight normLower normUpper a e : ℝ) (u : HighRow K c)
    (hu : u ∈ highFixedRowBin K c P E Θ
      selectedHeight upperHeight normLower normUpper a e) :
    u ∈ frequencyRows K _ normUpper ∧ normLower < frequencyRowNorm K _ u ∧
      rowZeroBelow K _ (targetCharacter K c) Θ P E u upperHeight (a + 2 * e) := by
  by_cases ha : a = 51 / 100
  · rw [highFixedRowBin, if_pos ha] at hu
    have h := Finset.mem_filter.mp hu
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · rw [highFixedRowBin, if_neg ha] at hu
    have h := (mem_bufferedPhysicalRowBin_iff K _ (targetCharacter K c) Θ P E
      selectedHeight upperHeight normLower normUpper a e u).mp hu
    exact ⟨h.1, h.2.1, h.2.2.2.2⟩

/-- The original presentation's smallness and shell fields already imply
the numerical ranges needed by the coarse arithmetic boundary theorem. -/
theorem presentation_e_small (c : TargetContext K) (P : ActualHighPresentation K c) :
    P.e ≤ 1 / 10000 := by
  linarith [P.e_small, min_le_left c.family.lamA c.lamB, c.family.lamA_small]

theorem presentation_shell_le_one (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    (((targetData K c).expansion Z T).block b).shell ≤ 1 := by
  linarith [(P.shell_range Z T hZ hT b).2, P.zeta_small]

/-- Exactly one summand of the repository's whole-bin boundary. This is
only an abbreviation of the original initial-minus-final fixed-bin sum. -/
def presentationBoundaryPiece (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) (b : HighBlockIndex K c Z T) : ℂ :=
  (∑ u ∈ highFixedRowBin K c (targetData K c).probe P.euler P.companions
    (P.selectedHeight Z T b) (P.upperHeight Z T b)
    (Z ^ (((targetData K c).expansion Z T).block b).shell)
    (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
    (((targetData K c).expansion Z T).block b).bin P.e,
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
      Z (P.contourHeight Z T b) (c.family.B + 20 * P.e)
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) -
  (∑ u ∈ highFixedRowBin K c (targetData K c).probe P.euler P.companions
    (P.selectedHeight Z T b) (P.upperHeight Z T b)
    (Z ^ (((targetData K c).expansion Z T).block b).shell)
    (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
    (((targetData K c).expansion Z T).block b).bin P.e,
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u
      Z (P.contourHeight Z T b)
      ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50))

theorem wholeBinBoundary_eq_sum (c : TargetContext K) (P : ActualHighPresentation K c)
    (Z T : ℝ) :
    wholeBinBoundary K c P Z T =
      ∑ b : HighBlockIndex K c Z T, presentationBoundaryPiece K c P Z T b := rfl

/-- The actual fixed-row theorem applies to every retained block. No
row counting, zero-free continuation or contour estimate is a premise. -/
theorem exists_presentationBoundaryPiece_external_tail
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T → ∀ b : HighBlockIndex K c Z T,
      δ * T ≤ P.contourHeight Z T b →
      P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b →
      ‖presentationBoundaryPiece K c P Z T b‖ ≤
        C * Z ^ 13 * (2 + P.upperHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ := exists_arithmetic_fixedRows_external_tail
    K (targetData K c).S (targetData K c).measures.haar (targetData K c).probe
    (targetCharacter K c) P.companions hcompanions c.geometry P.e_pos
    (presentation_e_small K c P)
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hfixed⟩ := hb N
  refine ⟨C * δ ^ (-(N : ℝ)), mul_pos hC (Real.rpow_pos_of_pos hδ _), ?_⟩
  intro Z T hZ hT hδT b hTH hHU
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  let d := (((targetData K c).expansion Z T).block b).shell
  let a := (((targetData K c).expansion Z T).block b).bin
  let R := highFixedRowBin K c (targetData K c).probe P.euler P.companions
    (P.selectedHeight Z T b) (P.upperHeight Z T b) (Z ^ d) (2 * Z ^ d) a P.e
  have hdata (u : HighRow K c) (hu : u ∈ R) := highFixedRowBin_member_data K c
    (targetData K c).probe P.euler P.companions (P.selectedHeight Z T b)
    (P.upperHeight Z T b) (Z ^ d) (2 * Z ^ d) a P.e u hu
  have hR : R ⊆ frequencyRows K _ (2 * Z ^ d) := fun u hu => (hdata u hu).1
  have hlo : ∀ u ∈ R, Z ^ d ≤ frequencyRowNorm K _ u :=
    fun u hu => (hdata u hu).2.1.le
  have hbelow : ∀ u ∈ R, rowZeroBelow K _ (targetCharacter K c) P.companions
      (targetData K c).probe
      (HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
        (targetData K c).probe (targetCharacter K c))
      u (P.upperHeight Z T b) (a + 2 * P.e) := by
    intro u hu
    simpa only [← hEuler] using (hdata u hu).2.2
  have hbound := hfixed (targetData K c).rayFilter Z hZ d
    (P.shell_range Z T hZ1 hT b).1 (presentation_shell_le_one K c P Z T hZ1 hT b)
    R hR hlo a c.family.B (P.contourHeight Z T b) (P.upperHeight Z T b) (δ * T)
    (P.bin_range Z T hZ1 hT b).1 (P.bin_range Z T hZ1 hT b).2 c.family.B_upper
    hδT hTH hHU hbelow
  have hbound' : ‖presentationBoundaryPiece K c P Z T b‖ ≤
      C * Z ^ 13 * (2 + P.upperHeight Z T b) ^
        HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * (δ * T) ^ (-(N : ℝ)) := by
    simpa only [presentationBoundaryPiece, R, d, a, ← hEuler] using hbound
  apply hbound'.trans_eq
  rw [Real.mul_rpow hδ.le (zero_le_one.trans hT)]
  ring

/-- The whole original retained family has an arbitrary external tail.
The only remaining arithmetic weight is the displayed finite sum of
upper-height powers, selected independently of the decay order. -/
theorem exists_wholeBinBoundary_heightSum_bound
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z T : ℝ, Z₀ ≤ Z → 1 ≤ T → 1 ≤ δ * T →
      (∀ b : HighBlockIndex K c Z T, δ * T ≤ P.contourHeight Z T b) →
      (∀ b : HighBlockIndex K c Z T,
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b) →
      ‖wholeBinBoundary K c P Z T‖ ≤ C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T,
          (2 + P.upperHeight Z T b) ^
            HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K) * T ^ (-(N : ℝ)) := by
  obtain ⟨Z₀, hZ₀, hb⟩ :=
    exists_presentationBoundaryPiece_external_tail K c P hEuler hcompanions δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N
  obtain ⟨C, hC, hpiece⟩ := hb N
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT hδT hTH hHU
  rw [wholeBinBoundary_eq_sum]
  calc
    _ ≤ ∑ b : HighBlockIndex K c Z T, ‖presentationBoundaryPiece K c P Z T b‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : HighBlockIndex K c Z T,
        C * Z ^ 13 * (2 + P.upperHeight Z T b) ^
          HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum (fun b _ => hpiece Z T hZ hT hδT b (hTH b) (hHU b))
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- Explicit geometric polynomials close the actual whole-bin boundary.
Their degrees precede both the power-height parameter and every tail
order. These hypotheses are the currently missing choices/count facts of
the named presentation, not the requested boundary conclusion. -/
theorem highBoundaryControl_of_arithmetic_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HeckeSkeleton.HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB AU RU ceiling Cb Cu Zg : ℝ)
    (hAB : 0 ≤ AB) (hAU : 0 ≤ AU) (hceiling : 0 < ceiling)
    (hCb : 0 < Cb) (hCu : 0 < Cu) (hZg : 1 ≤ Zg)
    (hcount : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      (((targetData K c).expansion Z T).blockCount : ℝ) ≤
        Cb * Z ^ RB * (1 + T) ^ AB)
    (hheights : ∀ Z T : ℝ, Zg ≤ Z → 1 ≤ T → T ≤ Z ^ ceiling →
      ∀ b : HighBlockIndex K c Z T,
        δ * T ≤ P.contourHeight Z T b ∧
        P.contourHeight Z T b + 3 / 2 ≤ P.upperHeight Z T b ∧
        2 + P.upperHeight Z T b ≤ Cu * Z ^ RU * (1 + T) ^ AU) :
    HighBoundaryControl K c P := by
  let k : ℕ := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Zb, hZb, hb⟩ :=
    exists_wholeBinBoundary_heightSum_bound K c P hEuler hcompanions δ hδ
  refine ⟨AB + AU * (k : ℝ), 13 + RB + RU * (k : ℝ), ceiling,
    by positivity, hceiling, ?_⟩
  intro τ hτ hτc N
  obtain ⟨C, hC, hmain⟩ := hb N
  let Zδ : ℝ := (1 / δ) ^ (1 / τ)
  refine ⟨C * Cb * Cu ^ k, max (max Zb Zg) Zδ, by positivity,
    hZb.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro Z hZ
  have hZZb : Zb ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZZg : Zg ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZZδ : Zδ ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZb.trans hZZb
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let T := Z ^ τ
  have hT : 1 ≤ T := Real.one_le_rpow hZ1 hτ.le
  have hδT : 1 ≤ δ * T := by
    have hrecip : 1 / δ ≤ T := by
      calc
        1 / δ = Zδ ^ τ := by
          dsimp [Zδ]
          rw [← Real.rpow_mul (one_div_pos.mpr hδ).le]
          simp only [one_div, inv_mul_cancel₀ hτ.ne', Real.rpow_one]
        _ ≤ T := Real.rpow_le_rpow (Real.rpow_nonneg (one_div_pos.mpr hδ).le _) hZZδ hτ.le
    have hm := mul_le_mul_of_nonneg_left hrecip hδ.le
    simpa only [one_div, mul_inv_cancel₀ hδ.ne'] using hm
  have hTc : T ≤ Z ^ ceiling := Real.rpow_le_rpow_of_exponent_le hZ1 hτc
  have hT0 : 0 < 1 + T := by linarith
  have hh := hheights Z T hZZg hT hTc
  have hbound := hmain Z T hZZb hT hδT (fun b => (hh b).1) (fun b => (hh b).2.1)
  have hheightSum :
      (∑ b : HighBlockIndex K c Z T, (2 + P.upperHeight Z T b) ^ k) ≤
        (((targetData K c).expansion Z T).blockCount : ℝ) *
          (Cu * Z ^ RU * (1 + T) ^ AU) ^ k := by
    calc
      _ ≤ ∑ _b : HighBlockIndex K c Z T, (Cu * Z ^ RU * (1 + T) ^ AU) ^ k := by
        apply Finset.sum_le_sum
        intro b _
        have hU0 : 0 ≤ 2 + P.upperHeight Z T b := by
          have h₁ := (hh b).1
          have h₂ := (hh b).2.1
          linarith
        exact pow_le_pow_left₀ hU0 (hh b).2.2 k
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmass := hheightSum.trans (mul_le_mul_of_nonneg_right
    (hcount Z T hZZg hT hTc) (by positivity))
  apply hbound.trans
  calc
    C * Z ^ 13 *
        (∑ b : HighBlockIndex K c Z T, (2 + P.upperHeight Z T b) ^ k) *
        T ^ (-(N : ℝ)) ≤
      C * Z ^ 13 *
        ((Cb * Z ^ RB * (1 + T) ^ AB) * (Cu * Z ^ RU * (1 + T) ^ AU) ^ k) *
        T ^ (-(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity))
        (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
    _ = (C * Cb * Cu ^ k) * Z ^ (13 + RB + RU * (k : ℝ)) *
        (1 + T) ^ (AB + AU * (k : ℝ)) * T ^ (-(N : ℝ)) := by
      simp only [Real.rpow_add hZ0, Real.rpow_add hT0,
        Real.rpow_mul hZ0.le, Real.rpow_mul hT0.le, Real.rpow_natCast, mul_pow]
      ring

#print axioms highFixedRowBin_member_data
#print axioms exists_presentationBoundaryPiece_external_tail
#print axioms exists_wholeBinBoundary_heightSum_bound
#print axioms highBoundaryControl_of_arithmetic_geometry

end HeckeSkeleton.HighBinBoundaryPresentation
