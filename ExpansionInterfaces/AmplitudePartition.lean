import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite amplitude labels for the EXPANSION interface

The construction is independent of the number of rows.  Every coordinate has
`floor(cap / width) + 2` labels, including one label for the capped value.
The row sets are literal fibers of this common finite code.  The theorems below
prove support, finite cardinality, disjointness and the exact sum identity.
No zero detector, prime upper estimate or contour-shift theorem is postulated.
The prime upper estimate appears explicitly only as a hypothesis of the
separate amplitude upper-bound lemma.
-/

noncomputable section
namespace ExpansionInterfaces
open scoped BigOperators

/-- The downward rounded, nonnegative, capped amplitude. -/
def amplitude (width cap x : ℝ) : ℝ :=
  min cap (width * (Nat.floor (x / width) : ℝ))

theorem amplitude_nonneg {width cap x : ℝ}
    (hw : 0 ≤ width) (hc : 0 ≤ cap) : 0 ≤ amplitude width cap x := by
  exact le_min hc (mul_nonneg hw (Nat.cast_nonneg _))

theorem amplitude_le_cap (width cap x : ℝ) : amplitude width cap x ≤ cap :=
  min_le_left _ _

theorem amplitude_le_of_pos {width cap x : ℝ}
    (hw : 0 < width) (ha : 0 < amplitude width cap x) :
    amplitude width cap x ≤ x := by
  have hfloor : 0 < Nat.floor (x / width) := by
    have hmul : 0 < width * (Nat.floor (x / width) : ℝ) :=
      ha.trans_le (min_le_right _ _)
    have hcast : (0 : ℝ) < Nat.floor (x / width) :=
      (mul_pos_iff_of_pos_left hw).mp hmul
    exact_mod_cast hcast
  have hxw : 0 ≤ x / width := (Nat.pos_of_floor_pos hfloor).le
  have hfloor_le := Nat.floor_le hxw
  have hscaled := mul_le_mul_of_nonneg_left hfloor_le hw.le
  have hw0 : width ≠ 0 := hw.ne'
  have heq : width * (x / width) = x := by field_simp
  exact (min_le_right _ _).trans (hscaled.trans_eq heq)

theorem le_amplitude_add_width {width cap x : ℝ}
    (hw : 0 < width) (hcap : x ≤ cap + width) :
    x ≤ amplitude width cap x + width := by
  unfold amplitude
  by_cases hle : cap ≤ width * (Nat.floor (x / width) : ℝ)
  · simpa only [min_eq_left hle] using hcap
  · rw [min_eq_right (le_of_not_ge hle)]
    have hlt := Nat.lt_floor_add_one (x / width)
    have hscaled := (div_lt_iff₀ hw).mp hlt
    nlinarith

/-- A scale-independent finite alphabet, with one overflow/cap label. -/
abbrev AmplitudeCode (width cap : ℝ) := Fin (Nat.floor (cap / width) + 2)

/-- The capped natural floor code. It is defined for every real input. -/
def amplitudeCode (width cap x : ℝ) : AmplitudeCode width cap :=
  ⟨min (Nat.floor (cap / width) + 1) (Nat.floor (x / width)),
    Nat.lt_of_le_of_lt (min_le_left _ _) (by omega)⟩

/-- Decode by the same cap used in the original amplitude. -/
def decodeAmplitude (width cap : ℝ) (code : AmplitudeCode width cap) : ℝ :=
  min cap (width * (code.val : ℝ))

theorem decode_amplitudeCode {width cap x : ℝ}
    (hw : 0 < width) :
    decodeAmplitude width cap (amplitudeCode width cap x) =
      amplitude width cap x := by
  unfold decodeAmplitude amplitudeCode amplitude
  dsimp only
  by_cases h : Nat.floor (x / width) ≤ Nat.floor (cap / width) + 1
  · rw [min_eq_right h]
  · have hN : Nat.floor (cap / width) + 1 ≤ Nat.floor (x / width) := by omega
    rw [min_eq_left hN]
    have hcap : cap < width * (Nat.floor (cap / width) + 1 : ℕ) := by
      have hh := Nat.lt_floor_add_one (cap / width)
      have := (div_lt_iff₀ hw).mp hh
      push_cast
      nlinarith
    have hcast : ((Nat.floor (cap / width) + 1 : ℕ) : ℝ) ≤ Nat.floor (x / width) := by
      exact_mod_cast hN
    have hlarge : cap ≤ width * (Nat.floor (x / width) : ℝ) :=
      hcap.le.trans (mul_le_mul_of_nonneg_left hcast hw.le)
    rw [min_eq_left hcap.le, min_eq_left hlarge]

theorem rpow_logRatio {P x : ℝ} (hP : 1 < P) (hx : 0 < x) :
    P ^ (Real.log x / Real.log P) = x := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < P)]
  have hlog : Real.log P ≠ 0 := (Real.log_pos hP).ne'
  have hh : Real.log P * (Real.log x / Real.log P) = Real.log x := by
    field_simp
  rw [hh, Real.exp_log hx]

/-- Actual complex-slot amplitude, with the zero slot assigned amplitude zero. -/
def slotAmplitude (width cap P : ℝ) (value : ℂ) : ℝ :=
  if value = 0 then 0 else amplitude width cap ((Real.log ‖value‖ / Real.log P))

theorem slotAmplitude_bounds {width cap P : ℝ} (value : ℂ)
    (hw : 0 ≤ width) (hc : 0 ≤ cap) :
    0 ≤ slotAmplitude width cap P value ∧ slotAmplitude width cap P value ≤ cap := by
  unfold slotAmplitude
  split_ifs
  · exact ⟨le_rfl, hc⟩
  · exact ⟨amplitude_nonneg hw hc, amplitude_le_cap _ _ _⟩

theorem slotAmplitude_lower {width cap P : ℝ} (value : ℂ)
    (hw : 0 < width) (hP : 1 < P)
    (ha : 0 < slotAmplitude width cap P value) :
    P ^ slotAmplitude width cap P value ≤ ‖value‖ := by
  have hv : value ≠ 0 := by
    intro h
    simp only [slotAmplitude, ite_eq_left h] at ha
    exact (lt_irrefl 0) ha
  have hnorm : 0 < ‖value‖ := norm_pos_iff.mpr hv
  simp only [slotAmplitude, ite_eq_right hv] at ha ⊢
  have hround := amplitude_le_of_pos hw ha
  calc P ^ amplitude width cap ((Real.log ‖value‖ / Real.log P)) ≤ P ^ (Real.log ‖value‖ / Real.log P) :=
      Real.rpow_le_rpow_of_exponent_le hP.le hround
    _ = ‖value‖ := rpow_logRatio hP hnorm

theorem slotAmplitude_upper {width cap P : ℝ} (value : ℂ)
    (hw : 0 < width) (hP : 1 < P)
    (hprime : ‖value‖ ≤ P ^ (cap + width)) :
    ‖value‖ ≤ P ^ (slotAmplitude width cap P value + width) := by
  by_cases hv : value = 0
  · simp only [hv, norm_zero]
    exact Real.rpow_nonneg (by linarith) _
  · have hnorm : 0 < ‖value‖ := norm_pos_iff.mpr hv
    have hx : (Real.log ‖value‖ / Real.log P) ≤ cap + width :=
      by
        apply (div_le_iff₀ (Real.log_pos hP)).mpr
        have hh := Real.log_le_log hnorm hprime
        rwa [Real.log_rpow (by linarith : 0 < P)] at hh
    simp only [slotAmplitude, ite_eq_right hv]
    calc ‖value‖ = P ^ (Real.log ‖value‖ / Real.log P) :=
        (rpow_logRatio hP hnorm).symm
      _ ≤ P ^ (amplitude width cap ((Real.log ‖value‖ / Real.log P)) + width) :=
        Real.rpow_le_rpow_of_exponent_le hP.le (le_amplitude_add_width hw hx)

/-- The zero code is used for an exactly zero physical slot. -/
def slotCode (width cap P : ℝ) (value : ℂ) : AmplitudeCode width cap :=
  if value = 0 then ⟨0, by omega⟩
  else amplitudeCode width cap ((Real.log ‖value‖ / Real.log P))

theorem decode_slotCode {width cap P : ℝ} (value : ℂ)
    (hw : 0 < width) (hc : 0 ≤ cap) :
    decodeAmplitude width cap (slotCode width cap P value) =
      slotAmplitude width cap P value := by
  unfold slotCode slotAmplitude
  split_ifs
  · simp [decodeAmplitude, min_eq_right hc]
  · exact decode_amplitudeCode hw

/-- A literal fiber of a finite label map. -/
def rowPiece {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (code : Row → Label) (label : Label) : Finset Row :=
  rows.filter (fun u => code u = label)

theorem rowPiece_subset {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (code : Row → Label) (label : Label) :
    rowPiece rows code label ⊆ rows := Finset.filter_subset _ _

theorem rowPiece_support {Row Label : Type*} [DecidableEq Label]
    (rows envelope : Finset Row) (code : Row → Label) (label : Label)
    (hrows : rows ⊆ envelope) : rowPiece rows code label ⊆ envelope :=
  (rowPiece_subset rows code label).trans hrows

theorem rowPiece_covers {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (code : Row → Label) {u : Row} (hu : u ∈ rows) :
    u ∈ rowPiece rows code (code u) := by
  simp [rowPiece, hu]

theorem rowPiece_disjoint {Row Label : Type*} [DecidableEq Label]
    (rows : Finset Row) (code : Row → Label) {a b : Label} (hab : a ≠ b) :
    Disjoint (rowPiece rows code a) (rowPiece rows code b) := by
  apply Finset.disjoint_left.mpr
  intro u ha hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact hab (ha'.symm.trans hb')

/-- The finite label sum exactly reconstructs the original row contribution. -/
theorem sum_rowPiece {Row Label M : Type*} [Fintype Label] [DecidableEq Label]
    [AddCommMonoid M] (rows : Finset Row) (code : Row → Label) (f : Row → M) :
    (∑ label, ∑ u ∈ rowPiece rows code label, f u) = ∑ u ∈ rows, f u := by
  simp only [rowPiece, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp

/-- One coordinate for each physical slot, without a factor for the rows. -/
abbrev AmplitudeLabels (J : ℕ) (width cap : ℝ) :=
  Fin J → AmplitudeCode width cap

theorem card_amplitudeLabels (J : ℕ) (width cap : ℝ) :
    Fintype.card (AmplitudeLabels J width cap) =
      (Nat.floor (cap / width) + 2) ^ J := by
  simp [AmplitudeLabels, AmplitudeCode]

/-- Uniform cap bound, needed because the buffered bin may vary with scale. -/
theorem card_amplitudeLabels_le (J : ℕ) {width cap capMax : ℝ}
    (hw : 0 < width) (hcap : cap ≤ capMax) :
    Fintype.card (AmplitudeLabels J width cap) ≤
      (Nat.floor (capMax / width) + 2) ^ J := by
  rw [card_amplitudeLabels]
  have hf : Nat.floor (cap / width) ≤ Nat.floor (capMax / width) :=
    Nat.floor_mono (div_le_div_of_nonneg_right hcap hw.le)
  exact Nat.pow_le_pow_left (show Nat.floor (cap / width) + 2 ≤
    Nat.floor (capMax / width) + 2 by omega) J

/-- Pure amplitude labels cost no height power and only the displayed fixed
constant.  The estimate is uniform in every capped bin `cap ≤ capMax`. -/
theorem amplitudeLabels_uniform_bound (J : ℕ) {width cap capMax Z η : ℝ}
    (hw : 0 < width) (hcap : cap ≤ capMax) (hZ : 1 ≤ Z) (hη : 0 ≤ η) :
    (Fintype.card (AmplitudeLabels J width cap) : ℝ) ≤
      ((Nat.floor (capMax / width) + 2) ^ J : ℕ) * Z ^ η := by
  have hc : (Fintype.card (AmplitudeLabels J width cap) : ℝ) ≤
      ((Nat.floor (capMax / width) + 2) ^ J : ℕ) := by
    exact_mod_cast card_amplitudeLabels_le J hw hcap
  have hp : 1 ≤ Z ^ η := Real.one_le_rpow hZ hη
  have hN : (0 : ℝ) ≤ ((Nat.floor (capMax / width) + 2) ^ J : ℕ) := Nat.cast_nonneg _
  exact hc.trans (le_mul_of_one_le_right hN hp)

/-- The amplitude vector is fixed throughout every row fiber. -/
theorem slotAmplitude_eq_on_piece {Row : Type*} (J : ℕ)
    (rows : Finset Row) (width cap : ℝ) (P : Fin J → ℝ)
    (Q : Fin J → Row → ℂ) (hw : 0 < width) (hc : 0 ≤ cap)
    (label : AmplitudeLabels J width cap) (u : Row)
    (hu : u ∈ rowPiece rows (fun u i => slotCode width cap (P i) (Q i u)) label)
    (i : Fin J) :
    slotAmplitude width cap (P i) (Q i u) = decodeAmplitude width cap (label i) := by
  have hcode := congrFun (Finset.mem_filter.mp hu).2 i
  rw [← hcode]
  exact (decode_slotCode (Q i u) hw hc).symm

/-- Every label carries legal amplitudes, including labels whose row fiber is empty. -/
theorem decodeAmplitude_bounds {width cap : ℝ} (hw : 0 ≤ width) (hc : 0 ≤ cap)
    (code : AmplitudeCode width cap) :
    0 ≤ decodeAmplitude width cap code ∧ decodeAmplitude width cap code ≤ cap := by
  exact ⟨le_min hc (mul_nonneg hw (Nat.cast_nonneg _)), min_le_left _ _⟩

/-- The exact amplitude portion of `BlockSource`, before constructing its
independent zero-detector witness subdivision. -/
theorem amplitudePiece_spec {Row : Type*} (J : ℕ)
    (rows : Finset Row) (width cap : ℝ) (P : Fin J → ℝ)
    (Q : Fin J → Row → ℂ) (hw : 0 < width) (hc : 0 ≤ cap)
    (hP : ∀ i, 1 < P i) (label : AmplitudeLabels J width cap) :
    (∀ i, 0 ≤ decodeAmplitude width cap (label i) ∧
      decodeAmplitude width cap (label i) ≤ cap) ∧
    (∀ i, 0 < decodeAmplitude width cap (label i) →
      ∀ u ∈ rowPiece rows (fun u i => slotCode width cap (P i) (Q i u)) label,
        (P i) ^ decodeAmplitude width cap (label i) ≤ ‖Q i u‖) := by
  constructor
  · intro i
    exact decodeAmplitude_bounds hw.le hc _
  · intro i hi u hu
    have heq := slotAmplitude_eq_on_piece J rows width cap P Q hw hc label u hu i
    rw [← heq] at hi ⊢
    exact slotAmplitude_lower (Q i u) hw (hP i) hi

/-- The mean amplitude is bounded uniformly by the bin cap. -/
theorem meanAmplitude_bounds (J : ℕ) (hJ : 0 < J) {width cap : ℝ}
    (hw : 0 ≤ width) (hc : 0 ≤ cap) (label : AmplitudeLabels J width cap) :
    0 ≤ (∑ i, decodeAmplitude width cap (label i)) / J ∧
      (∑ i, decodeAmplitude width cap (label i)) / J ≤ cap := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ =>
      (decodeAmplitude_bounds hw hc (label i)).1)) hJr.le
  · apply (div_le_iff₀ hJr).mpr
    calc
      (∑ i, decodeAmplitude width cap (label i)) ≤ ∑ _i : Fin J, cap :=
        Finset.sum_le_sum (fun i _ => (decodeAmplitude_bounds hw hc (label i)).2)
      _ = cap * J := by simp [mul_comm]

/-- Add a sector to a label without adding any real parameter coordinates. -/
theorem refinedRowPiece_eq {Row Sector Label : Type*}
    [DecidableEq Sector] [DecidableEq Label]
    (rows : Finset Row) (sector : Row → Sector) (code : Row → Label)
    (s : Sector) (label : Label) :
    rowPiece rows (fun u => (sector u, code u)) (s, label) =
      rowPiece (rowPiece rows sector s) code label := by
  ext u
  simp [rowPiece, and_assoc]

theorem sector_eq_on_refinedPiece {Row Sector Label : Type*}
    [DecidableEq Sector] [DecidableEq Label]
    (rows : Finset Row) (sector : Row → Sector) (code : Row → Label)
    (s : Sector) (label : Label) {u : Row}
    (hu : u ∈ rowPiece rows (fun u => (sector u, code u)) (s, label)) :
    sector u = s := by
  exact congrArg Prod.fst (Finset.mem_filter.mp hu).2

/-- Once the sector is a label coordinate, an ideal-indexed shift uses the
correct row-sector parameter with no enlargement of the parameter dimension. -/
theorem sectorParameter_eq_on_refinedPiece {Row Sector Label Ideal Param : Type*}
    [DecidableEq Sector] [DecidableEq Label]
    (rows : Finset Row) (sector : Row → Sector) (code : Row → Label)
    (s : Sector) (label : Label) (ideal : Row → Ideal)
    (parameter : Sector → Ideal → Param) {u : Row}
    (hu : u ∈ rowPiece rows (fun u => (sector u, code u)) (s, label)) :
    parameter (sector u) (ideal u) = parameter s (ideal u) := by
  rw [sector_eq_on_refinedPiece rows sector code s label hu]

abbrev SectorAmplitudeLabels (Sector : Type*) (J : ℕ) (width cap : ℝ) :=
  Sector × AmplitudeLabels J width cap

theorem card_sectorAmplitudeLabels (Sector : Type*) [Fintype Sector]
    (J : ℕ) (width cap : ℝ) :
    Fintype.card (SectorAmplitudeLabels Sector J width cap) =
      Fintype.card Sector * (Nat.floor (cap / width) + 2) ^ J := by
  simp [SectorAmplitudeLabels]

/-- The uniform physical prime-slot base used in the current skeleton. -/
def physicalSlotBase (J : ℕ) (Z : ℝ) : ℝ := Z ^ ((1 / 6 : ℝ) / J)

theorem physicalSlotBase_gt_one (J : ℕ) (hJ : 0 < J) {Z : ℝ} (hZ : 1 < Z) :
    1 < physicalSlotBase J Z := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  exact Real.one_lt_rpow hZ (div_pos (by norm_num) hJr)

/-- This is the literal base-Z lower bound requested by the `BlockSource`
amplitude fields, for the same finite rows and same complex slot values. -/
theorem physical_amplitudePiece_spec {Row : Type*} (J : ℕ) (hJ : 0 < J)
    (rows : Finset Row) (width cap Z : ℝ) (Q : Fin J → Row → ℂ)
    (hw : 0 < width) (hc : 0 ≤ cap) (hZ : 1 < Z)
    (label : AmplitudeLabels J width cap) :
    (∀ i, 0 ≤ decodeAmplitude width cap (label i) ∧
      decodeAmplitude width cap (label i) ≤ cap) ∧
    (∀ i, 0 < decodeAmplitude width cap (label i) →
      ∀ u ∈ rowPiece rows
        (fun u i => slotCode width cap (physicalSlotBase J Z) (Q i u)) label,
        Z ^ ((1 / 6 : ℝ) / J * decodeAmplitude width cap (label i)) ≤ ‖Q i u‖) := by
  have h := amplitudePiece_spec J rows width cap (fun _ => physicalSlotBase J Z) Q hw hc
    (fun _ => physicalSlotBase_gt_one J hJ hZ) label
  refine ⟨h.1, ?_⟩
  intro i hi u hu
  have hh := h.2 i hi u hu
  simpa only [physicalSlotBase, ← Real.rpow_mul (by linarith : 0 ≤ Z)] using hh

end ExpansionInterfaces
