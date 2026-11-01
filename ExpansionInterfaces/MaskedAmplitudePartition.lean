import ExpansionInterfaces.AmplitudePartition
import ExpansionInterfaces.AmplitudeMeasurability

/-!
# Error slots retain their actual values while having amplitude zero

The mask changes only the amplitude code and amplitude assigned to a label.
The complex slot value is always the original Q.  Thus this construction
never replaces a zero-amplitude error slot by a zero polynomial.
-/

noncomputable section
namespace ExpansionInterfaces

/-- A false main flag gives the distinguished zero amplitude code. -/
def maskedSlotCode (main : Bool) (width cap P : ℝ) (value : ℂ) :
    AmplitudeCode width cap :=
  if main then slotCode width cap P value else ⟨0, by omega⟩

/-- Error amplitudes are identically zero even on empty label fibers. -/
def maskedLabelAmplitude (J : ℕ) (main : Fin J → Bool) (width cap : ℝ)
    (label : AmplitudeLabels J width cap) (i : Fin J) : ℝ :=
  if main i then decodeAmplitude width cap (label i) else 0

theorem masked_amplitudePiece_spec {Row : Type*} (J : ℕ)
    (rows : Finset Row) (main : Fin J → Bool) (width cap : ℝ) (P : Fin J → ℝ)
    (Q : Fin J → Row → ℂ) (hw : 0 < width) (hc : 0 ≤ cap)
    (hP : ∀ i, 1 < P i) (label : AmplitudeLabels J width cap) :
    (∀ i, 0 ≤ maskedLabelAmplitude J main width cap label i ∧
      maskedLabelAmplitude J main width cap label i ≤ cap) ∧
    (∀ i, 0 < maskedLabelAmplitude J main width cap label i →
      ∀ u ∈ rowPiece rows
        (fun u i => maskedSlotCode (main i) width cap (P i) (Q i u)) label,
        (P i) ^ maskedLabelAmplitude J main width cap label i ≤ ‖Q i u‖) := by
  constructor
  · intro i
    cases hm : main i with
    | false => simpa [maskedLabelAmplitude, hm] using hc
    | true => simpa [maskedLabelAmplitude, hm] using decodeAmplitude_bounds hw.le hc (label i)
  · intro i hi u hu
    cases hm : main i with
    | false => simp [maskedLabelAmplitude, hm] at hi
    | true =>
      simp only [maskedLabelAmplitude, hm, ↓reduceIte] at hi ⊢
      have hcode := congrFun (Finset.mem_filter.mp hu).2 i
      have hc' : slotCode width cap (P i) (Q i u) = label i := by
        simpa only [maskedSlotCode, hm, ↓reduceIte] using hcode
      have heq := decode_slotCode (P := P i) (Q i u) hw hc
      rw [hc'] at heq
      rw [heq] at hi ⊢
      exact slotAmplitude_lower (Q i u) hw (hP i) hi

theorem maskedLabelAmplitude_error (J : ℕ) (main : Fin J → Bool)
    (width cap : ℝ) (label : AmplitudeLabels J width cap) (i : Fin J)
    (hi : main i = false) : maskedLabelAmplitude J main width cap label i = 0 := by
  simp [maskedLabelAmplitude, hi]

variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_maskedSlotCode_eq (main : Bool) (width cap P : ℝ)
    {Q : X → ℂ} (hQ : Measurable Q) (code : AmplitudeCode width cap) :
    MeasurableSet {x | maskedSlotCode main width cap P (Q x) = code} := by
  cases main with
  | false =>
    unfold maskedSlotCode
    simp only [Bool.false_eq_true, ite_false]
    by_cases h : (⟨0, by omega⟩ : AmplitudeCode width cap) = code <;> simp [h]
  | true =>
    simpa only [maskedSlotCode, ↓reduceIte] using
      measurableSet_slotCode_eq width cap P hQ code

theorem measurableSet_maskedAmplitudeLabel_eq (J : ℕ) (main : Fin J → Bool)
    (width cap : ℝ) (P : Fin J → ℝ) (Q : Fin J → X → ℂ)
    (hQ : ∀ i, Measurable (Q i)) (label : AmplitudeLabels J width cap) :
    MeasurableSet {x | (fun i => maskedSlotCode (main i) width cap (P i) (Q i x)) = label} := by
  have heq : {x | (fun i => maskedSlotCode (main i) width cap (P i) (Q i x)) = label} =
      ⋂ i : Fin J, {x | maskedSlotCode (main i) width cap (P i) (Q i x) = label i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_maskedSlotCode_eq (main i) width cap (P i) (hQ i) (label i)

/-- Sector, one of the finite correction masks, and the amplitude vector. -/
abbrev CompleteAmplitudeLabels (Sector : Type*) (J : ℕ) (width cap : ℝ) :=
  Sector × ((Fin J → Bool) × AmplitudeLabels J width cap)

theorem card_completeAmplitudeLabels (Sector : Type*) [Fintype Sector]
    (J : ℕ) (width cap : ℝ) :
    Fintype.card (CompleteAmplitudeLabels Sector J width cap) =
      Fintype.card Sector * (2 ^ J * (Nat.floor (cap / width) + 2) ^ J) := by
  simp [CompleteAmplitudeLabels]

/-- One fixed label constant works throughout all caps bounded by `capMax`.
It is independent of the contour parameters, scale, and height. -/
theorem completeAmplitudeLabels_uniform_bound (Sector : Type*) [Fintype Sector]
    (J : ℕ) {width cap capMax Z η : ℝ} (hw : 0 < width)
    (hc : cap ≤ capMax) (hZ : 1 ≤ Z) (hη : 0 ≤ η) :
    (Fintype.card (CompleteAmplitudeLabels Sector J width cap) : ℝ) ≤
      ((Fintype.card Sector : ℝ) *
        (2 ^ J * (Nat.floor (capMax / width) + 2 : ℕ) ^ J) + 1) * Z ^ η := by
  have hcard := card_amplitudeLabels_le J hw hc
  rw [card_amplitudeLabels] at hcard
  have hnat : Fintype.card (CompleteAmplitudeLabels Sector J width cap) ≤
      Fintype.card Sector * (2 ^ J * (Nat.floor (capMax / width) + 2) ^ J) := by
    rw [card_completeAmplitudeLabels]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcard)
  have hr : (Fintype.card (CompleteAmplitudeLabels Sector J width cap) : ℝ) ≤
      (Fintype.card Sector : ℝ) *
        (2 ^ J * (Nat.floor (capMax / width) + 2 : ℕ) ^ J) := by
    exact_mod_cast hnat
  have hn : (0 : ℝ) ≤ (Fintype.card Sector : ℝ) *
      (2 ^ J * (Nat.floor (capMax / width) + 2 : ℕ) ^ J) := by positivity
  have hp : 1 ≤ Z ^ η := Real.one_le_rpow hZ hη
  nlinarith

end ExpansionInterfaces
