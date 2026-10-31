module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite propagation of logarithmic and height losses

The algebraic part of revised Lemma 4.12: sums, products and fixed
nonnegative powers preserve finite logarithmic/height degrees and the
corresponding arithmetic exponents.  A finite reduction tree is handled
by induction.  Its analytic edges must first supply a common majorant;
this module makes no assertion that slice bounds construct that measure.
-/

@[expose] public section
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open scoped BigOperators

def growthEnvelope (C p L H Z T : ℝ) : ℝ :=
  C * Z ^ p * (1 + Real.log Z) ^ L * (1 + T) ^ H

theorem growthEnvelope_nonneg {C p L H Z T : ℝ}
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hT : 0 ≤ T) :
    0 ≤ growthEnvelope C p L H Z T := by
  unfold growthEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hZ) _))
      (Real.rpow_nonneg (by linarith [Real.log_nonneg hZ]) _))
    (Real.rpow_nonneg (by linarith) _)

theorem growthEnvelope_mono {C C' p p' L L' H H' Z T : ℝ}
    (hC : 0 ≤ C) (hCC : C ≤ C') (hpp : p ≤ p')
    (hLL : L ≤ L') (hHH : H ≤ H') (hZ : 1 ≤ Z) (hT : 0 ≤ T) :
    growthEnvelope C p L H Z T ≤ growthEnvelope C' p' L' H' Z T := by
  have hlog : 1 ≤ 1 + Real.log Z := by linarith [Real.log_nonneg hZ]
  have ht : 1 ≤ 1 + T := by linarith
  unfold growthEnvelope
  apply mul_le_mul
  · apply mul_le_mul
    · exact mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hZ hpp)
        (Real.rpow_nonneg (zero_le_one.trans hZ) _) (hC.trans hCC)
    · exact Real.rpow_le_rpow_of_exponent_le hlog hLL
    · exact Real.rpow_nonneg (zero_le_one.trans hlog) _
    · exact mul_nonneg (hC.trans hCC) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  · exact Real.rpow_le_rpow_of_exponent_le ht hHH
  · exact Real.rpow_nonneg (zero_le_one.trans ht) _
  · exact mul_nonneg
      (mul_nonneg (hC.trans hCC) (Real.rpow_nonneg (zero_le_one.trans hZ) _))
      (Real.rpow_nonneg (zero_le_one.trans hlog) _)

theorem growthEnvelope_mul {C C' p p' L L' H H' Z T : ℝ}
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) :
    growthEnvelope C p L H Z T * growthEnvelope C' p' L' H' Z T =
      growthEnvelope (C * C') (p + p') (L + L') (H + H') Z T := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hl : 0 < 1 + Real.log Z := by linarith [Real.log_nonneg hZ]
  have ht : 0 < 1 + T := by linarith
  simp only [growthEnvelope, Real.rpow_add hz, Real.rpow_add hl, Real.rpow_add ht]
  ring

theorem growthEnvelope_rpow {C p L H Z T q : ℝ}
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hT : 0 ≤ T) :
    growthEnvelope C p L H Z T ^ q =
      growthEnvelope (C ^ q) (p * q) (L * q) (H * q) Z T := by
  have hz : 0 ≤ Z := zero_le_one.trans hZ
  have hl : 0 ≤ 1 + Real.log Z := by linarith [Real.log_nonneg hZ]
  have ht : 0 ≤ 1 + T := by linarith
  simp only [growthEnvelope, Real.mul_rpow (mul_nonneg (mul_nonneg hC
      (Real.rpow_nonneg hz _)) (Real.rpow_nonneg hl _)) (Real.rpow_nonneg ht _),
    Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hz _)) (Real.rpow_nonneg hl _),
    Real.mul_rpow hC (Real.rpow_nonneg hz _),
    ← Real.rpow_mul hz, ← Real.rpow_mul hl, ← Real.rpow_mul ht]

/-- Constants and finite degrees precede both moving scales. -/
def LogHeightBound (f : ℝ → ℝ → ℝ) (p : ℝ) : Prop :=
  ∃ C L H : ℝ, 0 < C ∧ 0 ≤ L ∧ 0 ≤ H ∧
    ∀ Z T : ℝ, 1 ≤ Z → 0 ≤ T → |f Z T| ≤ growthEnvelope C p L H Z T

theorem LogHeightBound.const (a : ℝ) : LogHeightBound (fun _ _ => a) 0 := by
  refine ⟨|a| + 1, 0, 0, by positivity, le_rfl, le_rfl, ?_⟩
  intro Z T _ _
  simp only [growthEnvelope, Real.rpow_zero, mul_one]
  linarith

theorem LogHeightBound.zero (p : ℝ) :
    LogHeightBound (fun _ _ => 0) p := by
  refine ⟨1, 0, 0, zero_lt_one, le_rfl, le_rfl, ?_⟩
  intro Z T hZ hT
  simpa only [abs_zero] using growthEnvelope_nonneg (p := p) (L := 0) (H := 0)
    zero_le_one hZ hT

theorem LogHeightBound.mono {f g : ℝ → ℝ → ℝ} {p : ℝ}
    (hf : LogHeightBound f p)
    (hgf : ∀ Z T, 1 ≤ Z → 0 ≤ T → |g Z T| ≤ |f Z T|) :
    LogHeightBound g p := by
  obtain ⟨C, L, H, hC, hL, hH, hb⟩ := hf
  exact ⟨C, L, H, hC, hL, hH, fun Z T hZ hT =>
    (hgf Z T hZ hT).trans (hb Z T hZ hT)⟩

theorem LogHeightBound.add {f g : ℝ → ℝ → ℝ} {p q : ℝ}
    (hf : LogHeightBound f p) (hg : LogHeightBound g q) :
    LogHeightBound (fun Z T => f Z T + g Z T) (max p q) := by
  obtain ⟨C₁, L₁, H₁, hC₁, hL₁, hH₁, hb₁⟩ := hf
  obtain ⟨C₂, L₂, H₂, hC₂, hL₂, hH₂, hb₂⟩ := hg
  refine ⟨C₁ + C₂, max L₁ L₂, max H₁ H₂, add_pos hC₁ hC₂,
    hL₁.trans (le_max_left _ _), hH₁.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT
  have h₁ := growthEnvelope_mono hC₁.le le_rfl (le_max_left p q)
    (le_max_left L₁ L₂) (le_max_left H₁ H₂) hZ hT
  have h₂ := growthEnvelope_mono hC₂.le le_rfl (le_max_right p q)
    (le_max_right L₁ L₂) (le_max_right H₁ H₂) hZ hT
  calc
    _ ≤ |f Z T| + |g Z T| := abs_add_le _ _
    _ ≤ growthEnvelope C₁ (max p q) (max L₁ L₂) (max H₁ H₂) Z T +
        growthEnvelope C₂ (max p q) (max L₁ L₂) (max H₁ H₂) Z T :=
      add_le_add ((hb₁ Z T hZ hT).trans h₁) ((hb₂ Z T hZ hT).trans h₂)
    _ = _ := by unfold growthEnvelope; ring

theorem LogHeightBound.mul {f g : ℝ → ℝ → ℝ} {p q : ℝ}
    (hf : LogHeightBound f p) (hg : LogHeightBound g q) :
    LogHeightBound (fun Z T => f Z T * g Z T) (p + q) := by
  obtain ⟨C₁, L₁, H₁, hC₁, hL₁, hH₁, hb₁⟩ := hf
  obtain ⟨C₂, L₂, H₂, hC₂, hL₂, hH₂, hb₂⟩ := hg
  refine ⟨C₁ * C₂, L₁ + L₂, H₁ + H₂, mul_pos hC₁ hC₂,
    add_nonneg hL₁ hL₂, add_nonneg hH₁ hH₂, ?_⟩
  intro Z T hZ hT
  rw [abs_mul, ← growthEnvelope_mul hZ hT]
  exact mul_le_mul (hb₁ Z T hZ hT) (hb₂ Z T hZ hT) (abs_nonneg _)
    (growthEnvelope_nonneg hC₁.le hZ hT)

theorem LogHeightBound.rpow {f : ℝ → ℝ → ℝ} {p q : ℝ}
    (hf : LogHeightBound f p) (hq : 0 ≤ q) :
    LogHeightBound (fun Z T => |f Z T| ^ q) (p * q) := by
  obtain ⟨C, L, H, hC, hL, hH, hb⟩ := hf
  refine ⟨C ^ q, L * q, H * q, Real.rpow_pos_of_pos hC _,
    mul_nonneg hL hq, mul_nonneg hH hq, ?_⟩
  intro Z T hZ hT
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    ← growthEnvelope_rpow hC.le hZ hT]
  exact Real.rpow_le_rpow (abs_nonneg _) (hb Z T hZ hT) hq

theorem LogHeightBound.finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) (p : ℝ)
    (hf : ∀ i ∈ s, LogHeightBound (f i) p) :
    LogHeightBound (fun Z T => ∑ i ∈ s, f i Z T) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LogHeightBound.zero p
  | @insert a s ha ih =>
    have h := (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))
    simpa only [max_self, Finset.sum_insert ha] using h

theorem LogHeightBound.finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ → ℝ) (p : ι → ℝ)
    (hf : ∀ i ∈ s, LogHeightBound (f i) (p i)) :
    LogHeightBound (fun Z T => ∏ i ∈ s, f i Z T) (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LogHeightBound.const (1 : ℝ)
  | @insert a s ha ih =>
    have h := (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))
    simpa only [Finset.prod_insert ha, Finset.sum_insert ha] using h

/-- A normalized finite outer measure contributes precisely its remaining
mass envelope.  The row estimate uses common constants before the varying
index set is selected, so this does not insert an additional row count. -/
theorem weighted_finite_sum_envelope {ι : Type*} (s : Finset ι)
    (w f : ι → ℝ) {C p L H C' p' L' H' Z T : ℝ}
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hT : 0 ≤ T)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, |f i| ≤ growthEnvelope C p L H Z T)
    (hmass : ∑ i ∈ s, w i ≤ growthEnvelope C' p' L' H' Z T) :
    |∑ i ∈ s, w i * f i| ≤
      growthEnvelope (C * C') (p + p') (L + L') (H + H') Z T := by
  calc
    _ ≤ ∑ i ∈ s, |w i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |f i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * growthEnvelope C p L H Z T :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (hw i hi))
    _ = growthEnvelope C p L H Z T * ∑ i ∈ s, w i := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ growthEnvelope C p L H Z T * growthEnvelope C' p' L' H' Z T :=
      mul_le_mul_of_nonneg_left hmass (growthEnvelope_nonneg hC hZ hT)
    _ = _ := growthEnvelope_mul hZ hT

/-- A finite-depth algebraic reduction, with the same fixed Cauchy/Hölder
powers at every occurrence of a node. -/
inductive ReductionTree (ι : Type*) where
  | leaf (i : ι)
  | add (left right : ReductionTree ι)
  | mul (left right : ReductionTree ι)
  | power (child : ReductionTree ι) (q : ℝ) (nonnegative : 0 ≤ q)

def ReductionTree.eval {ι : Type*} (f : ι → ℝ → ℝ → ℝ) :
    ReductionTree ι → ℝ → ℝ → ℝ
  | .leaf i => f i
  | .add l r => fun Z T => l.eval f Z T + r.eval f Z T
  | .mul l r => fun Z T => l.eval f Z T * r.eval f Z T
  | .power t q _ => fun Z T => |t.eval f Z T| ^ q

def ReductionTree.arithmeticPower {ι : Type*} (p : ι → ℝ) : ReductionTree ι → ℝ
  | .leaf i => p i
  | .add l r => max (l.arithmeticPower p) (r.arithmeticPower p)
  | .mul l r => l.arithmeticPower p + r.arithmeticPower p
  | .power t q _ => t.arithmeticPower p * q

theorem ReductionTree.propagate {ι : Type*} (t : ReductionTree ι)
    (f : ι → ℝ → ℝ → ℝ) (p : ι → ℝ)
    (h : ∀ i, LogHeightBound (f i) (p i)) :
    LogHeightBound (t.eval f) (t.arithmeticPower p) := by
  induction t with
  | leaf i => exact h i
  | add l r hl hr => exact hl.add hr
  | mul l r hl hr => exact hl.mul hr
  | power t q hq ht => exact ht.rpow hq

/-- Every finite logarithmic degree is absorbed by any positive arithmetic
loss.  The loss is given before the degree; only the constant depends on it. -/
theorem log_power_absorption (η : ℝ) (hη : 0 < η) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (1 + Real.log Z) ^ L ≤ C * Z ^ η := by
  let δ := η / (L + 1)
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hδL : δ * L ≤ η := by
    have heq : δ * (L + 1) = η := by
      dsimp [δ]
      exact div_mul_cancel₀ η (by linarith : L + 1 ≠ 0)
    nlinarith
  refine ⟨(1 + 1 / δ) ^ L, Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro Z hZ
  have hZn : 0 ≤ Z := zero_le_one.trans hZ
  have hlogn : 0 ≤ 1 + Real.log Z := by linarith [Real.log_nonneg hZ]
  have hlog : 1 + Real.log Z ≤ (1 + 1 / δ) * Z ^ δ := by
    calc
      _ ≤ Z ^ δ + Z ^ δ / δ :=
        add_le_add (Real.one_le_rpow hZ hδ.le) (Real.log_le_rpow_div hZn hδ)
      _ = _ := by ring
  calc
    _ ≤ ((1 + 1 / δ) * Z ^ δ) ^ L := Real.rpow_le_rpow hlogn hlog hL
    _ = (1 + 1 / δ) ^ L * Z ^ (δ * L) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZn _), ← Real.rpow_mul hZn]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hδL) (Real.rpow_nonneg (by positivity) _)

theorem LogHeightBound.absorb {f : ℝ → ℝ → ℝ} {p : ℝ}
    (h : LogHeightBound f p) (η : ℝ) (hη : 0 < η) :
    ∃ C H : ℝ, 0 < C ∧ 0 ≤ H ∧
      ∀ Z T : ℝ, 1 ≤ Z → 0 ≤ T →
        |f Z T| ≤ C * Z ^ (p + η) * (1 + T) ^ H := by
  obtain ⟨C, L, H, hC, hL, hH, hb⟩ := h
  obtain ⟨C', hC', hlog⟩ := log_power_absorption η hη L hL
  refine ⟨C * C', H, mul_pos hC hC', hH, ?_⟩
  intro Z T hZ hT
  calc
    _ ≤ growthEnvelope C p L H Z T := hb Z T hZ hT
    _ ≤ C * Z ^ p * (C' * Z ^ η) * (1 + T) ^ H := by
      unfold growthEnvelope
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlog Z hZ)
          (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hZ) _)))
        (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [Real.rpow_add (zero_lt_one.trans_le hZ)]; ring

/-- Internal polynomial height degree is fixed before the external tail
order.  This explicit ceiling never depends on that later order. -/
theorem polynomial_height_budget {A ε d τ Z : ℝ}
    (hA : 0 ≤ A) (_hε : 0 < ε) (_hd : 0 < d) (hτ : 0 ≤ τ)
    (hceiling : τ ≤ d * ε / (20 * (A + 1))) (hZ : 1 ≤ Z) :
    (1 + Z ^ τ) ^ A ≤ 2 ^ A * Z ^ (d * ε / 20) := by
  have hz : 0 ≤ Z := zero_le_one.trans hZ
  have hτA : τ * A ≤ d * ε / 20 := by
    have h := (le_div_iff₀ (by positivity : 0 < 20 * (A + 1))).mp hceiling
    nlinarith
  have hpow := Real.one_le_rpow hZ hτ
  calc
    _ ≤ (2 * Z ^ τ) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
    _ = 2 ^ A * Z ^ (τ * A) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hz _),
        ← Real.rpow_mul hz]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hτA) (Real.rpow_nonneg (by norm_num) _)

end HeckeSkeleton.Moments.UniformAmplify
