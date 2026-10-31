import HeckeGeneral.Analysis.MomentInputs
import HeckeGeneral.Analysis.GlobalThetaData

/-!
# All profile slices used by a moment model

The three ideal tests and every prime window use the same constants.  The
index type includes the actual row of an ideal test, so rowwise uniformity
is retained.  These definitions describe analytic data and contain no
moment estimate.  Mixed parameter regularity and common Fourier measures
are separate inputs to a canonical induction.
-/

noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField
open HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical ContDiff

variable {K : Type} [Field K] [NumberField K]
variable {omega ψ : HeckeCharacter K}

/-- Every scalar profile actually evaluated by `inversePolynomial`,
`plainPolynomial`, and `primePolynomial`. -/
inductive ModelProfileIndex (d : MomentData K omega ψ) where
  | inverse (u : NonzeroIdeal K)
  | plain₁ (u : NonzeroIdeal K)
  | plain₂ (u : NonzeroIdeal K)
  | prime (j : Fin d.geometry.slotCount)

def modelProfile (d : MomentData K omega ψ) : ModelProfileIndex d → ℝ → ℂ
  | .inverse u => d.inverseTest.profile u 0
  | .plain₁ u => d.plainTest₁.profile u 0
  | .plain₂ u => d.plainTest₂.profile u 0
  | .prime j => (d.geometry.slots j).profile 0

def SliceControl (J : ℕ) (A C H a b T : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
    (∀ y, f y ≠ 0 → a ≤ y ∧ y ≤ b) ∧
    testSeminorm f J A ≤ C * (1 + T) ^ H

/-- This replaces the ideal-test-only clause of the source interface. -/
def ModelProfileControl (d : MomentData K omega ψ)
    (J : ℕ) (A C H a b T : ℝ) : Prop :=
  ∀ q : ModelProfileIndex d, SliceControl J A C H a b T (modelProfile d q)

theorem modelProfileControl_inverse {d : MomentData K omega ψ}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) (u : NonzeroIdeal K) :
    SliceControl J A C H a b T (d.inverseTest.profile u 0) := h (.inverse u)

theorem modelProfileControl_plain₁ {d : MomentData K omega ψ}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) (u : NonzeroIdeal K) :
    SliceControl J A C H a b T (d.plainTest₁.profile u 0) := h (.plain₁ u)

theorem modelProfileControl_plain₂ {d : MomentData K omega ψ}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) (u : NonzeroIdeal K) :
    SliceControl J A C H a b T (d.plainTest₂.profile u 0) := h (.plain₂ u)

theorem modelProfileControl_prime {d : MomentData K omega ψ}
    {J : ℕ} {A C H a b T : ℝ}
    (h : ModelProfileControl d J A C H a b T) (j : Fin d.geometry.slotCount) :
    SliceControl J A C H a b T ((d.geometry.slots j).profile 0) := h (.prime j)

theorem modelProfileControl_iff {d : MomentData K omega ψ}
    {J : ℕ} {A C H a b T : ℝ} :
    ModelProfileControl d J A C H a b T ↔
      (∀ W ∈ [d.inverseTest, d.plainTest₁, d.plainTest₂], ∀ u,
        SliceControl J A C H a b T (W.profile u 0)) ∧
      (∀ j, SliceControl J A C H a b T ((d.geometry.slots j).profile 0)) := by
  constructor
  · intro h
    refine ⟨?_, modelProfileControl_prime h⟩
    intro W hW u
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact modelProfileControl_inverse h u
    · exact modelProfileControl_plain₁ h u
    · exact modelProfileControl_plain₂ h u
  · rintro ⟨hideal, hprime⟩ q
    cases q with
    | inverse u => exact hideal _ (by simp) u
    | plain₁ u => exact hideal _ (by simp) u
    | plain₂ u => exact hideal _ (by simp) u
    | prime j => exact hprime j

/-- The finite Euler-integral maximum is bounded by a common bound on its
constituents.  This uses the repository's literal `testSeminorm`. -/
theorem testSeminorm_le_of_integrals (f : ℝ → ℂ) (J : ℕ) (A B : ℝ)
    (hB : 0 ≤ B) (h : ∀ j ≤ J, testIntegral f j A ≤ B) :
    testSeminorm f J A ≤ B := by
  apply Finset.sup'_le
  intro j hj
  exact max_le hB (h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

theorem testSeminorm_nonneg (f : ℝ → ℂ) (J : ℕ) (A : ℝ) :
    0 ≤ testSeminorm f J A := by
  exact (le_max_left _ _).trans
    (Finset.le_sup' (fun j => max 0 (testIntegral f j A)) (by simp : 0 ∈ Finset.range (J + 1)))

theorem testIntegral_le_testSeminorm (f : ℝ → ℂ) {j J : ℕ} (A : ℝ)
    (hj : j ≤ J) : testIntegral f j A ≤ testSeminorm f J A := by
  exact (le_max_right _ _).trans
    (Finset.le_sup' (fun k => max 0 (testIntegral f k A))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem testSeminorm_mono_order (f : ℝ → ℂ) {J L : ℕ} (A : ℝ)
    (hJL : J ≤ L) : testSeminorm f J A ≤ testSeminorm f L A :=
  testSeminorm_le_of_integrals f J A _ (testSeminorm_nonneg f L A)
    (fun j hj => testIntegral_le_testSeminorm f A (hj.trans hJL))

/-- A single common family of finite Euler-integral bounds covers all
ideal tests and all prime windows, including their independent row indices. -/
theorem modelProfileControl_of_integrals (d : MomentData K omega ψ)
    (J : ℕ) (A C H a b T : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsmooth : ∀ q, ContDiff ℝ ∞ (modelProfile d q))
    (hsupport : ∀ q y, modelProfile d q y ≠ 0 → a ≤ y ∧ y ≤ b)
    (hintegral : ∀ q, ∀ j ≤ J,
      testIntegral (modelProfile d q) j A ≤ C * (1 + T) ^ H) :
    ModelProfileControl d J A C H a b T := by
  intro q
  refine ⟨hsmooth q, hsupport q, ?_⟩
  exact testSeminorm_le_of_integrals _ J A _
    (mul_nonneg hC (Real.rpow_nonneg (by linarith) _)) (hintegral q)

/-- Moving scales and rowwise parameters are part of the index.  Constants
are chosen for the whole family, before any index is selected. -/
def UniformProfileControl {ι : Sort*} (f : ι → ℝ → ℂ) (height : ι → ℝ) : Prop :=
  ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
    ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
      ∀ i, SliceControl J A C H a b (height i) (f i)

theorem UniformProfileControl.reindex {ι κ : Sort*}
    {f : ι → ℝ → ℂ} {height : ι → ℝ}
    (h : UniformProfileControl f height) (g : κ → ι) :
    UniformProfileControl (fun k => f (g k)) (fun k => height (g k)) := by
  intro J A hA
  obtain ⟨C, H, a, b, hC, hH, ha, hab, hbound⟩ := h J A hA
  exact ⟨C, H, a, b, hC, hH, ha, hab, fun k => hbound (g k)⟩

/-- Combining finitely many kinds of profiles changes constants and height
degree, while preserving one common annulus and quantifier order. -/
theorem UniformProfileControl.sum {ι κ : Type*}
    {f : ι → ℝ → ℂ} {g : κ → ℝ → ℂ} {hf : ι → ℝ} {hg : κ → ℝ}
    (hfn : ∀ i, 0 ≤ hf i) (hgn : ∀ k, 0 ≤ hg k)
    (hF : UniformProfileControl f hf) (hG : UniformProfileControl g hg) :
    UniformProfileControl (Sum.elim f g) (Sum.elim hf hg) := by
  intro J A hA
  obtain ⟨C₁, H₁, a₁, b₁, hC₁, hH₁, ha₁, hab₁, hbF⟩ := hF J A hA
  obtain ⟨C₂, H₂, a₂, b₂, hC₂, hH₂, ha₂, hab₂, hbG⟩ := hG J A hA
  refine ⟨max C₁ C₂, max H₁ H₂, min a₁ a₂, max b₁ b₂,
    hC₁.trans_le (le_max_left _ _), hH₁.trans (le_max_left _ _),
    lt_min ha₁ ha₂, (min_le_left _ _).trans_lt (hab₁.trans_le (le_max_left _ _)), ?_⟩
  have raise (C H a b T : ℝ) (f₀ : ℝ → ℂ) (hT : 0 ≤ T)
      (hC : 0 ≤ C) (hCC : C ≤ max C₁ C₂) (hHH : H ≤ max H₁ H₂)
      (haa : min a₁ a₂ ≤ a) (hbb : b ≤ max b₁ b₂)
      (h : SliceControl J A C H a b T f₀) :
      SliceControl J A (max C₁ C₂) (max H₁ H₂)
        (min a₁ a₂) (max b₁ b₂) T f₀ := by
    refine ⟨h.1, fun y hy => ⟨haa.trans (h.2.1 y hy).1,
      (h.2.1 y hy).2.trans hbb⟩, h.2.2.trans ?_⟩
    exact mul_le_mul hCC
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + T) hHH)
      (Real.rpow_nonneg (by linarith) _) (hC.trans hCC)
  intro i
  cases i with
  | inl i =>
    exact raise _ _ _ _ _ _ (hfn i) hC₁.le (le_max_left _ _)
      (le_max_left _ _) (min_le_left _ _) (le_max_left _ _) (hbF i)
  | inr k =>
    exact raise _ _ _ _ _ _ (hgn k) hC₂.le (le_max_right _ _)
      (le_max_right _ _) (min_le_right _ _) (le_max_right _ _) (hbG k)

end HeckeSkeleton.Moments.UniformAmplify

