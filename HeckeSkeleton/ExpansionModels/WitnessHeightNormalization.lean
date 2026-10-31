import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed six-dimensional witness parameters with the original height box

Coordinates 0,1,2 are the common physical Mellin point; coordinate 3 is
half the cutoff exponent t; coordinate 4 is a bounded finite presentation
code; coordinate 5 is the physical height T.  Imaginary witness frequencies
are divided by one fixed positive constant and multiplied back inside the
actual profile.  Thus no replacement of SourceMomentIndex(Z,T) by (Z,C*T)
is needed.
-/

set_option autoImplicit false
noncomputable section
namespace ExpansionRecipe
open scoped Classical

def finitePresentationCode {n : ℕ} (i : Fin n) : ℝ := (i.val : ℝ) / (n + 1)

lemma finitePresentationCode_nonneg {n : ℕ} (i : Fin n) :
    0 ≤ finitePresentationCode i := by unfold finitePresentationCode; positivity

lemma finitePresentationCode_lt_one {n : ℕ} (i : Fin n) :
    finitePresentationCode i < 1 := by
  unfold finitePresentationCode
  apply (div_lt_one (by positivity)).mpr
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  linarith

lemma finitePresentationCode_injective (n : ℕ) :
    Function.Injective (finitePresentationCode (n := n)) := by
  intro i j h
  apply Fin.ext
  apply Nat.cast_injective (R := ℝ)
  exact (div_left_inj' (by positivity : (n : ℝ) + 1 ≠ 0)).mp h

def decodePresentation (n : ℕ) (hn : 0 < n) (x : ℝ) : Fin n :=
  if h : ∃ i : Fin n, finitePresentationCode i = x then Classical.choose h else ⟨0, hn⟩

lemma decodePresentation_code (n : ℕ) (hn : 0 < n) (i : Fin n) :
    decodePresentation n hn (finitePresentationCode i) = i := by
  have h : ∃ j : Fin n, finitePresentationCode j = finitePresentationCode i := ⟨i, rfl⟩
  rw [decodePresentation, dif_pos h]
  exact finitePresentationCode_injective n (Classical.choose_spec h)

def sourceHeightVector (physical : Fin 3 → ℝ) (t code T : ℝ) : Fin 6 → ℝ :=
  ![physical 0, physical 1, physical 2, t / 2, code, T]

lemma sourceHeightVector_anchor (physical : Fin 3 → ℝ) (t code T : ℝ) :
    sourceHeightVector physical t code T 5 = T := rfl

theorem sourceHeightVector_norm_le (physical : Fin 3 → ℝ) (t code T : ℝ)
    (hT : 1 ≤ T) (hp : ‖physical‖ ≤ T) (ht : 1 ≤ t ∧ t ≤ 3 / 2)
    (hc : 0 ≤ code ∧ code ≤ 1) : ‖sourceHeightVector physical t code T‖ ≤ T := by
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hT)).mpr
  intro i
  have h0 := (norm_le_pi_norm physical 0).trans hp
  have h1 := (norm_le_pi_norm physical 1).trans hp
  have h2 := (norm_le_pi_norm physical 2).trans hp
  have ht' : ‖t / 2‖ ≤ T := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hc' : ‖code‖ ≤ T := by
    rw [Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact hc.2.trans hT
  have hT' : ‖T‖ ≤ T := by rw [Real.norm_of_nonneg (zero_le_one.trans hT)]
  fin_cases i
  · simpa [sourceHeightVector] using h0
  · simpa [sourceHeightVector] using h1
  · simpa [sourceHeightVector] using h2
  · simpa [sourceHeightVector] using ht'
  · simpa [sourceHeightVector] using hc'
  · simpa [sourceHeightVector] using hT' 

theorem sourceHeightVector_norm_eq (physical : Fin 3 → ℝ) (t code T : ℝ)
    (hT : 1 ≤ T) (hp : ‖physical‖ ≤ T) (ht : 1 ≤ t ∧ t ≤ 3 / 2)
    (hc : 0 ≤ code ∧ code ≤ 1) : ‖sourceHeightVector physical t code T‖ = T := by
  apply le_antisymm (sourceHeightVector_norm_le physical t code T hT hp ht hc)
  have h := norm_le_pi_norm (sourceHeightVector physical t code T) 5
  simpa only [sourceHeightVector_anchor, Real.norm_of_nonneg (zero_le_one.trans hT)] using h

variable {Row : Type*}

def normalizedImaginaryParameters (ν : Row → ℝ) (C : ℝ) : Row → Fin 6 → ℝ :=
  fun u _ => ν u / C

lemma normalizedImaginaryParameters_exact (ν : Row → ℝ) (C : ℝ) (hC : 0 < C)
    (u : Row) (j : Fin 6) :
    C * normalizedImaginaryParameters ν C u j = ν u := by
  dsimp [normalizedImaginaryParameters]
  field_simp

theorem normalizedImaginaryParameters_bound (ν : Row → ℝ) (C T : ℝ)
    (hC : 0 < C) (ξ : Fin 6 → ℝ) (hT : 0 ≤ T) (hanchor : ξ 5 = T)
    (hν : ∀ u, |ν u| ≤ C * T) :
    ∀ u, ‖normalizedImaginaryParameters ν C u‖ ≤ 1 + ‖ξ‖ := by
  have hξ : T ≤ ‖ξ‖ := by
    have h := norm_le_pi_norm ξ 5
    simpa [hanchor, Real.norm_of_nonneg hT] using h
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖ν u / C‖ ≤ 1 + ‖ξ‖
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hC]
  have hdiv : |ν u| / C ≤ T := (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hν u)
  linarith

end ExpansionRecipe

#print axioms ExpansionRecipe.sourceHeightVector_norm_eq
#print axioms ExpansionRecipe.normalizedImaginaryParameters_bound
