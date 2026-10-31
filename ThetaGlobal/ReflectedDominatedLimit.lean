import ThetaGlobal.ReflectedCoefficientSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Uniform domination and regularizer removal for the literal reflected series

The coefficient is proved bounded in ReflectedCoefficientModel and ideal
counting is supplied by Mathlib. A common quadratic kernel tail automatically
produces the summable majorant required by Tannery's theorem. The index keeps
all three ideal variables, every finite branch, and all unit sectors.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedDominatedLimit

open Filter
open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedCoefficientModel
open ThetaGlobal.ReflectedCoefficientSummability
open scoped Classical BigOperators Topology nonZeroDivisors

variable {P I A U : Type} [CommMonoid A] [Finite U]
variable (D : ScalarData P I A U) (d : Frame P I)

def argument (X : ℝ) (i : AdmissibleIndex (U := U) d) : ℝ :=
  X * D.normI i.val.numeratorFrozen * D.normI i.val.c * D.normI i.val.n ^ 3 /
    (D.normI d.moving * D.normI (activeFrozenIdeal D i.val) *
      D.normI (activeMarkedIdeal D i.val)) ^ 2

theorem argument_pos {X : ℝ} (hX : 0 < X) (i : AdmissibleIndex (U := U) d) :
    0 < argument D d X i := by
  have hnorm (a : I) : 0 < D.normI a :=
    lt_of_lt_of_le zero_lt_one (D.normI_ge_one a)
  exact div_pos
    (mul_pos (mul_pos (mul_pos hX (hnorm _)) (hnorm _)) (pow_pos (hnorm _) _))
    (sq_pos_of_pos (mul_pos (mul_pos (hnorm _) (hnorm _)) (hnorm _)))

/-- A summable envelope independent of the regularizer and the sector. -/
def majorant (B X : ℝ) (i : AdmissibleIndex (U := U) d) : ℝ :=
  ‖reflectedCoefficient D d i.val‖ * B * inverseSquare (argument D d X i)

theorem summable_majorant
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X) :
    Summable (majorant D d B X) := by
  let k : Unit → ℝ → ℂ := fun _ y => ((B * inverseSquare y : ℝ) : ℂ)
  have hk : ∀ (c : Unit) y, 0 < y → ‖k c y‖ ≤ B * inverseSquare y := by
    intro c y _
    change ‖((B * inverseSquare y : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg y))]
  have hs := summable_reflectedTerm D d hcount (fun _ => ()) k B hB hk hX
  apply hs.norm.congr
  intro i
  change ‖reflectedCoefficient D d i.val *
      ((B * inverseSquare (argument D d X i) : ℝ) : ℂ)‖ =
    ‖reflectedCoefficient D d i.val‖ * B * inverseSquare (argument D d X i)
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hB (inverseSquare_nonneg _))]
  ring

theorem norm_reflectedTerm_le_majorant {C : Type*}
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : C → ℝ → ℂ) {B X : ℝ}
    (htail : ∀ c y, 0 < y → ‖kernel c y‖ ≤ B * inverseSquare y)
    (hX : 0 < X) (i : AdmissibleIndex (U := U) d) :
    ‖reflectedTerm D d sector kernel X i‖ ≤ majorant D d B X i := by
  change ‖reflectedCoefficient D d i.val * kernel (sector i) (argument D d X i)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ ‖reflectedCoefficient D d i.val‖ *
        (B * inverseSquare (argument D d X i)) :=
      mul_le_mul_of_nonneg_left (htail _ _ (argument_pos D d hX i)) (norm_nonneg _)
    _ = _ := by dsimp only [majorant]; ring

/-- An eventual common quadratic tail suffices for exchanging a regularizer
limit with the full literal reflected series. The limit series is proved
summable as part of the conclusion; its convergence is not a premise. -/
theorem tendsto_tsum_reflectedTerm {T C : Type*} {l : Filter T} [l.NeBot]
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y))) :
    Summable (reflectedTerm D d sector kernel₀ X) ∧
      Tendsto (fun n => ∑' i, reflectedTerm D d sector (kernel n) X i)
        l (𝓝 (∑' i, reflectedTerm D d sector kernel₀ X i)) := by
  have hmajor := summable_majorant D d hcount hB hX
  have hpoint (i : AdmissibleIndex (U := U) d) :
      Tendsto (fun n => reflectedTerm D d sector (kernel n) X i)
        l (𝓝 (reflectedTerm D d sector kernel₀ X i)) := by
    exact tendsto_const_nhds.mul (hlim (sector i) _ (argument_pos D d hX i))
  have hbound : ∀ᶠ n in l, ∀ i,
      ‖reflectedTerm D d sector (kernel n) X i‖ ≤ majorant D d B X i :=
    htail.mono (fun n hn i => norm_reflectedTerm_le_majorant D d sector (kernel n) hn hX i)
  refine ⟨hmajor.of_norm_bounded (fun i => ?_),
    tendsto_tsum_of_dominated_convergence hmajor hpoint hbound⟩
  exact le_of_tendsto (hpoint i).norm (hbound.mono (fun n hn => hn i))

/-- If scalar convolution and fixed-profile unfolding have supplied the
regularized equalities, the only remaining limit step is uniqueness of limits.
This theorem neither assumes nor constructs the automorphic seed identity. -/
theorem equality_of_regularized_equalities {T C : Type*} {l : Filter T} [l.NeBot]
    (hcount : Summable (fun a => inverseSquare (D.normI a)))
    (sector : AdmissibleIndex (U := U) d → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y)))
    (forward : T → ℂ) (forward₀ : ℂ)
    (hforward : Tendsto forward l (𝓝 forward₀))
    (heq : ∀ᶠ n in l, forward n = ∑' i, reflectedTerm D d sector (kernel n) X i) :
    forward₀ = ∑' i, reflectedTerm D d sector kernel₀ X i := by
  have href := (tendsto_tsum_reflectedTerm D d hcount sector kernel kernel₀
    hB hX htail hlim).2
  exact tendsto_nhds_unique (hforward.congr' heq) href

section NumberField

open NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Actual ideal counting, including any exterior-ideal subtype, discharges
the majorant's last counting premise automatically. -/
theorem tendsto_tsum_numberField_subtype_reflectedTerm
    (Q : (Ideal (𝓞 K))⁰ → Prop)
    (DS : ScalarData P {a : (Ideal (𝓞 K))⁰ // Q a} A U)
    (dS : Frame P {a : (Ideal (𝓞 K))⁰ // Q a})
    (hNorm : ∀ a, DS.normI a = ReflectedIdealMajorant.positiveIdealNorm K a.val)
    {T C : Type*} {l : Filter T} [l.NeBot]
    (sector : AdmissibleIndex (U := U) dS → C)
    (kernel : T → C → ℝ → ℂ) (kernel₀ : C → ℝ → ℂ)
    {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X)
    (htail : ∀ᶠ n in l, ∀ c y, 0 < y →
      ‖kernel n c y‖ ≤ B * inverseSquare y)
    (hlim : ∀ c y, 0 < y → Tendsto (fun n => kernel n c y) l (𝓝 (kernel₀ c y))) :
    Summable (reflectedTerm DS dS sector kernel₀ X) ∧
      Tendsto (fun n => ∑' i, reflectedTerm DS dS sector (kernel n) X i)
        l (𝓝 (∑' i, reflectedTerm DS dS sector kernel₀ X i)) := by
  apply tendsto_tsum_reflectedTerm DS dS _ sector kernel kernel₀ hB hX htail hlim
  simpa only [Function.comp_def, hNorm] using
    (ReflectedIdealMajorant.summable_positiveIdealNorm_inverseSquare K).subtype Q

end NumberField
end ThetaGlobal.ReflectedDominatedLimit

