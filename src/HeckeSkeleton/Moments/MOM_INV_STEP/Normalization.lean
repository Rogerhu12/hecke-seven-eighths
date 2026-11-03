import HeckePort.Moments.Descent.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic

/-!
# Physical normalization of one canonical inverse step

The two prefactors, the count of distinct frozen triples, and the restored
child normalization are defined separately. Their cancellation is proved
from these definitions; it is not an input to the step.

The formulas are those of `can-child-identities` and `can-energy-identity`
in §4.5 of `weil_seven_eighths_revised.tex`. The physical scalar calculation
also follows `openai/math`, `Descent/PhysicalExponents.lean` and
`Descent/PhysicalBlockBudget.lean`, revision
`4eaee87548250b2682affda7d05d947c05554bae`.

This module proves the normalization and geometric ledger. The source
reindexing and estimates of the actual transformed kernels are separate
claims; none is encoded as a numerical definition here.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep

open HeckePort.Moments

/-- The product of extracted norms and the two column square roots after
the first weighted Cauchy inequality. -/
def firstRootScale (s : Fin 9 → ℝ) : ℝ :=
  s 3 * Real.sqrt (s 4) * s 5 * Real.sqrt (s 7) * Real.sqrt (s 8)

def firstKappa (M r ell V delta A B R : ℝ) : ℝ :=
  M - 2 * r - 2 * ell - V - delta + A + B - R / 2

def firstPhysicalHeight (M r ell V delta B j : ℝ) : ℝ :=
  2 * r - 2 * B - M + 4 * ell + 2 * V + delta - j

def secondLambda (M r ell V delta A B j t g theta : ℝ) : ℝ :=
  firstPhysicalHeight M r ell V delta B j - theta - (r - A - B - t - g)

/-- Norm count of distinct triples `(q₀,t',g'/d₂)`. -/
def secondCount (ell R j t g theta : ℝ) : ℝ :=
  ell + R / 2 - j + t + g - theta

def secondFormalColumn (r A B t g v : ℝ) : ℝ := r - A - B - t - g - v

def secondFormalLabel (B theta v j : ℝ) : ℝ := B + theta + v + j

theorem firstRootScale_rpow (Z : ℝ) (hZ : 0 < Z) (s : Fin 9 → ℝ) :
    firstRootScale (fun i => Z ^ s i) =
      Z ^ (s 3 + s 4 / 2 + s 5 + s 7 / 2 + s 8 / 2) := by
  have hs (x : ℝ) : Real.sqrt (Z ^ x) = Z ^ (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  unfold firstRootScale
  rw [hs, hs, hs, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]

theorem first_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V delta A₁ A₂ B R t h : ℝ) :
    Z ^ (-r - 2 * ell - V) * Z ^ M /
      firstRootScale (fun i =>
        Z ^ (![A₁, A₂, B, delta, R, t, h, r - A₁ - B - t, r - A₂ - B - t] i)) =
      Z ^ ((firstKappa M r ell V delta A₁ B R +
        firstKappa M r ell V delta A₂ B R) / 2) := by
  rw [firstRootScale_rpow Z hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  norm_num [firstKappa]
  ring

theorem second_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V delta A B j t g theta v eta tau : ℝ) :
    Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) /
      (Z ^ theta * Z ^ v * Z ^ secondFormalColumn r A B t g v) *
      Real.exp (6 * (eta * Real.log Z)) =
      Z ^ (secondLambda M r ell V delta A B j t g theta + 18 * eta + tau) := by
  have he : Real.exp (6 * (eta * Real.log Z)) = Z ^ (6 * eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ, ← Real.rpow_add hZ]
  congr 1
  unfold secondLambda secondFormalColumn
  ring

/-- The restored column plus label length equals the canonical `childF`
already used by the repository's margin lemmas. -/
theorem child_combined_length (r ell V A B t g theta v j : ℝ) :
    secondFormalColumn r A B t g v + secondFormalLabel B theta v j =
      childF (r + 3 * ell + V) ell A t g theta V j 0 := by
  unfold secondFormalColumn secondFormalLabel childF decrease
  ring

/-- Exact identity (17.64): the distinct-triple count occurs once. -/
theorem physical_prefactor_identity (M r ell V delta A B R j t g theta v : ℝ) :
    firstKappa M r ell V delta A B R +
      secondLambda M r ell V delta A B j t g theta +
      secondCount ell R j t g theta +
      2 * (secondFormalColumn r A B t g v + secondFormalLabel B theta v j) =
      r + 3 * ell + V := by
  unfold firstKappa secondLambda firstPhysicalHeight secondCount
    secondFormalColumn secondFormalLabel
  ring

theorem physical_step_energy_exponent
    (M r ell V delta A B R j t g theta v eta tau pi eps clip : ℝ)
    (hclip : clip ≤ 6 * eta) :
    firstKappa M r ell V delta A B R +
      secondLambda M r ell V delta A B j t g theta +
      secondCount ell R j t g theta +
      2 * (secondFormalColumn r A B t g v + secondFormalLabel B theta v j + clip) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      r + 3 * ell + V + 40 * eta + tau + pi + eps :=
  step_energy_exponent
    (physical_prefactor_identity M r ell V delta A B R j t g theta v) hclip

/-- The full physical scalar budget. `massEps` is charged after the two
Cauchy square roots, against the measure on distinct frozen triples. -/
theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1 ≤ Z) (M r ell V delta A B R j t g theta v eta tau pi eps massEps : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v) -
      secondFormalColumn r A B t g v ≤ 6 * eta)
    (hmass : massEps * (secondCount ell R j t g theta + 11 * eta / 2) ≤ pi) :
    Z ^ firstKappa M r ell V delta A B R * Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) *
      (Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) /
        (Z ^ theta * Z ^ v * Z ^ secondFormalColumn r A B t g v) *
        Real.exp (6 * (eta * Real.log Z))) *
      Z ^ ((secondCount ell R j t g theta + 11 * eta / 2) * (1 + massEps)) *
      Z ^ (2 * (max 0 (secondFormalColumn r A B t g v) +
        secondFormalLabel B theta v j) + eps) ≤
      Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) = Z ^ ((9 / 2 : ℝ) * eta) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp, ← Real.rpow_add hZpos, ← Real.rpow_add hZpos,
    ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V delta A B R j t g theta v
    eta tau pi eps
    (max 0 (secondFormalColumn r A B t g v) - secondFormalColumn r A B t g v) hclip
  nlinarith

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0 < Y) (hE : 0 < E) (hV : 0 < V) (hX : 0 < X) (a : ℂ) :
    ‖(Y : ℂ) * a * ((E * V * X : ℝ) : ℂ)⁻¹‖ = ‖a‖ * (Y / (E * V * X)) := by
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY,
    abs_of_pos (by positivity : 0 < E * V * X)]
  ring

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1 ≤ Z) (M r ell V delta A B R j t g theta v eta tau pi eps massEps : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hclip : max 0 (secondFormalColumn r A B t g v) -
      secondFormalColumn r A B t g v ≤ 6 * eta)
    (hmass : massEps * (secondCount ell R j t g theta + 11 * eta / 2) ≤ pi) :
    C * Z ^ firstKappa M r ell V delta A B R *
      Real.exp ((9 / 2 : ℝ) * (eta * Real.log Z)) *
      (Real.exp (6 * (eta * Real.log Z)) *
        ‖((Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) : ℝ) : ℂ) * ray *
          ((Z ^ theta * Z ^ v * Z ^ secondFormalColumn r A B t g v : ℝ) : ℂ)⁻¹‖) *
      Z ^ ((secondCount ell R j t g theta + 11 * eta / 2) * (1 + massEps)) *
      Z ^ (2 * (max 0 (secondFormalColumn r A B t g v) +
        secondFormalLabel B theta v j) + eps) ≤
      C * ‖ray‖ * Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity)
    (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V delta A B R j t g theta v
      eta tau pi eps massEps hclip hmass) (mul_nonneg hC (norm_nonneg ray))
  convert hh using 1 <;> ring

/-- The numerical source witnesses of a nonterminal child. Each field is a
support-length or puncture bound, never an energy estimate. -/
structure ChildGeometry (F M Q z c d eta : ℝ) where
  ell : ℝ
  A : ℝ
  t : ℝ
  g : ℝ
  theta : ℝ
  V : ℝ
  j : ℝ
  Qnew : ℝ
  clip : ℝ
  ell_nonneg : 0 ≤ ell
  A_nonneg : 0 ≤ A
  t_nonneg : 0 ≤ t
  V_nonneg : 0 ≤ V
  j_nonneg : 0 ≤ j
  common_divisor : -2 * eta ≤ g - theta
  label_bound : j ≤ 2 * ell + 3 * eta
  puncture : Qnew ≤ Q + decrease ell A t g theta V + 4 * eta
  clip_nonneg : 0 ≤ clip
  clip_bound : clip ≤ 6 * eta
  nonterminal : d ≤ ell + V

namespace ChildGeometry

variable {F M Q z c d eta : ℝ}

def Fchild (x : ChildGeometry F M Q z c d eta) : ℝ :=
  childF F x.ell x.A x.t x.g x.theta x.V x.j x.clip

def Mchild (x : ChildGeometry F M Q z c d eta) : ℝ :=
  childM M x.ell x.A x.t x.g x.theta x.V x.j eta

/-- Sharp first margin, sharp second margin, strict row decrease, and
combined-length cap. The statement keeps the original slot cap `z`. -/
theorem step (x : ChildGeometry F M Q z c d eta)
    (hparent : CanonicalMargins F M Q z c) (heta : 0 ≤ eta) (hstep : eta ≤ d / 16) :
    c - 5 * eta ≤ x.Fchild - x.Mchild - x.Qnew - z ∧
    c - 7 * eta ≤ 4 * x.Fchild - 3 * x.Mchild - 6 * z ∧
    3 * d / 2 ≤ M - x.Mchild ∧ x.Fchild ≤ F + 11 * eta := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := x.clip) hparent
    x.A_nonneg x.t_nonneg x.V_nonneg x.j_nonneg x.common_divisor x.puncture
  refine ⟨?_, ?_, ?_, ?_⟩
  · change c - 5 * eta ≤ childF _ _ _ _ _ _ _ _ _ - childM _ _ _ _ _ _ _ _ _ - _ - z
    linarith [x.clip_nonneg]
  · change c - 7 * eta ≤ 4 * childF _ _ _ _ _ _ _ _ _ -
      3 * childM _ _ _ _ _ _ _ _ _ - 6 * z
    linarith [x.clip_nonneg]
  · exact child_row_decrease x.A_nonneg x.t_nonneg x.common_divisor
      x.label_bound x.nonterminal hstep
  · exact childF_upper x.A_nonneg x.t_nonneg x.ell_nonneg x.V_nonneg
      x.common_divisor x.label_bound x.clip_bound

theorem margins (x : ChildGeometry F M Q z c d eta)
    (hparent : CanonicalMargins F M Q z c) (heta : 0 ≤ eta) :
    CanonicalMargins x.Fchild x.Mchild x.Qnew z (c - 7 * eta) :=
  child_margins hparent x.A_nonneg x.t_nonneg x.V_nonneg x.j_nonneg
    x.common_divisor x.clip_nonneg heta x.puncture

end ChildGeometry

end HeckeSkeleton.Moments.MOMInvStep
