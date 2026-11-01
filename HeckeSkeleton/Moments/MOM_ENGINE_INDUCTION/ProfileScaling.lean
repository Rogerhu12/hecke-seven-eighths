import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MomentProfileScaling
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact scalar normalization of the actual profiles

All three ideal tests and every prime profile may be multiplied by one
positive scalar. Their original finite supports, rows, characters, masks,
slot counts and lengths are unchanged. The same scalar is used in both
rectangles of a centered coefficient, so the complete centered energy has
exactly the same homogeneity as the ordinary paired energy.

Dividing the profiles of one node by `A > 0` extracts the explicit factor
`A^((slotCount + 2)*2)` from its energy. The scalar can subsequently depend
on a continuous child parameter, provided that this extracted factor is
charged to the common kernel. No uniform bound for frequency derivatives
or for the resulting weighted kernel mass is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]

variable {ω ψ : HeckeCharacter K}

/-- Both rectangles receive the same profile normalization. -/
def Node.scaleProfiles (n : Node K ω ψ) (a : ℝ) (ha : 0 < a) : Node K ω ψ :=
  { n with data := scaledMomentProfiles n.data a ha }

theorem Node.scaleProfiles_invariants (n : Node K ω ψ) (a : ℝ) (ha : 0 < a) :
    (n.scaleProfiles a ha).parameters = n.parameters ∧
    (n.scaleProfiles a ha).centered = n.centered ∧
    (n.scaleProfiles a ha).comparison₁ = n.comparison₁ ∧
    (n.scaleProfiles a ha).comparison₂ = n.comparison₂ ∧
    (n.scaleProfiles a ha).width = n.width := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Scaling commutes with the entire centered difference before absolute
values are taken, rather than scaling its rectangles independently. -/
theorem Node.plainPair_scaleProfiles (n : Node K ω ψ) (a : ℝ) (ha : 0 < a)
    (u : NonzeroIdeal K) (U t : ℝ) :
    (n.scaleProfiles a ha).plainPair u U t = (a : ℂ) ^ 2 * n.plainPair u U t := by
  have h₁ (N : ℝ) :
      plainPolynomial (scaledMomentProfiles n.data a ha)
        (scaledMomentProfiles n.data a ha).plainTest₁ u N t =
          (a : ℂ) * plainPolynomial n.data n.data.plainTest₁ u N t :=
    plainPolynomial_scaledMomentProfiles n.data n.data.plainTest₁ a ha u N t
  have h₂ (N : ℝ) :
      plainPolynomial (scaledMomentProfiles n.data a ha)
        (scaledMomentProfiles n.data a ha).plainTest₂ u N t =
          (a : ℂ) * plainPolynomial n.data n.data.plainTest₂ u N t :=
    plainPolynomial_scaledMomentProfiles n.data n.data.plainTest₂ a ha u N t
  simp only [Node.plainPair, Node.scaleProfiles, h₁, h₂]
  split_ifs <;> ring

/-- Exact homogeneity of the complete finite energy with its true rows,
common mask, and centered coefficient. -/
theorem Node.energy_scaleProfiles (n : Node K ω ψ) (a : ℝ) (ha : 0 < a) (U t : ℝ) :
    (n.scaleProfiles a ha).energy U t =
      a ^ ((n.data.geometry.slotCount + 2) * 2) * n.energy U t := by
  change (∑ u ∈ pairedRows (scaledMomentProfiles n.data a ha) n.parameters U,
    ‖(n.scaleProfiles a ha).plainPair u U t *
      slotProduct (scaledMomentProfiles n.data a ha) u U t‖ ^ 2) = _
  rw [pairedRows_scaledMomentProfiles, Node.energy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Node.plainPair_scaleProfiles, slotProduct_scaledMomentProfiles]
  have hamp : (a : ℂ) ^ 2 * n.plainPair u U t *
      ((a : ℂ) ^ n.data.geometry.slotCount * slotProduct n.data u U t) =
        (a : ℂ) ^ (n.data.geometry.slotCount + 2) *
          (n.plainPair u U t * slotProduct n.data u U t) := by
    rw [pow_add]
    ring
  rw [hamp, norm_mul, norm_pow, Complex.norm_of_nonneg ha.le, mul_pow, ← pow_mul]

/-- Width normalization is unchanged, so the same exact factor is charged
to a common child kernel in the induction. -/
theorem Node.normalizedEnergy_scaleProfiles (n : Node K ω ψ)
    (a : ℝ) (ha : 0 < a) (U t : ℝ) :
    (n.scaleProfiles a ha).normalizedEnergy U t =
      a ^ ((n.data.geometry.slotCount + 2) * 2) * n.normalizedEnergy U t := by
  have hwidth : (n.scaleProfiles a ha).width = n.width := rfl
  unfold Node.normalizedEnergy
  rw [hwidth, Node.energy_scaleProfiles, mul_div_assoc]

/-- Divide every profile by one fixed positive envelope. The envelope is
constant across the rows, the test variable, and the two rectangles. -/
def Node.normalizeProfiles (n : Node K ω ψ) (A : ℝ) (hA : 0 < A) : Node K ω ψ :=
  n.scaleProfiles A⁻¹ (inv_pos.mpr hA)

/-- The exact extracted energy factor, ready to be included in the
positive common kernel before its weighted mass is estimated. -/
theorem Node.energy_normalizeProfiles (n : Node K ω ψ) (A : ℝ) (hA : 0 < A) (U t : ℝ) :
    n.energy U t = A ^ ((n.data.geometry.slotCount + 2) * 2) *
      (n.normalizeProfiles A hA).energy U t := by
  rw [Node.normalizeProfiles, Node.energy_scaleProfiles, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), one_mul]

theorem Node.normalizedEnergy_normalizeProfiles (n : Node K ω ψ)
    (A : ℝ) (hA : 0 < A) (U t : ℝ) :
    n.normalizedEnergy U t = A ^ ((n.data.geometry.slotCount + 2) * 2) *
      (n.normalizeProfiles A hA).normalizedEnergy U t := by
  rw [Node.normalizeProfiles, Node.normalizedEnergy_scaleProfiles, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), one_mul]

end HeckeSkeleton.Moments.EngineInduction
