import HeckeGeneral.Characters.LocalUniformizer
import HeckeGeneral.Characters.LocalResidueCharacter
import ThetaGlobal.FiniteShellCoefficients

/-!
# Literal valuation shells in the project's local fields

This file fixes the local shell parameter to the existing project
uniformizer and the actual embedding of integral units.  Consequently the
radius and residue cardinality fields of the generic construction are
proved equal to the genuine local absolute value and prime-ideal norm.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.ProjectLocalShell

open NumberField IsDedekindDomain
open HeckeGeneral.Characters
open ThetaGlobal.FiniteShell

variable (K : Type) [Field K] [NumberField K]

/-- The literal shell element π_p^k u, including negative valuations. -/
def shellPoint (p : HeightOneSpectrum (𝓞 K)) (k : ℤ)
    (u : (LocalIntegerRing K p)ˣ) : (p.adicCompletion K)ˣ :=
  localUniformizerUnit K p ^ k * localIntegerUnitsEmbedding K p u

/-- Its normalized local absolute value is exactly `q_p^(-k)`. -/
theorem shellPoint_norm (p : HeightOneSpectrum (𝓞 K)) (k : ℤ)
    (u : (LocalIntegerRing K p)ˣ) :
    ‖(shellPoint K p k u).val‖ = (p.asIdeal.absNorm : ℝ) ^ (-(k : ℝ)) := by
  simp only [shellPoint, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul,
    norm_zpow, localUniformizerUnit_norm, localIntegerUnitsEmbedding_norm, mul_one,
    Real.rpow_neg_eq_inv_rpow, Real.rpow_intCast, residueCard]

/-- Local shell data for a specified actual Whittaker value and unitary
local period.  The local period may have infinite-order uniformizer value. -/
def shellData (p : HeightOneSpectrum (𝓞 K))
    (W : (p.adicCompletion K)ˣ → ℂ) (L : (p.adicCompletion K)ˣ → Circle) :
    LocalShellData PUnit (p.adicCompletion K)ˣ (LocalIntegerRing K p)ˣ where
  q := p.asIdeal.absNorm
  q_gt_one := NumberField.HeightOneSpectrum.one_lt_absNorm p
  radius z := ‖z.val‖
  shell := shellPoint K p
  shell_radius := shellPoint_norm K p
  value := W
  multiplier _ k u := (L (shellPoint K p k u) : ℂ)
  multiplier_norm _ _ _ := (Circle.norm_coe _).le

/-- Transfer the actual local fixed-vector estimates.  These hypotheses
are stated directly on W at every local point, before integration. -/
theorem shellData_bounds (p : HeightOneSpectrum (𝓞 K))
    (W : (p.adicCompletion K)ˣ → ℂ) (L : (p.adicCompletion K)ˣ → Circle)
    (hlarge : ∃ M : ℝ, 0 < M ∧ ∀ z, M < ‖z.val‖ → W z = 0)
    (hsmall : ∀ δ : ℝ, 0 < δ → δ < 1 / 3 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ z, ‖z.val‖ ≤ 1 → ‖W z‖ ≤ B * ‖z.val‖ ^ δ) :
    LocalWhittakerBounds (shellData K p W L) where
  large_support := hlarge
  small_power := by
    intro δ hδ hδthird
    obtain ⟨B, hB, hb⟩ := hsmall δ hδ hδthird
    exact ⟨B, hB, fun z _ hz => hb z hz⟩

@[simp] theorem shellData_q (p : HeightOneSpectrum (𝓞 K))
    (W : (p.adicCompletion K)ˣ → ℂ) (L : (p.adicCompletion K)ˣ → Circle) :
    (shellData K p W L).q = p.asIdeal.absNorm := rfl

end ThetaGlobal.ProjectLocalShell

#print axioms ThetaGlobal.ProjectLocalShell.shellPoint_norm
#print axioms ThetaGlobal.ProjectLocalShell.shellData_bounds
