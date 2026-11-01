import HeckeSkeleton.HighBinSupport.ActualPhysicalSlotBound
import Expansion.ActualPhysicalPrimeSlotBound

/-!
# Main-slot bounds on the unchanged physical amplitude fibers

The finite-height prime theorem is applied at the original power height.
Its cutoff may depend on that positive height exponent, but the width,
alphabet, detector-height range and all losses are fixed beforehand.
Rounding then gives the upper bound for each actual label at every point
of its moving fiber, not merely at its maximal-cardinality sample.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open Expansion.Project ExpansionInterfaces
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A common cap for all physical points and all finitely many detector
heights.  The positive gap between `2e` and the chosen width absorbs the
analytic losses and the remaining constant. -/
theorem exists_physicalRecipe_prime_cap
    (P : ProbeData K S) (E : RowEulerData K S P)
    (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry) (B : ℝ)
    (heightCount : ℕ) {e width tau : ℝ}
    (he : 0 ≤ e) (hgap : 2 * e < width) (htau : 0 < tau) (htau1 : tau ≤ 1) :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ d : ℝ, 1 / 16 ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
        frequencyRowNorm K S u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      ∀ h : ℕ, h ≤ heightCount → ∀ p : Fin 3 → ℝ, ‖p‖ ≤ Z ^ tau →
      rowZeroBelow K S psi {1} P E u (3 * ((h : ℝ) + 2) * Z ^ tau) (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖recipePhysicalSlots K S P E.rows omega psi g
          (physicalRecipeFamily K psi g B e) Z p i u‖ ≤
            (physicalSlotBase g.slots Z) ^ (a - 1 / 2 + width) := by
  let ell : ℝ := (1 / 6 : ℝ) / g.slots
  let rho : ℝ := (width - 2 * e) / 4
  let delta : ℝ := min (1 / 8) rho
  have hell : 0 < ell := div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  have hrho : 0 < rho := by dsimp only [rho]; linarith
  have hdelta : 0 < delta := lt_min (by norm_num) hrho
  have hdelta1 : delta ≤ 1 / 4 := (min_le_left _ _).trans (by norm_num)
  have hdeltar : delta ≤ rho := min_le_right _ _
  have hloss : ell * rho + delta * ell ≤ 2 * ell * rho := by
    have hh := mul_le_mul_of_nonneg_right hdeltar hell.le
    nlinarith
  have hwidth : 2 * e * ell + 2 * ell * rho ≤ ell * (width - rho) := by
    have hgap0 : 0 ≤ ell * (width - 2 * e) := mul_nonneg hell.le (by linarith)
    dsimp only [rho] at hgap0 ⊢
    nlinarith
  let F := physicalRecipeFamily K psi g B e
  have hlocal (h : Fin (heightCount + 1)) :=
    exists_actual_physical_primeSlot_absorbed K S P E omega psi {1}
      (Finset.mem_singleton_self 1)
      (F.presentation ⟨0, F.presentationCount_pos⟩) g (zeroIdealTest K) (zeroIdealTest K)
      e delta (ell * rho) (2 * ell * rho) tau (h.val : ℝ) width rho
      he hdelta hdelta1 (mul_pos hell hrho) hloss htau htau1
      (Nat.cast_nonneg _) hrho hwidth
  choose Zh hZh hb using hlocal
  let Z0 : ℝ := max 2 (∑ h : Fin (heightCount + 1), Zh h)
  refine ⟨Z0, le_max_left _ _, ?_⟩
  intro Z hZ d hd hd1 u hu hu1 a ha ha1 h hh p hp hbelow i
  let hfin : Fin (heightCount + 1) := ⟨h, Nat.lt_succ_of_le hh⟩
  have hZhZ : Zh hfin ≤ Z :=
    (Finset.single_le_sum (fun j _ => zero_le_one.trans (hZh j))
      (Finset.mem_univ hfin)).trans ((le_max_right _ _).trans hZ)
  have hZpos : 0 < Z := (by norm_num : (0 : ℝ) < 2).trans_le
    ((le_max_left _ _).trans hZ)
  have hbound := hb hfin Z hZhZ d hd hd1 u hu hu1 a ha ha1 p hp hbelow i
  let poly : ℂ → ℂ := fun z => primePolynomial
    (sharedMomentData K S P E.rows omega psi (F.presentation ⟨0, F.presentationCount_pos⟩)
      (compensationPrimeGeometry K g z) (fun _ => 1) u.sector
      (zeroIdealTest K) (zeroIdealTest K)) i u.ideal.val Z 0
  have hvertical : ExpansionInterfaces.Mellin.vertical (17 / 50) (p 2) =
      (17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I := by
    norm_num [ExpansionInterfaces.Mellin.vertical]
  have hslot := congrArg norm (physicalRecipeSlot_eq_compensationPrimePolynomial
    K S P E.rows omega psi g B e Z p i u)
  have hpoly := congrArg norm (congrArg poly hvertical)
  exact (hslot.le.trans (hpoly.symm.le.trans hbound)).trans_eq
    (Real.rpow_mul hZpos.le ell (a - 1 / 2 + width))

/-- A row in a moving label fiber satisfies the main-slot estimate with
that label's amplitude.  The cap is supplied uniformly on the original
fixed row set, before the finite-pattern transport. -/
theorem physicalRecipe_mainSlot_bound_on_fiber
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry) (B e : ℝ)
    {width cap Z : ℝ} (hw : 0 < width) (hc : 0 ≤ cap) (hZ : 1 < Z)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (hprime : ∀ i, ∀ u ∈ rows,
      ‖recipePhysicalSlots K S P R omega psi g
        (physicalRecipeFamily K psi g B e) Z p i u‖ ≤
          physicalSlotBase g.slots Z ^ (cap + width))
    (label : AmplitudeLabels g.slots width cap) (i : Fin g.slots)
    (u : FrequencyRow K S)
    (hu : u ∈ recipeAmplitudeRows K S P R omega psi g
      (physicalRecipeFamily K psi g B e) width cap Z rows p label) :
    ‖actualCompensationMainSlot K S P g ∅ u Z
      ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) i‖ ≤
        (primeScale g Z) ^ (-(4 / 25 : ℝ) + decodeAmplitude width cap (label i) + width) := by
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hXpos : 0 < primeScale g Z := Real.rpow_pos_of_pos hZpos _
  have hh := recipeAmplitudeRows_slot_upper K S P R omega psi g
    (physicalRecipeFamily K psi g B e) width cap Z rows p hw hc hZ hprime label i u hu
  rw [norm_actualCompensationMainSlot_eq_physicalRecipeSlot K S P R omega psi g B e Z hZpos]
  calc
    _ ≤ (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
        (primeScale g Z) ^ (decodeAmplitude width cap (label i) + width) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hXpos.le _)
      exact hh.trans_eq (Real.rpow_mul hZpos.le ((1 / 6 : ℝ) / g.slots)
        (decodeAmplitude width cap (label i) + width))
    _ = _ := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_physicalRecipe_prime_cap
#print axioms HeckeSkeleton.HighBinPhysicalNorm.physicalRecipe_mainSlot_bound_on_fiber
