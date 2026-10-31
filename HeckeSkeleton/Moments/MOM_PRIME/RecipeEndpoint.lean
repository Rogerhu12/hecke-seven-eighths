import HeckeSkeleton.ExpansionModels.SourceData
import HeckeSkeleton.Moments.MOM_PRIME.AbsoluteBounds
import HeckeSkeleton.Moments.MOM_PRIME.TwistedWindows

/-!
# The prime endpoint for the same actual source recipe

The source's moment models are evaluated at their original physical point,
with their original selected slots, common masks and dyadic row enumeration.
The row exponent is `rho(U)`, with `U ^ rho(U) = 2 * U`.  The fixed factor
two is included in the bound constant; the physical exponent is `1 + z`.

The generic theorem uses only an upper bound on the real parts of the
recipe's actual prime-window powers.  It has height degree zero and does
not require an additional profile or energy premise.  The separate actual
specialization proves the real-part bound for the concrete detector.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local instance recipePrimeSectorFintype :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

variable
  (R : RecipeExpansion K (places K c) (targetCharacter K c)
    c.geometry (expansionShellAllowance K c))
  {Z T : ℝ}
  (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
  (s : SixthUnitClasses K (places K c))

/-- Restricting the actual recipe retains exactly the selected slots. -/
@[simp] theorem recipePairedModel_slotCount :
    (pairedModelFor (recipeMomentModels K c R) i s).geometry.slotCount =
      i.selected.card := rfl

theorem recipePairedModel_slotCount_le :
    (pairedModelFor (recipeMomentModels K c R) i s).geometry.slotCount ≤
      c.geometry.slots := by
  rw [recipePairedModel_slotCount]
  simpa only [Fintype.card_fin] using Finset.card_le_univ i.selected

/-- Physical freezing does not change the original shell-rescaled length. -/
theorem recipePairedModel_slot_length
    (j : Fin (pairedModelFor (recipeMomentModels K c R) i s).geometry.slotCount) :
    ((pairedModelFor (recipeMomentModels K c R) i s).geometry.slots j).length =
      HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots
        (momentBlockFor i).shell := by
  change ((1 / 6 : ℝ) / c.geometry.slots) / (momentBlockFor i).shell =
    (1 / 6 : ℝ) / (c.geometry.slots * (momentBlockFor i).shell)
  rw [div_div]

theorem recipePairedModel_totalLength :
    (pairedModelFor (recipeMomentModels K c R) i s).geometry.totalLength =
      selectedLengthFor i := by
  calc
    _ = ∑ _j : Fin i.selected.card,
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots
          (momentBlockFor i).shell := by
      unfold SlotGeometry.totalLength
      apply Finset.sum_congr rfl
      intro j _
      exact recipePairedModel_slot_length K c R i s j
    _ = ∑ _j ∈ i.selected,
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots
          (momentBlockFor i).shell :=
      selectedSlots_sum i.selected (fun _ =>
        HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots
          (momentBlockFor i).shell)
    _ = _ := rfl

/-- Every frozen physical prime window keeps the original annular support. -/
theorem recipePairedModel_prime_annular
    (j : Fin (pairedModelFor (recipeMomentModels K c R) i s).geometry.slotCount)
    (t : ℝ) :
    Function.support
        (((pairedModelFor (recipeMomentModels K c R) i s).geometry.slots j).profile t) ⊆
      Ioo (1 : ℝ) 2 := by
  let p := recipePhysicalPoint ((recipeMomentModels K c R).heights Z T i)
  let k := selectedSlotIndex i.selected j
  change Function.support
    (((analyticMomentPrimeWindow K c.geometry k).freezeTwist
      (R.family.slotTime k p) (R.family.slotPower k p)).profile t) ⊆ Ioo (1 : ℝ) 2
  exact primeWindow_freezeTwist_annular
    (analyticMomentPrimeWindow K c.geometry k) (R.family.slotTime k p)
    (R.family.slotPower k p) (c.geometry.support_annular k) t

variable {Z T i s}

/-- A single constant works for all source indices, sectors, selected
subproducts, external scales and physical heights of the fixed recipe. -/
theorem exists_recipePairedModel_prime_profile_bound (L : ℝ)
    (hpower : ∀ (j : Fin c.geometry.slots) (p : Fin 3 → ℝ),
      (R.family.slotPower j p).re ≤ L) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Z T : ℝ)
        (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
        (s : SixthUnitClasses K (places K c))
        (j : Fin (pairedModelFor (recipeMomentModels K c R) i s).geometry.slotCount)
        (t y : ℝ),
        ‖((pairedModelFor (recipeMomentModels K c R) i s).geometry.slots j).profile t y‖ ≤
          B := by
  obtain ⟨B, hB, hbound⟩ := exists_actualFrozenPrimeGeometry_profile_bound K c.geometry L
  refine ⟨B, hB, ?_⟩
  intro Z T i s j t y
  let p := recipePhysicalPoint ((recipeMomentModels K c R).heights Z T i)
  exact hbound (fun k => R.family.slotTime k p) (fun k => R.family.slotPower k p)
    (fun k => hpower k p) (selectedSlotIndex i.selected j) t y

/-- The exact physical exponent, including the zero-slot branch.  The
entire original paired row sum and the complete sector sum are retained.
No eligibility, capacity, profile-bound or prime-cancellation estimate is
assumed: only the real parts of the actual recipe powers are bounded. -/
theorem exists_recipePairedPrimeAbsoluteBound (L : ℝ)
    (hpower : ∀ (j : Fin c.geometry.slots) (p : Fin 3 → ℝ),
      (R.family.slotPower j p).re ≤ L) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Z T : ℝ)
        (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T),
        (∑ s : SixthUnitClasses K (places K c),
          ∑ u ∈ pairedRows (pairedModelFor (recipeMomentModels K c R) i s)
            (pairedParametersFor i) (momentBaseFor i),
            ‖slotProduct (pairedModelFor (recipeMomentModels K c R) i s)
              u (momentBaseFor i) 0‖ ^ 2) ≤
          C * momentBaseFor i ^ (1 + selectedLengthFor i) := by
  obtain ⟨B, hB, hprofiles⟩ :=
    exists_recipePairedModel_prime_profile_bound K c R L hpower
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_pairedPrimeAbsoluteBound_fixed K c.geometry.slots B hB.le
  refine ⟨((Fintype.card (SixthUnitClasses K (places K c)) : ℝ) + 1) * (2 * C₀),
    by positivity, ?_⟩
  intro Z T i
  have hU : 1 ≤ momentBaseFor i :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (recipeMomentBase_ge_two i)
  have hU0 : 0 < momentBaseFor i := zero_lt_one.trans_le hU
  have hwidth : (pairedParametersFor i).m + (pairedParametersFor i).q =
      rowWidthFor i := by
    change rowWidthFor i + 0 = rowWidthFor i
    exact add_zero _
  have hw : 0 ≤ (pairedParametersFor i).m + (pairedParametersFor i).q := by
    rw [hwidth]
    exact zero_le_one.trans (recipeMoment_rowWidth_spec i).1.le
  have hs (s : SixthUnitClasses K (places K c)) :
      (∑ u ∈ pairedRows (pairedModelFor (recipeMomentModels K c R) i s)
        (pairedParametersFor i) (momentBaseFor i),
        ‖slotProduct (pairedModelFor (recipeMomentModels K c R) i s)
          u (momentBaseFor i) 0‖ ^ 2) ≤
      (2 * C₀) * momentBaseFor i ^ (1 + selectedLengthFor i) := by
    have h := hbound (pairedModelFor (recipeMomentModels K c R) i s)
      (pairedParametersFor i) (momentBaseFor i) 0 hU hw
      (recipePairedModel_slotCount_le K c R i s)
      (fun j => recipePairedModel_prime_annular K c R i s j 0)
      (fun j y => hprofiles Z T i s j 0 y)
    rw [hwidth, recipePairedModel_totalLength K c R i s] at h
    calc
      _ ≤ C₀ * momentBaseFor i ^ (rowWidthFor i + selectedLengthFor i) := h
      _ = (2 * C₀) * momentBaseFor i ^ (1 + selectedLengthFor i) := by
        rw [Real.rpow_add hU0 (rowWidthFor i) (selectedLengthFor i),
          Real.rpow_add hU0 1 (selectedLengthFor i), Real.rpow_one,
          (recipeMoment_rowWidth_spec i).2.2]
        ring
  calc
    _ ≤ ∑ _s : SixthUnitClasses K (places K c),
        (2 * C₀) * momentBaseFor i ^ (1 + selectedLengthFor i) :=
      Finset.sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card (SixthUnitClasses K (places K c)) : ℝ) * (2 * C₀) *
        momentBaseFor i ^ (1 + selectedLengthFor i) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card (SixthUnitClasses K (places K c)) : ℝ) + 1) * (2 * C₀) *
        momentBaseFor i ^ (1 + selectedLengthFor i) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
        (Real.rpow_nonneg hU0.le _)

/-- The canonical shared-source endpoint in the original quantifier order.
Height order zero, ceiling one and threshold one work before every source
index; the source's existing positive loss only enlarges this bound. -/
theorem recipe_paired_primes_endpoint (L : ℝ)
    (hpower : ∀ (j : Fin c.geometry.slots) (p : Fin 3 → ℝ),
      (R.family.slotPower j p).re ≤ L) :
    PairedPrimeProductBoundFor (recipeMomentModels K c R) 1 := by
  obtain ⟨C, hC, hbound⟩ := exists_recipePairedPrimeAbsoluteBound K c R L hpower
  refine ⟨0, 1, le_rfl, zero_lt_one, ?_⟩
  intro τ _hτ _hτc
  refine ⟨1, C, le_rfl, hC.le, ?_⟩
  intro Z _hZ i _hbin _hcap
  have hU : 1 ≤ momentBaseFor i :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (recipeMomentBase_ge_two i)
  have h := (hbound Z (Z ^ τ) i).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU
        (by linarith [c.family.lamA_pos] :
          1 + selectedLengthFor i ≤ 1 + selectedLengthFor i + c.family.lamA)) hC.le)
  simpa only [one_mul, Real.rpow_zero, mul_one] using h

end HeckeSkeleton.Moments.MOM_PRIME

#print axioms HeckeSkeleton.Moments.MOM_PRIME.recipePairedModel_totalLength
#print axioms HeckeSkeleton.Moments.MOM_PRIME.recipePairedModel_prime_annular
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_recipePairedModel_prime_profile_bound
#print axioms HeckeSkeleton.Moments.MOM_PRIME.exists_recipePairedPrimeAbsoluteBound
#print axioms HeckeSkeleton.Moments.MOM_PRIME.recipe_paired_primes_endpoint
