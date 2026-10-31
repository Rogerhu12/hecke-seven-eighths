import HeckeSkeleton.HighBinSupport.ActualPhysicalConductorProduct
import Expansion.ActualCompensationSlotIdentity
import Expansion.PhysicalRecipeSchedule

/-!
# Physical main-slot amplitudes bound the complete correction

The source's main prime polynomial is retained exactly.  The regular and
valuation-one errors cost a small row-norm power, while the repeated-prime
mass remains explicit until `fullSlot_product_of_physical_bounds` absorbs
it against the conductor radical.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open Expansion.Project ExpansionInterfaces
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Exact identification of the original physical slot with the shared
polynomial in the compensation identity.  No row mask is removed here. -/
theorem physicalRecipeSlot_eq_compensationPrimePolynomial
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry) (B e Z : ℝ)
    (p : Fin 3 → ℝ) (i : Fin g.slots) (u : FrequencyRow K S) :
    recipePhysicalSlots K S P R omega psi g (physicalRecipeFamily K psi g B e) Z p i u =
      primePolynomial
        (sharedMomentData K S P R omega psi
          ((physicalRecipeFamily K psi g B e).presentation
            ⟨0, (physicalRecipeFamily K psi g B e).presentationCount_pos⟩)
          (compensationPrimeGeometry K g
            ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I))
          (fun _ => 1) u.sector
          (zeroIdealTest K) (zeroIdealTest K)) i u.ideal.val Z 0 := by
  rfl

/-- The physical square-root normalization contributes exactly `P^(-4/25)`
on the actual line.  The label therefore measures the unchanged main
polynomial, rather than a newly selected complete-slot amplitude. -/
theorem norm_actualCompensationMainSlot_eq_physicalRecipeSlot
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry) (B e Z : ℝ)
    (hZ : 0 < Z) (p : Fin 3 → ℝ) (i : Fin g.slots) (u : FrequencyRow K S) :
    ‖actualCompensationMainSlot K S P g ∅ u Z
        ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) i‖ =
      (primeScale g Z) ^ (-(4 / 25 : ℝ)) *
        ‖recipePhysicalSlots K S P R omega psi g
          (physicalRecipeFamily K psi g B e) Z p i u‖ := by
  rw [physicalRecipeSlot_eq_compensationPrimePolynomial]
  have h := norm_actualCompensationMainSlot_eq_shared_primePolynomial
    K S P R omega psi ((physicalRecipeFamily K psi g B e).presentation
      ⟨0, (physicalRecipeFamily K psi g B e).presentationCount_pos⟩) g
      (zeroIdealTest K) (zeroIdealTest K)
      u Z hZ ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) i
  norm_num at h ⊢
  exact h

/-- A common constant for every original full slot.  The only pointwise
input is a bound for the main prime polynomial; the actual local tables
supply all three error classes. -/
theorem exists_actualFullSlot_bound_of_main
    (g : PrimeWindowGeometry) {e eta : ℝ}
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K),
      ThetaCalibrationInput K S P.arithmetic P.Lambda P.G →
      (∀ p : ExteriorPrime K S, UnramifiedAt K psi p.val) →
      ∀ (ray : Finset (HeckeCharacter K)) (u : FrequencyRow K S)
        (a width : ℝ), 51 / 100 ≤ a → a ≤ 1 → 0 ≤ width →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
      ∀ (i : Fin g.slots) (amplitude : ℝ), 0 ≤ amplitude →
        ‖actualCompensationMainSlot K S P g ray u Z z i‖ ≤
          (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude + width) →
        ‖actualFullCorrectionSlot K S P psi g ray u Z s w z i‖ ≤
          C * frequencyRowNorm K S u ^ eta *
            (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude + (width + eta)) *
              (1 + repeatedSlotMass K S u g ray Z (a - 1 / 2 + 6 * e) i) := by
  obtain ⟨CR, ZR, hCR, hZR, hregular⟩ := exists_actualRegularErrorSlot_bound K S g he he1 heta
  obtain ⟨CV, ZV, hCV, hZV, hvaluation⟩ := exists_actualValuationOneSlot_bound K S g he he1 heta
  obtain ⟨CQ, ZQ, hCQ, hZQ, hrepeated⟩ := exists_actualRepeatedSlot_bound K S g he he1
  let C := 1 + CR + CV + CQ
  refine ⟨C, max ZR (max ZV ZQ), by dsimp only [C]; positivity,
    hZR.trans (le_max_left _ _), ?_⟩
  intro Z hZ P psi hcal hpsi ray u a width ha ha1 hwidth s w z hs hw hz i amplitude
    hamp hmain
  have hZZR : ZR ≤ Z := (le_max_left _ _).trans hZ
  have hZZV : ZV ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZQ : ZQ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 ≤ Z := hZR.trans hZZR
  have hX1 : 1 ≤ primeScale g Z :=
    Real.one_le_rpow hZ1 (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hX0 : 0 < primeScale g Z := zero_lt_one.trans_le hX1
  have hNu : 1 ≤ frequencyRowNorm K S u := one_le_idealNorm K u.ideal.val
  have hNeta : 1 ≤ frequencyRowNorm K S u ^ eta := Real.one_le_rpow hNu heta.le
  let W := frequencyRowNorm K S u ^ eta *
    (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude + (width + eta))
  let M := repeatedSlotMass K S u g ray Z (a - 1 / 2 + 6 * e) i
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hM : 0 ≤ M := repeatedSlotMass_nonneg K S u g ray Z _ i
  have hp0 : (primeScale g Z) ^ (-(4 / 25 : ℝ)) ≤ W := by
    apply (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hX0.le _) hNeta
  have hpeta : (primeScale g Z) ^ (-(4 / 25 : ℝ) + eta) ≤ W := by
    apply (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hX0.le _) hNeta
  have hmain' : ‖actualCompensationMainSlot K S P g ray u Z z i‖ ≤ W := by
    apply hmain.trans
    apply (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hX0.le _) hNeta
  have hreg : ‖actualRegularErrorSlot K S P psi g ray u Z s w z i‖ ≤ CR * W :=
    (hregular Z hZZR P psi hpsi ray u a ha ha1 s w z hs hw hz i).trans
      (mul_le_mul_of_nonneg_left hpeta hCR.le)
  have hval : ‖actualValuationOneSlot K S P psi g ray u Z s w z i‖ ≤ CV * W := by
    apply (hvaluation Z hZZV P psi hcal ray u a ha ha1 s w z hs hw hz i).trans
    dsimp only [W]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCV.le
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith))
      (Real.rpow_nonneg (zero_le_one.trans hNu) _)
  have hrep : ‖actualRepeatedSlot K S P psi g ray u Z s w z i‖ ≤ CQ * W * M := by
    apply (hrepeated Z hZZQ P psi hcal ray u a ha ha1 s w z hs hw hz i).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp0 hCQ.le) hM
  have htriangle : ‖actualFullCorrectionSlot K S P psi g ray u Z s w z i‖ ≤
      W + CR * W + CV * W + CQ * W * M := by
    rw [actualFullCorrectionSlot_decomposition]
    exact (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (by simpa only [norm_neg] using hmain') hreg)) hval)) hrep)
  apply htriangle.trans
  change _ ≤ C * W * (1 + M)
  have h1 : 1 + CR + CV ≤ C := by dsimp only [C]; linarith
  have h2 : CQ ≤ C := by dsimp only [C]; linarith
  calc
    _ = (1 + CR + CV) * W + CQ * (W * M) := by ring
    _ ≤ C * W + C * (W * M) := add_le_add
      (mul_le_mul_of_nonneg_right h1 hW)
      (mul_le_mul_of_nonneg_right h2 (mul_nonneg hW hM))
    _ = _ := by ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.norm_actualCompensationMainSlot_eq_physicalRecipeSlot
#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_actualFullSlot_bound_of_main
