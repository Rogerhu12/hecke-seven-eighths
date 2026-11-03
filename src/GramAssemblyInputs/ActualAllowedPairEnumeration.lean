import ActualAllowedGeneratorOrbitEnumeration
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
UNCOMPILED / native 0. The actual two-column choice mask is reindexed by
the existing chosen-generator orbit equivalence, with the SAME ideals
and sixth-power units. The first identity is a single product-indexed
tsum and needs no convergence premise. Finite support of the supplied
whole-column function then justifies the stated iterated ideal/unit sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedPairEnumerationDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualProbeGaussFourierDraft
open ActualGeneratorChoiceDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "E" => ExteriorIdeal K S
local notation "Γ" => sixthPowerUnits K S
local notation "SelectedPairs" => {m : NZ × NZ //
  choiceFiniteMask K w (Prod.snd (sLocalNonzeroIntegerDiagonal K S (Prod.fst m))) = 1 ∧
  choiceFiniteMask K w (Prod.snd (sLocalNonzeroIntegerDiagonal K S (Prod.snd m))) = 1}

/-- Only a shuffle and the existing actual orbit enumeration are used.
The subtype condition is precisely the two original finite choice masks. -/
def choiceIdealUnitPairEquiv : (E × E) × (Γ × Γ) ≃ SelectedPairs :=
  (Equiv.prodProdProdComm E E Γ Γ).trans
    ((choiceGeneratorPairEquiv K w).trans Equiv.subtypeProdEquivProd.symm)

@[simp] theorem choiceIdealUnitPairEquiv_apply_val (p : (E × E) × (Γ × Γ)) :
    (choiceIdealUnitPairEquiv K w p).val =
      (sIntegerOrbitTranslate K S Γ p.2.1 (probeGenerator K S w.D p.1.1),
       sIntegerOrbitTranslate K S Γ p.2.2 (probeGenerator K S w.D p.1.2)) := rfl

/-- Exact mask restriction followed by one bijection. No Fubini step or
summability of f is used in this product-indexed identity. -/
theorem tsum_choiceFiniteMask_pair_eq_idealUnitPair (f : NZ × NZ → ℂ) :
    (∑' m : NZ × NZ,
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.1).2 *
        choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.2).2 * f m) =
    ∑' p : (E × E) × (Γ × Γ), f
      (sIntegerOrbitTranslate K S Γ p.2.1 (probeGenerator K S w.D p.1.1),
       sIntegerOrbitTranslate K S Γ p.2.2 (probeGenerator K S w.D p.1.2)) := by
  have hind (m : NZ × NZ) :
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.1).2 *
          choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.2).2 * f m =
        ({n : NZ × NZ |
          choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S n.1).2 = 1 ∧
          choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S n.2).2 = 1} :
          Set (NZ × NZ)).indicator f m := by
    by_cases h₁ : choiceFiniteClassHom K w (sLocalNonzeroIntegerDiagonal K S m.1).2 ∈ w.C6
    <;> by_cases h₂ : choiceFiniteClassHom K w (sLocalNonzeroIntegerDiagonal K S m.2).2 ∈ w.C6
    <;> rw [choiceFiniteClassHom_diagonal] at h₁ h₂
    <;> simp [choiceFiniteMask, Set.indicator, h₁, h₂]
  calc
    _ = ∑' m : NZ × NZ,
        ({n : NZ × NZ |
          choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S n.1).2 = 1 ∧
          choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S n.2).2 = 1} :
          Set (NZ × NZ)).indicator f m := tsum_congr hind
    _ = ∑' m : SelectedPairs, f m.val := (tsum_subtype _ _).symm
    _ = _ := by
      simpa only [choiceIdealUnitPairEquiv_apply_val] using
        ((choiceIdealUnitPairEquiv K w).tsum_eq (fun m : SelectedPairs => f m.val)).symm

/-- Finite support of the actual whole-column function survives the
injective chosen-generator pullback, even though the ideal/unit index
types themselves need not be finite. -/
theorem summable_choiceIdealUnitPair_of_hasFiniteSupport (f : NZ × NZ → ℂ)
    (hf : Function.HasFiniteSupport f) :
    Summable (fun p : (E × E) × (Γ × Γ) => f
      (sIntegerOrbitTranslate K S Γ p.2.1 (probeGenerator K S w.D p.1.1),
       sIntegerOrbitTranslate K S Γ p.2.2 (probeGenerator K S w.D p.1.2))) := by
  have hinj : Function.Injective
      (fun p : (E × E) × (Γ × Γ) => (choiceIdealUnitPairEquiv K w p).val) :=
    Subtype.val_injective.comp (choiceIdealUnitPairEquiv K w).injective
  have hfin : Function.HasFiniteSupport
      (fun p : (E × E) × (Γ × Γ) => f (choiceIdealUnitPairEquiv K w p).val) := by
    exact (show Set.Finite (Function.support f) from hf).preimage hinj.injOn
  simpa only [choiceIdealUnitPairEquiv_apply_val] using summable_of_hasFiniteSupport hfin

/-- The iterated sum is justified by the preceding genuine summability,
as supplied by the actual annular consumer's finite-support theorem. -/
theorem tsum_choiceFiniteMask_pair_eq_idealPair_unitPair (f : NZ × NZ → ℂ)
    (hf : Function.HasFiniteSupport f) :
    (∑' m : NZ × NZ,
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.1).2 *
        choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m.2).2 * f m) =
    ∑' I : E × E, ∑' u : Γ × Γ, f
      (sIntegerOrbitTranslate K S Γ u.1 (probeGenerator K S w.D I.1),
       sIntegerOrbitTranslate K S Γ u.2 (probeGenerator K S w.D I.2)) := by
  rw [tsum_choiceFiniteMask_pair_eq_idealUnitPair]
  exact (summable_choiceIdealUnitPair_of_hasFiniteSupport K w f hf).tsum_prod

end HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedPairEnumerationDraft
