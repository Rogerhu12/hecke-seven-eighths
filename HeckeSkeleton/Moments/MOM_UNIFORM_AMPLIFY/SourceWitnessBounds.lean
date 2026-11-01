import Expansion.PhysicalRecipeAssembly
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceGeometry

/-!
# Inverse lengths in the selected physical source

A successful physical source selection contains the original `BlockSource`,
which bounds every live-bin subdivision by `t + lam`.  At earlier scales the
default amplitude has inverse length exactly `t`.  Consequently the same
bound holds throughout the all-scale source on every live bin, including
empty fibers and copied padding labels.  No eventual source assumption or
uniform moment estimate is required.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)
variable (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)

/-- The selected physical source and its default branch have the same
bounded inverse-length range on every live bin. -/
theorem physicalSourceOrDefault_witness_lengths
    (F : RecipeFamily K ψ g) (width Z T d a B lam k : ℝ)
    (hw : 0 < width) (hcap : (2 * a - 1) / 2 ≤ 1 / 2)
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S) (value : ℂ)
    (hlam : 0 ≤ lam) :
    let b := physicalSourceOrDefault K S P R ω ψ g F width Z T d a B lam k
      hw hcap rows sector value
    51 / 100 < b.bin → ∀ l, ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
      ∀ j : Fin ((b.amplitude l).witnessCount t),
        0 ≤ ((b.amplitude l).witness t j).inverseLength ∧
          ((b.amplitude l).witness t j).inverseLength ≤ 3 / 2 + lam := by
  dsimp only
  by_cases hex : ∃ b, PhysicalRecipeBlockSource K S P R ω ψ g F width Z T d a B lam k
    hw hcap rows sector value b
  · intro hbin l t ht ht' j
    have hsource := (physicalSourceOrDefault_source K S P R ω ψ g F
      width Z T d a B lam k hw hcap rows sector value hex).2.2.1
    have hlength := blockSource_witness_lengths hsource hbin l t ht ht' j
    exact ⟨hlength.1, hlength.2.1⟩
  · simp only [physicalSourceOrDefault, dif_neg hex]
    intro _hbin l t ht ht' j
    change 0 ≤ t ∧ t ≤ 3 / 2 + lam
    exact ⟨zero_le_one.trans ht, by linarith⟩

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.physicalSourceOrDefault_witness_lengths
