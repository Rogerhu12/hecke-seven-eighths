import Expansion.PhysicalRecipeAssembly

/-!
# One parameter choice before the analytic components and power height

The internal width, finite alphabet and buffered height count are chosen
from the actual detector theorem. The shell loss remains lam, while a
separately prescribed positive cap controls the width for the other error
terms. The same choice is used for every scale, height and component.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (ω ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
variable (E : RowEulerData K S P)
variable {B : ℝ} (hψ : ψ ∈ HeckePacket K ω)
variable (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1)
variable (hbound : ∀ χ r, r ∈ heckePacketZeros K ω χ →
  1 / 2 ≤ r → r ≤ 1 → r ≤ B)
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]
variable (windowCharacters : Finset (HeckeCharacter K))

structure PhysicalRecipeParameters (lam ζ eCap : ℝ) where
  e : ℝ
  width : ℝ
  ceiling : ℝ
  k : ℝ
  e_pos : 0 < e
  width_pos : 0 < width
  e_small : e < 1 / 1000
  e_lam : e ≤ lam / 1000
  e_cap : e ≤ eCap
  ceiling_pos : 0 < ceiling
  k_pos : 0 < k
  source : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      PhysicalRecipeSourceAtScale K S P ω ψ g E hψ hB0 hB e_pos hbound
        μ windowCharacters lam ζ width k width_pos Z (Z ^ τ)

theorem physicalRecipeParameters_nonempty
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam ζ eCap : ℝ) (hlam : 0 < lam) (hlamSmall : lam < 1 / 48)
    (hζ : ζ ≤ lam) (heCap : 0 < eCap) :
    Nonempty (PhysicalRecipeParameters K S P ω ψ g E hψ hB0 hB hbound
      μ windowCharacters lam ζ eCap) := by
  obtain ⟨e, width, ceiling, k, he, hw, heSmall, heLam, heCap', hc, hk, hsource⟩ :=
    exists_physical_recipe_parameters K S P ω ψ g E hψ hB0 hB hbound
      μ windowCharacters hcomplex lam ζ hlam hlamSmall hζ eCap heCap
  exact ⟨⟨e, width, ceiling, k, he, hw, heSmall, heLam, heCap', hc, hk, hsource⟩⟩

def choosePhysicalRecipeParameters
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam ζ eCap : ℝ) (hlam : 0 < lam) (hlamSmall : lam < 1 / 48)
    (hζ : ζ ≤ lam) (heCap : 0 < eCap) :
    PhysicalRecipeParameters K S P ω ψ g E hψ hB0 hB hbound
      μ windowCharacters lam ζ eCap :=
  Classical.choice (physicalRecipeParameters_nonempty K S P ω ψ g E hψ hB0 hB hbound
    μ windowCharacters hcomplex lam ζ eCap hlam hlamSmall hζ heCap)

end Expansion.Project

#print axioms Expansion.Project.physicalRecipeParameters_nonempty
#print axioms Expansion.Project.choosePhysicalRecipeParameters
