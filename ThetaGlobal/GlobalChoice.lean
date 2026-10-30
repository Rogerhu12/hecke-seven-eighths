import ThetaGlobal.GlobalProjectEmbedding
import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation
import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

/-!
# A single aligned arithmetic choice with its trivial modulus retained

The original arithmetic existence proof starts with modulus `⊤` and never
changes the modulus, but its public existential statement forgets that fact.
The strengthening below retains it.  This supplies the principal Hecke data
required by the existing `ActualRecipe` interface without introducing a new
global analytic assumption or making a second arithmetic choice.

Project-facing source: see the report for the separate compilation boundary.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalChoice

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

private theorem principal_cast {m n : Ideal (𝓞 F)} (h : m = n)
    (η : RayClassCharacter F n) (hη : η.IsPrincipal) :
    (h.symm ▸ η : RayClassCharacter F m).IsPrincipal := by
  subst h
  exact hη

/-- The same construction as `HeckeAxiom.exists_arithmeticChoice`, with
the preserved modulus included in the conclusion. -/
theorem exists_arithmeticChoice_top
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ) :
    ∃ X : HeckeAxiom.ArithmeticChoice F S₀ ζ σ, X.A.modulus = ⊤ := by
  obtain ⟨T, hT₀, hT⟩ := exists_finiteS_localDifferentExponent_eq_zero F S₀
  obtain ⟨S, hST, hroot, hmod, -, -⟩ := SArithmeticData.exists_generalArithmeticContext F T
    ⊤ top_ne_bot ζ hζ σ (AbelianQuotient.trivialRayCharacter F)
  have hη := principal_cast hmod _
    (HeckeAxiom.trivialRayCharacter_isPrincipal (F := F))
  obtain ⟨A, hsub, hrootA, hmodA, hS, hdiff, C, hC⟩ :=
    PrincipalProbeConstruction.exists_enlarged_principal_context S σ _ hη
  have hTA : T ⊆ A.Sf := fun v hv => hsub (S.bad_subset (hST ▸ hv))
  refine ⟨{
    A := A
    initial := hT₀.trans hTA
    root := hrootA.trans hroot
    hS := hS
    η := _
    principal := principal_cast hmodA _ hη
    C := C
    principalIdele := hC
    containsDifferent := hdiff
    different := HeckeAxiom.different_outside_of_subset A hT hTA }, ?_⟩
  exact hmodA.trans hmod

/-- Align first and then choose `A,C` once. -/
def alignedChoice (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    HeckeAxiom.ArithmeticChoice F S₀ ζ (GlobalEmbedding.alignedEmbedding ζ hζ) :=
  Classical.choose (exists_arithmeticChoice_top S₀ ζ hζ
    (GlobalEmbedding.alignedEmbedding ζ hζ))

theorem alignedChoice_modulus (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    (alignedChoice S₀ ζ hζ).A.modulus = ⊤ :=
  Classical.choose_spec (exists_arithmeticChoice_top S₀ ζ hζ
    (GlobalEmbedding.alignedEmbedding ζ hζ))

theorem primitive_of_modulus_top {m : Ideal (𝓞 F)}
    (η : RayClassCharacter F m) (hm : m = ⊤) : η.IsPrimitive := by
  subst m
  intro f hf
  exact absurd hf (not_lt_of_ge le_top)

/-- The global Hecke datum is obtained from the already proved principal
functional equation; it is not a new hypothesis in the theta construction. -/
def continuation {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
    {ζ : F} {σ : F →+* ℂ}
    (X : HeckeAxiom.ArithmeticChoice F S₀ ζ σ) (hmod : X.A.modulus = ⊤) :
    PrincipalRayHeckeData F X.A.modulus X.η :=
  principalRayHeckeData F
    (primitive12_totallyComplex F X.A.zeta12 X.A.primitive_zeta12)
    X.A.modulus X.A.modulus_ne_zero X.η
    (primitive_of_modulus_top X.η hmod) X.principal

end ThetaGlobal.GlobalChoice
