import ThetaGlobal.GlobalEmbedding
import HeckeAxiom.ArithmeticChoice
import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalCoverAlgebra

/-!
# Same-choice arithmetic adapter for the KP coefficient convention

This file repairs the ordering issue in the original `Base.complexEmbedding`:
the primitive root is aligned first, then the existing arithmetic constructor
is called once.  No second enlargement or replacement generator context is
used to establish root alignment.

This is a project-facing module.  Its upstream dependency closure is not
included in the supplied attachment; see the compilation-status report.
-/

noncomputable section

namespace ThetaGlobal.GlobalProjectEmbedding

open NumberField IsDedekindDomain
open DedekindZetaZeroFree
open GlobalEmbedding

variable {F : Type} [Field F] [NumberField F]

/-- Any embedding sending the prescribed twelfth root to the canonical
one agrees with KP on every sixth root, including KP's chosen exponent. -/
theorem coefficientEmbedding_eq_of_root12
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (σ : F →+* ℂ)
    (hσ : σ ζ = canonicalTwelfthRoot) (z : rootsOfUnity 6 F) :
    σ ((z : Fˣ) : F) = (KPLocalCover.coefficientEmbedding F ζ hζ z : ℂ) := by
  have hz : (ζ ^ 2) ^ KPLocalCover.sixthExponent F ζ hζ z = ((z : Fˣ) : F) :=
    (Classical.choose_spec (KPLocalCover.exists_sixthExponent F ζ hζ z)).2
  have hσ6 : σ (ζ ^ 2) = (KPLocalCover.complexSixthGenerator : ℂ) := by
    rw [map_pow, hσ, canonicalTwelfthRoot_sq]
    rfl
  change σ ((z : Fˣ) : F) =
    ((KPLocalCover.complexSixthGenerator ^
      KPLocalCover.sixthExponent F ζ hζ z : ℂˣ) : ℂ)
  rw [Units.val_pow_eq_pow_val, ← hz, map_pow, hσ6]

theorem alignedEmbedding_coefficientEmbedding
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (z : rootsOfUnity 6 F) :
    alignedEmbedding ζ hζ ((z : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F ζ hζ z : ℂ) :=
  coefficientEmbedding_eq_of_root12 ζ hζ (alignedEmbedding ζ hζ)
    (alignedEmbedding_root12 ζ hζ) z

/-- The final set, character and generator context are selected only once,
for the already aligned embedding. -/
def alignedArithmeticChoice
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    HeckeAxiom.ArithmeticChoice F S₀ ζ (alignedEmbedding ζ hζ) :=
  Classical.choice
    (HeckeAxiom.exists_arithmeticChoice F S₀ ζ hζ (alignedEmbedding ζ hζ))

section AnyChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))}
  {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  (X : HeckeAxiom.ArithmeticChoice F S₀ ζ (alignedEmbedding ζ hζ))

theorem choice_root12 :
    alignedEmbedding ζ hζ X.A.zeta12 = canonicalTwelfthRoot := by
  rw [X.root, alignedEmbedding_root12]

/-- Alignment is obtained for the chosen context's own root and primitive
root proof.  No identification of independent arithmetic choices occurs. -/
theorem choice_coefficientEmbedding (z : rootsOfUnity 6 F) :
    alignedEmbedding ζ hζ ((z : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F X.A.zeta12 X.A.primitive_zeta12 z : ℂ) :=
  coefficientEmbedding_eq_of_root12 X.A.zeta12 X.A.primitive_zeta12
    (alignedEmbedding ζ hζ) (choice_root12 X) z

theorem thetaData_embedding :
    X.thetaData.embedding = alignedEmbedding ζ hζ := rfl

theorem thetaData_root12 : X.thetaData.root12 = ζ := X.thetaData_root12

theorem thetaData_embedding_root12 :
    X.thetaData.embedding X.thetaData.root12 = canonicalTwelfthRoot := by
  rw [thetaData_embedding, thetaData_root12, alignedEmbedding_root12]

theorem thetaData_coefficientEmbedding (z : rootsOfUnity 6 F) :
    X.thetaData.embedding ((z : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F X.A.zeta12 X.A.primitive_zeta12 z : ℂ) :=
  choice_coefficientEmbedding X z

end AnyChoice

end ThetaGlobal.GlobalProjectEmbedding
