import HeckeAxiom.SeriesBridge
import DedekindZetaZeroFree.HeckeCorollary

/-!
# The 31/32 zero-free region for finite-order Hecke characters

AxiomMath's `heckeL_ne_zero`, applied to the ray class character of an actual
finite-order Hecke character, is transported to `heckeContinuation` by
`HeckeAxiom.zeroFree_of_rayOutput`. Norm twists are removed by the existing
vertical-shift theorem.
-/

noncomputable section

namespace HeckeAxiom

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis

variable (K : Type) [Field K] [NumberField K]

/-- **Finite-order Hecke characters have no zeros in `Re s > 31/32`.** -/
theorem finiteOrder_heckeContinuation_zeroFree (χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane (31 / 32)) := by
  obtain ⟨f, hfd, hfent, hfsum, hfnz⟩ := DedekindZetaZeroFree.heckeL_ne_zero K
    (conductorIdeal K χ) (conductorIdeal_ne_bot K χ) (toRayClassCharacter K χ hχ)
  exact zeroFree_of_rayOutput K χ hχ f hfd hfent hfsum hfnz

/-- The same region for every finite-order character twisted by a norm character. -/
theorem finiteOrder_normTwist_heckeContinuation_zeroFree (ψ : HeckeCharacter K)
    (hψ : FiniteOrder ψ) (t : ℝ) :
    MeromorphicZeroFreeOn (heckeContinuation K (ψ * heckeNormTwist K t))
      (rightHalfPlane (31 / 32)) :=
  (heckeContinuation_normTwist_zeroFreeOn_iff K ψ t (31 / 32)).mpr
    (finiteOrder_heckeContinuation_zeroFree K ψ hψ)

end HeckeAxiom
