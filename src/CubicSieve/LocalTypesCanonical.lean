import CubicSieve.LocalTypes

set_option autoImplicit false
noncomputable section
namespace CubicSieve.LocalTypes

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.Detector
open scoped NumberField

variable {K : Type} [Field K] [NumberField K]

theorem cover_of_idelic_cube (A : SArithmeticData K) (hc : NumberField.IsTotallyComplex K)
    (ω : PrimitiveFrequencyCharacter K)
    (hω : ∀ c : _root_.IdeleClassGroup K,
      RayClassBridge.ideleClassCharacter K hc ω.conductor ω.conductor_ne_zero
        ω.character c ^ 3 = 1) :
    ∃ σ ∈ typeSet A, HasFixedFullSLocalTuple K A ω σ := by
  let δ := fun v : {v // v ∈ A.Sf} =>
    Conductor.canonicalFrequencyLocalCharacter K hc ω v.val
  apply cover_of_cubic_local_components A ω δ
  · intro v x
    exact hω (_root_.IdeleGroup.finitePlaceIdeleClass v.val x)
  · intro v
    exact Conductor.LocalTwistSteps.idelic_restriction_is_raw_local_component
      K hc ω v.val (δ v) (fun _ => rfl)

end CubicSieve.LocalTypes
