import HeckeGeneral.Characters.InfinityPacket
import HeckeGeneral.Analysis.HeckeNormTwistZeros

/-!
# Canonical removal of the global norm parameter

At one fixed infinite place the normalized radial parameter is zero. This
normalization removes a norm factor intrinsic to the packet generator as
well as one written separately in a packet presentation. Relative radial
parameters and zero real parts are unchanged; no assertion is made that all
radial parameters vanish.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeGeneral.Characters

open NumberField

variable (K : Type) [Field K] [NumberField K]

/-- A field-dependent choice, made before the target character. -/
def normNormalizationPlace : InfinitePlace K := Classical.choice inferInstance

/-- Removing the radial parameter at a fixed place is multiplicative. -/
def radialNormalization (w : InfinitePlace K) :
    HeckeCharacter K →* HeckeCharacter K where
  toFun χ := χ * heckeNormTwist K (heckeRadialParameter K w χ)
  map_one' := by simp [heckeNormTwist]
  map_mul' χ ψ := by
    rw [heckeRadialParameter_mul]
    change (χ * ψ) * normTwist (heckeLogNorm K)
        (heckeRadialParameter K w χ + heckeRadialParameter K w ψ) = _
    rw [normTwist_add]
    ac_rfl

theorem radialNormalization_apply (w : InfinitePlace K) (χ : HeckeCharacter K) :
    radialNormalization K w χ = χ * heckeNormTwist K (heckeRadialParameter K w χ) := rfl

@[simp] theorem radialParameter_radialNormalization (w : InfinitePlace K)
    (χ : HeckeCharacter K) :
    heckeRadialParameter K w (radialNormalization K w χ) = 0 := by
  rw [radialNormalization_apply, heckeRadialParameter_mul,
    heckeRadialParameter_normTwist, add_neg_cancel]

theorem radialNormalization_finiteOrder (w : InfinitePlace K)
    {χ : HeckeCharacter K} (hχ : FiniteOrder χ) : radialNormalization K w χ = χ := by
  simp [radialNormalization_apply, heckeRadialParameter_finiteOrder K w hχ,
    heckeNormTwist]

@[simp] theorem radialNormalization_normTwist (w : InfinitePlace K) (t : ℝ) :
    radialNormalization K w (heckeNormTwist K t) = 1 := by
  rw [radialNormalization_apply, heckeRadialParameter_normTwist]
  simp [heckeNormTwist]

theorem radialNormalization_mem_packet (w : InfinitePlace K)
    (ω χ : HeckeCharacter K) (hχ : χ ∈ HeckePacket K ω) :
    radialNormalization K w χ ∈ HeckePacket K ω :=
  heckePacket_mul_normTwist K ω hχ _

/-- The generator itself is normalized in the correct packet formula. -/
theorem radialNormalization_packet (w : InfinitePlace K)
    (ω θ : HeckeCharacter K) (hθ : FiniteOrder θ) (e : ℤ) (t : ℝ) :
    radialNormalization K w (θ * ω ^ e * heckeNormTwist K t) =
      θ * radialNormalization K w ω ^ e := by
  rw [map_mul, map_mul, map_zpow, radialNormalization_finiteOrder K w hθ,
    radialNormalization_normTwist, mul_one]

theorem radialNormalization_zeroRealParts (w : InfinitePlace K) (χ : HeckeCharacter K) :
    HeckeGeneral.Analysis.zeroRealParts (HeckeGeneral.Analysis.heckeContinuation K
      (radialNormalization K w χ)) =
      HeckeGeneral.Analysis.zeroRealParts (HeckeGeneral.Analysis.heckeContinuation K χ) :=
  HeckeGeneral.Analysis.zeroRealParts_heckeContinuation_normTwist K χ _

/-- On the normalized slice the only pure norm character is the identity. -/
theorem ne_normTwist_of_radial_zero (w : InfinitePlace K) (χ : HeckeCharacter K)
    (hzero : heckeRadialParameter K w χ = 0) (hne : χ ≠ 1) (t : ℝ) :
    χ ≠ heckeNormTwist K t := by
  intro h
  have ht : t = 0 := by
    rw [h, heckeRadialParameter_normTwist] at hzero
    linarith
  exact hne (by simpa [ht, heckeNormTwist] using h)

theorem radial_zero_mul_finiteOrder (w : InfinitePlace K) (χ θ : HeckeCharacter K)
    (hχ : heckeRadialParameter K w χ = 0) (hθ : FiniteOrder θ) :
    heckeRadialParameter K w (χ * θ) = 0 := by
  rw [heckeRadialParameter_mul, hχ, heckeRadialParameter_finiteOrder K w hθ, add_zero]

end HeckeGeneral.Characters

#print axioms HeckeGeneral.Characters.radialNormalization
#print axioms HeckeGeneral.Characters.radialNormalization_packet
#print axioms HeckeGeneral.Characters.radialNormalization_zeroRealParts
#print axioms HeckeGeneral.Characters.ne_normTwist_of_radial_zero
