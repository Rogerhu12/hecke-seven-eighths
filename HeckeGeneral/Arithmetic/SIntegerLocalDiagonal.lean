import HeckeGeneral.Arithmetic.SIntegerOrbits
import HeckeGeneral.Arithmetic.SLocalNormSection

/-!
# Actual nonzero S-integers in the local multiplicative group

The local diagonal is defined on all nonzero field elements, not just
global S-units. This supplies the base points of all ideal sectors in
orbital integrals. Its restriction to S-units is the existing diagonal.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The genuine local diagonal of an arbitrary nonzero field element. -/
def sLocalFieldUnitDiagonal : Kˣ →* sLocalMultiplicativeGroup K S where
  toFun u :=
    (Units.map (mixedEmbedding K).toMonoidHom u,
      fun v => Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom u)
  map_one' := by ext <;> simp
  map_mul' u w := by ext <;> simp

@[simp] theorem sLocalFieldUnitDiagonal_sUnit (u : S.unit K) :
    sLocalFieldUnitDiagonal K S (u : Kˣ) = sLocalDiagonal K S u := rfl

theorem sLocalFieldUnitDiagonal_injective :
    Function.Injective (sLocalFieldUnitDiagonal K S) := by
  intro u w huw
  apply Units.ext
  apply mixedEmbedding_injective K
  exact congrArg (fun p : sLocalMultiplicativeGroup K S =>
    (p.1 : mixedEmbedding.mixedSpace K)) huw

/-- The actual field unit represented by a nonzero S-integer. -/
def nonzeroSIntegerFieldUnit (a : NonzeroRingElements (S.integer K)) : Kˣ :=
  Units.mk0 (a.val : K) (by
    intro ha
    exact a.property (Subtype.ext ha))

@[simp] theorem nonzeroSIntegerFieldUnit_val
    (a : NonzeroRingElements (S.integer K)) :
    (nonzeroSIntegerFieldUnit K S a : K) = (a.val : K) := rfl

theorem nonzeroSIntegerFieldUnit_injective :
    Function.Injective (nonzeroSIntegerFieldUnit K S) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : Kˣ => (u : K)) hab

def sLocalNonzeroIntegerDiagonal (a : NonzeroRingElements (S.integer K)) :
    sLocalMultiplicativeGroup K S :=
  sLocalFieldUnitDiagonal K S (nonzeroSIntegerFieldUnit K S a)

theorem sLocalNonzeroIntegerDiagonal_injective :
    Function.Injective (sLocalNonzeroIntegerDiagonal K S) :=
  (sLocalFieldUnitDiagonal_injective K S).comp (nonzeroSIntegerFieldUnit_injective K S)

end HeckeGeneral.Arithmetic
