import HeckeSkeleton.LowEnergy.ClassSlices
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
# Literal local-frequency classes of the reflected coefficient

`frequencyClass` is a product of four moving classes and three frozen
classes.  The frozen product is displayed explicitly.  The generic four-class
identity therefore applies to the actual reflected Mellin kernel.  This
avoids a coupled indicator for the product class.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualClassSlices
open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ClassSlices
open scoped BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- These three classes are fixed before a row/mark/dual-column block is formed. -/
def frozenFrequencyClass (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    SixthLocalClasses K S :=
  unitLocalClass K S (frequencyUnit K S d i) *
    generatorLocalClass K S D i.numeratorFrozen *
    generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ)

/-- The four moving coordinates in the actual frequency-class product. -/
def blockFrequency {G : Type*} [CommGroup G] (frozen row mark squarefree cube : G) : G :=
  frozen * squarefree * cube ^ (3 : ℕ) * row ^ (-2 : ℤ) * mark ^ (-2 : ℤ)

private theorem move_frozen_factor {G : Type*} [CommGroup G]
    (a b c d e f g : G) :
    a * b * c * d * e * f * g = a * b * f * c * d * e * g := by
  ac_rfl

theorem frequencyClass_eq_block (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    frequencyClass K S D d i =
      blockFrequency (frozenFrequencyClass K S D d i)
        (generatorLocalClass K S D d.moving)
        (generatorLocalClass K S D (activeMarkedIdeal K S d i))
        (generatorLocalClass K S D i.c) (generatorLocalClass K S D i.n) := by
  exact move_frozen_factor
    (unitLocalClass K S (frequencyUnit K S d i))
    (generatorLocalClass K S D i.numeratorFrozen)
    (generatorLocalClass K S D i.c)
    (generatorLocalClass K S D i.n ^ (3 : ℕ))
    (generatorLocalClass K S D d.moving ^ (-2 : ℤ))
    (generatorLocalClass K S D (activeFrozenIdeal K S d i) ^ (-2 : ℤ))
    (generatorLocalClass K S D (activeMarkedIdeal K S d i) ^ (-2 : ℤ))

/-- Every function of the actual local-frequency class has an exact
componentwise expansion.  The masks are respectively row-only, mark-only
and joint-column-only, as required by the hybrid sieve. -/
theorem frequency_function_expansion [Fintype (SixthLocalClasses K S)]
    (d : MarkedDatum K S) (i : ReflectionIndex K S d)
    (H : SixthLocalClasses K S → ℂ) :
    H (frequencyClass K S D d i) =
      ∑ q : FourClasses (SixthLocalClasses K S),
        H (blockFrequency (frozenFrequencyClass K S D d i)
          q.1.1 q.1.2 q.2.1 q.2.2) *
        rowMask q (generatorLocalClass K S D d.moving) *
        markMask q (generatorLocalClass K S D (activeMarkedIdeal K S d i)) *
        columnMask q (generatorLocalClass K S D i.c) (generatorLocalClass K S D i.n) := by
  rw [frequencyClass_eq_block K S D d i]
  exact class_expansion
    (fun r m c n => H (blockFrequency (frozenFrequencyClass K S D d i) r m c n))
    _ _ _ _

/-- In particular this is an identity for the actual zero-line Mellin kernel. -/
theorem kernel_frequency_expansion [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeGeneral.Characters.HeckeCharacter K)
    (d : MarkedDatum K S) (i : ReflectionIndex K S d)
    (V : ℝ → ℂ) (y : ℝ) :
    mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
      (frequencyClass K S D d i) V 0 y =
      ∑ q : FourClasses (SixthLocalClasses K S),
        mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
          (blockFrequency (frozenFrequencyClass K S D d i)
            q.1.1 q.1.2 q.2.1 q.2.2) V 0 y *
        rowMask q (generatorLocalClass K S D d.moving) *
        markMask q (generatorLocalClass K S D (activeMarkedIdeal K S d i)) *
        columnMask q (generatorLocalClass K S D i.c) (generatorLocalClass K S D i.n) :=
  frequency_function_expansion K S D d i
    (fun σ => mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit) σ V 0 y)

#print axioms frequencyClass_eq_block
#print axioms frequency_function_expansion
#print axioms kernel_frequency_expansion

end HeckeSkeleton.LowEnergy.ActualClassSlices
