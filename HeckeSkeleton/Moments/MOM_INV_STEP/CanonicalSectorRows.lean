import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectors
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalPoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren

/-!
# Canonical row values with every original sector retained

Allowed generators have a sixth-power unit defect. Actual sextic column
values therefore admit an unchanged sector label under ideal dilation,
even for a subgroup smaller than the full sixth-power subgroup. This is
an equality of column values, not a claim that arbitrary subgroup orbits
themselves have the same unchanged sector under dilation.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectorRows

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def sectorCharacter (n I : Ext) (ξ : Sector) : ℂ :=
  idealSymbol K Sset D n (CanonicalSectors.rowElement K Sset Γ D (I, ξ)).val

theorem sectorCharacter_eq (n I : Ext) (ξ : Sector) :
    sectorCharacter K S Γ D n I ξ =
      idealSymbol K Sset D n
        (Sset.unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val *
        idealSymbol K Sset D n (D.generator I) := by
  exact CanonicalPoissonSource.idealSymbol_mul K S D n _ _

include hallowed in
theorem generator_mul_character (n I J : Ext) :
    idealSymbol K Sset D n (D.generator (exteriorMul K Sset I J)) =
      idealSymbol K Sset D n (D.generator I) *
        idealSymbol K Sset D n (D.generator J) := by
  have h := (CanonicalIdealRow.row K S D hallowed n).map_mul
    (CanonicalIdealRow.ofExterior K S I) (CanonicalIdealRow.ofExterior K S J)
  simpa only [CanonicalIdealRow.row_apply, CanonicalIdealRow.generator,
    CanonicalIdealRow.toExterior_mul, CanonicalIdealRow.toExterior_ofExterior] using h

include hallowed in
theorem sectorCharacter_mul (n I J : Ext) (ξ : Sector) :
    sectorCharacter K S Γ D n (exteriorMul K Sset I J) ξ =
      idealSymbol K Sset D n (D.generator I) * sectorCharacter K S Γ D n J ξ := by
  rw [sectorCharacter_eq, generator_mul_character K S D hallowed,
    sectorCharacter_eq]
  ring

def firstRowIdeal (f E h : Ext) : Ext :=
  exteriorMul K Sset (exteriorMul K Sset (exteriorMul K Sset f f) E) h

@[simp] theorem firstRowIdeal_val (f E h : Ext) :
    (firstRowIdeal K S f E h).val.val = f.val.val ^ 2 * E.val.val * h.val.val := by
  simp only [firstRowIdeal, exteriorMul, Submonoid.coe_mul, pow_two]

include hallowed in
/-- The original f⁴ character moves into the row as f², including its
coprimality zero. The frozen E and every original unit sector remain. -/
theorem first_label_absorb (n f E h : Ext) (ξ : Sector) :
    idealSymbol K Sset D n (D.generator f) ^ 4 *
        star (sectorCharacter K S Γ D n (exteriorMul K Sset E h) ξ) =
      star (sectorCharacter K S Γ D n (firstRowIdeal K S f E h) ξ) := by
  let χ := CanonicalIdealRow.row K S D hallowed n
  let f₀ := CanonicalIdealRow.ofExterior K S f
  let z₀ := CanonicalIdealRow.ofExterior K S (exteriorMul K Sset E h)
  have hb : χ f₀ ^ 4 * star (χ z₀) = star (χ (z₀ * f₀ ^ 2)) := by
    simpa only [χ, CanonicalIdealRow.row_apply] using
      (CanonicalIdealRow.fourth_label_absorb_row K S D hallowed n f₀ z₀)
  rw [map_mul, map_pow] at hb
  have hb' : idealSymbol K Sset D n (D.generator f) ^ 4 *
      star (idealSymbol K Sset D n (D.generator (exteriorMul K Sset E h))) =
      star (idealSymbol K Sset D n (D.generator (exteriorMul K Sset E h)) *
        idealSymbol K Sset D n (D.generator f) ^ 2) := by
    simpa only [χ, f₀, z₀, CanonicalIdealRow.row_apply,
      CanonicalIdealRow.generator_ofExterior] using hb
  have he := congrArg (fun z : ℂ =>
    star (idealSymbol K Sset D n
      (Sset.unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val) * z) hb'
  simp only [sectorCharacter_eq, firstRowIdeal,
    generator_mul_character K S D hallowed, star_mul, star_pow] at he ⊢
  convert he using 1 <;> ring

/-- The row in the literal child definition is the same actual
canonical-generator character on exterior row ideals. -/
theorem child_sectorRow (n I : Ext) (ξ : Sector) :
    CanonicalChildren.sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ)
      n (I.val.val, ξ) = sectorCharacter K S Γ D n I ξ := by
  exact CanonicalChildren.sectorRow_exterior K Sset D
    (CanonicalSectors.sectorUnit K Sset Γ) n I ξ

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectorRows

end
