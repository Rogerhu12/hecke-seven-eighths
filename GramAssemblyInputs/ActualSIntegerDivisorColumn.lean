import HeckeGeneral.Arithmetic.SIntegerOrbits

/-! The literal nonzero product column, extracted from the original CRT
provider without changing its namespace, parameters or definition. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramJointChartDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "N" => NonzeroRingElements (S.integer K)

/-- Actual nonzero product column for the same Mobius divisor. -/
def divisorColumn (d m : N) : N := ⟨d.val * m.val, mul_ne_zero d.property m.property⟩

end HeckeGeneral.Characters.ActualGramJointChartDraft
