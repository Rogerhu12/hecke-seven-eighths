import ActualChoiceMaskedWholeAnnular
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
UNCOMPILED / native 0. Multiplication by the SAME witness's actual
allowed generator preserves its original finite-S choice mask on EVERY
nonzero S-integer column. Its finite power class belongs to the actual
subgroup C6, so subgroup membership is unchanged by multiplication.
No coprimality, column-mask identity, summability or analytic input is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedColumnMaskDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open ActualGeneratorChoiceDraft ActualChoiceMaskedAnnularDraft
open ActualProbeGaussFourierDraft ActualGramJointChartDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)

local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "E" => ExteriorIdeal K S

private theorem choiceFiniteMask_allowedGenerator_mul
    (I : E) (x : SFiniteLocalGroup K S) :
    choiceFiniteMask K w
      ((sLocalNonzeroIntegerDiagonal K S (probeGenerator K S w.D I)).2 * x) =
      choiceFiniteMask K w x := by
  unfold choiceFiniteMask
  rw [map_mul, choiceFiniteClassHom_diagonal]
  change (if generatorSameSClass K w.S w.D I * choiceFiniteClassHom K w x ∈ w.C6
    then (1 : ℂ) else 0) =
      (if choiceFiniteClassHom K w x ∈ w.C6 then (1 : ℂ) else 0)
  rw [w.C6.mul_mem_cancel_left (w.generator_class_mem I)]

/-- The original product-column mask equals the original column mask
for every column, including columns outside the allowed-generator orbits. -/
@[simp] theorem choiceColumnMask_probeGenerator (I : E) (m : NZ) :
    choiceColumnMask K w (probeGenerator K S w.D I) m =
      choiceFiniteMask K w (sLocalNonzeroIntegerDiagonal K S m).2 := by
  have hcolumn : divisorColumn K S (probeGenerator K S w.D I) m =
      sIntegerNonzeroMul K S (probeGenerator K S w.D I) m := rfl
  unfold choiceColumnMask
  rw [hcolumn, sLocalNonzeroIntegerDiagonal_nonzeroMul]
  exact choiceFiniteMask_allowedGenerator_mul K w I
    (sLocalNonzeroIntegerDiagonal K S m).2

end HeckeGeneral.ThetaSkeleton.Physical.ActualAllowedColumnMaskDraft
