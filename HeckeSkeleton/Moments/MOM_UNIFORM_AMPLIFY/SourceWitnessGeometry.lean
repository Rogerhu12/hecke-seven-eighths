import HeckeSkeleton.ExpansionModels.SourceData
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceWitnessBounds

/-!
# The actual all-scale source supplies witness calibration geometry

The lower row scale, bounded inverse length and admissible height/shift
parameters are proved for the same source and the same chosen models.
The inverse bound is needed precisely on live bins, as in
`UniformMomentBoundFor`; it holds before imposing a detection threshold.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

attribute [local instance] Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  expansionNormOneSpace expansionNormOneBorel expansionLocalHaar

local notation "Raw" => expansionRecipeRaw K c
local notation "Source" => recipeMomentSourceData K c (expansionRecipeRaw K c)
local notation "Models" => recipeMomentModels K c (expansionRecipeRaw K c)
local notation "q" => expansionPhysicalParameters K c
local notation "Eactual" => HighBinActualEuler.arithmeticHighEulerData K (places K c)
  (probeData K c) (targetCharacter K c)

variable {Z T : ℝ}

/-- Every high-bin witness of the actual source has a common bounded
inverse length, including the default choices at early active scales. -/
theorem actual_source_witness_inverseLength_range
    (i : SourceMomentIndexFor K c Source Z T)
    (hbin : 51 / 100 < (momentBlockFor i).bin) :
    0 ≤ (momentWitnessFor i).inverseLength ∧
      (momentWitnessFor i).inverseLength ≤ 3 / 2 + c.family.lamA := by
  let b := (Raw).rawBlockIndex Z T i.block
  let j := physicalRecipeShellIndex K (places K c) c.family.B (q).e
    (expansionShellAllowance K c) Z b
  let a := physicalRecipeChoice K (places K c) c.family.B (q).e
    (expansionShellAllowance K c) Z b
  exact physicalSourceOrDefault_witness_lengths
    K (places K c) (probeData K c) (Eactual).rows c.family.omega
    (targetCharacter K c) c.geometry
    (physicalRecipeFamily K (targetCharacter K c) c.geometry c.family.B (q).e)
    (q).width Z T (shellExponent Z (1 / 16) j.val) a.1.center
    c.family.B c.family.lamA (q).k (q).width_pos
    (physicalRecipeChoice_cap K (places K c) (expansionBoundary_lower K c)
      c.family.B_upper (q).e_pos a)
    (physicalRecipeRows K (places K c) (probeData K c) (Eactual)
      c.family.omega (targetCharacter K c) (representative K c).val.property
      (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
      (expansionShellAllowance K c) Z T j a)
    a.2
    (physicalRecipeBlockValue K (places K c) (probeData K c) (Eactual)
      c.family.omega (targetCharacter K c) (representative K c).val.property
      (expansionBoundary_lower K c) c.family.B_upper (q).e_pos c.family.boundary
      (probeMeasures K c).haar c.geometry ∅ (expansionShellAllowance K c) Z T j a)
    c.family.lamA_pos.le hbin i.label i.t i.t_lower i.t_upper i.subdivision

/-- The physical row base is at least the fixed power `Z^(1/16)`.  This
constant is chosen independently of every height and witness index. -/
theorem actual_source_witness_base_lower
    (i : SourceMomentIndexFor K c Source Z T) :
    Z ^ (1 / 16 : ℝ) ≤ momentBaseFor i := by
  have hZ : 1 ≤ Z :=
    (by norm_num : (1 : ℝ) ≤ 2 ^ (16 : ℕ)).trans (recipeMoment_scale_of_index i).1
  exact Real.rpow_le_rpow_of_exponent_le hZ (recipeMoment_shell_lower i)

/-- The exact model parameters stay in the originally quantified region,
at the original source height. -/
theorem actual_source_witness_parameter_control :
    SourceMomentParameterControlFor Models :=
  (recipeMomentModels_geometry K c (expansionRecipeRaw K c)
    (expansionRecipeRaw_geometry K c)).2

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_source_witness_inverseLength_range
#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_source_witness_base_lower
#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_source_witness_parameter_control
