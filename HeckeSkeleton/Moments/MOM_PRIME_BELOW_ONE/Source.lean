import HeckeSkeleton.ExpansionModels.SourceData

/-!
# The actual source below the moment theorem layer

The prime-cancellation adapters use the same explicit source recipe as
`HeckeSkeleton.Moments`.  These source aliases depend only on its data,
so the proved analytic adapter can in turn supply the moment theorem.
The legacy aliases in `Moments` are definitionally equal to these types.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE

open NumberField

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

abbrev ActualSource : MomentSourceData K c :=
  recipeMomentSourceData K c (expansionRecipeRaw K c)

abbrev ActualSourceIndex (Z T : ℝ) : Type 1 :=
  SourceMomentIndexFor K c (ActualSource K c) Z T

abbrev ActualSourceModels := SourceMomentModelsFor K c (ActualSource K c)

end HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE
