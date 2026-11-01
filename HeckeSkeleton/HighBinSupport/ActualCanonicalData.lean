import HeckeSkeleton.HighBinSupport.ActualTargetEuler

/-!
Primitive numeric and arithmetic data shared by the canonical HIGHBIN
Euler, norm-form and boundary constructions. These declarations are
moved verbatim from ActualCanonicalTarget. In particular, the actual
Euler endpoint does not import the norm-form or presentation layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalTarget

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinActualInitial
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

/-- The loss shared by the two independently fixed target loss budgets. -/
def targetLoss : ℝ := min c.family.lamA c.lamB

theorem targetLoss_pos : 0 < targetLoss K c :=
  lt_min c.family.lamA_pos c.lamB_pos

/-- A concrete positive buffer, fixed before the analytic parameters. -/
def targetBuffer : ℝ := targetLoss K c / 100

theorem targetBuffer_pos : 0 < targetBuffer K c :=
  div_pos (targetLoss_pos K c) (by norm_num)

theorem targetBuffer_le_loss : targetBuffer K c ≤ targetLoss K c / 100 := le_rfl

theorem targetBuffer_small : targetBuffer K c ≤ 1 / 10000 := by
  have hm : targetLoss K c ≤ c.family.lamA := min_le_left _ _
  have ha := c.family.lamA_small
  unfold targetBuffer
  linarith

theorem targetBoundary_lower : 51 / 100 ≤ c.family.B := by
  have hb := c.family.B_lower
  linarith

/-- The actual correction packet only needs the trivial companion. -/
def targetCompanions (_c : TargetContext K) : Finset (HeckeCharacter K) := {1}

theorem one_mem_targetCompanions : (1 : HeckeCharacter K) ∈ targetCompanions K c := by
  simp only [targetCompanions, Finset.mem_singleton]

theorem targetCompanions_finiteOrder :
    ∀ chi ∈ targetCompanions K c, FiniteOrder chi := by
  intro chi hchi
  have h : chi = 1 := Finset.mem_singleton.mp hchi
  subst chi
  exact IsOfFinOrder.one

/-- The provider is definitionally the arithmetic Euler construction. -/
abbrev targetEuler : RowEulerData K (places K c) (probeData K c) :=
  arithmeticHighEulerData K (places K c) (probeData K c) (targetCharacter K c)

theorem targetEuler_input :
    TRowEulerInput K (places K c) (probeData K c) (targetCharacter K c)
      (targetEuler K c) :=
  targetTRowEulerInput K c

end HeckeSkeleton.HighBinCanonicalTarget
