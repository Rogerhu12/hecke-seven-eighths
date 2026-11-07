module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationProfiles

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Restoring the two genuine comparison supports

Each transformed factor is evaluated from its global original profile
formula. Nonvanishing forces membership in the original finite support
at the actual divided scale. Both comparison rectangles therefore fit
in the same finite union, and adding the fixed/paid gates only removes
zeros of the corresponding masked factors.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {input : ProfileInput call} {k : ℕ}

namespace SmoothSideSupport

variable (S : SmoothSideSupport input k)

theorem plain_original (rectangle side : Bool) (x : ℝ) :
    (S.plain rectangle side).formula.original x =
      (S.plainTest side).profile (S.plain rectangle side).row
        (S.plain rectangle side).time x := by
  cases side with
  | false => exact (S.plain rectangle false).left_original (S.plain_kind rectangle false) x
  | true => exact (S.plain rectangle true).right_original (S.plain_kind rectangle true) x

/-- The original support scale is divided by the same positive
dilation that occurs in the globally fixed transformed profile. -/
theorem mem_rectangleSupport_of_value_ne_zero (rectangle side : Bool)
    (ξ : EngineParameter) (I : NonzeroIdeal K)
    (h : (S.plain rectangle side).formula.value ξ
      (idealNorm K I / S.plainScale rectangle side) ≠ 0) :
    I ∈ S.rectangleSupport rectangle side := by
  have hs := (S.plain rectangle side).formula.scalar_ne_zero_of_value_ne_zero ξ _ h
  rw [rectangleSupport, if_neg hs]
  apply ((S.plainTest side).support_spec (S.plain rectangle side).row
    (S.plain rectangle side).time
    (S.plainScale rectangle side / (S.plain rectangle side).formula.dilation) I).mpr
  rw [ProfileFormula.quotient_argument, ← S.plain_original rectangle side]
  exact (S.plain rectangle side).formula.original_ne_zero_of_value_ne_zero ξ _ h

theorem mem_smoothPlain_of_value_ne_zero (rectangle side : Bool)
    (ξ : EngineParameter) (I : NonzeroIdeal K)
    (h : (S.plain rectangle side).formula.value ξ
      (idealNorm K I / S.plainScale rectangle side) ≠ 0) :
    I ∈ S.smoothPlain side := by
  have hm := S.mem_rectangleSupport_of_value_ne_zero rectangle side ξ I h
  cases rectangle with
  | false => exact Finset.mem_union_left _ hm
  | true => exact Finset.mem_union_right _ hm

theorem plain_value_zero_of_not_mem_smoothPlain (rectangle side : Bool)
    (ξ : EngineParameter) (I : NonzeroIdeal K) (hI : I ∉ S.smoothPlain side) :
    (S.plain rectangle side).formula.value ξ
      (idealNorm K I / S.plainScale rectangle side) = 0 := by
  by_contra h
  exact hI (S.mem_smoothPlain_of_value_ne_zero rectangle side ξ I h)

/-- Prime profiles have no support dilation and retain their actual
original occurrence length. -/
theorem mem_smoothSlot_of_value_ne_zero (i : Fin k) (ξ : EngineParameter)
    (q : HeightOneSpectrum (𝓞 K))
    (h : (S.prime i).formula.value ξ
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ S.length i) ≠ 0) :
    q ∈ S.smoothSlot i := by
  have hs := (S.prime i).formula.scalar_ne_zero_of_value_ne_zero ξ _ h
  rw [smoothSlot, if_neg hs]
  apply ((call.node.data.geometry.slots (S.slotEmbedding i)).support_spec
    (S.prime i).time (call.base ^ S.length i) q).mpr
  have ho := (S.prime i).formula.original_ne_zero_of_value_ne_zero ξ _ h
  rw [S.prime_dilation i, one_mul,
    (S.prime i).prime_original (S.slotEmbedding i) (S.prime_kind i)] at ho
  exact ho

theorem prime_value_zero_of_not_mem_smoothSlot (i : Fin k) (ξ : EngineParameter)
    (q : HeightOneSpectrum (𝓞 K)) (hq : q ∉ S.smoothSlot i) :
    (S.prime i).formula.value ξ
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ S.length i) = 0 := by
  by_contra h
  exact hq (S.mem_smoothSlot_of_value_ne_zero i ξ q h)

/-- The common fixed/paid gate, applied to a single original plain
formula, is supported on the restored finite carrier. -/
theorem masked_plain_zero_of_not_mem_carrier
    (paid : (Arithmetic.data c).Exterior) (rectangle side : Bool)
    (ξ : EngineParameter) (I : NonzeroIdeal K)
    (hI : I ∉ S.plainCarrier paid side) :
    (if IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val then
      (S.plain rectangle side).formula.value ξ
        (idealNorm K I / S.plainScale rectangle side) else 0) = 0 := by
  by_cases hg : IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val
  · rw [if_pos hg]
    apply S.plain_value_zero_of_not_mem_smoothPlain rectangle side ξ I
    intro hm
    exact hI (Finset.mem_filter.mpr ⟨hm, hg⟩)
  · exact if_neg hg

theorem masked_prime_zero_of_not_mem_carrier
    (paid : (Arithmetic.data c).Exterior) (i : Fin k)
    (ξ : EngineParameter) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∉ S.slotCarrier paid i) :
    (if IsCoprime q.asIdeal (Arithmetic.data c).cS ∧ IsCoprime q.asIdeal paid.val then
      (S.prime i).formula.value ξ
        ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ S.length i) else 0) = 0 := by
  by_cases hg : IsCoprime q.asIdeal (Arithmetic.data c).cS ∧ IsCoprime q.asIdeal paid.val
  · rw [if_pos hg]
    apply S.prime_value_zero_of_not_mem_smoothSlot i ξ q
    intro hm
    exact hq (Finset.mem_filter.mpr ⟨hm, hg⟩)
  · exact if_neg hg

end SmoothSideSupport
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SmoothSideSupport.mem_smoothPlain_of_value_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.SmoothSideSupport.masked_prime_zero_of_not_mem_carrier
