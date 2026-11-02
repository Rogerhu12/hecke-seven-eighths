import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependentCore
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryProfileNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileScaling

/-!
# Actual profiles which have already absorbed their time parameters

The literal source recipe has fixed its inverse/plain/slot times inside
the test profiles. Its remaining evaluation-time argument is unused.
The same property is proved for the actual ordinary power child and
positive profile normalization. Arbitrary MomentData are not assumed to
have this property.

For this proved class, freezing any evaluation time preserves every
profile function used by the actual Euler control. Hence all source,
base and unit/budget controls transfer with exactly the same seminorm
order, annulus, coefficient and height degree. Together with the separate
arithmetic preservation facts this supplies genuine freeze closure for
a primitive admissibility predicate, rather than an extra label premise.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

private theorem idealTest_eq_of_profile (V W : IdealTest K)
    (hp : V.profile = W.profile) : V = W := by
  have hs : V.support = W.support := by
    funext u t N
    apply Finset.ext
    intro I
    rw [V.support_spec, W.support_spec, hp]
  cases V with
  | mk vp vs hv =>
    cases W with
    | mk wp ws hw =>
      change vp = wp at hp
      change vs = ws at hs
      cases hp
      cases hs
      rfl

private theorem primeWindow_eq_of_length_profile (V W : PrimeWindow K)
    (hl : V.length = W.length) (hp : V.profile = W.profile) : V = W := by
  have hs : V.support = W.support := by
    funext t N
    apply Finset.ext
    intro p
    rw [V.support_spec, W.support_spec, hp]
  cases V with
  | mk vl hvl vp vs hv =>
    cases W with
    | mk wl hwl wp ws hw =>
      change vl = wl at hl
      change vp = wp at hp
      change vs = ws at hs
      cases hl
      cases hp
      cases hs
      rfl

private theorem idealTest_freeze_zero_eq (W : IdealTest K)
    (h : ∀ u t, W.profile u t = W.profile u 0)
    (time : NonzeroIdeal K → ℝ) :
    W.freezeTwist time (fun _ => 0) = W := by
  apply idealTest_eq_of_profile
  funext u t y
  change W.profile u (time u) y * profilePower 0 y = W.profile u t y
  rw [profilePower_zero, mul_one, h u (time u), h u t]

private theorem primeWindow_freeze_zero_eq (W : PrimeWindow K)
    (h : ∀ t, W.profile t = W.profile 0) (time : ℝ) :
    W.freezeTwist time 0 = W := by
  apply primeWindow_eq_of_length_profile (W.freezeTwist time 0) W rfl
  funext t y
  change W.profile time y * profilePower 0 y = W.profile t y
  rw [profilePower_zero, mul_one, h time, h t]

/-- The literal independent-time/power constructor already freezes every
profile. Its powers need not be zero, and may depend on the original row. -/
theorem profileTimeIndependent_separatedProfiles (d : MomentData K ω ψ)
    (inverseTime plainTime₁ plainTime₂ : NonzeroIdeal K → ℝ)
    (inversePower plainPower₁ plainPower₂ : NonzeroIdeal K → ℂ)
    (slotTime : Fin d.geometry.slotCount → ℝ)
    (slotPower : Fin d.geometry.slotCount → ℂ) :
    ProfileTimeIndependent (d.separatedProfiles inverseTime plainTime₁ plainTime₂
      inversePower plainPower₁ plainPower₂ slotTime slotPower) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem profileTimeIndependent_freezeMomentTime (d : MomentData K ω ψ) (time : ℝ) :
    ProfileTimeIndependent (freezeMomentTime d time) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

namespace ProfileTimeIndependent

variable {d : MomentData K ω ψ}

/-- The entire original slot selection retains literal time independence. -/
theorem restrictSlots (h : ProfileTimeIndependent d)
    (keep : Finset (Fin d.geometry.slotCount)) :
    ProfileTimeIndependent (d.restrictSlots keep) :=
  ⟨h.inverse, h.plain₁, h.plain₂, fun j t => h.prime (selectedSlotIndex keep j) t⟩

theorem changeSlotBase (h : ProfileTimeIndependent d) (scale : ℝ) (hscale : 0 < scale) :
    ProfileTimeIndependent (d.changeSlotBase scale hscale) :=
  ⟨h.inverse, h.plain₁, h.plain₂, h.prime⟩

/-- A positive common scalar changes only values, never their time
arguments or the exact original finite supports. -/
theorem scaledMomentProfiles (h : ProfileTimeIndependent d) (a : ℝ) (ha : 0 < a) :
    ProfileTimeIndependent (EngineInduction.scaledMomentProfiles d a ha) := by
  constructor
  · intro u t
    funext y
    exact congrArg (fun z : ℂ => (a : ℂ) * z) (congrFun (h.inverse u t) y)
  · intro u t
    funext y
    exact congrArg (fun z : ℂ => (a : ℂ) * z) (congrFun (h.plain₁ u t) y)
  · intro u t
    funext y
    exact congrArg (fun z : ℂ => (a : ℂ) * z) (congrFun (h.plain₂ u t) y)
  · intro j t
    funext y
    exact congrArg (fun z : ℂ => (a : ℂ) * z) (congrFun (h.prime j t) y)

/-- The replacement power window is genuinely frozen at its operator
frequency. The unreplaced profiles are the original independent ones. -/
theorem ordinaryPowerChild (h : ProfileTimeIndependent d)
    (first : Bool) (σ frequency : ℝ) :
    ProfileTimeIndependent (EngineInduction.ordinaryPowerChild K d first σ frequency) := by
  constructor
  · exact h.inverse
  · intro u t
    cases first with
    | false => exact h.plain₁ u t
    | true => rfl
  · intro u t
    cases first with
    | false => rfl
    | true => exact h.plain₂ u t
  · exact h.prime

/-- The actual frequency envelope is constant in the evaluation-time
argument, so the normalized child remains in the same primitive class. -/
theorem normalizedOrdinaryPowerChild (h : ProfileTimeIndependent d)
    (first : Bool) (σ frequency E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) :
    ProfileTimeIndependent
      (EngineInduction.normalizedOrdinaryPowerChild d first σ frequency E0 hE0 J) :=
  (h.ordinaryPowerChild first σ frequency).scaledMomentProfiles _ _

/-- For this actual class freezing changes no data at all. Exact support
sets follow from their defining profile equivalence, rather than being
assumed time independent as an additional primitive. -/
theorem freezeMomentTime_eq (h : ProfileTimeIndependent d) (time : ℝ) :
    freezeMomentTime d time = d := by
  have hi := idealTest_freeze_zero_eq d.inverseTest h.inverse (fun _ => time)
  have h₁ := idealTest_freeze_zero_eq d.plainTest₁ h.plain₁ (fun _ => time)
  have h₂ := idealTest_freeze_zero_eq d.plainTest₂ h.plain₂ (fun _ => time)
  have hs : (fun j => (d.geometry.slots j).freezeTwist time 0) = d.geometry.slots :=
    funext (fun j => primeWindow_freeze_zero_eq (d.geometry.slots j) (h.prime j) time)
  simp only [freezeMomentTime, MomentData.separatedProfiles, SlotGeometry.freezeTwists,
    hi, h₁, h₂]
  exact congrArg
    (fun slots : Fin d.geometry.slotCount → PrimeWindow K =>
      ({ d with geometry := { slotCount := d.geometry.slotCount, slots := slots } } :
        MomentData K ω ψ)) hs

/-- Equality of every profile used by source/base/budget seminorms.
No uniformity in the original, unabsorbed time family is postulated. -/
theorem freeze_profiles (h : ProfileTimeIndependent d) (time : ℝ) :
    (∀ u, (freezeMomentTime d time).inverseTest.profile u 0 = d.inverseTest.profile u 0) ∧
    (∀ u, (freezeMomentTime d time).plainTest₁.profile u 0 = d.plainTest₁.profile u 0) ∧
    (∀ u, (freezeMomentTime d time).plainTest₂.profile u 0 = d.plainTest₂.profile u 0) ∧
    (∀ j, ((freezeMomentTime d time).geometry.slots j).profile 0 =
      (d.geometry.slots j).profile 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    funext y
    change d.inverseTest.profile u time y * profilePower 0 y = d.inverseTest.profile u 0 y
    rw [profilePower_zero, mul_one, h.inverse u time]
  · intro u
    funext y
    change d.plainTest₁.profile u time y * profilePower 0 y = d.plainTest₁.profile u 0 y
    rw [profilePower_zero, mul_one, h.plain₁ u time]
  · intro u
    funext y
    change d.plainTest₂.profile u time y * profilePower 0 y = d.plainTest₂.profile u 0 y
    rw [profilePower_zero, mul_one, h.plain₂ u time]
  · intro j
    funext y
    change (d.geometry.slots j).profile time y * profilePower 0 y =
      (d.geometry.slots j).profile 0 y
    rw [profilePower_zero, mul_one, h.prime j time]

/-- The coefficient may be an arbitrary current root budget, or one for
normalized descendants. Neither the coefficient nor the height degree
is increased by the freeze operation. -/
theorem freeze_modelProfileControl_iff (h : ProfileTimeIndependent d) (time : ℝ)
    (J : ℕ) (A C H a b T : ℝ) :
    ModelProfileControl (freezeMomentTime d time) J A C H a b T ↔
      ModelProfileControl d J A C H a b T := by
  rw [h.freezeMomentTime_eq time]

end ProfileTimeIndependent

/-- The actual node itself is unchanged, including both comparison
rectangles, once its profile time-independence has been proved. -/
theorem Node.freezeTime_eq (n : Node K ω ψ) (h : ProfileTimeIndependent n.data)
    (time : ℝ) : n.freezeTime time = n := by
  unfold Node.freezeTime
  rw [h.freezeMomentTime_eq time]

/-- Node normalization uses precisely the common scalar constructor
whose time-independence was proved above. -/
theorem Node.scaleProfiles_timeIndependent (n : Node K ω ψ)
    (h : ProfileTimeIndependent n.data) (a : ℝ) (ha : 0 < a) :
    ProfileTimeIndependent (n.scaleProfiles a ha).data :=
  h.scaledMomentProfiles a ha

theorem Node.normalizeProfiles_timeIndependent (n : Node K ω ψ)
    (h : ProfileTimeIndependent n.data) (A : ℝ) (hA : 0 < A) :
    ProfileTimeIndependent (n.normalizeProfiles A hA).data :=
  h.scaledMomentProfiles A⁻¹ (inv_pos.mpr hA)

namespace Source

variable {c : TargetContext K}
variable (recipe : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))
variable {Z T : ℝ}
variable (i : SourceMomentIndexFor K c (recipeMomentSourceData K c recipe) Z T)
variable (s : SixthUnitClasses K (places K c))

/-- All final time arguments in the literal fixed recipe have already
been frozen. This holds on every complete ideal and every actual slot. -/
theorem recipeRoot_timeIndependent : ProfileTimeIndependent (recipeRoot recipe i s).data :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem recipeRoot_noSlots_timeIndependent :
    ProfileTimeIndependent (recipeRoot recipe i.noSlots s).data :=
  recipeRoot_timeIndependent recipe i.noSlots s

/-- The evaluated source control moves to any frozen root time without
changing the selected order, support interval or polynomial height cost. -/
theorem recipeRoot_freeze_control_iff (time : ℝ) (J : ℕ) (A C H a b height : ℝ) :
    ModelProfileControl (freezeMomentTime (recipeRoot recipe i s).data time)
      J A C H a b height ↔
      ModelProfileControl (recipeRoot recipe i s).data J A C H a b height :=
  (recipeRoot_timeIndependent recipe i s).freeze_modelProfileControl_iff
    time J A C H a b height

end Source
end HeckeSkeleton.Moments.EngineInduction
