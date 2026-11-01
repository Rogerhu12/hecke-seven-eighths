import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CompleteSourcePrimitive

/-!
# The original open prime annulus survives every local source operation

The canonical primitive engine asks for each actual prime test to be
supported in (1,2). A common larger Schwartz window does not imply this
fact. We retain it separately, using the same literal prime functions.

The source's original weight has this support. Changes of the scale
exponent, actual slot selection, time freezing, Mellin normalization and
ordinary reflection preserve it. No arithmetic mask is used to improve
the analytic support of the test itself.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The same open annulus for every original prime profile and every
time; this is stronger than the recursive common annulus. -/
def PrimeProfileSupport (d : MomentData K omegaCharacter psiCharacter) : Prop :=
  ∀ j t, Function.support ((d.geometry.slots j).profile t) ⊆ Set.Ioo (1 : ℝ) 2

namespace PrimeProfileSupport

variable {d : MomentData K omegaCharacter psiCharacter}

theorem freezeMomentTime (h : PrimeProfileSupport d) (time : ℝ) :
    PrimeProfileSupport (EngineInduction.freezeMomentTime d time) := by
  intro j t y hy
  apply h j time
  simpa only [EngineInduction.freezeMomentTime, MomentData.separatedProfiles,
    SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_zero, mul_one] using hy

theorem scaledMomentProfiles (h : PrimeProfileSupport d) (scalar : ℝ) (hscalar : 0 < scalar) :
    PrimeProfileSupport (EngineInduction.scaledMomentProfiles d scalar hscalar) := by
  intro j t
  change Function.support ((scaledPrimeWindow (d.geometry.slots j) scalar hscalar).profile t) ⊆ _
  rw [scaledPrimeWindow_profile_support]
  exact h j t

theorem normalizedMellinPlainData (h : PrimeProfileSupport d)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    PrimeProfileSupport
      (EngineInduction.normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency) :=
  h.scaledMomentProfiles P⁻¹ (inv_pos.mpr (zero_lt_one.trans_le hP))

theorem ordinaryPowerChild (h : PrimeProfileSupport d)
    (first : Bool) (sigma frequency : ℝ) :
    PrimeProfileSupport (EngineInduction.ordinaryPowerChild K d first sigma frequency) := h

theorem normalizedOrdinaryPowerChild (h : PrimeProfileSupport d)
    (first : Bool) (sigma frequency E : ℝ) (hE : 1 ≤ E) (J : ℕ) :
    PrimeProfileSupport
      (EngineInduction.normalizedOrdinaryPowerChild d first sigma frequency E hE J) :=
  (h.ordinaryPowerChild first sigma frequency).scaledMomentProfiles _ _

theorem changeSlotBase (h : PrimeProfileSupport d) (shell : ℝ) (hshell : 0 < shell) :
    PrimeProfileSupport (d.changeSlotBase shell hshell) := h

theorem restrictSlots (h : PrimeProfileSupport d) (keep : Finset (Fin d.geometry.slotCount)) :
    PrimeProfileSupport (d.restrictSlots keep) :=
  fun j t => h (selectedSlotIndex keep j) t

/-- Exact representatives inherit this tighter support independently
of the larger common Schwartz window used for their seminorm bounds. -/
theorem rawProfileWindow (h : PrimeProfileSupport d)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : EngineStep.RawProfileWindow rowDomain heightDomain window orders d amplitude) :
    ∀ j t, Function.support (profiles.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2 := by
  intro j t y hy
  apply h j t
  simpa only [Function.mem_support, profiles.prime_eq] using hy

end PrimeProfileSupport

/-- The original weight is retained, multiplied only by its original
complex power. Nonvanishing therefore implies nonvanishing of that
same weight in its original open annulus. -/
theorem recipeFullModel_primeSupport
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (rows : RowCharacterInput K S P)
    (g : PrimeWindowGeometry) (F : ExpansionRecipe.RecipeFamily K psiCharacter g)
    (U D : ℝ) (sector : SixthUnitClasses K S) (xi : ExpansionRecipe.RecipeVector)
    (sigma tau : NonzeroIdeal K → ExpansionRecipe.RecipeVector) :
    PrimeProfileSupport (F.fullModel K S P rows omegaCharacter psiCharacter g
      U D sector xi sigma tau) := by
  intro j t y hy
  apply g.support_annular j
  change (g.weight j).toFun y * profilePower
    (F.slotPower j (ExpansionRecipe.recipePhysicalPoint xi)) y ≠ 0 at hy
  exact left_ne_zero_of_mul hy

namespace Source

variable {c : TargetContext K}

/-- Slot selection and shell exponents do not enlarge the physical
prime test. This applies to every original recipe and every root. -/
theorem recipeRoot_primeSupport
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)) {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) :
    PrimeProfileSupport (recipeRoot R i s).data := by
  apply PrimeProfileSupport.restrictSlots
  apply PrimeProfileSupport.changeSlotBase
  exact recipeFullModel_primeSupport (places K c) (probeData K c)
    (momentRowCharacters K c) c.geometry R.family _ _ s _ _ _

end Source

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.PrimeProfileSupport.normalizedMellinPlainData
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_primeSupport
