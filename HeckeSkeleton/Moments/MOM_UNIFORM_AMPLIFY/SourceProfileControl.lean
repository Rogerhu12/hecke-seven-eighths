import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.CanonicalProfileControl
import HeckeSkeleton.ExpansionModels.SourceData
import Expansion.PhysicalRecipeSchedule

/-!
# The whole profile bound of the actual source

The fixed family is expanded to its literal dyadic windows, original cutoff,
and compensation prime powers.  Its inverse, plain, and all prime slices
therefore have one uniform annulus and a polynomial height exponent fixed
before every source index.  The independent unmarked U,D family and the
actual selected parameter box are included in the same source interface.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

theorem recipe_source_profile_control
    (R : RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (hinverse : ∀ u t y, R.family.inverseAnnular.profile u t y = Expansion.Dyadic.annularProfile y)
    (hplain : ∀ u t y, R.family.plainAnnular.profile u t y = Expansion.Dyadic.annularProfile y)
    (hcutoff : R.family.cutoff = Expansion.Dyadic.cutoffProfile)
    (hprime : ∀ j p, R.family.slotPower j p =
      conj ((17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I) - 1)
    (hparameters : SourceMomentParameterControlFor (recipeMomentModels K c R))
    (hlengths : ∃ L : ℝ, 0 ≤ L ∧
      SourceWitnessLengthBoundFor (recipeMomentSourceData K c R) L) :
    WholeMomentProfileControlFor (recipeMomentModels K c R) := by
  have hfamily (J : ℕ) (A : ℝ) := canonical_recipe_model_profile_control
    (places K c) (probeData K c) (momentRowCharacters K c)
    c.family.omega (targetCharacter K c) c.geometry R.family
    hinverse hplain hcutoff hprime J A
  refine ⟨?_, ?_, hparameters, hlengths⟩
  · intro J A _hA
    obtain ⟨C, hC, hb⟩ := hfamily J A
    refine ⟨C, (J : ℝ), 1 / 2, 2, hC, Nat.cast_nonneg _, by norm_num, by norm_num, ?_⟩
    intro Z T i _hZ hT s ξ σ τ hξ hσ hτ d hd
    have hU : 0 < momentBaseFor i := (by norm_num : (0 : ℝ) < 2).trans_le
      (recipeMomentBase_ge_two i)
    have hD : 0 ≤ momentBaseFor i ^ (momentWitnessFor i).inverseLength :=
      (Real.rpow_pos_of_pos hU _).le
    have hfull := (hb T (zero_le_one.trans hT) (momentBaseFor i)
      (momentBaseFor i ^ (momentWitnessFor i).inverseLength) hU hD s ξ σ τ hξ hσ hτ).1
    have hselected := (modelProfileControl_changeSlotBase _ (momentBlockFor i).shell
      (recipeMoment_shell_pos i) hfull)
    have h := modelProfileControl_restrictSlots _ i.selected hselected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> exact h
  · intro J A _hA
    obtain ⟨C, hC, hb⟩ := hfamily J A
    refine ⟨C, (J : ℝ), 1 / 2, 2, hC, Nat.cast_nonneg _, by norm_num, by norm_num, ?_⟩
    intro U D T hU hD hT s ξ σ τ hξ hσ hτ
    exact (hb T (zero_le_one.trans hT) U D (zero_lt_one.trans_le hU)
      (zero_le_one.trans hD) s ξ σ τ hξ hσ hτ).2

/-- The same actual source has one plain-length bound before all scales,
heights and later losses.  Inverse lengths are nonnegative on every index. -/
theorem actual_source_uniform_lengths (K : Type) [Field K] [NumberField K]
    (c : TargetContext K) :
    SourceWitnessLengthBoundFor (recipeMomentSourceData K c (expansionRecipeRaw K c)) 22 :=
  (recipeMomentModels_geometry K c (expansionRecipeRaw K c)
    (expansionRecipeRaw_geometry K c)).1

/-- MI-M-PROFILE-UNIFORMITY for the named actual data.  The primitive
identifications are definitional facts of the physical recipe, and the
selected parameter box is the geometry theorem of that same recipe. -/
theorem actual_source_profile_control (K : Type) [Field K] [NumberField K]
    (c : TargetContext K) :
    WholeMomentProfileControlFor (recipeMomentModels K c (expansionRecipeRaw K c)) := by
  apply recipe_source_profile_control (expansionRecipeRaw K c)
  · intro u t y
    rfl
  · intro u t y
    rfl
  · rfl
  · intro j p
    rfl
  · exact (recipeMomentModels_geometry K c (expansionRecipeRaw K c)
      (expansionRecipeRaw_geometry K c)).2
  · exact ⟨22, by norm_num, actual_source_uniform_lengths K c⟩

end HeckeSkeleton.Moments.UniformAmplify

#print axioms HeckeSkeleton.Moments.UniformAmplify.recipe_source_profile_control
#print axioms HeckeSkeleton.Moments.UniformAmplify.actual_source_profile_control
