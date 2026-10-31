import HeckeGeneral.Analysis.PhysicalProbeRows
import Mathlib.Tactic.Linarith

/-! Exact support of the repository's complete frequency-row enumeration. -/
set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- No sector or sixth-power-free row is lost in the actual finite
enumeration. Its cutoff is on the original row norm. -/
theorem mem_frequencyRows_iff (U : ℝ) (hU : 0 ≤ U) (u : FrequencyRow K S) :
    u ∈ frequencyRows K S U ↔ frequencyRowNorm K S u ≤ U := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  let F := (dyadicIdealSupport K (U / 2)).filter fun I =>
    (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S) ∧
      (∀ p : HeightOneSpectrum (𝓞 K), primeExponents I p < 6)
  unfold frequencyRows
  dsimp only
  constructor
  · intro hu
    obtain ⟨⟨I, s⟩, _, rfl⟩ := Finset.mem_image.mp hu
    have hn := (mem_dyadicIdealSupport_iff K (div_nonneg hU (by norm_num)) I.val).mp
      (Finset.mem_filter.mp I.property).1
    change idealNorm K I.val ≤ U
    linarith
  · intro hu
    have hI : u.ideal.val ∈ F := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, u.ideal.property, u.sixthPowerFree⟩
      apply (mem_dyadicIdealSupport_iff K (div_nonneg hU (by norm_num)) u.ideal.val).mpr
      change idealNorm K u.ideal.val ≤ U at hu
      linarith
    apply Finset.mem_image.mpr
    refine ⟨(⟨u.ideal.val, hI⟩, u.sector), ?_, ?_⟩
    · simp
    · rfl

end Expansion.Project

#print axioms Expansion.Project.mem_frequencyRows_iff
