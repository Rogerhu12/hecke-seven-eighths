import Expansion.PhysicalRowDetection
import Expansion.FiniteTerminalLabels
import Mathlib.Tactic.Choose

/-!
# One finite choice and one fixed-sector parameter map for actual detection

The local data are the output structure of the physical row detector. The
finite classification retains its actual presentation and both dyadic
indices. The real part and the common frequency are extended along the
actual ideal/sector embedding; the same maps feed all finite subdivisions.
Outside the source exponent interval, the maps are zero. The analytic
existence theorem is consumed separately by the physical endpoint.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open Expansion.ActualTerminalSaturation Expansion.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ψ : HeckeCharacter K)

/-- The two lower bounds on the literal factors used by the canonical
amplitude recipe. The source cutoff remains exactly `U^t`. -/
def physicalDetectionSpikes (U a t lam : ℝ) (u : FrequencyRow K S)
    (l : TerminalLabel U) (β ν : ℝ) : Prop :=
  let χ := canonicalDetectorCharacter K ψ S P E l.1 u
  U ^ ((2 * a - 1) * dyadicLength U l.2.1 - lam) ≤
    ‖inverseDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
      cutoffProfile (U ^ t) U l.2.1 β ν‖ ^ 2 ∧
  U ^ ((2 * a - 1) * dyadicLength U l.2.2 - lam) ≤
    ‖plainDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
      U l.2.2 β ν‖ ^ 2

variable {K S P E ψ}

/-- No new finite choice is introduced after saturation. -/
def CanonicalDyadicDetection.toTerminalLabel
    {u : FrequencyRow K S} {U a t η τ T : ℝ} {N : ℕ}
    (d : CanonicalDyadicDetection K S P E ψ u U a t η τ T N) : TerminalLabel U :=
  (d.presentation, ⟨d.inverseIndex, Nat.lt_succ_of_le d.inverseIndex_le⟩,
    ⟨d.plainIndex, Nat.lt_succ_of_le d.plainIndex_le⟩)

/-- The proved local saturation losses may be weakened to the one common
cover loss, without changing either factor or the common frequency. -/
theorem CanonicalDyadicDetection.spikes
    {u : FrequencyRow K S} {U a t η τ T lam : ℝ} {N : ℕ}
    (d : CanonicalDyadicDetection K S P E ψ u U a t η τ T N)
    (hU : 1 ≤ U) (hloss : 2 * η ≤ lam) :
    physicalDetectionSpikes K S P E ψ U a t lam u d.toTerminalLabel
      d.zero.re (2 * Real.pi * d.fourier - d.zero.im) := by
  have hsat := d.saturation
  dsimp only at hsat
  dsimp only [physicalDetectionSpikes, CanonicalDyadicDetection.toTerminalLabel]
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hU
      (sub_le_sub_left hloss _)).trans hsat.2.2.2.1
  · exact (Real.rpow_le_rpow_of_exponent_le hU
      (sub_le_sub_left hloss _)).trans hsat.2.2.2.2.1

variable (K S P E ψ)

/-- Assemble every genuine local detector into one finite label choice and
one pair of ideal-indexed parameter maps for the fixed sector. The bounds
hold for all source exponents, including those outside `[1,3/2]`; the actual
spike and label geometry are required only on that interval.

`hlength` is the numerical output of `exists_terminal_label_support` at its
common threshold. The final physical endpoint supplies `hdetect` from
`exists_physical_row_detection`, so no detector hypothesis is left there. -/
theorem exists_physical_detection_parameters
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (hsector : ∀ u ∈ rows, u.sector = sector)
    (U a η τ T lam : ℝ) (N : ℕ)
    (hU : 1 < U) (ha : 51 / 100 ≤ a) (hT : 0 ≤ T) (hloss : 2 * η ≤ lam)
    (hlength : ∀ t : ℝ, ∀ l : TerminalLabel U,
      (2 : ℝ) ^ (l.2.1 : ℕ) < 4 * U ^ t →
      U ^ t / 8 < (2 : ℝ) ^ (l.2.1 : ℕ) * (2 : ℝ) ^ (l.2.2 : ℕ) →
      terminalLabelValid U t lam l)
    (hdetect : ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 → ∀ u ∈ rows,
      Nonempty (CanonicalDyadicDetection K S P E ψ u U a t η τ T N)) :
    ∃ choice : ℝ → FrequencyRow K S → TerminalLabel U,
    ∃ β ν : ℝ → NonzeroIdeal K → ℝ,
      (∀ t I, |β t I| ≤ 1) ∧
      (∀ t I, |ν t I| ≤ 3 * ((N : ℝ) + 1) * T) ∧
      (∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 → ∀ u ∈ rows,
        terminalLabelValid U t lam (choice t u) ∧
        physicalDetectionSpikes K S P E ψ U a t lam u (choice t u)
          (β t u.ideal.val) (ν t u.ideal.val)) := by
  have hC : 0 < 3 * ((N : ℝ) + 1) := by positivity
  have hexists (t : ℝ) :
      ∃ choice : FrequencyRow K S → TerminalLabel U,
      ∃ β ν : NonzeroIdeal K → ℝ,
        (∀ I, |β I| ≤ 1) ∧ (∀ I, |ν I| ≤ 3 * ((N : ℝ) + 1) * T) ∧
        (1 ≤ t → t ≤ 3 / 2 → ∀ u ∈ rows,
          terminalLabelValid U t lam (choice u) ∧
          physicalDetectionSpikes K S P E ψ U a t lam u (choice u)
            (β u.ideal.val) (ν u.ideal.val)) := by
    by_cases ht : 1 ≤ t ∧ t ≤ 3 / 2
    · let good : FrequencyRow K S → TerminalLabel U → Prop := fun u l =>
        ∃ β ν : ℝ, |β| ≤ 1 ∧ |ν| ≤ 3 * ((N : ℝ) + 1) * T ∧
          terminalLabelValid U t lam l ∧ physicalDetectionSpikes K S P E ψ U a t lam u l β ν
      have hlocal : ∀ u ∈ rows, ∃ l, good u l := by
        intro u hu
        let d := Classical.choice (hdetect t ht.1 ht.2 u hu)
        have hβ : |d.zero.re| ≤ 1 := by
          rw [abs_of_nonneg (by linarith [d.zero_lower])]
          exact d.zero_upper
        have hvalid : terminalLabelValid U t lam d.toTerminalLabel :=
          hlength t d.toTerminalLabel d.source_support.1 d.source_support.2.1
        exact ⟨d.toTerminalLabel, d.zero.re, 2 * Real.pi * d.fourier - d.zero.im,
          hβ, d.frequency_bound, hvalid, d.spikes hU.le hloss⟩
      let choice := chooseTerminalLabel U rows good hlocal
      have hchosen : ∀ u ∈ rows, good u (choice u) :=
        chooseTerminalLabel_spec U rows good hlocal
      obtain ⟨β, ν, hβ, hν, hactual⟩ := assemble_terminal_raw_parameters_on_sector
        (frequencyRowIdealSectorEmbedding (K := K) (S := S)) sector rows hsector
        (3 * ((N : ℝ) + 1)) T hC hT
        (fun u β ν => terminalLabelValid U t lam (choice u) ∧
          physicalDetectionSpikes K S P E ψ U a t lam u (choice u) β ν) hchosen
      exact ⟨choice, β, ν, hβ, hν, fun _ _ => hactual⟩
    · refine ⟨fun _ => defaultTerminalLabel U, fun _ => 0, fun _ => 0,
        ?_, ?_, ?_⟩
      · intro I
        norm_num
      · intro I
        simpa only [abs_zero] using mul_nonneg hC.le hT
      · intro ht₁ ht₂
        exact (ht ⟨ht₁, ht₂⟩).elim
  choose choice β ν hβ hν hactual using hexists
  refine ⟨(fun t u => if 1 ≤ t ∧ t ≤ 3 / 2 then choice t u else defaultTerminalLabel U),
    (fun t I => if 1 ≤ t ∧ t ≤ 3 / 2 then β t I else 0),
    (fun t I => if 1 ≤ t ∧ t ≤ 3 / 2 then ν t I else 0), ?_, ?_, ?_⟩
  · intro t I
    dsimp only
    split_ifs with ht
    · exact hβ t I
    · norm_num
  · intro t I
    dsimp only
    split_ifs with ht
    · exact hν t I
    · simpa only [abs_zero] using mul_nonneg hC.le hT
  · intro t ht₁ ht₂ u hu
    simpa only [if_pos (And.intro ht₁ ht₂)] using hactual t ht₁ ht₂ u hu

end Expansion.Project

#print axioms Expansion.Project.CanonicalDyadicDetection.spikes
#print axioms Expansion.Project.exists_physical_detection_parameters
