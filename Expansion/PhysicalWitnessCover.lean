import Expansion.CanonicalAmplitudeCover
import Expansion.PhysicalDetectionParameters

/-!
# Actual physical zero bins produce the repository's finite WitnessCover

This is the complete detector-to-recipe endpoint: no terminal source,
polynomial spike, norm-twist exclusion, conductor bound, infinity-type
identification, or pointwise detector conclusion is an input. Those are
proved from the original arithmetic row and buffered zero-bin predicates.

The actual RecipeAmplitudeData is constructed with the same physical
point, amplitude data, complete ideal mask, two character presentations,
cutoff U^t and normalized frequency used by every moment model. Its
continuous row parameters satisfy the existing six-dimensional moment box.
The separate physical integral and amplitude-size estimates are not
claimed by this witness-cover theorem.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ω ψ : HeckeCharacter K)
variable (g : PrimeWindowGeometry)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)

/-- Internal detector losses and the count constant are fixed before the
finite height multiplicity N and before tau.
A single scale threshold then works for every shell, bin, height index,
sector, physical point, source exponent and all original rows in it. -/
theorem exists_physical_witness_cover
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ e ε ceiling k : ℝ,
      0 < e ∧ e < 1 / 1000 ∧ 0 < ε ∧ 0 < ceiling ∧ 0 < k ∧
      ∀ N : ℕ, ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
          ∀ d a : ℝ, 1 / 16 ≤ d → d ≤ 1 → 51 / 100 ≤ a →
          ∀ h : ℕ, h ≤ N → ∀ sector : SixthUnitClasses K S,
          ∀ rows : Finset (FrequencyRow K S),
            (∀ u ∈ rows, Z ^ d < frequencyRowNorm K S u) →
            (∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * Z ^ d) →
            (∀ u ∈ rows, u.sector = sector) →
            (∀ u ∈ rows, rowZeroAbove K S ψ {1} P E u
              (ExpansionInterfaces.selectedHeight h (Z ^ τ)) a) →
            (∀ u ∈ rows, rowZeroBelow K S ψ {1} P E u
              (ExpansionInterfaces.upperHeight h (Z ^ τ)) (a + 2 * e)) →
            ∀ p : Fin 3 → ℝ, ‖p‖ ≤ Z ^ τ → ∀ amplitude : Fin g.slots → ℝ,
            ∃ A : RecipeAmplitudeData K S ψ g
              (scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower slotCoefficient
                (3 * ((N : ℝ) + 1))),
              A.candidates = rows ∧ A.sector = sector ∧ A.physical = p ∧
              A.amplitude = amplitude ∧ A.rows (Z ^ d) = rows ∧
              ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
                WitnessCover (A.toAmplitude (P := P) (R := E.rows) (ω := ω)
                  Z (Z ^ τ) (Z ^ d)) t (2 * a - 1) (Z ^ d) lam k ∧
                ∀ j : Fin (A.witnessCount t),
                  ‖(A.witness t j).heights p t (Z ^ τ)‖ = Z ^ τ ∧
                  (∀ I : NonzeroIdeal K, ‖(A.witness t j).realShifts I‖ ≤ 8) ∧
                  (∀ I : NonzeroIdeal K, ‖(A.witness t j).imagShifts I‖ ≤
                    1 + ‖(A.witness t j).heights p t (Z ^ τ)‖) := by
  let η : ℝ := lam / 1000
  have hη : 0 < η := by dsimp [η]; positivity
  have hloss : 2 * η ≤ lam := by dsimp [η]; linarith
  obtain ⟨e, ε, ceiling, he, heSmall, hε, hceiling, hphysical⟩ :=
    exists_physical_row_detection K S P E ψ hcomplex η hη
  obtain ⟨k, hk, hcount⟩ := terminalLabelCount_subpower lam hlam
  obtain ⟨Ulabel, hUlabel, hlabel⟩ := exists_terminal_label_support lam hlam
  obtain ⟨Zlabel, hZlabel⟩ := (tendsto_atTop_atTop.mp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16))) Ulabel
  refine ⟨e, ε, ceiling, k, he, heSmall, hε, hceiling, hk, ?_⟩
  intro N τ hτ hτc
  obtain ⟨Zphysical, hZphysical, hdetect⟩ := hphysical N τ hτ hτc
  refine ⟨max Zphysical Zlabel, hZphysical.trans (le_max_left _ _), ?_⟩
  intro Z hZ d a hd hd' ha h hh sector rows hlower hnorm hsector habove hbelow
    p hp amplitude
  have hZphys : Zphysical ≤ Z := (le_max_left _ _).trans hZ
  have hZtwo : 2 ≤ Z := hZphysical.trans hZphys
  have hZone : 1 ≤ Z := by linarith
  have hUlabel' : Ulabel ≤ Z ^ d :=
    (hZlabel Z ((le_max_right _ _).trans hZ)).trans
      (Real.rpow_le_rpow_of_exponent_le hZone hd)
  have hU : 1 < Z ^ d := by linarith [hUlabel.trans hUlabel']
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZone hτ.le
  have hC : 0 < 3 * ((N : ℝ) + 1) := by positivity
  have hlocal : ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 → ∀ u ∈ rows,
      Nonempty (CanonicalDyadicDetection K S P E ψ u (Z ^ d) a t η τ (Z ^ τ) N) := by
    intro t ht ht' u hu
    exact hdetect Z hZphys d t a hd hd' ht ht' ha h hh u
      (hlower u hu) (hnorm u hu) (habove u hu) (hbelow u hu)
  obtain ⟨choice, β, ν, hβ, hν, hactual⟩ := exists_physical_detection_parameters
    K S P E ψ rows sector hsector (Z ^ d) a η τ (Z ^ τ) lam N hU ha
    (zero_le_one.trans hT) hloss (hlabel (Z ^ d) hUlabel') hlocal
  let A := canonicalAmplitudeRecipe K ψ g slotTime slotPower slotCoefficient S
    rows sector p amplitude (3 * ((N : ℝ) + 1)) (Z ^ d) lam choice β ν
  have hrows : A.rows (Z ^ d) = rows := canonicalAmplitudeRecipe_rows
    K ψ g slotTime slotPower slotCoefficient S rows sector p amplitude
      (3 * ((N : ℝ) + 1)) (Z ^ d) lam choice β ν (zero_lt_one.trans hU).le hnorm hsector
  refine ⟨A, rfl, rfl, rfl, rfl, hrows, ?_⟩
  intro t ht ht'
  refine ⟨?_, ?_⟩
  · exact canonicalAmplitudeRecipe_witnessCover K ψ g slotTime slotPower slotCoefficient
      S P E ω rows sector p amplitude (3 * ((N : ℝ) + 1)) (Z ^ d) lam a Z (Z ^ τ) k
      hC hU hlam.le choice β ν hnorm hsector (hcount (Z ^ d) hU.le) t (by linarith)
      (fun u hu => (hactual t ht ht' u hu).1)
      (fun u hu => (hactual t ht ht' u hu).2)
  · intro j
    let l := (encodeTerminalLabel (Z ^ d)).symm j
    refine ⟨(A.witness t j).heights_norm_eq p t (Z ^ τ) hT hp ⟨ht, ht'⟩, ?_, ?_⟩
    · exact scaledCanonicalRecipeWitness_realShifts_bound K ψ g cutoffProfile
        slotTime slotPower slotCoefficient (3 * ((N : ℝ) + 1)) (Z ^ d)
        l.2.1 l.2.2 l.1 (β t) (ν t) (fun I => (hβ t I).trans (by norm_num))
    · exact scaledCanonicalRecipeWitness_imagShifts_bound K ψ g cutoffProfile
        slotTime slotPower slotCoefficient (3 * ((N : ℝ) + 1)) hC (Z ^ d)
        l.2.1 l.2.2 l.1 (β t) (ν t) p t (Z ^ τ) (zero_le_one.trans hT) (hν t)

end Expansion.Project

#print axioms Expansion.Project.exists_physical_witness_cover
