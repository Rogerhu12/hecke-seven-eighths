import Expansion.ActualCanonicalRecipe
import Expansion.CanonicalCutoff
import Expansion.FiniteTerminalLabels
import Expansion.PhysicalRowSupport

/-!
# A literal canonical amplitude recipe and its finite witness cover

The source and moment values are both evaluated from the same concrete
RecipeWitnessData. Discrete labels retain the two actual characters and
two terminal scales; the original cutoff remains U^t. Invalid unused
labels get admissible dummy lengths but never assert a polynomial spike.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.ActualTerminalSaturation Expansion.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)

def terminalRecipeWitness (C U t lam : ℝ) (l : TerminalLabel U)
    (β ν : NonzeroIdeal K → ℝ) :
    RecipeWitnessData K ψ g
      (scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower slotCoefficient C) :=
  { scaledCanonicalRecipeWitness K ψ g cutoffProfile slotTime slotPower slotCoefficient
      C U l.2.1 l.2.2 l.1 β ν with
    inverseLength := terminalLabelInverseLength U t lam l
    plainLength := terminalLabelPlainLength U t lam l }

theorem terminalRecipeWitness_eq_scaled (C U t lam : ℝ) (l : TerminalLabel U)
    (β ν : NonzeroIdeal K → ℝ) (hl : terminalLabelValid U t lam l) :
    terminalRecipeWitness K ψ g slotTime slotPower slotCoefficient C U t lam l β ν =
      scaledCanonicalRecipeWitness K ψ g cutoffProfile slotTime slotPower slotCoefficient
        C U l.2.1 l.2.2 l.1 β ν := by
  simp only [terminalRecipeWitness, terminalLabelInverseLength, terminalLabelPlainLength, if_pos hl]
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P) (ω : HeckeCharacter K)

def canonicalAmplitudeRecipe (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ)
    (C U lam : ℝ) (choice : ℝ → FrequencyRow K S → TerminalLabel U)
    (β ν : ℝ → NonzeroIdeal K → ℝ) :
    RecipeAmplitudeData K S ψ g
      (scaledCanonicalRecipeFamily K ψ g cutoffProfile slotTime slotPower slotCoefficient C) where
  candidates := rows
  sector := sector
  physical := p
  amplitude := amplitude
  witnessCount _ := terminalLabelCount U
  witnessChoice t u := encodeTerminalLabel U (choice t u)
  witness t j := terminalRecipeWitness K ψ g slotTime slotPower slotCoefficient C U t lam
    ((encodeTerminalLabel U).symm j) (β t) (ν t)

theorem canonicalAmplitudeRecipe_rows (rows : Finset (FrequencyRow K S))
    (sector : SixthUnitClasses K S) (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ)
    (C U lam : ℝ) (choice : ℝ → FrequencyRow K S → TerminalLabel U)
    (β ν : ℝ → NonzeroIdeal K → ℝ) (hU : 0 ≤ U)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * U)
    (hsector : ∀ u ∈ rows, u.sector = sector) :
    (canonicalAmplitudeRecipe K ψ g slotTime slotPower slotCoefficient S
      rows sector p amplitude C U lam choice β ν).rows U = rows := by
  ext u
  simp only [RecipeAmplitudeData.rows, canonicalAmplitudeRecipe, Finset.mem_filter]
  constructor
  · exact fun h => h.2.1
  · intro hu
    exact ⟨(mem_frequencyRows_iff K S (2 * U) (by positivity) u).mpr (hnorm u hu),
      hu, hsector u hu⟩

/-- All finite-cover conclusions are proved against the actual repository
WitnessCover definition and its actual polynomial projections. The local
parameter estimates are discharged by PhysicalRowDetection in the final
physical specialization. -/
theorem canonicalAmplitudeRecipe_witnessCover
    (rows : Finset (FrequencyRow K S)) (sector : SixthUnitClasses K S)
    (p : Fin 3 → ℝ) (amplitude : Fin g.slots → ℝ)
    (C U lam a Z T k : ℝ) (hC : 0 < C) (hU : 1 < U) (hlam : 0 ≤ lam)
    (choice : ℝ → FrequencyRow K S → TerminalLabel U)
    (β ν : ℝ → NonzeroIdeal K → ℝ)
    (hnorm : ∀ u ∈ rows, frequencyRowNorm K S u ≤ 2 * U)
    (hsector : ∀ u ∈ rows, u.sector = sector)
    (hcount : (terminalLabelCount U : ℝ) ≤ k * U ^ lam)
    (t : ℝ) (ht : 0 ≤ t)
    (hvalid : ∀ u ∈ rows, terminalLabelValid U t lam (choice t u))
    (hspikes : ∀ u ∈ rows,
      let l := choice t u
      let χ := canonicalDetectorCharacter K ψ S P E l.1 u
      U ^ ((2 * a - 1) * dyadicLength U l.2.1 - lam) ≤
        ‖inverseDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
          cutoffProfile (U ^ t) U l.2.1 (β t u.ideal.val) (ν t u.ideal.val)‖ ^ 2 ∧
      U ^ ((2 * a - 1) * dyadicLength U l.2.2 - lam) ≤
        ‖plainDetectorValue K χ (originalDeletedPrimes K S u.ideal.val)
          U l.2.2 (β t u.ideal.val) (ν t u.ideal.val)‖ ^ 2) :
    WitnessCover
      ((canonicalAmplitudeRecipe K ψ g slotTime slotPower slotCoefficient S
        rows sector p amplitude C U lam choice β ν).
          toAmplitude (P := P) (R := E.rows) (ω := ω) Z T U)
      t (2 * a - 1) U lam k := by
  let A := canonicalAmplitudeRecipe K ψ g slotTime slotPower slotCoefficient S
    rows sector p amplitude C U lam choice β ν
  have hrows : A.rows U = rows := canonicalAmplitudeRecipe_rows K ψ g slotTime slotPower
    slotCoefficient S rows sector p amplitude C U lam choice β ν
    (zero_lt_one.trans hU).le hnorm hsector
  refine ⟨hcount, ?_, ?_⟩
  · intro u hu
    refine ⟨encodeTerminalLabel U (choice t u), ?_⟩
    exact Finset.mem_filter.mpr ⟨hu, rfl⟩
  · intro j
    let l := (encodeTerminalLabel U).symm j
    have hlens := terminalLabel_lengths U t lam ht hlam l
    refine ⟨Finset.filter_subset _ _, hlens.1, hlens.2.1, hlens.2.2.1,
      hlens.2.2.2, ?_, ?_⟩
    · intro u hu
      obtain ⟨hur, heq⟩ := Finset.mem_filter.mp hu
      have hur' : u ∈ rows := hrows ▸ hur
      have hl : choice t u = l := by
        apply (encodeTerminalLabel U).injective
        exact heq.trans ((encodeTerminalLabel U).apply_symm_apply j).symm
      have hlvalid : terminalLabelValid U t lam l := hl ▸ hvalid u hur'
      have hinverse := (hspikes u hur').1
      rw [hl] at hinverse
      change U ^ ((2 * a - 1) * terminalLabelInverseLength U t lam l - lam) ≤
        ‖((terminalRecipeWitness K ψ g slotTime slotPower slotCoefficient C U t lam l (β t) (ν t)).
          toWitness (P := P) (R := E.rows) (ω := ω)
            ((A.rows U).filter fun v => A.witnessChoice t v = j) p t T U).inverseValue u‖ ^ 2
      rw [terminalRecipeWitness_eq_scaled K ψ g slotTime slotPower slotCoefficient
        C U t lam l (β t) (ν t) hlvalid,
        scaledCanonicalRecipeWitness_inverseValue K ψ g cutoffProfile slotTime slotPower
          slotCoefficient S P E C hC ω cutoffProfile_smooth _ p U t T l.2.1 l.2.2 l.1
          (β t) (ν t) u hU (Nat.le_of_lt_succ l.2.1.isLt)]
      simpa only [terminalLabelInverseLength, if_pos hlvalid] using hinverse
    · intro u hu
      obtain ⟨hur, heq⟩ := Finset.mem_filter.mp hu
      have hur' : u ∈ rows := hrows ▸ hur
      have hl : choice t u = l := by
        apply (encodeTerminalLabel U).injective
        exact heq.trans ((encodeTerminalLabel U).apply_symm_apply j).symm
      have hlvalid : terminalLabelValid U t lam l := hl ▸ hvalid u hur'
      have hplain := (hspikes u hur').2
      rw [hl] at hplain
      change U ^ ((2 * a - 1) * terminalLabelPlainLength U t lam l - lam) ≤
        ‖((terminalRecipeWitness K ψ g slotTime slotPower slotCoefficient C U t lam l (β t) (ν t)).
          toWitness (P := P) (R := E.rows) (ω := ω)
            ((A.rows U).filter fun v => A.witnessChoice t v = j) p t T U).plainValue u‖ ^ 2
      rw [terminalRecipeWitness_eq_scaled K ψ g slotTime slotPower slotCoefficient
        C U t lam l (β t) (ν t) hlvalid,
        scaledCanonicalRecipeWitness_plainValue K ψ g cutoffProfile slotTime slotPower
          slotCoefficient S P E C hC ω _ p U t T l.2.1 l.2.2 l.1
          (β t) (ν t) u hU (Nat.le_of_lt_succ l.2.2.isLt)]
      simpa only [terminalLabelPlainLength, if_pos hlvalid] using hplain

end Expansion.Project

#print axioms Expansion.Project.terminalRecipeWitness_eq_scaled
#print axioms Expansion.Project.canonicalAmplitudeRecipe_witnessCover
