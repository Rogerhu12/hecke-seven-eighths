import Expansion.ActualRecipePolynomials
import Expansion.ActualTerminalSaturation
import Expansion.CanonicalDetectorCharacters
import HeckeSkeleton.ExpansionModels.SourceRecipeNormalization

/-!
# A concrete canonical recipe for the actual detector factors

There are exactly the two original permitted arithmetic presentations.
Both annular tests are the literal dyadic profile, the cutoff is unchanged,
and the frequency scale in this algebraic constructor is one. Physical
slot data are ordinary inputs shared by every witness; no calibration,
saturation, or admissibility conclusion is accepted as data.

The real part and the one common frequency occupy coordinate zero in the
existing six-dimensional rowwise parameter maps. The identities below
connect the named recipe polynomials and witness values to the same raw
factors extracted from the actual ideal source.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.ActualRecipePolynomials Expansion.ActualTerminalSaturation
open Expansion.Dyadic
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
variable (V : ℝ → ℂ)
variable (slotTime : Fin g.slots → (Fin 3 → ℝ) → ℝ)
variable (slotPower : Fin g.slots → (Fin 3 → ℝ) → ℂ)
variable (slotCoefficient : Fin g.slots → HeckeCharacter K)

/-- All recipe fields are actual data from the source and physical slots. -/
def canonicalRecipeFamily : RecipeFamily K ψ g where
  presentationCount := 2
  presentationCount_pos := by norm_num
  presentation := canonicalDetectorPresentation K ψ
  inverseAnnular := dyadicAnnularIdealTest K
  plainAnnular := dyadicAnnularIdealTest K
  cutoff := V
  frequencyScale := 1
  slotTime := slotTime
  slotPower := slotPower
  slotCoefficient := slotCoefficient

/-- Only coordinate zero stores a varying detector parameter. -/
def coordinateZeroParameters (f : NonzeroIdeal K → ℝ) : NonzeroIdeal K → RecipeVector :=
  fun u j => if j = 0 then f u else 0

@[simp] theorem coordinateZeroParameters_zero (f : NonzeroIdeal K → ℝ) (u : NonzeroIdeal K) :
    coordinateZeroParameters K f u 0 = f u := by simp [coordinateZeroParameters]

/-- The same dyadic pair, presentation, real part and frequency determine
both witnesses. No separately assigned polynomial value is stored. -/
def canonicalRecipeWitness (U : ℝ) (j k : ℕ) (i : Fin 2)
    (β ν : NonzeroIdeal K → ℝ) :
    RecipeWitnessData K ψ g (canonicalRecipeFamily K ψ g V slotTime slotPower slotCoefficient) where
  inverseLength := dyadicLength U j
  plainLength := dyadicLength U k
  presentation := i
  realShifts := coordinateZeroParameters K β
  imagShifts := coordinateZeroParameters K ν

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P)

/-- The named inverse detector polynomial of this concrete recipe is the
unchanged raw inverse factor of the actual source, with `Dsource = U^t`. -/
theorem canonicalRecipeWitness_inverseDetectorPolynomial
    (hV : ContDiff ℝ ∞ V) (U t : ℝ) (j k : ℕ) (i : Fin 2)
    (β ν : NonzeroIdeal K → ℝ) (u : FrequencyRow K S)
    (hU : 1 < U) (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    (canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
        inverseDetectorPolynomial (R := E.rows) t U u =
      inverseDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) V (U ^ t) U j (β u.ideal.val) (ν u.ideal.val) := by
  have hscale : (2 : ℝ) ^ j ≤ 6 * U ^ (21 : ℕ) :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans
      (two_pow_terminal_dyadicCap_le (one_le_pow₀ hU.le))
  have hid := actual_inverse_normalized_eq_test K u.ideal.val
    (canonicalDetectorCharacter K ψ S P E i u) (originalDeletedPrimes K S u.ideal.val)
    V hV (U ^ (21 : ℕ)) (U ^ t) ((2 : ℝ) ^ j) (β u.ideal.val) (ν u.ideal.val)
    (by positivity) (by positivity) hscale
  simpa only [RecipeWitnessData.inverseDetectorPolynomial, canonicalRecipeWitness,
    canonicalRecipeFamily, coordinateZeroParameters_zero, one_mul,
    canonicalDetectorPresentation, canonicalDetectorCharacter, zpow_one,
    rpow_dyadicLength hU, inverseDetectorValue] using hid.symm

/-- The plain polynomial uses the same canonical character, real part and
frequency as the inverse factor, with its own dyadic length. -/
theorem canonicalRecipeWitness_plainDetectorPolynomial
    (U : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hk : k ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    (canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
        plainDetectorPolynomial (R := E.rows) U u =
      plainDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) U k (β u.ideal.val) (ν u.ideal.val) := by
  have hscale : (2 : ℝ) ^ k ≤ 6 * U ^ (21 : ℕ) :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans
      (two_pow_terminal_dyadicCap_le (one_le_pow₀ hU.le))
  have hid := actual_plain_normalized_eq_test K u.ideal.val
    (canonicalDetectorCharacter K ψ S P E i u) (originalDeletedPrimes K S u.ideal.val)
    (U ^ (21 : ℕ)) ((2 : ℝ) ^ k) (β u.ideal.val) (ν u.ideal.val)
    (by positivity) hscale
  simpa only [RecipeWitnessData.plainDetectorPolynomial, canonicalRecipeWitness,
    canonicalRecipeFamily, coordinateZeroParameters_zero, one_mul,
    canonicalDetectorPresentation, canonicalDetectorCharacter,
    rpow_dyadicLength hU, plainDetectorValue] using hid.symm

/-- The actual named source witness value inherits the same finite-sum
identity, including every physical-model parameter. -/
theorem canonicalRecipeWitness_inverseValue
    (ω : HeckeCharacter K) (hV : ContDiff ℝ ∞ V)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (U t T : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    ((canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
        toWitness (P := P) (R := E.rows) (ω := ω) rows p t T U).inverseValue u =
      inverseDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) V (U ^ t) U j (β u.ideal.val) (ν u.ideal.val) := by
  let w := canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν
  change inversePolynomial (w.model (P := P) (R := E.rows) (ω := ω) p t T U u.sector)
    u.ideal.val (U ^ w.inverseLength) 0 = _
  rw [w.inversePolynomial_eq_normalized (P := P) (R := E.rows) (ω := ω)
    p t T U u (zero_lt_one.trans hU)]
  exact canonicalRecipeWitness_inverseDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E hV U t j k i β ν u hU hj

/-- The named plain source witness is the second raw source factor. -/
theorem canonicalRecipeWitness_plainValue
    (ω : HeckeCharacter K) (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (U t T : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hk : k ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    ((canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
        toWitness (P := P) (R := E.rows) (ω := ω) rows p t T U).plainValue u =
      plainDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) U k (β u.ideal.val) (ν u.ideal.val) := by
  let w := canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν
  let F := canonicalRecipeFamily K ψ g V slotTime slotPower slotCoefficient
  change plainPolynomial (w.model (P := P) (R := E.rows) (ω := ω) p t T U u.sector)
    (F.plainTest K ψ g w.realShifts w.imagShifts) u.ideal.val (U ^ w.plainLength) 0 = _
  rw [w.plainPolynomial_eq_normalized (P := P) (R := E.rows) (ω := ω)
    p t T U u (zero_lt_one.trans hU)]
  exact canonicalRecipeWitness_plainDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E U j k i β ν u hU hk

/-- A fixed frequency normalization for the same two-presentation family.
Only the stored parameter convention changes; the physical frequency and
both finite polynomials remain unchanged. -/
def scaledCanonicalRecipeFamily (C : ℝ) : RecipeFamily K ψ g :=
  { canonicalRecipeFamily K ψ g V slotTime slotPower slotCoefficient with frequencyScale := C }

/-- Store the true frequency divided by the same fixed scale used by the
family. This uses the repository's established height-normalized maps. -/
def scaledCanonicalRecipeWitness (C U : ℝ) (j k : ℕ) (i : Fin 2)
    (β ν : NonzeroIdeal K → ℝ) :
    RecipeWitnessData K ψ g
      (scaledCanonicalRecipeFamily K ψ g V slotTime slotPower slotCoefficient C) where
  inverseLength := dyadicLength U j
  plainLength := dyadicLength U k
  presentation := i
  realShifts := coordinateZeroParameters K β
  imagShifts := _root_.ExpansionRecipe.normalizedImaginaryParameters ν C

/-- Fixed positive rescaling reconstructs the original inverse frequency
inside the actual profile, before any polynomial estimate is considered. -/
theorem scaledCanonicalRecipeWitness_inverseDetectorPolynomial
    (C : ℝ) (hC : 0 < C) (hV : ContDiff ℝ ∞ V)
    (U t : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    (scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
        inverseDetectorPolynomial (R := E.rows) t U u =
      inverseDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) V (U ^ t) U j (β u.ideal.val) (ν u.ideal.val) := by
  have heq :
      (scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
          inverseDetectorPolynomial (R := E.rows) t U u =
      (canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
          inverseDetectorPolynomial (R := E.rows) t U u := by
    simp only [RecipeWitnessData.inverseDetectorPolynomial, scaledCanonicalRecipeWitness,
      scaledCanonicalRecipeFamily, canonicalRecipeWitness, canonicalRecipeFamily,
      coordinateZeroParameters_zero,
      _root_.ExpansionRecipe.normalizedImaginaryParameters_exact ν C hC, one_mul]
  exact heq.trans (canonicalRecipeWitness_inverseDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E hV U t j k i β ν u hU hj)

/-- The second factor uses exactly the same restored common frequency. -/
theorem scaledCanonicalRecipeWitness_plainDetectorPolynomial
    (C : ℝ) (hC : 0 < C) (U : ℝ) (j k : ℕ) (i : Fin 2)
    (β ν : NonzeroIdeal K → ℝ) (u : FrequencyRow K S)
    (hU : 1 < U) (hk : k ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    (scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
        plainDetectorPolynomial (R := E.rows) U u =
      plainDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) U k (β u.ideal.val) (ν u.ideal.val) := by
  have heq :
      (scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
          plainDetectorPolynomial (R := E.rows) U u =
      (canonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient U j k i β ν).
          plainDetectorPolynomial (R := E.rows) U u := by
    simp only [RecipeWitnessData.plainDetectorPolynomial, scaledCanonicalRecipeWitness,
      scaledCanonicalRecipeFamily, canonicalRecipeWitness, canonicalRecipeFamily,
      coordinateZeroParameters_zero,
      _root_.ExpansionRecipe.normalizedImaginaryParameters_exact ν C hC, one_mul]
  exact heq.trans (canonicalRecipeWitness_plainDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E U j k i β ν u hU hk)

/-- Exact named inverse-witness identity for the normalized parameter family. -/
theorem scaledCanonicalRecipeWitness_inverseValue
    (C : ℝ) (hC : 0 < C) (ω : HeckeCharacter K) (hV : ContDiff ℝ ∞ V)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (U t T : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hj : j ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    ((scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
        toWitness (P := P) (R := E.rows) (ω := ω) rows p t T U).inverseValue u =
      inverseDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) V (U ^ t) U j (β u.ideal.val) (ν u.ideal.val) := by
  let w := scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν
  change inversePolynomial (w.model (P := P) (R := E.rows) (ω := ω) p t T U u.sector)
    u.ideal.val (U ^ w.inverseLength) 0 = _
  rw [w.inversePolynomial_eq_normalized (P := P) (R := E.rows) (ω := ω)
    p t T U u (zero_lt_one.trans hU)]
  exact scaledCanonicalRecipeWitness_inverseDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E C hC hV U t j k i β ν u hU hj

/-- Exact named plain-witness identity for the same normalized parameters. -/
theorem scaledCanonicalRecipeWitness_plainValue
    (C : ℝ) (hC : 0 < C) (ω : HeckeCharacter K)
    (rows : Finset (FrequencyRow K S)) (p : Fin 3 → ℝ)
    (U t T : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (u : FrequencyRow K S) (hU : 1 < U) (hk : k ≤ dyadicCap (3 * U ^ (21 : ℕ))) :
    ((scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν).
        toWitness (P := P) (R := E.rows) (ω := ω) rows p t T U).plainValue u =
      plainDetectorValue K (canonicalDetectorCharacter K ψ S P E i u)
        (originalDeletedPrimes K S u.ideal.val) U k (β u.ideal.val) (ν u.ideal.val) := by
  let w := scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν
  let F := scaledCanonicalRecipeFamily K ψ g V slotTime slotPower slotCoefficient C
  change plainPolynomial (w.model (P := P) (R := E.rows) (ω := ω) p t T U u.sector)
    (F.plainTest K ψ g w.realShifts w.imagShifts) u.ideal.val (U ^ w.plainLength) 0 = _
  rw [w.plainPolynomial_eq_normalized (P := P) (R := E.rows) (ω := ω)
    p t T U u (zero_lt_one.trans hU)]
  exact scaledCanonicalRecipeWitness_plainDetectorPolynomial K ψ g V slotTime slotPower
    slotCoefficient S P E C hC U j k i β ν u hU hk

/-- The fixed rescaling is exactly what the existing moment-height box
requires. The stored global height remains the physical `T`. -/
theorem scaledCanonicalRecipeWitness_imagShifts_bound
    (C : ℝ) (hC : 0 < C) (U : ℝ) (j k : ℕ) (i : Fin 2)
    (β ν : NonzeroIdeal K → ℝ) (p : Fin 3 → ℝ) (t T : ℝ)
    (hT : 0 ≤ T) (hν : ∀ u, |ν u| ≤ C * T) :
    let w := scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν
    ∀ u, ‖w.imagShifts u‖ ≤ 1 + ‖w.heights p t T‖ := by
  let w := scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν
  exact _root_.ExpansionRecipe.normalizedImaginaryParameters_bound ν C hC (w.heights p t T)
    hT (by rfl) hν

/-- A coordinate-zero real-part map satisfies the original uniform real
parameter bound, without introducing a larger parameter dimension. -/
theorem scaledCanonicalRecipeWitness_realShifts_bound
    (C U : ℝ) (j k : ℕ) (i : Fin 2) (β ν : NonzeroIdeal K → ℝ)
    (hβ : ∀ u, |β u| ≤ 8) :
    let w := scaledCanonicalRecipeWitness K ψ g V slotTime slotPower slotCoefficient C U j k i β ν
    ∀ u, ‖w.realShifts u‖ ≤ 8 := by
  dsimp only
  intro u
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)).mpr
  intro q
  by_cases hq : q = 0
  · simpa only [scaledCanonicalRecipeWitness, coordinateZeroParameters, if_pos hq,
      Real.norm_eq_abs] using hβ u
  · simp only [scaledCanonicalRecipeWitness, coordinateZeroParameters, if_neg hq, norm_zero]
    norm_num

end Expansion.Project

#print axioms Expansion.Project.canonicalRecipeFamily
#print axioms Expansion.Project.canonicalRecipeWitness_inverseValue
#print axioms Expansion.Project.canonicalRecipeWitness_plainValue

#print axioms Expansion.Project.scaledCanonicalRecipeWitness_inverseValue
#print axioms Expansion.Project.scaledCanonicalRecipeWitness_plainValue
#print axioms Expansion.Project.scaledCanonicalRecipeWitness_imagShifts_bound
