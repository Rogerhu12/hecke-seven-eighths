import HeckeGeneral.Characters.LocalResidueCharacter
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! Finite residue transition maps and primitivity at the least conductor depth. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem natCard_localResidueRing (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (LocalResidueRing K v n) = residueCard K v ^ n := by
  rw [← Nat.card_congr (localResidueRingEquivGlobal K v n).toEquiv]
  exact cardQuot_pow_of_prime v.ne_bot

def localResidueTransition (v : HeightOneSpectrum (𝓞 K)) {n m : ℕ} (hmn : m ≤ n) :
    LocalResidueRing K v n →+* LocalResidueRing K v m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)

@[simp] theorem localResidueTransition_mk (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} (hmn : m ≤ n) (x : LocalIntegerRing K v) :
    localResidueTransition K v hmn (Ideal.Quotient.mk (localMaximalIdeal K v ^ n) x) =
      Ideal.Quotient.mk (localMaximalIdeal K v ^ m) x := Ideal.Quotient.factor_mk _ _

theorem localResidueTransition_surjective (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} (hmn : m ≤ n) : Function.Surjective (localResidueTransition K v hmn) :=
  Ideal.Quotient.factor_surjective _

def localResidueUnitTransition (v : HeightOneSpectrum (𝓞 K)) {n m : ℕ} (hmn : m ≤ n) :
    (LocalResidueRing K v n)ˣ →* (LocalResidueRing K v m)ˣ :=
  Units.map (localResidueTransition K v hmn).toMonoidHom

@[simp] theorem localResidueUnitTransition_reduction (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} (hmn : m ≤ n) (u : (LocalIntegerRing K v)ˣ) :
    localResidueUnitTransition K v hmn (localUnitReduction K v n u) =
      localUnitReduction K v m u := by
  apply Units.ext
  exact localResidueTransition_mk K v hmn u.val

theorem localResidueUnitTransition_surjective (v : HeightOneSpectrum (𝓞 K))
    {n m : ℕ} (hmn : m ≤ n) : Function.Surjective (localResidueUnitTransition K v hmn) := by
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v m y
  exact ⟨localUnitReduction K v n u, localResidueUnitTransition_reduction K v hmn u⟩

theorem localResidueUnitTransition_comp (v : HeightOneSpectrum (𝓞 K))
    {n m r : ℕ} (hmn : m ≤ n) (hrm : r ≤ m) :
    (localResidueUnitTransition K v hrm).comp (localResidueUnitTransition K v hmn) =
      localResidueUnitTransition K v (hrm.trans hmn) := by
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
  simp only [MonoidHom.comp_apply, localResidueUnitTransition_reduction]

@[simp] theorem localResidueUnitTransition_self (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localResidueUnitTransition K v (le_refl n) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
  exact localResidueUnitTransition_reduction K v (le_refl n) u

theorem localResidueCharacter_transition (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) {n m : ℕ} (hmn : m ≤ n)
    (hm : localConductorExponent K χ v ≤ m) :
    (localResidueCharacter K v χ m hm).comp (localResidueUnitTransition K v hmn) =
      localResidueCharacter K v χ n (hm.trans hmn) := by
  apply MonoidHom.ext
  intro y
  obtain ⟨u, rfl⟩ := localUnitReduction_surjective K v n y
  simp only [MonoidHom.comp_apply, localResidueUnitTransition_reduction,
    localResidueCharacter_reduction]

/-- The actual conductor is precisely the least residue level admitting descent. -/
theorem localConductorExponent_le_iff_residue_descent (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) (n : ℕ) :
    localConductorExponent K χ v ≤ n ↔
      ∃ ψ : (LocalResidueRing K v n)ˣ →* Circle,
        ∀ u, ψ (localUnitReduction K v n u) = localIntegralComponent K v χ u := by
  constructor
  · intro hn
    exact ⟨localResidueCharacter K v χ n hn, localResidueCharacter_reduction K v χ n hn⟩
  · rintro ⟨ψ, hψ⟩
    apply (localConductorExponent_le_iff K χ v n).mpr
    apply (trivialAtDepth_iff_principalUnits_le_ker K v χ n).mpr
    intro u hu
    change localIntegralComponent K v χ u = 1
    rw [← hψ u, show localUnitReduction K v n u = 1 from hu, map_one]

/-- A conductor-level residue character does not descend through any smaller level. -/
theorem conductorResidueCharacter_primitive (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) {n : ℕ} (hn : n < localConductorExponent K χ v) :
    ¬ ∃ ψ : (LocalResidueRing K v n)ˣ →* Circle,
      ψ.comp (localResidueUnitTransition K v hn.le) = conductorResidueCharacter K v χ := by
  rintro ⟨ψ, hψ⟩
  have hdesc : localConductorExponent K χ v ≤ n :=
    (localConductorExponent_le_iff_residue_descent K v χ n).mpr ⟨ψ, fun u => ?_⟩
  · exact (not_le_of_gt hn) hdesc
  · have hu := congrArg
      (fun f : (LocalResidueRing K v (localConductorExponent K χ v))ˣ →* Circle =>
        f (localUnitReduction K v (localConductorExponent K χ v) u)) hψ
    simpa only [MonoidHom.comp_apply, localResidueUnitTransition_reduction,
      conductorResidueCharacter_reduction] using hu

theorem principalUnits_index_bound (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card ((LocalIntegerRing K v)ˣ ⧸ principalUnits K v n) ≤ residueCard K v ^ n := by
  rw [Nat.card_congr (principalUnitsQuotientEquiv K v n).toEquiv,
    ← natCard_localResidueRing K v n]
  exact Nat.card_le_card_of_injective Units.val Units.val_injective

end HeckeGeneral.Characters
