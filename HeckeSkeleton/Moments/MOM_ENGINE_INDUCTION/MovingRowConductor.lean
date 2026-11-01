import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionConductor

/-!
# Actual moving complete-row characters cost their displayed support

An integer power does not increase a character's conductor depth.
Products have conductor depth bounded by the maximum, so any finite
number of moving characters sharing one displayed support can use one
copy of the fixed S-wild budget.  In particular neither the exponent
five nor the number of factors is charged to the moving norm exponent.

Every moving factor below is the literal complete-ideal row character
of an exterior ideal in an original unit sector.  The support premise
is divisibility of its genuine radical into a displayed ideal; it is
not a conductor or polynomial estimate.  The residual row remains the
original complete ideal u throughout.  The new canonical moving-row
recipe may instantiate these theorems once its exact fields are fixed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

private theorem primeExponents_le_of_nonzero_dvd
    (I J : NonzeroIdeal K) (h : I.val ∣ J.val) : primeExponents I ≤ primeExponents J := by
  obtain ⟨Q, hQ⟩ := h
  have hQzero : Q ≠ 0 := by
    intro hz
    apply nonZeroDivisors.coe_ne_zero J
    rw [hQ, hz, mul_zero]
  let quotient : NonzeroIdeal K := ⟨Q, mem_nonZeroDivisors_of_ne_zero hQzero⟩
  have hJ : J = I * quotient := Subtype.ext hQ
  rw [hJ, primeExponents_mul]
  intro p
  simp only [Finsupp.add_apply]
  exact Nat.le_add_right _ _

/-- No factor |e| is paid in the conductor of the actual integer power. -/
theorem finiteConductor_zpow_dvd (chi : HeckeCharacter K) (e : ℤ) :
    (finiteConductor K (chi ^ e)).val ∣ (finiteConductor K chi).val := by
  apply nonzeroIdeal_dvd_of_primeExponents_le K
  intro p
  simp only [primeExponents_finiteConductor, conductorExponents_apply]
  exact localConductorExponent_zpow_le K chi p e

/-- Two conductors contained in one actual modulus retain that modulus
under multiplication; the modulus is not multiplied by itself. -/
theorem finiteConductor_mul_dvd_common (chi psi : HeckeCharacter K)
    (modulus : NonzeroIdeal K)
    (hchi : (finiteConductor K chi).val ∣ modulus.val)
    (hpsi : (finiteConductor K psi).val ∣ modulus.val) :
    (finiteConductor K (chi * psi)).val ∣ modulus.val := by
  have hchiExp := primeExponents_le_of_nonzero_dvd (finiteConductor K chi) modulus hchi
  have hpsiExp := primeExponents_le_of_nonzero_dvd (finiteConductor K psi) modulus hpsi
  apply nonzeroIdeal_dvd_of_primeExponents_le K
  intro p
  have hc : localConductorExponent K chi p ≤ primeExponents modulus p := by
    simpa only [primeExponents_finiteConductor, conductorExponents_apply] using hchiExp p
  have hp : localConductorExponent K psi p ≤ primeExponents modulus p := by
    simpa only [primeExponents_finiteConductor, conductorExponents_apply] using hpsiExp p
  simpa only [primeExponents_finiteConductor, conductorExponents_apply] using
    (localConductorExponent_mul_le_max K chi psi p).trans (max_le hc hp)

theorem finiteConductor_prod_dvd_common {Index : Type*}
    (indices : Finset Index) (character : Index → HeckeCharacter K)
    (modulus : NonzeroIdeal K)
    (hcharacter : ∀ i ∈ indices, (finiteConductor K (character i)).val ∣ modulus.val) :
    (finiteConductor K (∏ i ∈ indices, character i)).val ∣ modulus.val := by
  revert hcharacter
  induction indices using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty]
    apply nonzeroIdeal_dvd_of_primeExponents_le K
    intro p
    simp only [primeExponents_finiteConductor, conductorExponents_apply,
      localConductorExponent_one]
    exact Nat.zero_le _
  | @insert i indices hi ih =>
    intro hcharacter
    rw [Finset.prod_insert hi]
    exact finiteConductor_mul_dvd_common _ _ modulus
      (hcharacter i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hcharacter j (Finset.mem_insert_of_mem hj)))

/-- The complete ideal's character only costs the radical of that
ideal, even when the row contains redundant sixth powers. -/
theorem completeRowCharacter_conductor_dvd_radical
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    (finiteConductor K (completeIdealRowCharacter K S probe rows sector u.val)).val ∣
      (sexticSConductorBudgetIdeal K S * nonzeroIdealRadical K u.val).val := by
  rw [completeIdealRowCharacter_exterior, rowCharacterInput_character_eq_arithmetic]
  have h := arithmeticRowCharacter_finiteConductor_dvd_SBudget_mul_radical
    K S probe (decomposedFrequencyRow K S u sector)
  have hradical :
      (nonzeroIdealRadical K (decomposedFrequencyRow K S u sector).ideal.val).val ∣
        (nonzeroIdealRadical K u.val).val := by
    apply Ideal.dvd_iff_le.mpr
    exact Ideal.radical_mono (Ideal.dvd_iff_le.mp (sixthPowerFreePart_dvd u.val))
  exact h.trans (by
    simpa only [Submonoid.coe_mul] using
      mul_dvd_mul (dvd_refl (sexticSConductorBudgetIdeal K S).val) hradical)

/-- All genuine moving factors use the same displayed support and one
fixed S budget, independently of their integer exponents or number. -/
theorem completeMovingCharacter_conductor_dvd {Index : Type*}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (indices : Finset Index) (factor : Index → ExteriorIdeal K S)
    (sector : Index → SixthUnitClasses K S) (exponent : Index → ℤ)
    (displayed : NonzeroIdeal K)
    (hsupport : ∀ i ∈ indices, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val) :
    (finiteConductor K (∏ i ∈ indices,
      completeIdealRowCharacter K S probe rows (sector i) (factor i).val ^ exponent i)).val ∣
        (sexticSConductorBudgetIdeal K S * displayed).val := by
  apply finiteConductor_prod_dvd_common
  intro i hi
  refine (finiteConductor_zpow_dvd _ _).trans
    ((completeRowCharacter_conductor_dvd_radical S probe rows (sector i) (factor i)).trans ?_)
  simpa only [Submonoid.coe_mul] using
    mul_dvd_mul (dvd_refl (sexticSConductorBudgetIdeal K S).val) (hsupport i hi)

/-- The residual ideal remains u, and the displayed moving support is
charged exactly once alongside it.  A fixed background is separate. -/
theorem completeMovingRowCharacter_conductor_dvd {Index : Type*}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (beta : HeckeCharacter K)
    (indices : Finset Index) (factor : Index → ExteriorIdeal K S)
    (factorSector : Index → SixthUnitClasses K S) (exponent : Index → ℤ)
    (displayed : NonzeroIdeal K)
    (hsupport : ∀ i ∈ indices, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val)
    (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    (finiteConductor K (beta * ((∏ i ∈ indices,
        completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
          completeIdealRowCharacter K S probe rows sector u.val))).val ∣
      (finiteConductor K beta * sexticSConductorBudgetIdeal K S * displayed * u.val).val := by
  let moving := ∏ i ∈ indices,
    completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i
  let modulus := sexticSConductorBudgetIdeal K S * displayed * u.val
  have hmoving : (finiteConductor K moving).val ∣ modulus.val := by
    exact dvd_mul_of_dvd_left
      (completeMovingCharacter_conductor_dvd S probe rows indices factor factorSector
        exponent displayed hsupport) u.val.val
  have hrow : (finiteConductor K
      (completeIdealRowCharacter K S probe rows sector u.val)).val ∣ modulus.val := by
    simpa only [modulus, Submonoid.coe_mul, mul_assoc, mul_left_comm, mul_comm] using
      dvd_mul_of_dvd_left (completeRowCharacter_conductor_dvd S probe rows sector u)
        displayed.val
  have hcombined := finiteConductor_mul_dvd_common moving
    (completeIdealRowCharacter K S probe rows sector u.val) modulus hmoving hrow
  have hfinal := (finiteConductor_mul_dvd K beta
    (moving * completeIdealRowCharacter K S probe rows sector u.val)).trans
      (mul_dvd_mul (dvd_refl (finiteConductor K beta).val) hcombined)
  simpa only [moving, modulus, Submonoid.coe_mul, mul_assoc] using hfinal

set_option maxHeartbeats 800000 in
/-- The actual FE scale has the same linear norm dependence.  In
particular N(displayed) is not replaced by N(product b_i^e_i). -/
theorem completeMovingRowCharacter_scale_le {Index : Type*}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (beta : HeckeCharacter K)
    (indices : Finset Index) (factor : Index → ExteriorIdeal K S)
    (factorSector : Index → SixthUnitClasses K S) (exponent : Index → ℤ)
    (displayed : NonzeroIdeal K)
    (hsupport : ∀ i ∈ indices, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val)
    (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S) :
    heckeConductorScale K (beta * ((∏ i ∈ indices,
        completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
          completeIdealRowCharacter K S probe rows sector u.val)) ≤
      (((NumberField.discr K).natAbs : ℝ) *
        (Ideal.absNorm (finiteConductor K beta).val : ℝ) *
          (Ideal.absNorm (sexticSConductorBudgetIdeal K S).val : ℝ)) *
            idealNorm K u.val * idealNorm K displayed := by
  have hn := Nat.le_of_dvd
    (Ideal.absNorm_pos_of_nonZeroDivisors
      (finiteConductor K beta * sexticSConductorBudgetIdeal K S * displayed * u.val))
    (map_dvd Ideal.absNorm
      (completeMovingRowCharacter_conductor_dvd S probe rows beta indices factor factorSector
        exponent displayed hsupport sector u))
  simp only [Submonoid.coe_mul, map_mul] at hn
  have hreal :
      (Ideal.absNorm (finiteConductor K (beta * ((∏ i ∈ indices,
        completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
          completeIdealRowCharacter K S probe rows sector u.val))).val : ℝ) ≤
      (Ideal.absNorm (finiteConductor K beta).val : ℝ) *
        (Ideal.absNorm (sexticSConductorBudgetIdeal K S).val : ℝ) *
          idealNorm K displayed * idealNorm K u.val := by
    dsimp only [idealNorm]
    exact_mod_cast hn
  simpa only [heckeConductorScale, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg (NumberField.discr K).natAbs)

end HeckeSkeleton.Moments.EngineInduction
