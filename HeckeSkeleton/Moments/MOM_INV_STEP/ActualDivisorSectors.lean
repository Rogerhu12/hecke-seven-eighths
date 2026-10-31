import HeckeSkeleton.Moments.MOM_INV_STEP.FirstInversePoisson

/-!
# Actual mask divisors and the original unit sectors

An actual Poisson mask generator need not be the selected generator of
its contracted exterior ideal. Its unit factor is computed from equality
of the two principal ideals. The corresponding inverse unit acts by a
permutation of all original subgroup sectors.

Both absorption identities retain that unit and every coprimality zero.
The first removes a divisor from the fourth-power label; the second adds
it. Both multiply the row ideal by the divisor exactly once. No moving
unit character is turned into an outer scalar, and no fifth-power row
norm is substituted for the required first-power row norm.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualDivisorSectors

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalSectorRows
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def unitCharacter (n : Ext) : (Sset).unit K →* ℂ where
  toFun u := idealSymbol K Sset D n (((Sset).unitEquivUnitsInteger K u).val)
  map_one' := by
    simp only [map_one, Units.val_one, idealSymbol, sIntegerSexticIdealEvaluation_one]
  map_mul' := by
    intro u v
    simp only [map_mul, Units.val_mul, CanonicalPoissonSource.idealSymbol_mul]

theorem unitCharacter_sixth (n : Ext) (u : (Sset).unit K) :
    unitCharacter K S D n u ^ 6 = 1 := by
  have h := sIntegerSexticIdealEvaluation_sixth_power_unit K Sset
    D.root6 D.primitive6 D.embedding n.val.val (nonZeroDivisors.coe_ne_zero n.val)
    n.property (fun p hp => D.away_six p (n.property p hp)) u
  change idealSymbol K Sset D n (((Sset).unitEquivUnitsInteger K u).val ^ 6) = 1 at h
  rw [CanonicalPoissonSource.idealSymbol_pow] at h
  exact h

theorem unitCharacter_star_inv (n : Ext) (u : (Sset).unit K) :
    star (unitCharacter K S D n u⁻¹) = unitCharacter K S D n u := by
  have hn : ‖unitCharacter K S D n u‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (unitCharacter_sixth K S D n u) (by decide)
  have hm : unitCharacter K S D n u⁻¹ * unitCharacter K S D n u = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have he := (eq_inv_of_mul_eq_one_left hm).trans (Complex.inv_eq_conj hn)
  rw [he, Complex.star_def, Complex.conj_conj]

/-- The actual contraction, with its exterior proof supplied by arithmetic. -/
def divisorIdeal (d : NonzeroRingElements OS) : Ext :=
  CanonicalSectors.orbitExterior K Sset (⊥ : Subgroup ((Sset).unit K)) (Quotient.mk _ d)

@[simp] theorem divisorIdeal_val (d : NonzeroRingElements OS) :
    (divisorIdeal K S d).val.val = sIntegerModulusContraction K Sset d.val := rfl

theorem divisorIdeal_span (d : NonzeroRingElements OS) :
    Ideal.span ({D.generator (divisorIdeal K S d)} : Set OS) =
      Ideal.span ({d.val} : Set OS) := by
  rw [D.generator_span, divisorIdeal_val]
  exact map_sIntegerModulusContraction K Sset d.val

theorem exists_divisorUnit (d : NonzeroRingElements OS) :
    ∃ u : (Sset).unit K, d.val =
      ((Sset).unitEquivUnitsInteger K u).val * D.generator (divisorIdeal K S d) := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (divisorIdeal_span K S D d)
  refine ⟨((Sset).unitEquivUnitsInteger K).symm u, ?_⟩
  rw [((Sset).unitEquivUnitsInteger K).apply_symm_apply]
  exact hu.symm.trans (mul_comm _ _)

def divisorUnit (d : NonzeroRingElements OS) : (Sset).unit K :=
  Classical.choose (exists_divisorUnit K S D d)

theorem divisorUnit_spec (d : NonzeroRingElements OS) :
    d.val = ((Sset).unitEquivUnitsInteger K (divisorUnit K S D d)).val *
      D.generator (divisorIdeal K S d) :=
  Classical.choose_spec (exists_divisorUnit K S D d)

theorem divisorCharacter (n : Ext) (d : NonzeroRingElements OS) :
    idealSymbol K Sset D n d.val = unitCharacter K S D n (divisorUnit K S D d) *
      idealSymbol K Sset D n (D.generator (divisorIdeal K S d)) := by
  rw [divisorUnit_spec K S D d, CanonicalPoissonSource.idealSymbol_mul]
  rfl

/-- Its norm is exactly the original divisor norm, without any power loss. -/
theorem divisorIdeal_norm (d : NonzeroRingElements OS) :
    ((divisorIdeal K S d).val.val.absNorm : ℝ) = (sIntegerElementNorm K Sset d).val := by
  rw [divisorIdeal_val, ← natCard_sIntegerPrincipalResidue_eq_productNorm K Sset d.val d.property,
    natCard_sIntegerPrincipalResidue K Sset d.val d.property]

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hΓ in
theorem unitCharacter_class_eq (n : Ext) (u v : (Sset).unit K)
    (huv : QuotientGroup.mk' Γ u = QuotientGroup.mk' Γ v) :
    unitCharacter K S D n u = unitCharacter K S D n v := by
  obtain ⟨g, hg, huv⟩ := (QuotientGroup.mk'_eq_mk' Γ).mp huv
  have hgχ : unitCharacter K S D n g = 1 := by
    have h := CanonicalPoissonSource.idealSymbol_literal_invariant K S D Γ hΓ n ⟨g, hg⟩ 1
    change idealSymbol K Sset D n (((Sset).unitEquivUnitsInteger K g).val) = 1
    simpa only [mul_one, idealSymbol, sIntegerSexticIdealEvaluation_one] using h
  have he := congrArg (unitCharacter K S D n) huv
  rw [map_mul, hgχ, mul_one] at he
  exact he

/-- Translation permutes the complete original sector quotient. -/
def sectorTranslation (u : (Sset).unit K) : Sector ≃ Sector :=
  Equiv.mulLeft (QuotientGroup.mk' Γ u)

include hΓ in
theorem sectorCharacter_translate (n I : Ext) (u : (Sset).unit K) (ξ : Sector) :
    sectorCharacter K S Γ D n I (sectorTranslation K S Γ u ξ) =
      unitCharacter K S D n u * sectorCharacter K S Γ D n I ξ := by
  have he : QuotientGroup.mk' Γ
      (CanonicalSectors.sectorUnit K Sset Γ (sectorTranslation K S Γ u ξ)) =
      QuotientGroup.mk' Γ (u * CanonicalSectors.sectorUnit K Sset Γ ξ) := by
    calc
      _ = sectorTranslation K S Γ u ξ := Quotient.out_eq _
      _ = QuotientGroup.mk' Γ u * ξ := rfl
      _ = QuotientGroup.mk' Γ u *
          QuotientGroup.mk' Γ (CanonicalSectors.sectorUnit K Sset Γ ξ) :=
        congrArg (fun z : Sector => QuotientGroup.mk' Γ u * z) (Quotient.out_eq ξ).symm
      _ = _ := (map_mul (QuotientGroup.mk' Γ) u _).symm
  rw [sectorCharacter_eq, sectorCharacter_eq]
  change unitCharacter K S D n
      (CanonicalSectors.sectorUnit K Sset Γ (sectorTranslation K S Γ u ξ)) *
      idealSymbol K Sset D n (D.generator I) =
    unitCharacter K S D n u *
      (unitCharacter K S D n (CanonicalSectors.sectorUnit K Sset Γ ξ) *
        idealSymbol K Sset D n (D.generator I))
  rw [unitCharacter_class_eq K S Γ D hΓ n _ _ he, map_mul, mul_assoc]

def divisorTransport (d : NonzeroRingElements OS) : Sector ≃ Sector :=
  sectorTranslation K S Γ (divisorUnit K S D d)⁻¹

/-- A retained first divisor enters the final positive row directly.
Its unit acts in the positive direction, unlike the second divisor that
is simultaneously inserted into the fourth-power label. -/
def directDivisorTransport (d : NonzeroRingElements OS) : Sector ≃ Sector :=
  sectorTranslation K S Γ (divisorUnit K S D d)

include hΓ hallowed in
theorem actual_divisor_direct (n I : Ext) (ξ : Sector) (d : NonzeroRingElements OS) :
    idealSymbol K Sset D n d.val * sectorCharacter K S Γ D n I ξ =
      sectorCharacter K S Γ D n (exteriorMul K Sset (divisorIdeal K S d) I)
        (directDivisorTransport K S Γ D d ξ) := by
  rw [divisorCharacter, directDivisorTransport, sectorCharacter_translate K S Γ D hΓ,
    sectorCharacter_mul K S Γ D hallowed]
  ring

include hallowed in
theorem selectedSymbol_fifth (n I : Ext) :
    idealSymbol K Sset D n (D.generator I) ^ 5 =
      star (idealSymbol K Sset D n (D.generator I)) := by
  have h := CanonicalIdealRow.row_zero_or_one K S D hallowed n
    (CanonicalIdealRow.ofExterior K S I)
  simp only [CanonicalIdealRow.row_apply, CanonicalIdealRow.generator_ofExterior] at h
  rcases h with hzero | hone
  · have hz := (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hzero
    simp only [hz, zero_pow (by decide : (5 : ℕ) ≠ 0), star_zero]
  · have hn : ‖idealSymbol K Sset D n (D.generator I)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hone (by decide)
    have hm : idealSymbol K Sset D n (D.generator I) ^ 5 *
        idealSymbol K Sset D n (D.generator I) = 1 := by
      simpa only [← pow_succ] using hone
    rw [Complex.star_def]
    exact (eq_inv_of_mul_eq_one_left hm).trans (Complex.inv_eq_conj hn)

include hΓ hallowed in
/-- First-pass absorption when the divisor is removed from the old
fourth-power label. The actual divisor unit changes the original sector. -/
theorem actual_divisor_first (n j I : Ext) (ξ : Sector) (d : NonzeroRingElements OS) :
    idealSymbol K Sset D n d.val *
        idealSymbol K Sset D n (D.generator (exteriorMul K Sset (divisorIdeal K S d) j)) ^ 4 *
        star (sectorCharacter K S Γ D n I ξ) =
      idealSymbol K Sset D n (D.generator j) ^ 4 *
        star (sectorCharacter K S Γ D n
          (exteriorMul K Sset (divisorIdeal K S d) I) (divisorTransport K S Γ D d ξ)) := by
  rw [divisorCharacter, generator_mul_character K S D hallowed,
    divisorTransport, sectorCharacter_translate K S Γ D hΓ,
    sectorCharacter_mul K S Γ D hallowed]
  simp only [mul_pow, star_mul, unitCharacter_star_inv]
  calc
    _ = unitCharacter K S D n (divisorUnit K S D d) *
        idealSymbol K Sset D n (D.generator (divisorIdeal K S d)) ^ 5 *
        idealSymbol K Sset D n (D.generator j) ^ 4 *
        star (sectorCharacter K S Γ D n I ξ) := by ring
    _ = _ := by rw [selectedSymbol_fifth K S D hallowed]; ring

include hΓ hallowed in
/-- Second-pass absorption adds the actual divisor ideal to the new
label and multiplies the row ideal once, with the required inverse-unit
sector permutation. Vanishing divisor characters are included. -/
theorem actual_divisor_second (n j I : Ext) (ξ : Sector) (d : NonzeroRingElements OS) :
    idealSymbol K Sset D n d.val *
        star (idealSymbol K Sset D n (D.generator j) ^ 4 * sectorCharacter K S Γ D n I ξ) =
      star (idealSymbol K Sset D n
          (D.generator (exteriorMul K Sset j (divisorIdeal K S d))) ^ 4 *
        sectorCharacter K S Γ D n (exteriorMul K Sset (divisorIdeal K S d) I)
          (divisorTransport K S Γ D d ξ)) := by
  have hfive : star (idealSymbol K Sset D n (D.generator (divisorIdeal K S d))) ^ 5 =
      idealSymbol K Sset D n (D.generator (divisorIdeal K S d)) := by
    simpa only [star_pow, star_star] using congrArg star
      (selectedSymbol_fifth K S D hallowed n (divisorIdeal K S d))
  rw [divisorCharacter, generator_mul_character K S D hallowed,
    divisorTransport, sectorCharacter_translate K S Γ D hΓ,
    sectorCharacter_mul K S Γ D hallowed]
  simp only [mul_pow, star_mul, star_pow, unitCharacter_star_inv]
  calc
    _ = unitCharacter K S D n (divisorUnit K S D d) *
        star (idealSymbol K Sset D n (D.generator j)) ^ 4 *
        idealSymbol K Sset D n (D.generator (divisorIdeal K S d)) *
        star (sectorCharacter K S Γ D n I ξ) := by ring
    _ = unitCharacter K S D n (divisorUnit K S D d) *
        star (idealSymbol K Sset D n (D.generator j)) ^ 4 *
        star (idealSymbol K Sset D n (D.generator (divisorIdeal K S d))) ^ 5 *
        star (sectorCharacter K S Γ D n I ξ) := by rw [hfive]
    _ = _ := by ring

include hΓ hallowed in
/-- The retained first divisor and the second Poisson divisor combine
in the actual final row. Their unit directions differ, and the second
divisor also enters the new fourth-power label. -/
theorem actual_two_divisors (n j I : Ext) (ξ : Sector)
    (dk d₂ : NonzeroRingElements OS) :
    idealSymbol K Sset D n d₂.val *
        star (idealSymbol K Sset D n dk.val *
          idealSymbol K Sset D n (D.generator j) ^ 4 * sectorCharacter K S Γ D n I ξ) =
      star (idealSymbol K Sset D n
          (D.generator (exteriorMul K Sset j (divisorIdeal K S d₂))) ^ 4 *
        sectorCharacter K S Γ D n
          (exteriorMul K Sset (divisorIdeal K S d₂)
            (exteriorMul K Sset (divisorIdeal K S dk) I))
          (divisorTransport K S Γ D d₂ (directDivisorTransport K S Γ D dk ξ))) := by
  rw [show idealSymbol K Sset D n dk.val *
      idealSymbol K Sset D n (D.generator j) ^ 4 * sectorCharacter K S Γ D n I ξ =
      idealSymbol K Sset D n (D.generator j) ^ 4 *
        (idealSymbol K Sset D n dk.val * sectorCharacter K S Γ D n I ξ) by ring,
    actual_divisor_direct K S Γ D hΓ hallowed n I ξ dk,
    actual_divisor_second K S Γ D hΓ hallowed]

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualDivisorSectors

end
