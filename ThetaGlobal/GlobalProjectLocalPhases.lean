module

public import ThetaGlobal.GlobalProjectMarkedSupport
public import ThetaGlobal.GlobalProjectPhases
public import HeckeGeneral.Characters.SIntegerSexticCharacter

@[expose] public section

/-!
# Local unit phases of the actual rational frequency

The local unit part is a homomorphism on the field's unit group. Its
sextic residue phase therefore respects products and all integer powers.
Allowed-generator multiplicativity removes the entire prime-power
factor of an ideal, leaving exactly the literal `removePrime` generator
that occurs in Omega, rho, pi and lambda.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectLocalPhases

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F Sf)

def localUnitHom (p : P) : Fˣ →* Fˣ where
  toFun := ThetaBranch.localUnit R.A R.probe.allowed p
  map_one' := by simp [ThetaBranch.localUnit, ThetaBranch.order]
  map_mul' := by
    intro x y
    simp only [ThetaBranch.localUnit, ThetaBranch.ord_mul, zpow_add]
    exact (div_mul_div_comm x _ y _).symm

def phaseHom (p : P) : Fˣ →* ℂ where
  toFun := unitPhase R Adata p
  map_one' := by
    change thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
      (ThetaBranch.unitResidue p.val (localUnitHom R p 1)) = 1
    rw [map_one, ThetaBranch.reduction_one, map_one]
  map_mul' := by
    intro x y
    change thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
      (ThetaBranch.unitResidue p.val (localUnitHom R p (x * y))) = _
    rw [map_mul, ThetaBranch.reduction_mul p.val _ _
      (ThetaBranch.localUnit_order R.A R.probe.allowed p x)
      (ThetaBranch.localUnit_order R.A R.probe.allowed p y), map_mul]
    rfl

theorem phaseHom_sixth (p : P) (x : Fˣ) : phaseHom R Adata p x ^ 6 = 1 := by
  exact ThetaBranch.char_pow_six _
    (GlobalProjectFrequency.thetaPrimeCharacter_order_six F Sf Adata (skeletonPrime R p)) _
    (ThetaBranch.unitResidue_ne_zero p.val _
      (ThetaBranch.localUnit_order R.A R.probe.allowed p x))

theorem phaseHom_ne_zero (p : P) (x : Fˣ) : phaseHom R Adata p x ≠ 0 := by
  intro hz
  have h := phaseHom_sixth R Adata p x
  simpa only [hz, zero_pow (by decide : (6 : ℕ) ≠ 0)] using h

/-- The two actual residue constructions agree for every S-integer
which is a unit at p. This uses their fraction representatives, including
the denominator, rather than identifying two choices definitionally. -/
theorem unitResidue_sInteger (p : P) (x : Fˣ) (a : Sf.integer F)
    (ha : (x : F) = (a : F)) (hx : ThetaBranch.order p.val x = 0) :
    ThetaBranch.unitResidue p.val x = sIntegerSexticResidueMap F Sf p.val p.property a := by
  obtain ⟨b, c, hb, hc, hbc, hr⟩ := ThetaBranch.reduction_spec p.val x hx
  have hcF : (c : F) ≠ 0 := by
    exact_mod_cast (fun h => hc (h ▸ p.val.asIdeal.zero_mem) : c ≠ 0)
  have he : a * algebraMap (𝓞 F) (Sf.integer F) c =
      algebraMap (𝓞 F) (Sf.integer F) b := by
    apply Subtype.ext
    change (a : F) * (c : F) = (b : F)
    rw [← ha, hbc, div_mul_cancel₀ _ hcF]
  have hm := congrArg (sIntegerSexticResidueMap F Sf p.val p.property) he
  simp only [map_mul, sIntegerSexticResidueMap_algebraMap] at hm
  have hcR : Ideal.Quotient.mk p.val.asIdeal c ≠ 0 :=
    fun h => hc (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [hr]
  exact ((eq_div_iff hcR).mpr hm).symm

theorem phaseHom_sInteger (p : P) (x : Fˣ) (a : Sf.integer F)
    (ha : (x : F) = (a : F)) (hx : ThetaBranch.order p.val x = 0) :
    phaseHom R Adata p x = primeEvaluation F Sf Adata (skeletonPrime R p) a := by
  have hu : ThetaBranch.localUnit R.A R.probe.allowed p x = x := by
    simp [ThetaBranch.localUnit, hx]
  change thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
    (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x)) = _
  rw [hu, unitResidue_sInteger R p x a ha hx]
  rfl

theorem phaseHom_sUnit (p : P) (u : Sf.unit F) :
    phaseHom R Adata p u.val =
      primeEvaluation F Sf Adata (skeletonPrime R p) (Sf.unitEquivUnitsInteger F u).val := by
  apply phaseHom_sInteger R Adata p u.val _ rfl
  exact ThetaBranch.unit_ord R.A p u

theorem phaseHom_generator_mul (hA : AllowedGeneratorInput F Sf Adata)
    (p : P) (I J : ExteriorIdeal F Sf) :
    phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata (exteriorMul F Sf I J)) =
      phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata I) *
        phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata J) := by
  obtain ⟨u, hu⟩ := hA.multiplicative I J
  have he : GlobalActualFrequency.generatorUnit F Sf Adata (exteriorMul F Sf I J) =
      u.val ^ 6 * GlobalActualFrequency.generatorUnit F Sf Adata I *
        GlobalActualFrequency.generatorUnit F Sf Adata J := by
    apply Units.ext
    exact congrArg (fun a : Sf.integer F => (a : F)) hu
  rw [he, map_mul, map_mul, map_pow, phaseHom_sixth, one_mul]

def primePower (p : P) (n : ℕ) : ExteriorIdeal F Sf :=
  ⟨idealOfPrimeExponents (Finsupp.single p.val n), by
    intro q hq
    have he : (Finsupp.single p.val n : HeightOneSpectrum (𝓞 F) →₀ ℕ) q ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp ((mem_idealPrimeSupport_iff F _ q).mpr hq)
      simpa only [primeExponents_idealOfPrimeExponents] using h
    have hqp : q = p.val := by
      by_contra hn
      exact he (Finsupp.single_eq_of_ne hn)
    exact hqp ▸ p.property⟩

theorem primePower_exponent (p q : P) (n : ℕ) :
    primeExponents (primePower R p n).val q.val = if q = p then n else 0 := by
  change primeExponents (idealOfPrimeExponents (Finsupp.single p.val n)) q.val = _
  rw [primeExponents_idealOfPrimeExponents]
  by_cases h : q = p
  · subst q
    simp
  · have hv : q.val ≠ p.val := fun he => h (Subtype.ext he)
    simp only [Finsupp.single_eq_of_ne hv, if_neg h]

theorem primePower_one (p : P) : primePower R p 1 = exteriorPrimeIdeal F Sf (skeletonPrime R p) := by
  apply Subtype.ext
  apply Subtype.ext
  change (idealOfPrimeExponents (Finsupp.single p.val 1)).val = p.val.asIdeal
  rw [idealOfPrimeExponents_single, pow_one]

theorem primePower_succ (p : P) (n : ℕ) :
    primePower R p (n + 1) = exteriorMul F Sf (primePower R p n) (primePower R p 1) := by
  apply GlobalIndexSupport.exterior_ext F Sf
  intro q
  change _ = primeExponents ((primePower R p n).val * (primePower R p 1).val) q.val
  rw [primeExponents_mul, Finsupp.add_apply, primePower_exponent,
    primePower_exponent, primePower_exponent]
  by_cases h : q = p <;> simp [h]

theorem primePower_zero_mul (p : P) :
    exteriorMul F Sf (primePower R p 0) (primePower R p 0) = primePower R p 0 := by
  apply GlobalIndexSupport.exterior_ext F Sf
  intro q
  change primeExponents ((primePower R p 0).val * (primePower R p 0).val) q.val = _
  rw [primeExponents_mul, Finsupp.add_apply]
  simp only [primePower_exponent, ite_self, add_zero]

theorem removePrime_factorization (p : P) (I : ExteriorIdeal F Sf) :
    exteriorMul F Sf (primePower R p (primeExponents I.val p.val))
      (removePrime F Sf I (skeletonPrime R p)) = I := by
  apply GlobalIndexSupport.exterior_ext F Sf
  intro q
  change primeExponents ((primePower R p (primeExponents I.val p.val)).val *
    (removePrime F Sf I (skeletonPrime R p)).val) q.val = _
  rw [primeExponents_mul, Finsupp.add_apply, primePower_exponent]
  change _ + primeExponents (idealOfPrimeExponents ((primeExponents I.val).erase p.val)) q.val = _
  rw [primeExponents_idealOfPrimeExponents]
  by_cases h : q = p
  · subst q
    simp
  · simp [h, show q.val ≠ p.val from fun he => h (Subtype.ext he)]

theorem removePrime_order (p : P) (I : ExteriorIdeal F Sf) :
    ThetaBranch.order p.val
      (GlobalActualFrequency.generatorUnit F Sf Adata (removePrime F Sf I (skeletonPrime R p))) = 0 := by
  rw [GlobalActualReindex.order_generator R.A Adata]
  change (primeExponents (idealOfPrimeExponents ((primeExponents I.val).erase p.val)) p.val : ℤ) = 0
  rw [primeExponents_idealOfPrimeExponents, Finsupp.erase_same]
  rfl

variable (hA : AllowedGeneratorInput F Sf Adata)
  (hgen : ∀ I : ExteriorIdeal F Sf,
    GlobalActualFrequency.generatorUnit F Sf Adata I =
      R.probe.allowed.generator ((HeckeAxiom.exteriorEquiv R.A).symm I))

include hgen in
theorem phaseHom_generator_prime (p : P) :
    phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata (primePower R p 1)) = 1 := by
  rw [primePower_one, hgen]
  have he : (HeckeAxiom.exteriorEquiv R.A).symm
      (exteriorPrimeIdeal F Sf (skeletonPrime R p)) = ThetaBranch.primeIdeal R.A p :=
    Subtype.ext rfl
  rw [he]
  have ho : ThetaBranch.order p.val
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p)) = 1 := by
    rw [ThetaBranch.generator_order]
    simp [ThetaBranch.primeIdeal, idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible p.val.irreducible]
  change thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
    (ThetaBranch.unitResidue p.val
      (ThetaBranch.localUnit R.A R.probe.allowed p _)) = 1
  rw [ThetaBranch.localUnit, ho, zpow_one, div_self,
    ThetaBranch.reduction_one, map_one]

include hA hgen in
theorem phaseHom_generator_primePower (p : P) (n : ℕ) :
    phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata (primePower R p n)) = 1 := by
  induction n with
  | zero =>
      have h := phaseHom_generator_mul R Adata hA p (primePower R p 0) (primePower R p 0)
      rw [primePower_zero_mul] at h
      exact (mul_left_cancel₀ (phaseHom_ne_zero R Adata p _) (h.symm.trans (mul_one _).symm))
  | succ n ih =>
      rw [primePower_succ, phaseHom_generator_mul R Adata hA, ih,
        phaseHom_generator_prime R Adata hgen, one_mul]

include hA hgen in
/-- The local phase is exactly the literal generator with all p-powers
removed. The allowed section's sixth-unit ambiguity has disappeared. -/
theorem phaseHom_generator (p : P) (I : ExteriorIdeal F Sf) :
    phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata I) =
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf I (skeletonPrime R p))) := by
  calc
    _ = phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata
        (exteriorMul F Sf (primePower R p (primeExponents I.val p.val))
          (removePrime F Sf I (skeletonPrime R p)))) := by rw [removePrime_factorization]
    _ = phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata
        (removePrime F Sf I (skeletonPrime R p))) := by
      rw [phaseHom_generator_mul R Adata hA,
        phaseHom_generator_primePower R Adata hA hgen, one_mul]
    _ = _ := phaseHom_sInteger R Adata p _ _ rfl (removePrime_order R Adata p I)

include hA hgen in
theorem phaseHom_representative (d : MarkedDatum F Sf) (i : ReflectionIndex F Sf d) (p : P) :
    unitPhase R Adata p (GlobalActualFrequency.representative F Sf Adata d i) =
      primeEvaluation F Sf Adata (skeletonPrime R p) (Sf.unitEquivUnitsInteger F
        (frequencyUnit F Sf d i)).val *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf i.numeratorFrozen (skeletonPrime R p))) *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf i.c (skeletonPrime R p))) *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf i.n (skeletonPrime R p))) ^ 3 *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf d.moving (skeletonPrime R p))) ^ (-2 : ℤ) *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf (activeFrozenIdeal F Sf d i) (skeletonPrime R p))) ^ (-2 : ℤ) *
      primeEvaluation F Sf Adata (skeletonPrime R p)
        (Adata.generator (removePrime F Sf (activeMarkedIdeal F Sf d i) (skeletonPrime R p))) ^ (-2 : ℤ) := by
  change phaseHom R Adata p (GlobalActualFrequency.representative F Sf Adata d i) = _
  simp only [GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    phaseHom_sUnit, phaseHom_generator R Adata hA hgen]

end ThetaGlobal.GlobalProjectLocalPhases
