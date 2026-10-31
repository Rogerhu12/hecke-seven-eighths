import HeckeAxiom.GaussDictionary
import HeckeSkeleton.ThetaLocal.ProjectFinite
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.PrincipalExteriorCharacter
import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment

/-!
# The actual residue character and additive phase of one recipe

The arithmetic datum below uses the recipe's own allowed generators,
embedding and roots. These lemmas identify its literal finite-field
tables with the characters carried by the same actual source recipe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.LocalDigitArithmetic

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]

theorem sexticSphericalCoefficient_nat {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (e : ℕ) :
    sexticSphericalCoefficient χ ψ (e : ℤ) =
      HeckeSkeleton.ThetaLocal.ResidueField.sphericalDigit χ ψ e := by
  have hnonneg : ¬ (e : ℤ) < 0 := Int.not_lt.mpr (Int.natCast_nonneg e)
  have hdiv : (e : ℤ) / 3 = ((e / 3 : ℕ) : ℤ) :=
    (Int.natCast_ediv e 3).symm
  have hmod0 : (e : ℤ) % 3 = 0 ↔ e % 3 = 0 := by omega
  have hmod1 : (e : ℤ) % 3 = 1 ↔ e % 3 = 1 := by omega
  simp only [sexticSphericalCoefficient,
    HeckeSkeleton.ThetaLocal.ResidueField.sphericalDigit,
    HeckeSkeleton.ThetaLocal.ResidueField.gammaTwo,
    hnonneg, ite_false, hmod0, hmod1, hdiv, zpow_neg, zpow_natCast, inv_pow]

abbrev prime (A : SArithmeticData F) (p : ThetaBranch.ExteriorPrime A) :
    ExteriorPrime F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) := ⟨p.val, p.property⟩

section Arithmetic

variable (A : SArithmeticData F) (G : ThetaBranch.AllowedRecipe A)
  (σ : F →+* ℂ)
  (hdiff : ∀ p : HeightOneSpectrum (𝓞 F),
    p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      HeckeGeneral.Characters.localDifferentExponent F p = 0)

local notation "Sf" => (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "D" => HeckeAxiom.thetaArithmeticData A G σ hdiff

theorem thetaPrimeCharacter_eq (p : ThetaBranch.ExteriorPrime A) :
    thetaPrimeCharacter F Sf D (prime A p) = ThetaBranch.residueCharacter A σ p := by
  apply MulChar.ext'
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht := NormalizedProbe.principal_prime_residueCharacter_transport A σ p
    (Ideal.Quotient.mk p.val.asIdeal a)
  have hchar := HeckeAxiom.sexticResidue_pow_eq_powerChar A σ
    (ThetaBranch.primeIdeal A p) 1 (by decide) (by decide)
    (algebraMap (𝓞 F) A.R a)
  rw [pow_one] at hchar
  have hres := HeckeAxiom.sexticEvaluation_eq_sexticResidue A σ p.val p.property
    (algebraMap (𝓞 F) A.R a)
  rw [sIntegerSexticEvaluation_algebraMap] at hres
  exact (hres.trans hchar).trans ht.symm

end Arithmetic

section Recipe

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  (hdiff : ∀ p : HeightOneSpectrum (𝓞 F),
    p ∉ (R.A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      HeckeGeneral.Characters.localDifferentExponent F p = 0)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "D" => HeckeAxiom.thetaArithmeticData R.A R.probe.allowed R.σ hdiff

theorem probe_additive_eq (x : F) :
    R.probe.coefficients.additiveCharacter x = (R.A.fieldTraceCharacter x : ℂ) := by
  rw [R.probe.sameTrace, PrincipalProbeConstruction.Inputs.fieldTrace_phase]
  congr 1
  funext v
  exact R.normalization.sameFiniteTrace v

theorem primePhase_eq (p : ThetaBranch.ExteriorPrime R.A)
    (x : 𝓞 F ⧸ p.val.asIdeal) :
    primePhase F Sf D (prime R.A p) x = Characters.psi R p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Eq.trans (projectPrimePhase_mk F Sf D (prime R.A p) a :
    primePhase F Sf D (prime R.A p) (Ideal.Quotient.mk p.val.asIdeal a) = _) ?_
  rw [Characters.psi_apply, probe_additive_eq,
    HeckeAxiom.thetaArithmeticData_generator]
  have hp : (HeckeAxiom.exteriorEquiv R.A).symm
      (exteriorPrimeIdeal F Sf (prime R.A p)) = ThetaBranch.primeIdeal R.A p :=
    Subtype.ext rfl
  rw [hp]
  exact HeckeAxiom.sLocalPrincipalPhase_eq_fieldTraceCharacter R.A _

theorem projectPrimePhase_eq (p : ThetaBranch.ExteriorPrime R.A) :
    projectPrimePhase F Sf D (prime R.A p) = Characters.psi R p := by
  ext x
  exact primePhase_eq R hdiff p x

theorem sphericalDigit_eq (p : ThetaBranch.ExteriorPrime R.A) (e : ℕ) :
    sphericalDigit F Sf D (prime R.A p) e =
      sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p)
        (Characters.psi R p) (e : ℤ) := by
  rw [sphericalDigit_eq_residueField, thetaPrimeCharacter_eq,
    projectPrimePhase_eq, sexticSphericalCoefficient_nat]

theorem sphericalFactor_eq (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ) :
    ThetaBranch.sphericalFactor R.A R.probe.allowed R.σ (Characters.psi R) p x =
      if ThetaBranch.order p.val x < 0 then 0 else
        sphericalDigit F Sf D (prime R.A p) (ThetaBranch.order p.val x).toNat *
          thetaPrimeCharacter F Sf D (prime R.A p)
            (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x)) ^
              (2 * (ThetaBranch.order p.val x).toNat) := by
  by_cases he : ThetaBranch.order p.val x < 0
  · simp only [ThetaBranch.sphericalFactor, sexticSphericalCoefficient,
      he, ↓reduceIte, zero_mul]
  · have hn : ((ThetaBranch.order p.val x).toNat : ℤ) = ThetaBranch.order p.val x :=
      Int.toNat_of_nonneg (le_of_not_gt he)
    have hc : sexticSphericalCoefficient (ThetaBranch.residueCharacter R.A R.σ p)
        (Characters.psi R p) (ThetaBranch.order p.val x) =
          sphericalDigit F Sf D (prime R.A p) (ThetaBranch.order p.val x).toNat := by
      conv_lhs => rw [← hn]
      exact (sphericalDigit_eq R hdiff p _).symm
    rw [ThetaBranch.sphericalFactor, if_neg he, hc, ThetaBranch.symbol,
      ← thetaPrimeCharacter_eq R.A R.probe.allowed R.σ hdiff p]
    congr 1
    rw [show 2 * ThetaBranch.order p.val x =
      ((2 * (ThetaBranch.order p.val x).toNat : ℕ) : ℤ) by omega, zpow_natCast]

theorem forward_mask (p : ThetaBranch.ExteriorPrime R.A) (j : Fin 6)
    (t : 𝓞 F ⧸ p.val.asIdeal) :
    (∑ v : 𝓞 F ⧸ p.val.asIdeal,
      digitMask F Sf D (prime R.A p) j v * Characters.psi R p (t * v)) =
      if t = 0 then 0 else thetaPrimeCharacter F Sf D (prime R.A p) t ^ j.val := by
  have hsum : (∑ v : 𝓞 F ⧸ p.val.asIdeal,
      digitMask F Sf D (prime R.A p) j v * Characters.psi R p (t * v)) =
      ∑ v : 𝓞 F ⧸ p.val.asIdeal,
        digitMask F Sf D (prime R.A p) j v * primePhase F Sf D (prime R.A p) (t * v) :=
    Finset.sum_congr rfl fun v _ =>
      congrArg (digitMask F Sf D (prime R.A p) j v * ·) (primePhase_eq R hdiff p (t * v)).symm
  rw [hsum]
  refine (digitMask_fourier F Sf D (prime R.A p) j t).trans ?_
  by_cases ht : t = 0
  · subst ht
    rw [if_pos rfl]
    exact MulChar.map_nonunit _ not_isUnit_zero
  · rw [if_neg ht]
    exact (thetaPrimeCharacter F Sf D (prime R.A p)).pow_apply_coe
      j.val (Units.mk0 t ht)

theorem zeroth_weyl (p : ThetaBranch.ExteriorPrime R.A) :
    -localWeylScalar F Sf D (prime R.A p) 0 0 =
      (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
        thetaGamma F Sf D (exteriorPrimeIdeal F Sf (prime R.A p)) 2 := by
  rw [localWeylScalar_zero_zero]
  dsimp only [prime]
  ring

end Recipe

end ThetaGlobal.LocalDigitArithmetic

#print axioms ThetaGlobal.LocalDigitArithmetic.thetaPrimeCharacter_eq
#print axioms ThetaGlobal.LocalDigitArithmetic.probe_additive_eq
#print axioms ThetaGlobal.LocalDigitArithmetic.primePhase_eq
#print axioms ThetaGlobal.LocalDigitArithmetic.sphericalDigit_eq
#print axioms ThetaGlobal.LocalDigitArithmetic.sphericalFactor_eq
#print axioms ThetaGlobal.LocalDigitArithmetic.forward_mask
#print axioms ThetaGlobal.LocalDigitArithmetic.zeroth_weyl
