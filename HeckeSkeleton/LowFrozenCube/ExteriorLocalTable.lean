import HeckeSkeleton.LowFrozenCube.ExteriorData
import HeckeSkeleton.LowFrozenCube.ExteriorLocalBounds
import HeckeSkeleton.LowFrozenCube.SourceLedger
import HeckeGeneral.Analysis.ThetaPrimeGaussNorm

/-!
# The actual local Weyl table supplies the frozen-cube scalar inputs

The literal `primePhase`, `localTau`, `thetaGamma`, and `localWeylScalar`
are transported to the already proved finite residue-field calculations.
This gives exact equality with the frozen ordinary table and proves all
three `PrimitiveLocalBounds` fields for the actual local scalars.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowHybrid
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local instance residueField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
local instance residueFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- The actual prime phase, bundled as a primitive additive character. -/
def primeAddCharacter (p : ExteriorPrime K S) : AddChar (𝓞 K ⧸ p.val.asIdeal) ℂ :=
  transportCharacter (thetaPrimeResidueEquiv K S p)
    (thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p))

@[simp] theorem primeAddCharacter_apply (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    primeAddCharacter K S D p x = primePhase K S D p x := rfl

theorem primeAddCharacter_primitive (p : ExteriorPrime K S) :
    (primeAddCharacter K S D p).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (thetaPrincipalAddCharacter_isPrimitive K S D (exteriorPrimeIdeal K S p))

theorem primeCharacter_order (p : ExteriorPrime K S) :
    orderOf (thetaPrimeCharacter K S D p) = 6 :=
  sexticResidueCharacter_order K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val p.property)

private def primeQuotientFunction (p : ExteriorPrime K S) :
    ThetaQuotient K S (exteriorPrimeIdeal K S p) → ℂ :=
  sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    p.val.asIdeal p.val.ne_bot (exteriorPrimeIdeal K S p).property
    (fun q hq => D.away_six q ((exteriorPrimeIdeal K S p).property q hq))

private theorem primeQuotientFunction_equiv (p : ExteriorPrime K S)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    primeQuotientFunction K S D p (thetaPrimeResidueEquiv K S p x) =
      thetaPrimeCharacter K S D p x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  unfold primeQuotientFunction thetaPrimeResidueEquiv
  rw [sIntegerResidueEquiv_mk, sIntegerSexticIdealQuotientFunction_mk]
  change idealSymbol K S D (exteriorPrimeIdeal K S p)
      (algebraMap (𝓞 K) (S.integer K) a) = _
  rw [ExteriorSymbol.idealSymbol_exteriorPrime]
  exact sIntegerSexticEvaluation_algebraMap K S p.val p.property
    D.root6 D.primitive6 D.embedding (D.away_six p.val p.property) a

/-- The actual theta Gauss normalization agrees with the literal
residue-field Gauss sum after the existing localization equivalence. -/
theorem thetaGamma_eq_gammaTwo (p : ExteriorPrime K S) :
    thetaGamma K S D (exteriorPrimeIdeal K S p) 2 =
      ThetaLocal.ResidueField.gammaTwo (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) := by
  let F := 𝓞 K ⧸ p.val.asIdeal
  let Q := ThetaQuotient K S (exteriorPrimeIdeal K S p)
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S p.val.asIdeal
    p.val.ne_bot (exteriorPrimeIdeal K S p).property
  letI : Fintype Q := Fintype.ofFinite _
  let e : F ≃+* Q := thetaPrimeResidueEquiv K S p
  let χ : MulChar F ℂ := thetaPrimeCharacter K S D p
  let ψQ : AddChar Q ℂ := thetaPrincipalAddCharacter K S D (exteriorPrimeIdeal K S p)
  have hsum :
      (∑ x : Q, primeQuotientFunction K S D p x ^ 2 * ψQ x) =
        gaussSum (χ ^ 2) (primeAddCharacter K S D p) := by
    calc
      _ = ∑ x : F, primeQuotientFunction K S D p (e x) ^ 2 * ψQ (e x) :=
        (e.toEquiv.sum_comp (fun x => primeQuotientFunction K S D p x ^ 2 * ψQ x)).symm
      _ = gaussSum (χ ^ 2) (primeAddCharacter K S D p) := by
        unfold gaussSum
        apply Finset.sum_congr rfl
        intro x _
        rw [show primeQuotientFunction K S D p (e x) = χ x from
          primeQuotientFunction_equiv K S D p x,
          MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0)]
        rfl
  change (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
    (∑ x : Q, primeQuotientFunction K S D p x ^ 2 * ψQ x) = _
  rw [hsum]
  unfold ThetaLocal.ResidueField.gammaTwo
  rw [card_primeIdealResidueField K p.val]

theorem localTau_eq (p : ExteriorPrime K S) (j : Fin 6) :
    localTau K S D p j =
      ThetaLocal.ResidueField.localTau (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) j := rfl

theorem digitMask_eq (p : ExteriorPrime K S) (j : Fin 6)
    (x : 𝓞 K ⧸ p.val.asIdeal) :
    digitMask K S D p j x =
      ThetaLocal.ResidueField.digitMask (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) j x := by
  simp only [digitMask, ThetaLocal.ResidueField.digitMask,
    card_primeIdealResidueField K p.val, localTau_eq]

theorem sphericalDigit_eq (p : ExteriorPrime K S) (e : ℕ) :
    sphericalDigit K S D p e =
      ThetaLocal.ResidueField.sphericalDigit (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) e := by
  simp only [sphericalDigit, ThetaLocal.ResidueField.sphericalDigit,
    card_primeIdealResidueField K p.val, thetaGamma_eq_gammaTwo]

theorem localWeylScalar_eq (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    localWeylScalar K S D p j e =
      ThetaLocal.ResidueField.localWeylScalar (thetaPrimeCharacter K S D p)
        (primeAddCharacter K S D p) j e := by
  simp only [localWeylScalar, ThetaLocal.ResidueField.localWeylScalar,
    sphericalDigit_eq, digitMask_eq, primeAddCharacter_apply]

/-- Actual first spherical coefficient. -/
def first (p : ExteriorPrime K S) : ℂ :=
  (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
    thetaGamma K S D (exteriorPrimeIdeal K S p) 2

/-- Actual exceptional positive-valuation ordinary prefactor. -/
def prefactor (p : ExteriorPrime K S) : ℂ :=
  ((p.val.asIdeal.absNorm : ℂ) - 1) / localTau K S D p ⟨4, by decide⟩

/-- The actual finite Weyl sum at zero valuation, extended periodically
only to match the frozen core's natural-number digit parameter. -/
def atZero (p : ExteriorPrime K S) (j : ℕ) : ℂ :=
  localWeylScalar K S D p ⟨j % 6, Nat.mod_lt _ (by decide)⟩ 0

theorem first_eq (p : ExteriorPrime K S) :
    first K S D p = ExteriorLocalBounds.first (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) := by
  simp only [first, ExteriorLocalBounds.first, card_primeIdealResidueField K p.val,
    thetaGamma_eq_gammaTwo]

theorem prefactor_eq (p : ExteriorPrime K S) :
    prefactor K S D p = ExteriorLocalBounds.prefactor (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) := by
  simp only [prefactor, ExteriorLocalBounds.prefactor, card_primeIdealResidueField K p.val,
    localTau_eq]

theorem atZero_eq (p : ExteriorPrime K S) :
    atZero K S D p = ExteriorLocalBounds.atZero (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) := by
  funext j
  exact localWeylScalar_eq K S D p _ 0

/-- Exact equality of the original local Weyl sum with the frozen
ordinary table, including zero valuation and the forbidden residues. -/
theorem localWeylScalar_eq_ordinary (p : ExteriorPrime K S) (j : Fin 6) (e : ℕ) :
    localWeylScalar K S D p j e =
      LocalTable.ordinaryScalar (p.val.asIdeal.absNorm : ℂ)
        (first K S D p) (prefactor K S D p) (atZero K S D p) j.val e := by
  rw [localWeylScalar_eq, first_eq, prefactor_eq, atZero_eq]
  simpa only [card_primeIdealResidueField K p.val] using
    ExteriorLocalBounds.localWeyl_eq (thetaPrimeCharacter K S D p)
      (primeCharacter_order K S D p) (primeAddCharacter K S D p) j e

theorem first_sq (p : ExteriorPrime K S) :
    ‖first K S D p‖ ^ 2 = 1 / (p.val.asIdeal.absNorm : ℝ) := by
  rw [first_eq]
  simpa only [card_primeIdealResidueField K p.val] using
    ExteriorLocalBounds.first_sq (thetaPrimeCharacter K S D p)
      (primeCharacter_order K S D p) (primeAddCharacter K S D p)
      (primeAddCharacter_primitive K S D p)

theorem prefactor_sq (p : ExteriorPrime K S) :
    ‖prefactor K S D p‖ ^ 2 ≤ (p.val.asIdeal.absNorm : ℝ) := by
  rw [prefactor_eq]
  simpa only [card_primeIdealResidueField K p.val] using
    ExteriorLocalBounds.prefactor_sq (thetaPrimeCharacter K S D p)
      (primeCharacter_order K S D p) (primeAddCharacter K S D p)
      (primeAddCharacter_primitive K S D p)

theorem atZero_sq (p : ExteriorPrime K S) (j : Fin 6) :
    ‖atZero K S D p j.val‖ ^ 2 =
      if j.val = 0 ∨ j.val = 4 then 1 / (p.val.asIdeal.absNorm : ℝ) else 1 := by
  rw [atZero_eq]
  simpa only [card_primeIdealResidueField K p.val] using
    ExteriorLocalBounds.atZero_sq (thetaPrimeCharacter K S D p)
      (primeCharacter_order K S D p) (primeAddCharacter K S D p)
      (primeAddCharacter_primitive K S D p) j

/-- The complete ordinary local product is the literal product appearing
in the project's reflected coefficient. -/
theorem rawTable_eq (hD : AllowedGeneratorInput K S D) (f : Data K S)
    (a : ExteriorIdeal K S) :
    (f.toFrozen K S D hD).rawTable (ExteriorArithmetic.normHom K S)
      (first K S D) (prefactor K S D) (atZero K S D) a =
      ∏ p ∈ f.ordinary, localWeylScalar K S D p (f.digit p)
        (primeExponents a.val p.val) := by
  unfold FrozenReduction.Data.rawTable LocalTable.localProduct
  apply Finset.prod_congr rfl
  intro p _
  rw [Data.toFrozen_prime]
  change LocalTable.ordinaryScalar ((p.val.asIdeal.absNorm : ℝ) : ℂ)
    (first K S D p) (prefactor K S D p) (atZero K S D p) (f.digit p).val
    (primeExponents a.val p.val) = _
  simpa only [Complex.ofReal_natCast] using
    (localWeylScalar_eq_ordinary K S D p (f.digit p)
      (primeExponents a.val p.val)).symm

theorem tableMajorant_eq (hD : AllowedGeneratorInput K S D) (f : Data K S) :
    (f.toFrozen K S D hD).tableMajorant (ExteriorArithmetic.normHom K S)
      (first K S D) (prefactor K S D) (atZero K S D) =
      ∏ p ∈ f.ordinary, ‖localWeylScalar K S D p (f.digit p)
        (primeExponents f.minimum.val p.val)‖ := by
  unfold FrozenReduction.Data.tableMajorant
  apply Finset.prod_congr rfl
  intro p _
  rw [Data.toFrozen_prime]
  change ‖LocalTable.ordinaryScalar ((p.val.asIdeal.absNorm : ℝ) : ℂ)
    (first K S D p) (prefactor K S D p) (atZero K S D p) (f.digit p).val
    (primeExponents f.minimum.val p.val)‖ = _
  simpa only [Complex.ofReal_natCast] using
    congrArg norm (localWeylScalar_eq_ordinary K S D p (f.digit p)
      (primeExponents f.minimum.val p.val)).symm

/-- Insert the actual Gauss/Weyl scalars into arbitrary finite source
data, preserving all rows, marks, phases and coefficients. -/
def withActualLocalTables
    (b : FrozenReduction.SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)) :
    FrozenReduction.SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S) :=
  { b with first := first K S D, prefactor := prefactor K S D, atZero := atZero K S D }

/-- All primitive local estimates required by the source ledger are
theorems for the project's actual local coefficients. -/
theorem primitiveLocalBounds (hD : AllowedGeneratorInput K S D) (f : Data K S)
    (b : FrozenReduction.SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)) :
    FrozenReduction.PrimitiveLocalBounds (f.toFrozen K S D hD)
      (ExteriorArithmetic.normHom K S) (withActualLocalTables K S D b) where
  first_sq p _ := by
    change ‖first K S D p‖ ^ 2 ≤
      1 / ExteriorArithmetic.normHom K S ((f.toFrozen K S D hD).prime p)
    rw [Data.toFrozen_prime]
    exact le_of_eq (first_sq K S D p)
  prefactor_sq p _ := by
    change ‖prefactor K S D p‖ ^ 2 ≤
      ExteriorArithmetic.normHom K S ((f.toFrozen K S D hD).prime p)
    rw [Data.toFrozen_prime]
    exact prefactor_sq K S D p
  zero_sq p _ := by
    change ‖atZero K S D p (f.digit p).val‖ ^ 2 ≤
      if (f.digit p).val = 0 ∨ (f.digit p).val = 4 then
        1 / ExteriorArithmetic.normHom K S ((f.toFrozen K S D hD).prime p) else 1
    rw [Data.toFrozen_prime]
    exact le_of_eq (atZero_sq K S D p (f.digit p))

#print axioms thetaGamma_eq_gammaTwo
#print axioms localWeylScalar_eq_ordinary
#print axioms rawTable_eq
#print axioms primitiveLocalBounds

end HeckeSkeleton.LowFrozenCube.Exterior
