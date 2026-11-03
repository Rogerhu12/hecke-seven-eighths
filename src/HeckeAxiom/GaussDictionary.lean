import HeckeAxiom.SexticSymbolDictionary
import HeckeAxiom.TraceCharacterDictionary
import HeckeGeneral.Analysis.LocalThetaInput
import DedekindZetaZeroFree.CharacterSums.Gauss.SexticChineseRemainderReciprocity

/-!
# The skeleton's Gauss sums are Axiom's ideal Gauss sums

For the data of an arithmetic choice, the skeleton's normalized Gauss sum
`thetaGamma J j` is Axiom's `idealGauss` of the same ideal, with the chosen
allowed generator, for every exponent `0 < j < 6`. The two sums run over the
same quotient ring: the normalizations are the same absolute norm, the sextic
characters agree by the symbol dictionary (both vanish off the units), and the
additive characters agree by the trace character dictionary.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F) (σ : F →+* ℂ)

theorem sexticExponent_natCast (j : ℕ) (hj : j < 6) : sexticExponent (j : ℤ) = j := by
  unfold sexticExponent
  omega

/-- For `0 < j < 6`, the `j`-th power of `σ` of the sextic residue is Axiom's
power character on the residue class; both vanish off the units. -/
theorem sexticResidue_pow_eq_powerChar (I : A.Exterior) (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6)
    (x : A.R) :
    σ (A.sexticResidue I x) ^ j =
      A.sexticResiduePowerChar σ I j (Ideal.Quotient.mk (A.extendIdeal I) x) := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) x)
  · obtain ⟨u, hu⟩ := hx
    unfold sexticResiduePowerChar
    rw [sexticExponent_natCast j hj6, ← hu, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe]
    congr 1
    change σ (MulChar.ofUnitHom (A.sexticResidueFamily I) (Ideal.Quotient.mk (A.extendIdeal I) x)) = _
    rw [← hu, MulChar.ofUnitHom_coe]
    rfl
  · rw [A.sexticResiduePowerChar_nonunit σ I j _ hx,
      ArithmeticContext.actual_sextic_nonunit A I x hx, map_zero, zero_pow hj0.ne']

namespace ArithmeticChoice

variable {S₀ : Finset (HeightOneSpectrum (𝓞 F))} {root12 : F} {τ : F →+* ℂ}
variable (X : ArithmeticChoice F S₀ root12 τ)

/-- The skeleton's exterior ideal as an Axiom exterior ideal. -/
abbrev axiomIdeal (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    X.A.Exterior :=
  (exteriorEquiv X.A).symm J

/-- The chosen allowed generator, as an `Sf`-integer. -/
abbrev generator (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) : X.A.R :=
  recipeGenerator X.A (recipeOfContext X.A X.C) J

theorem generator_generates (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) :
    X.A.Generates (X.axiomIdeal J) (X.generator J) :=
  (recipeGenerator_spec X.A (recipeOfContext X.A X.C) J).1

/-- Axiom's ideal Gauss sum of the chosen data. -/
abbrev gauss (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) (j : ℤ) : ℂ :=
  X.A.idealGauss τ X.hS (X.axiomIdeal J) (X.generator J) (X.generator_generates J) j

/-- The skeleton's principal additive character is Axiom's residue trace character. -/
theorem thetaPrincipalAddCharacter_eq
    (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) (r : X.A.R) :
    thetaPrincipalAddCharacter F (X.places : Set (HeightOneSpectrum (𝓞 F))) X.thetaData J
        (Ideal.Quotient.mk _ r) =
      (X.A.residueTraceCharacter X.hS (X.axiomIdeal J) (X.generator J) (X.generator_generates J)
        (Ideal.Quotient.mk (X.A.extendIdeal (X.axiomIdeal J)) r) : ℂ) := by
  rw [thetaPrincipalAddCharacter_mk, X.A.residueTraceCharacter_apply]
  exact sLocalPrincipalPhase_eq_fieldTraceCharacter X.A _

/-- The skeleton's sextic quotient function is `τ` of Axiom's sextic residue. -/
theorem sexticQuotientFunction_eq
    (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) (r : X.A.R) :
    sIntegerSexticIdealQuotientFunction F (X.places : Set (HeightOneSpectrum (𝓞 F)))
        X.thetaData.root6 X.thetaData.primitive6 X.thetaData.embedding J.val.val
        (nonZeroDivisors.coe_ne_zero J.val) J.property
        (fun p hp => X.thetaData.away_six p (J.property p hp)) (Ideal.Quotient.mk _ r) =
      τ (X.A.sexticResidue (X.axiomIdeal J) r) := by
  rw [sIntegerSexticIdealQuotientFunction_mk]
  exact sexticIdealEvaluation_eq_sexticResidue X.A τ (X.axiomIdeal J) r _ _ _

/-- The skeleton's normalized Gauss sum is Axiom's ideal Gauss sum, `0 < j < 6`. -/
theorem thetaGamma_eq_gauss
    (J : ExteriorIdeal F (X.places : Set (HeightOneSpectrum (𝓞 F)))) (j : ℕ)
    (hj0 : 0 < j) (hj6 : j < 6) :
    thetaGamma F (X.places : Set (HeightOneSpectrum (𝓞 F))) X.thetaData J j = X.gauss J j := by
  let _ : Finite (ThetaQuotient F (X.places : Set (HeightOneSpectrum (𝓞 F))) J) :=
    finite_sIntegerSexticIdealQuotient F _ J.val.val (nonZeroDivisors.coe_ne_zero J.val) J.property
  let _ : Fintype (ThetaQuotient F (X.places : Set (HeightOneSpectrum (𝓞 F))) J) :=
    Fintype.ofFinite _
  let _ : Finite (X.A.R ⧸ X.A.extendIdeal (X.axiomIdeal J)) :=
    X.A.exteriorResidue_finite (X.axiomIdeal J)
  let _ : Fintype (X.A.R ⧸ X.A.extendIdeal (X.axiomIdeal J)) := Fintype.ofFinite _
  change _ = X.A.idealGauss τ X.hS (X.axiomIdeal J) (X.generator J) (X.generator_generates J) j
  unfold thetaGamma idealGauss
  dsimp only
  congr 1
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun x => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Equiv.refl_apply, X.sexticQuotientFunction_eq J r, X.thetaPrincipalAddCharacter_eq J r,
    sexticResidue_pow_eq_powerChar X.A τ (X.axiomIdeal J) j hj0 hj6 r]
  rfl

end ArithmeticChoice

end HeckeAxiom
