import HeckeGeneral.Bridge.FLTCharacter
import HeckeGeneral.Analysis.HeckeSeries
import HeckeGeneral.Analysis.IdealEulerIdentity
import FLTReuse.Me1ad2f4bf19c4ff0
import FLTReuse.M18c3f30cb8384583
import FLTReuse.M157b087506702f5d
import FLTReuse.M0a341b9f001ae4d1
import FLTReuse.M40aeee35a98f067b
import FLTReuse.M07acf709d74d501a

/-!
# Identification with the actual Tate-theory characters and Euler product

The imported fixed-commit definitions describe actual adelic characters, local
restrictions, and Haar modulus. Their conventions are identified with the existing
character and ideal-series constructions. No analytic continuation is assumed here.
-/

noncomputable section

namespace HeckeGeneral.Bridge

open NumberField HeckeGeneral.Characters

variable (K : Type*) [Field K] [NumberField K]

theorem complexIdeleCharacter_isUnitary (χ : HeckeCharacter K) :
    AutomorphicForm.IsUnitaryChar (𝓞 K) K (complexIdeleCharacter K χ) :=
  norm_complexIdeleCharacter K χ

theorem complexIdeleCharacter_isIdeleClass (χ : HeckeCharacter K) :
    AutomorphicForm.IsIdeleClassChar (𝓞 K) K (complexIdeleCharacter K χ) :=
  complexIdeleCharacter_principal K χ

/-- The genuine FLT predicates are exactly the existing-side bridge predicates. -/
theorem complexUnitaryPrincipalTrivial_iff_flt (ψ : IdeleGroup (𝓞 K) K →* ℂˣ) :
    ComplexUnitaryPrincipalTrivial K ψ ↔
      Continuous (fun x => (ψ x : ℂ)) ∧
        AutomorphicForm.IsUnitaryChar (𝓞 K) K ψ ∧
        AutomorphicForm.IsIdeleClassChar (𝓞 K) K ψ := Iff.rfl

/-- Every FLT continuous unitary idele-class character comes from an actual Hecke character. -/
def heckeCharacterEquivFLT : HeckeCharacter K ≃
    {ψ : IdeleGroup (𝓞 K) K →* ℂˣ // Continuous (fun x => (ψ x : ℂ)) ∧
      AutomorphicForm.IsUnitaryChar (𝓞 K) K ψ ∧
      AutomorphicForm.IsIdeleClassChar (𝓞 K) K ψ} :=
  heckeCharacterEquivComplex K

section TateCompatibility

open IsDedekindDomain
open scoped Classical

-- The imported global Tate definitions have universe-zero number-field parameters.
variable (F : Type) [Field F] [NumberField F]

/-- Both libraries use the same single-place idele embedding. -/
theorem fltLocalEmbedding_eq (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
      (NumberField.AdelicLevel.localUnit (𝓞 F) F v u) = localIdeleEmbedding F v u := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext w
    rfl

/-- The actual local Tate character is our continuous local component embedded into units. -/
theorem fltLocalChar_eq (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    NumberField.TateGlobal.localChar (complexIdeleCharacter F χ) v u =
      Circle.toUnits (localComponent F v χ u) := by
  rw [NumberField.TateGlobal.localChar_apply, fltLocalEmbedding_eq]
  rfl

theorem fltUnramifiedAt_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.TateGlobal.IsUnramifiedCharAt (complexIdeleCharacter F χ) v ↔
      UnramifiedAt F χ v := by
  rw [unramifiedAt_iff_complex_integral_units]
  unfold NumberField.TateGlobal.IsUnramifiedCharAt
  simp only [NumberField.TateGlobal.localChar_apply, fltLocalEmbedding_eq]

/-- Different uniformizer choices have the same normalized positive valuation. -/
theorem fltUniformizerUnit_norm (v : HeightOneSpectrum (𝓞 F)) :
    ‖(NumberField.AdelicLevel.uniformizerUnit F v : v.adicCompletion F)‖ =
      (residueCard F v : ℝ)⁻¹ :=
  localNorm_eq_inv_residueCard_of_valuation F v _
    (NumberField.AdelicLevel.valued_uniformizerUnit F v)

/-- The actual Euler coefficient in the imported global Tate statements. -/
def fltPrimeCoefficient (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if NumberField.TateGlobal.IsUnramifiedCharAt (complexIdeleCharacter F χ) v then
    (complexIdeleCharacter F χ (AutomorphicForm.uniformizerIdele F v) : ℂ) else 0

theorem primeCoefficient_eq_flt (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    primeCoefficient F χ v = fltPrimeCoefficient F χ v := by
  unfold fltPrimeCoefficient
  rw [fltUnramifiedAt_iff]
  split_ifs with h
  · rw [primeCoefficient_eq_of_norm F χ v h
      (NumberField.AdelicLevel.uniformizerUnit F v) (fltUniformizerUnit_norm F v)]
    change (localComponent F v χ (NumberField.AdelicLevel.uniformizerUnit F v) : ℂ) =
      (complexIdeleCharacter F χ
        (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
          (NumberField.AdelicLevel.localUnit (𝓞 F) F v
            (NumberField.AdelicLevel.uniformizerUnit F v))) : ℂ)
    rw [fltLocalEmbedding_eq, complexIdeleCharacter_local]
  · exact primeCoefficient_of_ramified F χ v h

/-- The precise Euler product occurring in the imported Hecke continuation theorem. -/
def fltEulerProduct (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 F),
    (1 - fltPrimeCoefficient F χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹

/-- Its product genuinely converges to the existing series indexed by all nonzero ideals. -/
theorem hasProd_fltEulerProduct (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
      (1 - fltPrimeCoefficient F χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (HeckeGeneral.Analysis.heckeLSeries F χ s) := by
  have h := HeckeGeneral.Analysis.hasProd_idealDirichletSeries F (primeCoefficient F χ)
    (norm_primeCoefficient_le_one F χ) hs
  change HasProd _ (HeckeGeneral.Analysis.heckeLSeries F χ s) at h
  apply h.congr_fun
  intro v
  simp only [HeckeGeneral.Analysis.primeIdealRatio, primeCoefficient_eq_flt]

/-- The continuation's Euler-product input is the genuine convergent Hecke ideal series. -/
theorem heckeLSeries_eq_fltEulerProduct (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re) :
    HeckeGeneral.Analysis.heckeLSeries F χ s = fltEulerProduct F χ s :=
  (hasProd_fltEulerProduct F χ hs).tprod_eq.symm

/-- The Tate Haar modulus equals the already constructed normalized product norm. -/
theorem fltIdeleNorm_eq (x : IdeleGroup (𝓞 F) F) :
    NumberField.TateGlobal.ideleNorm F x = idelicNorm F x := by
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  unfold idelicNorm
  rw [InfiniteAdeleRing.norm_def]
  congr 1
  exact (NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit (finiteIdelePart F x)).symm

/-- Our positive ideal-norm twist is the negative-parameter Haar norm-power character. -/
theorem complexIdeleCharacter_normTwist_eq (t : ℝ) :
    complexIdeleCharacter F (heckeNormTwist F t) = NumberField.TateGlobal.normPowChar F (-t) := by
  ext x
  rw [complexIdeleCharacter_normTwist_coe, NumberField.TateGlobal.coe_normPowChar_apply,
    fltIdeleNorm_eq]
  norm_cast

/-- The exceptional norm-power branch also matches exactly, with no excluded characters. -/
theorem complexIdeleCharacter_eq_normPow_iff (χ : HeckeCharacter F) (t : ℝ) :
    complexIdeleCharacter F χ = NumberField.TateGlobal.normPowChar F t ↔
      χ = heckeNormTwist F (-t) := by
  constructor
  · intro h
    apply complexIdeleCharacter_injective F
    rw [complexIdeleCharacter_normTwist_eq]
    simpa only [neg_neg] using h
  · intro h
    rw [h, complexIdeleCharacter_normTwist_eq, neg_neg]

theorem complexIdeleCharacter_ne_normPow_iff (χ : HeckeCharacter F) :
    (∀ t : ℝ, complexIdeleCharacter F χ ≠ NumberField.TateGlobal.normPowChar F t) ↔
      ∀ t : ℝ, χ ≠ heckeNormTwist F t := by
  constructor
  · intro h t ht
    exact h (-t) ((complexIdeleCharacter_eq_normPow_iff F χ (-t)).mpr
      (by simpa only [neg_neg] using ht))
  · intro h t ht
    exact h (-t) ((complexIdeleCharacter_eq_normPow_iff F χ t).mp ht)

end TateCompatibility

end HeckeGeneral.Bridge
