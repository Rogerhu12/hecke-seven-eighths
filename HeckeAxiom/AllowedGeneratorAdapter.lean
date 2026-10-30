import HeckeAxiom.ArithmeticAdapter
import HeckeGeneral.Analysis.GlobalThetaData
import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators

/-!
# Multiplicativity of the recipe generators

For the theta arithmetic data built from an Axiom allowed-generator recipe,
the generator of a product of exterior ideals is the product of the two
generators times the sixth power of an `Sf`-unit. This is the `multiplicative`
field of the skeleton's `AllowedGeneratorInput`.

Both sides generate the same ideal and are allowed for the recipe's complement
`B`, so their ratio is a sixth power of a unit. The uniqueness step below is
Axiom's `allowed_generator_unique_mod_sixth`, restated for any complement of
`E`: its proof uses only `IsCompl A.E B`, which every recipe records, and not
the isotropy of an `IsSUnitIsotropicComplement`.
-/

noncomputable section

namespace HeckeAxiom

open NumberField IsDedekindDomain
open DedekindZetaZeroFree DedekindZetaZeroFree.SArithmeticData
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

/-- Two allowed generators of one fractional ideal differ by the sixth power of
an `Sf`-unit, for any complement `B` of the unit classes `E`. -/
theorem unique_mod_sixth_of_isCompl (hCl : Subsingleton (ClassGroup A.R))
    {B : Subgroup A.V} (hB : IsCompl A.E B) (I : FractionalIdeal A.R⁰ F) (a a' : Fˣ)
    (ha : A.IsAllowedGenerator B I a) (ha' : A.IsAllowedGenerator B I a') :
    a / a' ∈ A.sUnitSixthPowers := by
  have heq : FractionalIdeal.spanSingleton A.R⁰ (a' : F) =
      FractionalIdeal.spanSingleton A.R⁰ (a : F) := ha'.1.symm.trans ha.1
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp heq
  let ε : A.U := A.unitEquiv.symm z
  have hzval : (ε.val : F) = ((z : A.R) : F) := by
    simp [ε, SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
  have hratio : a / a' = ε.val := by
    apply Units.ext
    rw [Units.val_div_eq_div_val, div_eq_iff a'.ne_zero, hzval]
    exact hz.symm
  have hE : A.sClass ε.val ∈ A.E := ⟨A.diagonal ε.val, ⟨ε.val, ε.property, rfl⟩, rfl⟩
  have hmemB : A.sClass ε.val ∈ B := by
    rw [← hratio, map_div]
    exact B.div_mem ha.2 ha'.2
  have hc : A.sClass ε.val = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hB.disjoint.eq_bot]
    exact ⟨hE, hmemB⟩
  obtain ⟨g, hg⟩ : A.diagonal ε.val ∈ A.sixthPowers := (QuotientGroup.eq_one_iff _).mp hc
  have hloc :
      (∀ w, ∃ b, b ^ 6 = (A.diagonal ε.val).1 w) ∧
      (∀ v, ∃ b, b ^ 6 = (A.diagonal ε.val).2 v) :=
    ⟨fun w => ⟨g.1 w, congrArg (fun x : A.G => x.1 w) hg⟩,
      fun v => ⟨g.2 v, congrArg (fun x : A.G => x.2 v) hg⟩⟩
  obtain ⟨b, hb⟩ := A.local_power_injection F hCl 6 (by simp) ε hloc
  rw [hratio]
  exact ⟨b.val, b.property, congrArg Subtype.val hb⟩

variable (allowed : ThetaBranch.AllowedRecipe A)

/-- Each recipe generator is an allowed generator of its extended ideal. -/
theorem recipe_isAllowedGenerator (I : A.Exterior) :
    A.IsAllowedGenerator allowed.B (A.extendIdeal I : FractionalIdeal A.R⁰ F)
      (allowed.generator I) := by
  obtain ⟨r, ⟨-, hspan⟩, hgen⟩ := allowed.generates I
  refine ⟨?_, allowed.allowed I⟩
  rw [← hspan, FractionalIdeal.coeIdeal_span_singleton]
  congr 1
  exact hgen.symm

/-- The generator of a product is the product of the generators up to the
sixth power of an `Sf`-unit. -/
theorem recipe_generator_mul (hCl : Subsingleton (ClassGroup A.R))
    (I J IJ : A.Exterior) (hIJ : IJ.val = I.val * J.val) :
    ∃ u : A.U, (allowed.generator IJ : F) =
      ((u : Fˣ) : F) ^ 6 * allowed.generator I * allowed.generator J := by
  have hideal : (A.extendIdeal IJ : FractionalIdeal A.R⁰ F) =
      (A.extendIdeal I : FractionalIdeal A.R⁰ F) * (A.extendIdeal J : FractionalIdeal A.R⁰ F) := by
    rw [← FractionalIdeal.coeIdeal_mul]
    congr 1
    simp only [SArithmeticData.extendIdeal, hIJ, Ideal.map_mul]
  have hprod := A.allowed_generator_mul allowed.B _ _ _ _
    (recipe_isAllowedGenerator A allowed I) (recipe_isAllowedGenerator A allowed J)
  rw [← hideal] at hprod
  obtain ⟨y, hy, hpow⟩ := Subgroup.mem_map.mp
    (unique_mod_sixth_of_isCompl A hCl allowed.complement _ _ _
      (recipe_isAllowedGenerator A allowed IJ) hprod)
  refine ⟨⟨y, hy⟩, ?_⟩
  have h := congrArg (fun x : Fˣ => (x : F)) hpow
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val,
    Units.val_mul] at h
  rw [eq_div_iff (mul_ne_zero (allowed.generator I).ne_zero (allowed.generator J).ne_zero)] at h
  rw [← h, mul_assoc]

/-- The `multiplicative` field of `AllowedGeneratorInput` for the recipe data. -/
theorem thetaArithmeticData_multiplicative (σ : F →+* ℂ)
    (hdiff : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 F))) →
      HeckeGeneral.Characters.localDifferentExponent F p = 0)
    (hCl : Subsingleton (ClassGroup A.R))
    (I J : ExteriorIdeal F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))) :
    ∃ u : (A.Sf : Set (HeightOneSpectrum (𝓞 F))).unit F,
      (thetaArithmeticData A allowed σ hdiff).generator
          (exteriorMul F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) I J) =
        ((A.Sf : Set (HeightOneSpectrum (𝓞 F))).unitEquivUnitsInteger F u).val ^ 6 *
          (thetaArithmeticData A allowed σ hdiff).generator I *
          (thetaArithmeticData A allowed σ hdiff).generator J := by
  obtain ⟨u, hu⟩ := recipe_generator_mul A allowed hCl ((exteriorEquiv A).symm I)
    ((exteriorEquiv A).symm J)
    ((exteriorEquiv A).symm (exteriorMul F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) I J)) rfl
  refine ⟨u, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, thetaArithmeticData_generator]
  exact hu

end HeckeAxiom
