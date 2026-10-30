import ThetaGlobal.GlobalTargetPeriod
import ThetaGlobal.GlobalProjectConvention
import HeckeAxiom.SexticSymbolDictionary
import HeckeGeneral.Analysis.HeckeSeries

/-!
# The target period evaluated on the fixed allowed generators

The principal-idele law is used for an arbitrary unitary Hecke character.
In particular, no finite-order hypothesis is imposed on its unramified
uniformizer values.  The auxiliary finite set used in the proof does not
change the chosen arithmetic data: it only contains the support of one
principal element while proving the product formula.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalGeneratorPeriod

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

theorem localComponent_of_valuation
    (θ : HeckeCharacter F) (p : HeightOneSpectrum (𝓞 F))
    (hθ : UnramifiedAt F θ p) (x : (p.adicCompletion F)ˣ) (e : ℕ)
    (hx : (Valued.v x.val : WithZero (Multiplicative ℤ)) = WithZero.exp (-(e : ℤ))) :
    (localComponent F p θ x : ℂ) = primeCoefficient F θ p ^ e := by
  let π := localUniformizerUnit F p
  let y : (p.adicCompletion F)ˣ := x * π ^ (-(e : ℤ))
  have hyv : (Valued.v y.val : WithZero (Multiplicative ℤ)) = 1 := by
    change Valued.v (x.val * (π ^ (-(e : ℤ)) : (p.adicCompletion F)ˣ).val) = 1
    rw [Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx,
      localUniformizerUnit_val, localUniformizer_valuation,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    have hzero : -(e : ℤ) + (-(e : ℤ)) • (-1 : ℤ) = 0 := by simp
    rw [hzero]
    rfl
  have hy : ‖y.val‖ = 1 :=
    (Valued.toNormedField.norm_eq_one_iff (L := p.adicCompletion F)
      (Γ₀ := WithZero (Multiplicative ℤ))).mpr hyv
  have hθy : localComponent F p θ y = 1 := hθ y hy
  have hxy : x = y * π ^ e := by
    change x = x * π ^ (-(e : ℤ)) * π ^ e
    rw [mul_assoc, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [hxy, map_mul, hθy, one_mul, map_pow, primeCoefficient_of_unramified F θ p hθ]
  simp [π]

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

/-- Every diagonal S-unit has trivial target period. The Hilbert part
uses actual global S-unit isotropy, not merely sixth-power invariance. -/
theorem period_diagonal_unit (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (u : R.A.UnitQuotient) (v : R.A.U) :
    GlobalTargetPeriod.period R θ u (R.A.diagonal v.val) = 1 := by
  have hp : TargetFinitePeriod.sectorPhaseHom R u (R.A.diagonal v.val) = 1 := by
    change R.σ ((R.A.H_S (R.A.diagonal (R.probe.unitReps.representative u).val)
      (R.A.diagonal v.val) : Fˣ) : F) = 1
    rw [R.A.H_S_sunit_isotropy]
    simp
  change ((GlobalTargetPeriod.sHeckeHom R θ (R.A.diagonal v.val) : Circle) : ℂ)⁻¹ *
    TargetFinitePeriod.sectorPhaseHom R u (R.A.diagonal v.val) = 1
  rw [GlobalTargetPeriod.sHeckeHom_diagonal_unit R θ hS v, hp]
  simp

/-- The stored unit section and any representative of its class give
the same actual sextic residue, including the actual row unit. -/
theorem sexticResidue_unitRepresentative (u : R.A.U) (I : R.A.Exterior) :
    R.A.sexticResidue I
      (R.A.unitEquiv (R.probe.unitReps.representative (QuotientGroup.mk u)) : R.A.R) =
    R.A.sexticResidue I (R.A.unitEquiv u : R.A.R) := by
  let v := R.probe.unitReps.representative (QuotientGroup.mk u)
  have hq : (QuotientGroup.mk v : R.A.UnitQuotient) = QuotientGroup.mk u :=
    R.probe.unitReps.represents (QuotientGroup.mk u)
  have hr := Quotient.exact hq
  change QuotientGroup.leftRel R.A.unitSixthPowers v u at hr
  rw [QuotientGroup.leftRel_apply] at hr
  obtain ⟨w, hw⟩ := hr
  change w ^ 6 = v⁻¹ * u at hw
  have hu : u = v * w ^ 6 := by rw [hw, mul_inv_cancel_left]
  symm
  rw [hu, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val,
    R.A.sexticResidue_sixth_unit_translate]

private theorem mem_support_iff (I : R.A.Exterior) (p : HeightOneSpectrum (𝓞 F)) :
    p ∈ ThetaBranch.support I.val ↔ idealPrimeExponent p.asIdeal I.val ≠ 0 := by
  simp only [ThetaBranch.support, Finset.mem_preimage, idealPrimeSupport,
    idealPrimeExponent, Multiset.mem_toFinset, Multiset.count_ne_zero]

theorem idealCoefficient_product (θ : HeckeCharacter F) (I : R.A.Exterior) :
    heckeIdealCoefficient F θ (HeckeAxiom.exteriorEquiv R.A I).val =
      ∏ p ∈ ThetaBranch.support I.val,
        primeCoefficient F θ p ^ idealPrimeExponent p.asIdeal I.val := by
  let I₀ : (Ideal (𝓞 F))⁰ := (HeckeAxiom.exteriorEquiv R.A I).val
  have hsupp : (primeExponents I₀).support ⊆ ThetaBranch.support I.val := by
    intro p hp
    apply (mem_support_iff R I p).mpr
    simpa only [Finsupp.mem_support_iff, primeExponents_apply, idealPrimeExponent]
      using hp
  have hI : I.val = (idealOfPrimeExponents (primeExponents I₀)).val :=
    (congrArg Subtype.val (idealOfPrimeExponents_primeExponents I₀)).symm
  change (idealCoefficientHom (primeCoefficient F θ)).toMonoidHom I.val = _
  rw [hI, map_idealOfPrimeExponents,
    Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _)]
  apply Finset.prod_congr rfl
  intro p _
  change idealCoefficient (primeCoefficient F θ) p.asIdeal ^ primeExponents I₀ p = _
  rw [idealCoefficient_prime]
  rfl

/-- The inverse S-character is the genuine ideal coefficient, for every
allowed generator and every character unramified outside the fixed S. -/
theorem inverse_sHeckeHom_generator (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (I : R.A.Exterior) :
    ((GlobalTargetPeriod.sHeckeHom R θ
      (R.A.diagonal (R.probe.allowed.generator I)) : Circle) : ℂ)⁻¹ =
        heckeIdealCoefficient F θ (HeckeAxiom.exteriorEquiv R.A I).val := by
  obtain ⟨r, hr, har⟩ := R.probe.allowed.generates I
  let a := R.probe.allowed.generator I
  let T := R.A.Sf ∪ ThetaBranch.support I.val
  have hdis : Disjoint R.A.Sf (ThetaBranch.support I.val) := by
    apply Finset.disjoint_left.mpr
    intro p hp hs
    exact ThetaBranch.support_outside R.A I p hs hp
  have hT : conductorPlaces F θ ⊆ T := fun p hp =>
    Finset.mem_union_left _ (hS hp)
  have ha : a ∈ (T : Set (HeightOneSpectrum (𝓞 F))).unit F := by
    intro p hp
    have hpS : p ∉ R.A.Sf := fun h => hp (Finset.mem_union_left _ h)
    have hpI : p ∉ ThetaBranch.support I.val := fun h => hp (Finset.mem_union_right _ h)
    have hz : idealPrimeExponent p.asIdeal I.val = 0 :=
      not_ne_iff.mp (fun h => hpI ((mem_support_iff R I p).mpr h))
    change p.valuation F (a : F) = 1
    rw [har, SIntegerLocalization.generator_valuation R.A.Sf I.val I.property.1
      r hr.1 hr.2 p hpS, hz]
    rfl
  let u : (T : Set (HeightOneSpectrum (𝓞 F))).unit F := ⟨a, ha⟩
  have hprincipal := sUnitFinite_mul_infinity_eq_one F (T : Set _) θ u
  rw [HeckeAxiom.sUnitFiniteCharacter_eq_prod F T θ hT u] at hprincipal
  have hprincipalC := congrArg Circle.coeHom hprincipal
  simp only [map_mul, map_prod, map_one] at hprincipalC
  let localValue (p : HeightOneSpectrum (𝓞 F)) : ℂ :=
    (localComponent F p θ (sUnitLocal F (T : Set _) p u) : ℂ)
  have hlocal (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ ThetaBranch.support I.val) :
      localValue p = primeCoefficient F θ p ^ idealPrimeExponent p.asIdeal I.val := by
    have hpS := ThetaBranch.support_outside R.A I p hp
    have hθ : UnramifiedAt F θ p := by
      by_contra hn
      exact hpS (hS ((mem_conductorPlaces F θ p).mpr hn))
    apply localComponent_of_valuation θ p hθ _ _
    change Valued.v (((a : F) : p.adicCompletion F)) = _
    rw [adicCompletion.valued_coe, har,
      SIntegerLocalization.generator_valuation R.A.Sf I.val I.property.1
        r hr.1 hr.2 p hpS]
  have hIprod : (∏ p ∈ ThetaBranch.support I.val, localValue p) =
      heckeIdealCoefficient F θ (HeckeAxiom.exteriorEquiv R.A I).val := by
    rw [idealCoefficient_product R]
    exact Finset.prod_congr rfl hlocal
  have hSprod : (∏ p ∈ R.A.Sf, localValue p) =
      ∏ p : R.A.Sf,
        (localComponent F p.val θ ((R.A.diagonal a).2 p) : ℂ) := by
    symm
    exact Finset.prod_coe_sort R.A.Sf localValue
  have harch : (sUnitInfinityCharacter F (T : Set _) θ u : ℂ) =
      ∏ w : InfinitePlace F,
        (infiniteComponent F w θ ((R.A.diagonal a).1 w) : ℂ) := by
    change Circle.coeHom (∏ w : InfinitePlace F,
      infiniteComponent F w θ ((R.A.diagonal a).1 w)) = _
    rw [map_prod]
    rfl
  have hprod : ((GlobalTargetPeriod.sHeckeHom R θ (R.A.diagonal a) : Circle) : ℂ) *
      heckeIdealCoefficient F θ (HeckeAxiom.exteriorEquiv R.A I).val = 1 := by
    change ((∏ w : InfinitePlace F,
      (infiniteComponent F w θ ((R.A.diagonal a).1 w) : ℂ)) *
      (∏ p : R.A.Sf,
        (localComponent F p.val θ ((R.A.diagonal a).2 p) : ℂ))) * _ = 1
    change (∏ p ∈ T, localValue p) *
      (sUnitInfinityCharacter F (T : Set _) θ u : ℂ) = 1 at hprincipalC
    rw [Finset.prod_union hdis, hIprod, hSprod, harch] at hprincipalC
    convert hprincipalC using 1 <;> ring
  exact inv_eq_of_mul_eq_one_right hprod

/-- The positive Axiom Hilbert sector is exactly the residue-symbol
twist of the fixed unit representative. -/
theorem sectorPhase_generator (u : R.A.UnitQuotient) (I : R.A.Exterior) :
    TargetFinitePeriod.sectorPhaseHom R u
      (R.A.diagonal (R.probe.allowed.generator I)) =
        R.σ (R.A.sexticResidue I
          (R.A.unitEquiv (R.probe.unitReps.representative u) : R.A.R)) := by
  obtain ⟨r, hr, har⟩ := R.probe.allowed.generates I
  have ha : ThetaReflectionData.rationalClass R.A (R.probe.allowed.generator I) ∈
      R.probe.correction.B := by
    rw [← R.probe.sameComplement]
    exact R.probe.allowed.allowed I
  have h := GlobalProjectConvention.unit_residue_eq_paperHilbert_inv R I r
    (R.probe.allowed.generator I) (R.probe.unitReps.representative u) hr har ha
  rw [GlobalProjectConvention.paperHilbert_on_representatives, inv_inv] at h
  exact h.symm

theorem period_generator (θ : HeckeCharacter F)
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (u : R.A.UnitQuotient) (I : R.A.Exterior) :
    GlobalTargetPeriod.period R θ u
      (R.A.diagonal (R.probe.allowed.generator I)) =
        heckeIdealCoefficient F θ (HeckeAxiom.exteriorEquiv R.A I).val *
          R.σ (R.A.sexticResidue I
            (R.A.unitEquiv (R.probe.unitReps.representative u) : R.A.R)) := by
  change ((GlobalTargetPeriod.sHeckeHom R θ
    (R.A.diagonal (R.probe.allowed.generator I)) : Circle) : ℂ)⁻¹ * _ = _
  rw [inverse_sHeckeHom_generator R θ hS, sectorPhase_generator R]

end ThetaGlobal.GlobalGeneratorPeriod
