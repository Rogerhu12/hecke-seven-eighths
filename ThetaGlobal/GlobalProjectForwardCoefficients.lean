import ThetaGlobal.GlobalProjectLocalDigitTables
import ThetaGlobal.GlobalProjectOrbitCoefficients

/-!
# Literal forward masks and their actual rational-unit invariance

The ordinary mask uses the zero-extended character even at digit zero.
The constant marked average is the complementary residue delta.  The
product with the genuine spherical exterior coefficient vanishes at
every nonintegral frequency and descends to the sixth S-unit quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectForwardCoefficients

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectDigitProduct ThetaGlobal.GlobalProjectLocalDigitTables
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

theorem marked_forward (p : P) (t : ThetaDigitAverage.Residue p.val) :
    (∑ v : ThetaDigitAverage.Residue p.val,
      (p.val.asIdeal.absNorm : ℂ)⁻¹ * Characters.psi R p (t * v)) =
        if t = 0 then 1 else 0 := by
  rw [← Finset.mul_sum]
  have h := AddChar.sum_mulShift t (Characters.primitive R p)
  have hc : Fintype.card (ThetaDigitAverage.Residue p.val) = p.val.asIdeal.absNorm :=
    AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField F p.val
  rw [hc] at h
  simp_rw [mul_comm _ t] at h
  rw [h]
  by_cases ht : t = 0
  · have hn : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one
        (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)).ne'
    simp [ht, hn]
  · simp [ht]

variable (Adata : ThetaArithmeticData F Sf)

def localMask (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ) : ℂ :=
  if marked then
    if ThetaBranch.unitResidue p.val x = 0 then 1 else 0
  else
    if ThetaBranch.unitResidue p.val x = 0 then 0 else
      thetaPrimeCharacter F Sf Adata (skeletonPrime R p) (ThetaBranch.unitResidue p.val x) ^ j.val

theorem localMask_gamma (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) :
    localMask R Adata p j marked (γ.val * x) = localMask R Adata p j marked x := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  let u' : R.A.U := ⟨u, hu⟩
  change u ^ 6 = γ.val at he
  rw [← he, mul_comm (u ^ 6) x]
  have hu0 : ThetaBranch.order p.val (u ^ 6) = 0 := by
    rw [← zpow_natCast, ThetaBranch.ord_zpow, ThetaBranch.unit_ord R.A p u', mul_zero]
  by_cases hx : ThetaBranch.order p.val x = 0
  · have hn := ThetaBranch.unitResidue_ne_zero p.val x hx
    have hun := ThetaBranch.unitResidue_ne_zero p.val u (ThetaBranch.unit_ord R.A p u')
    have hred := ThetaBranch.reduction_mul p.val x (u ^ 6) hx hu0
    rw [ThetaBranch.reduction_pow p.val u (ThetaBranch.unit_ord R.A p u')] at hred
    unfold localMask
    rw [hred]
    simp only [hn, pow_ne_zero 6 hun, mul_ne_zero, ↓reduceIte, map_mul, map_pow]
    rw [ThetaBranch.char_pow_six _
      (GlobalProjectFrequency.thetaPrimeCharacter_order_six F Sf Adata (skeletonPrime R p))
      _ hun, mul_one]
  · have hx' : ThetaBranch.order p.val (x * u ^ 6) ≠ 0 := by
      rw [ThetaBranch.ord_mul, hu0, add_zero]
      exact hx
    simp only [localMask, ThetaBranch.unitResidue, dif_neg hx, dif_neg hx']

theorem forwardCoefficient_literal (H : Input R D Adata)
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool)
    (x : Fˣ) (hx : (x : F) ∈ R.A.R) :
    forwardCoefficient R m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x =
      ∏ p : RowPrime R m, localMask R Adata (exteriorRowPrime R m p) (j p) (marked p) x := by
  rw [GlobalProjectLiteralDigitWeights.tensorWeight,
    forwardCoefficient_product R m x
      (fun p hp => hx p ((ThetaDigitAverage.rowPrimes_finite R.A m.val m.property).mem_toFinset.mp hp).1)]
  apply Finset.prod_congr rfl
  intro p _
  cases hmark : marked p with
  | false => simpa only [hmark, Bool.false_eq_true, if_false, localMask] using
      H.forward_mask (exteriorRowPrime R m p) (j p) (ThetaBranch.unitResidue p.val x)
  | true => simpa only [hmark, Bool.true_eq, if_true, localMask] using
      marked_forward R (exteriorRowPrime R m p) (ThetaBranch.unitResidue p.val x)

def scalar (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ) (x : Fˣ) : ℂ :=
  forwardCoefficient R m c x * ∏ᶠ p : P, D.exteriorValue R p x

theorem exteriorProduct_finite (E : ExteriorCoefficients R Q T D) (x : Fˣ) :
    Function.HasFiniteMulSupport (fun p : P => D.exteriorValue R p x) := by
  apply (exterior_order_support_finite R x).subset
  intro p hp
  by_contra hn
  simp only [Set.mem_setOf_eq, not_not] at hn
  apply hp
  rw [E.rational_exact]
  exact sphericalFactor_order_zero R p x hn

theorem scalar_nonintegral (E : ExteriorCoefficients R Q T D)
    (m : ThetaReflectionData.Row R.A) (c : GlobalProjectWeightedDigits.Digits R m → ℂ)
    (x : Fˣ) (hx : (x : F) ∉ R.A.R) : scalar R D m c x = 0 := by
  have hn : ∃ p : P, 1 < p.val.valuation F (x : F) := by
    change ¬ (∀ p, p ∉ R.A.Sf → p.valuation F (x : F) ≤ 1) at hx
    push Not at hx
    obtain ⟨p, hp, hv⟩ := hx
    exact ⟨⟨p, hp⟩, hv⟩
  obtain ⟨p, hp⟩ := hn
  have hz : (∏ᶠ q : P, D.exteriorValue R q x) = 0 := by
    apply finprod_eq_zero _ p _ (exteriorProduct_finite R D E x)
    rw [E.rational_exact]
    simp only [ThetaBranch.sphericalFactor, sexticSphericalCoefficient,
      if_pos (order_negative_of_valuation_gt_one p.val x hp), zero_mul]
  simp only [scalar, hz, mul_zero]

theorem gamma_integral_iff (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    (γ.val * x : Fˣ).val ∈ R.A.R ↔ (x : F) ∈ R.A.R := by
  constructor
  · intro h p hp
    have hg := gamma_valuation R γ ⟨p, hp⟩
    simpa only [Units.val_mul, map_mul, hg, one_mul] using h p hp
  · intro h p hp
    have hg := gamma_valuation R γ ⟨p, hp⟩
    simpa only [Units.val_mul, map_mul, hg, one_mul] using h p hp

theorem scalar_gamma (E : ExteriorCoefficients R Q T D) (H : Input R D Adata)
    (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool)
    (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    scalar R D m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) (γ.val * x) =
      scalar R D m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x := by
  by_cases hx : (x : F) ∈ R.A.R
  · rw [scalar, scalar, forwardCoefficient_literal R D Adata H m j marked _
      ((gamma_integral_iff R x γ).mpr hx), forwardCoefficient_literal R D Adata H m j marked x hx,
      GlobalProjectOrbitCoefficients.exteriorProduct_gamma R D E]
    simp_rw [localMask_gamma R Adata]
  · rw [scalar_nonintegral R D E m _ x hx,
      scalar_nonintegral R D E m _ (γ.val * x) (fun h => hx ((gamma_integral_iff R x γ).mp h))]

end ThetaGlobal.GlobalProjectForwardCoefficients
