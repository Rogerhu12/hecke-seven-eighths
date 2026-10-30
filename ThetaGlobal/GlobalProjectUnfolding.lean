module

public import ThetaGlobal.WeightedUnfolding
public import ThetaGlobal.GlobalProjectConvention
public import ThetaGlobal.GlobalTargetPeriod
public import DedekindZetaZeroFree.Theta.Unfolding.SheetFundamentalDomains

@[expose] public section

/-!
# Weighted unfolding on the actual norm sheets

Both substitutions use the fixed recipe's genuine sheet Haar measure:
`y ↦ a*y` on the direct side and `y ↦ a/y` on the reflected side.
The class cutoff and the target S-character stay inside the integral.
The reflected pairing is the inverse square of the actual Axiom pairing,
equivalently the square of the paper pairing.

The hypotheses are local-profile integrability and triviality of the
period on sixth S-units.  `GlobalTargetPeriod.period_gamma` proves the
latter for the actual target Hecke character.  No reflection identity
is used as an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectUnfolding

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open MeasureTheory
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "k" => QuotientGroup.mk' R.A.sixthPowers

theorem gamma_class (γ : R.A.Gamma1) : k γ.val.val = 1 := by
  let δ : R.A.Gamma := ⟨γ.val.val, γ.property⟩
  obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := δ.property
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨R.A.diagonal u, by simpa only [powMonoidHom_apply, map_pow] using hq⟩

theorem character_ne_zero (L : R.A.G →* ℂ) (y : R.A.G) : L y ≠ 0 := by
  have h : L y * L y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

def weight (L : R.A.G →* ℂ) (B : Subgroup R.A.V) (y : R.A.G) : ℂ :=
  (if k y ∈ B then 1 else 0) * (L y)⁻¹

def directWeight (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (κ : R.A.V) (v : R.A.G) : ℂ :=
  (if κ⁻¹ * k v ∈ B then 1 else 0) * (L v)⁻¹

def reflectedWeight (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (κ : R.A.V) (v : R.A.G) : ℂ :=
  (if κ * (k v)⁻¹ ∈ B then 1 else 0) *
    GlobalProjectConvention.paperHilbert R κ (k v) ^ 2 * L v

def reverseWeight (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (κ : R.A.V) (y : R.A.G) : ℂ :=
  weight R L B y * GlobalProjectConvention.paperHilbert R κ (k y⁻¹) ^ 2

theorem weight_gamma (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1) (γ : R.A.Gamma1) (y : R.A.G) :
    weight R L B (γ.val.val * y) = weight R L B y := by
  simp only [weight, map_mul, gamma_class, hL, one_mul]

theorem reverseWeight_gamma (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (κ : R.A.V) (γ : R.A.Gamma1) (y : R.A.G) :
    reverseWeight R L B κ (γ.val.val * y) = reverseWeight R L B κ y := by
  rw [reverseWeight, weight_gamma R L B hL]
  simp only [map_inv, map_mul, gamma_class, one_mul, reverseWeight]

theorem weight_mul_transport (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (a y : R.A.G) :
    weight R L B y = L a * directWeight R L B (k a) (a * y) := by
  simp only [weight, directWeight, map_mul, inv_mul_cancel_left, mul_inv_rev]
  field_simp [character_ne_zero R L a, character_ne_zero R L y] <;> ring

theorem reverseWeight_div_transport (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (a y : R.A.G) :
    reverseWeight R L B (k a) y =
      (L a)⁻¹ * reflectedWeight R L B (k a) (a / y) := by
  have hclass : k a * (k (a / y))⁻¹ = k y := by
    rw [map_div, inv_div]
    simp only [div_eq_mul_inv]
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  have hpair : GlobalProjectConvention.paperHilbert R (k a) (k (a / y)) =
      GlobalProjectConvention.paperHilbert R (k a) (k y⁻¹) := by
    unfold GlobalProjectConvention.paperHilbert
    rw [map_div, map_div, R.A.H_S6_alternating, one_div, map_inv, map_inv]
  unfold reverseWeight weight reflectedWeight
  rw [hclass, hpair, map_div, div_eq_mul_inv]
  field_simp [character_ne_zero R L a, character_ne_zero R L y] <;> ring

/-- Direct weighted orbit unfolding, with its exact absolute convergence. -/
theorem direct_sheet_unfold (w : InfinitePlace F) (μG : Measure R.A.G)
    [μG.IsHaarMeasure] (a : Fˣ) (x : PositiveAxis)
    (Ω : Set (Sheet R.A x))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG x))
    (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1) (f : R.A.G → ℂ)
    (hf : Integrable (fun v : Sheet R.A (q R.A a * x) =>
      directWeight R L B (k (R.A.diagonal a)) v.val * f v.val)
      (sheetHaar R.A w μG (q R.A a * x))) :
    Summable (fun γ : R.A.Gamma1 => ∫ y in Ω,
      weight R L B y.val * f (γ.val.val * R.A.diagonal a * y.val)
      ∂sheetHaar R.A w μG x) ∧
    (∑' γ : R.A.Gamma1, ∫ y in Ω,
      weight R L B y.val * f (γ.val.val * R.A.diagonal a * y.val)
      ∂sheetHaar R.A w μG x) =
      L (R.A.diagonal a) * ∫ v : Sheet R.A (q R.A a * x),
        directWeight R L B (k (R.A.diagonal a)) v.val * f v.val
        ∂sheetHaar R.A w μG (q R.A a * x) := by
  obtain ⟨hs, he⟩ := WeightedUnfolding.weighted_orbit_unfolding hΩ
    (sheetMul R.A a x).toMeasurableEquiv
    (sheetMul_measurePreserving R.A w μG a x)
    (fun y : Sheet R.A x => weight R L B y.val)
    (fun v : Sheet R.A (q R.A a * x) => directWeight R L B (k (R.A.diagonal a)) v.val)
    (fun v => f v.val) (L (R.A.diagonal a))
    (fun γ y => weight_gamma R L B hL γ y.val)
    (fun y => weight_mul_transport R L B (R.A.diagonal a) y.val) hf
  have heq (γ : R.A.Gamma1) :
      (∫ y in Ω, weight R L B y.val * f (sheetMul R.A a x (γ • y)).val
        ∂sheetHaar R.A w μG x) =
      ∫ y in Ω, weight R L B y.val *
        f (γ.val.val * R.A.diagonal a * y.val) ∂sheetHaar R.A w μG x := by
    apply integral_congr_ae
    filter_upwards [] with y
    congr 2
    change R.A.diagonal a * (γ.val.val * y.val) = _
    ac_rfl
  exact ⟨hs.congr heq, (tsum_congr fun γ => (heq γ).symm).trans he⟩

/-- Reflected weighted orbit unfolding.  The inverse action on the
unit orbit is reindexed explicitly, retaining the `a/y` substitution. -/
theorem reflected_sheet_unfold (w : InfinitePlace F) (μG : Measure R.A.G)
    [μG.IsHaarMeasure] (a : Fˣ) (x : PositiveAxis)
    (Ω : Set (Sheet R.A x))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG x))
    (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1) (f : R.A.G → ℂ)
    (hf : Integrable (fun v : Sheet R.A (q R.A a / x) =>
      reflectedWeight R L B (k (R.A.diagonal a)) v.val * f v.val)
      (sheetHaar R.A w μG (q R.A a / x))) :
    Summable (fun γ : R.A.Gamma1 => ∫ y in Ω,
      reverseWeight R L B (k (R.A.diagonal a)) y.val *
        f (γ.val.val * R.A.diagonal a / y.val) ∂sheetHaar R.A w μG x) ∧
    (∑' γ : R.A.Gamma1, ∫ y in Ω,
      reverseWeight R L B (k (R.A.diagonal a)) y.val *
        f (γ.val.val * R.A.diagonal a / y.val) ∂sheetHaar R.A w μG x) =
      (L (R.A.diagonal a))⁻¹ * ∫ v : Sheet R.A (q R.A a / x),
        reflectedWeight R L B (k (R.A.diagonal a)) v.val * f v.val
        ∂sheetHaar R.A w μG (q R.A a / x) := by
  let piece := fun γ : R.A.Gamma1 => ∫ y in Ω,
    reverseWeight R L B (k (R.A.diagonal a)) y.val *
      f (sheetDiv R.A a x (γ • y)).val ∂sheetHaar R.A w μG x
  obtain ⟨hs, he⟩ := WeightedUnfolding.weighted_orbit_unfolding hΩ
    (sheetDiv R.A a x).toMeasurableEquiv
    (sheetDiv_measurePreserving R.A w μG a x)
    (fun y : Sheet R.A x => reverseWeight R L B (k (R.A.diagonal a)) y.val)
    (fun v : Sheet R.A (q R.A a / x) => reflectedWeight R L B (k (R.A.diagonal a)) v.val)
    (fun v => f v.val) (L (R.A.diagonal a))⁻¹
    (fun γ y => reverseWeight_gamma R L B hL _ γ y.val)
    (fun y => reverseWeight_div_transport R L B (R.A.diagonal a) y.val) hf
  change Summable piece at hs
  change (∑' γ, piece γ) = _ at he
  have heq (γ : R.A.Gamma1) : piece γ⁻¹ = ∫ y in Ω,
      reverseWeight R L B (k (R.A.diagonal a)) y.val *
        f (γ.val.val * R.A.diagonal a / y.val) ∂sheetHaar R.A w μG x := by
    apply integral_congr_ae
    filter_upwards [] with y
    congr 2
    change R.A.diagonal a / (γ.val.val⁻¹ * y.val) = _
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl
  have hs' := hs.comp_injective (Equiv.inv R.A.Gamma1).injective
  have he' := ((Equiv.inv R.A.Gamma1).tsum_eq piece).trans he
  simp only [Function.comp_def, Equiv.inv_apply] at hs'
  simp only [Equiv.inv_apply] at he'
  simp_rw [heq] at hs' he'
  exact ⟨hs', he'⟩

end ThetaGlobal.GlobalProjectUnfolding
