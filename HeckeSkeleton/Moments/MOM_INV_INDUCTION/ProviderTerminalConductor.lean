import HeckeSkeleton.LowEnergy.ActualFrozenCharges
import Lean.Elab.Tactic.Omega

/-!
# The actual punctured-label terminal conductor bound

The row is split into its genuine powerful part, its valuation-one
part supported on the label/puncture, and its remaining squarefree
part. The reflected frozen ideal contains the first two parts and the
fourth power of the actual averaged label.

For every literal frozen state, the active conductor radical squared
divides the powerful/supported/label/puncture product times the three
actual minimum-charge ideals. This discharges the conductor-cost input
of the terminal logarithmic ledger by prime exponents, including the
zero-digit and cube-minimum branches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderTerminalConductor

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbolProducts
open HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualReflectionReindex HeckeSkeleton.LowEnergy.ActualFrozenCharges
open scoped Classical BigOperators nonZeroDivisors

/-- The exact local charging inequality. When no powerful or supported
row prime is present, a lone label prime has digit four and a lone
puncture prime has digit zero; either has the additional minimum charge. -/
theorem local_conductor_charge (p j f r m : ℕ)
    (hp : p = 0 ∨ 2 ≤ p) (hactive : p + j + 4 * f ≠ 0 ∨ r ≠ 0)
    (hm : m = 0 ∨ m = 1 ∨ m = 3) :
    2 ≤ p + 2 * j + f + r + (if m = 1 then 1 else 0) +
      (if m = 0 ∧ ((p + j + 4 * f) % 6 = 0 ∨ (p + j + 4 * f) % 6 = 4)
        then 1 else 0) + 4 * (if m = 3 then 1 else 0) := by
  by_cases hbudget : 2 ≤ p + 2 * j + f + r
  · omega
  have hp0 : p = 0 := by omega
  have hj0 : j = 0 := by omega
  have hf : f = 0 ∨ f = 1 := by omega
  have hdigit : (p + j + 4 * f) % 6 = 0 ∨ (p + j + 4 * f) % 6 = 4 := by
    rcases hf with hf | hf <;> simp [hp0, hj0, hf]
  rcases hm with hm | hm | hm <;> simp [hm, hdigit] <;> omega

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

theorem exponent_primeSetIdeal (T : Finset (ExteriorPrime K S)) (p : ExteriorPrime K S) :
    primeExponents (primeSetIdeal K S T).val p.val = if p ∈ T then 1 else 0 := by
  change primeExponents (squarefreeIdeal K (T.image Subtype.val)) p.val = _
  rw [primeExponents_squarefreeIdeal]
  simp only [mem_image_prime_val]

def frozenIdeal (P J f : Ext) : Ext :=
  exteriorMul K S (exteriorMul K S P J) (exteriorPower K S f 4)

theorem frozenIdeal_exponent (P J f : Ext) (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (frozenIdeal K S P J f).val p =
      primeExponents P.val p + primeExponents J.val p + 4 * primeExponents f.val p := by
  change primeExponents ((P.val * J.val) * f.val ^ 4) p = _
  rw [primeExponents_mul, Finsupp.add_apply, primeExponents_mul, Finsupp.add_apply,
    exponent_pow]

/-- No squarefreeness or disjointness is silently imposed on the frozen
label or puncture in this conductor inequality. Their full multiplicity
can only improve the budget. -/
theorem conductor_divisibility (P J f r : Ext) (hP : Powerful P.val)
    (s : FrozenState K S (frozenIdeal K S P J f) r) :
    (primeSetIdeal K S s.active).val.val ^ 2 ∣
      P.val.val * J.val.val ^ 2 * f.val.val * r.val.val *
        (minimumLinearIdeal K S s).val.val * (minimumSmallIdeal K S s).val.val *
          (minimumCubeIdeal K S s).val.val ^ 4 := by
  let B : (Ideal (𝓞 K))⁰ := P.val * J.val ^ 2 * f.val * r.val *
    (minimumLinearIdeal K S s).val * (minimumSmallIdeal K S s).val *
      (minimumCubeIdeal K S s).val ^ 4
  have hd : ((primeSetIdeal K S s.active).val ^ 2).val ∣ B.val := by
    apply dvd_of_exponents_le
    intro q
    by_cases hq : primeExponents (primeSetIdeal K S s.active).val q = 0
    · rw [exponent_pow, hq, mul_zero]
      exact Nat.zero_le _
    have hqS : q ∉ S := (primeSetIdeal K S s.active).property q
      ((exponent_ne_zero_iff_dvd _ q).mp hq)
    let p : ExteriorPrime K S := ⟨q, hqS⟩
    have hp : p ∈ s.active := (prime_dvd_primeSetIdeal_iff K S s.active p).mp
      ((exponent_ne_zero_iff_dvd _ q).mp hq)
    have hactive :
        primeExponents P.val q + primeExponents J.val q + 4 * primeExponents f.val q ≠ 0 ∨
          primeExponents r.val q ≠ 0 := by
      rcases Finset.mem_union.mp (s.active_subset hp) with hf | hr
      · left
        have hn := (exponent_ne_zero_iff_dvd (frozenIdeal K S P J f).val q).mpr
          ((mem_exteriorSupport_iff K S (frozenIdeal K S P J f) p).mp hf)
        simpa only [frozenIdeal_exponent] using hn
      · exact Or.inr ((exponent_ne_zero_iff_dvd r.val q).mpr
          ((mem_exteriorSupport_iff K S r p).mp hr))
    have hlin : primeExponents (minimumLinearIdeal K S s).val q =
        if primeExponents s.minimum.val q = 1 then 1 else 0 := by
      change primeExponents (primeSetIdeal K S (minimumLinearPrimes K S s)).val p.val = _
      rw [exponent_primeSetIdeal]
      simp only [minimumLinearPrimes, HeckeSkeleton.LowEnergy.FrozenChargeCore.linearPrimes,
        Finset.mem_filter, hp, true_and]
    have hcube : primeExponents (minimumCubeIdeal K S s).val q =
        if primeExponents s.minimum.val q = 3 then 1 else 0 := by
      change primeExponents (primeSetIdeal K S (minimumCubePrimes K S s)).val p.val = _
      rw [exponent_primeSetIdeal]
      simp only [minimumCubePrimes, HeckeSkeleton.LowEnergy.FrozenChargeCore.cubePrimes,
        Finset.mem_filter, hp, true_and]
    have hsmall : primeExponents (minimumSmallIdeal K S s).val q =
        if primeExponents s.minimum.val q = 0 ∧
          ((primeExponents P.val q + primeExponents J.val q + 4 * primeExponents f.val q) % 6 = 0 ∨
           (primeExponents P.val q + primeExponents J.val q + 4 * primeExponents f.val q) % 6 = 4)
        then 1 else 0 := by
      change primeExponents (primeSetIdeal K S (minimumSmallPrimes K S s)).val p.val = _
      rw [exponent_primeSetIdeal]
      simp only [minimumSmallPrimes, HeckeSkeleton.LowEnergy.FrozenChargeCore.smallPrimes,
        HeckeSkeleton.LowEnergy.FrozenChargeCore.smallCharge, Finset.mem_filter, hp, true_and,
        frozenDigit, frozenIdeal_exponent]
    have hcharge := local_conductor_charge
      (primeExponents P.val q) (primeExponents J.val q) (primeExponents f.val q)
      (primeExponents r.val q) (primeExponents s.minimum.val q) (hP q) hactive
      (s.minimum_values q)
    have ha : primeExponents (primeSetIdeal K S s.active).val q = 1 := by
      change primeExponents (primeSetIdeal K S s.active).val p.val = 1
      rw [exponent_primeSetIdeal, if_pos hp]
    simpa only [B, primeExponents_mul, Finsupp.add_apply, exponent_pow, ha,
      hlin, hsmall, hcube, mul_one] using hcharge
  simpa only [B, Submonoid.coe_mul, SubmonoidClass.coe_pow] using hd

/-- The actual positive norm inequality used in the reflected ledger. -/
theorem conductor_norm_bound (P J f r : Ext) (hP : Powerful P.val)
    (s : FrozenState K S (frozenIdeal K S P J f) r) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤
      exteriorNorm K S P * exteriorNorm K S J ^ 2 * exteriorNorm K S f * exteriorNorm K S r *
        exteriorNorm K S (minimumLinearIdeal K S s) *
        exteriorNorm K S (minimumSmallIdeal K S s) *
          exteriorNorm K S (minimumCubeIdeal K S s) ^ 4 := by
  let B : (Ideal (𝓞 K))⁰ := P.val * J.val ^ 2 * f.val * r.val *
    (minimumLinearIdeal K S s).val * (minimumSmallIdeal K S s).val *
      (minimumCubeIdeal K S s).val ^ 4
  have hd : (primeSetIdeal K S s.active).val.val ^ 2 ∣ B.val :=
    conductor_divisibility K S P J f r hP s
  have hn := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors B)
    (map_dvd Ideal.absNorm hd)
  simpa only [B, exteriorNorm, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using
    (Nat.cast_le.mpr hn :
      (Ideal.absNorm ((primeSetIdeal K S s.active).val.val ^ 2) : ℝ) ≤ (Ideal.absNorm B.val : ℝ))

/-- This is the raw conductor ratio; it no longer appears as an
unproved `hcost` input at the induction terminal. -/
theorem conductor_ratio_bound (P J f r : Ext) (hP : Powerful P.val)
    (s : FrozenState K S (frozenIdeal K S P J f) r) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 /
      (exteriorNorm K S (minimumLinearIdeal K S s) *
        exteriorNorm K S (minimumSmallIdeal K S s) *
          exteriorNorm K S (minimumCubeIdeal K S s) ^ 4) ≤
      exteriorNorm K S P * exteriorNorm K S J ^ 2 * exteriorNorm K S f * exteriorNorm K S r := by
  apply (div_le_iff₀ (mul_pos (mul_pos
    (exteriorNorm_pos K S (minimumLinearIdeal K S s))
    (exteriorNorm_pos K S (minimumSmallIdeal K S s)))
    (pow_pos (exteriorNorm_pos K S (minimumCubeIdeal K S s)) 4))).mpr
  exact (conductor_norm_bound K S P J f r hP s).trans_eq (by ring)

def rowSupport (f r : Ext) : Finset (ExteriorPrime K S) :=
  exteriorSupport K S f ∪ exteriorSupport K S r

def rowSupported (k f r : Ext) : Ext :=
  supportedExterior K S (rowSupport K S f r) (exteriorResidualPart K S k)

def rowResidual (k f r : Ext) : Ext :=
  awayExterior K S (rowSupport K S f r) (exteriorResidualPart K S k)

/-- The terminal row factorization consists of constructed actual ideals. -/
theorem row_decomposition (k f r : Ext) :
    exteriorMul K S (exteriorMul K S (exteriorPowerfulPart K S k) (rowSupported K S k f r))
      (rowResidual K S k f r) = k := by
  apply Subtype.ext
  change (powerfulPart k.val *
    supportedIdeal ((rowSupport K S f r).image Subtype.val) (residualPart k.val)) *
      awayIdeal ((rowSupport K S f r).image Subtype.val) (residualPart k.val) = k.val
  rw [mul_assoc, supported_away_decomposition, powerful_residual_decomposition]

theorem rowResidual_squarefree (k f r : Ext) :
    Squarefree (rowResidual K S k f r).val.val :=
  (residualPart_squarefree k.val).squarefree_of_dvd
    (awayIdeal_dvd ((rowSupport K S f r).image Subtype.val) (residualPart k.val))

theorem awayExterior_coprime_of_support (F : Finset (ExteriorPrime K S)) (b J : Ext)
    (hJ : exteriorSupport K S J ⊆ F) :
    IsCoprime (awayExterior K S F b).val.val J.val.val := by
  have hcop := awayExterior_coprime K S F b
  apply Ideal.coprime_of_no_prime_ge
  intro P haway hJ' hP
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero (awayExterior K S F b).val
      (le_bot_iff.mp (hz ▸ haway))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, J.property p (Ideal.dvd_iff_le.mpr hJ')⟩
  have hpF : ep ∈ F := hJ ((mem_exteriorSupport_iff K S J ep).mpr
    (Ideal.dvd_iff_le.mpr hJ'))
  exact p.prime.not_unit (hcop.isUnit_of_dvd' (Ideal.dvd_iff_le.mpr haway)
    ((prime_dvd_primeSetIdeal_iff K S F ep).mpr hpF))

theorem rowResidual_coprime_label (k f r : Ext) :
    IsCoprime (rowResidual K S k f r).val.val f.val.val :=
  awayExterior_coprime_of_support K S _ _ _ Finset.subset_union_left

theorem rowResidual_coprime_puncture (k f r : Ext) :
    IsCoprime (rowResidual K S k f r).val.val r.val.val :=
  awayExterior_coprime_of_support K S _ _ _ Finset.subset_union_right

theorem rowResidual_coprime_frozen (k f r : Ext) :
    IsCoprime (rowResidual K S k f r).val.val
      (frozenIdeal K S (exteriorPowerfulPart K S k) (rowSupported K S k f r) f).val.val := by
  have hP : IsCoprime (rowResidual K S k f r).val.val
      (exteriorPowerfulPart K S k).val.val :=
    ((powerful_residual_coprime k.val).of_isCoprime_of_dvd_right
      (awayIdeal_dvd ((rowSupport K S f r).image Subtype.val) (residualPart k.val))).symm
  have hJ : IsCoprime (rowResidual K S k f r).val.val (rowSupported K S k f r).val.val :=
    awayExterior_coprime_of_support K S _ _ _
      (supportedExterior_support K S (rowSupport K S f r) (exteriorResidualPart K S k))
  change IsCoprime (rowResidual K S k f r).val.val
    (((exteriorPowerfulPart K S k).val.val * (rowSupported K S k f r).val.val) * f.val.val ^ 4)
  exact (hP.mul_right hJ).mul_right (rowResidual_coprime_label K S k f r).pow_right

/-- The punctured-label terminal conductor bound with the actual row
decomposition substituted, ready for logarithmic norm windows. -/
theorem actual_row_conductor_bound (k f r : Ext)
    (s : FrozenState K S
      (frozenIdeal K S (exteriorPowerfulPart K S k) (rowSupported K S k f r) f) r) :
    exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 /
      (exteriorNorm K S (minimumLinearIdeal K S s) *
        exteriorNorm K S (minimumSmallIdeal K S s) *
          exteriorNorm K S (minimumCubeIdeal K S s) ^ 4) ≤
      exteriorNorm K S (exteriorPowerfulPart K S k) *
        exteriorNorm K S (rowSupported K S k f r) ^ 2 *
          exteriorNorm K S f * exteriorNorm K S r :=
  conductor_ratio_bound K S _ _ f r (powerfulPart_powerful k.val) s

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderTerminalConductor

end
