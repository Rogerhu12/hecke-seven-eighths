import Expansion.ActualPrimeSlotBridge
import Expansion.CompensationPrimeProfile
import HeckeGeneral.Analysis.MomentPrimeWindows
import HeckeSkeleton.HighBinSupport.ActualNormFormFullCorrection

/-!
# The actual compensation main slot is the original positive row slot

The physical window is real. Conjugating its prime polynomial therefore
accounts for the conjugate arithmetic row coefficient without replacing
the supplied row character or changing its orientation. The complete
original mask is removed only where the actual row coefficient vanishes.
The outside scale, including its square-root normalization, is exact.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (R : RowCharacterInput K S P)

/-- At an exterior row prime the zero is an arithmetic theorem, including
the full row ideal and not merely its squarefree part. -/
theorem actual_row_primeCoefficient_mul_completeMask (u : FrequencyRow K S)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K (R.character u) p *
        (if completeIdealCommonMask K S u.ideal.val p.asIdeal then 1 else 0) =
      if p ∉ S then primeCoefficient K (R.character u) p else 0 := by
  rw [completePrimeMask_eq_originalMask,
    HeckeSkeleton.PrimeCancellationIdealMask.originalMask_prime]
  by_cases hpS : p ∈ S
  · simp [hpS]
  · have hp6 : (6 : 𝓞 K) ∉ p.asIdeal := P.arithmetic.away_six p hpS
    by_cases hpRow : p.asIdeal ∣ u.ideal.val.val
    · have hz := HighBinVerified.RowPrimeCharacter.row_primeCoefficient_eq_zero_of_dvd
        K S P R u ⟨p, hpS⟩ hpRow
      simp [hpS, hp6, hpRow, hz]
    · simp [hpS, hp6, hpRow]

/-- Removing the subtype of exterior primes retains the literal original
window and all its zero coefficients. -/
theorem actualOriginalMaskedPrimeSum_eq_physicalWindow
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z : ℝ)
    (i : Fin g.slots) (W : ℝ → ℂ) :
    actualOriginalMaskedPrimeSum K S (R.character u) u.ideal.val W (primeScale g Z)
        ((analyticMomentPrimeWindow K g i).support 0 (primeScale g Z)) =
      ∑ p ∈ primeWindow K S g ∅ Z i,
        primeCoefficient K (R.character u) p.val *
          W ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) := by
  let A := (analyticMomentPrimeWindow K g i).support 0 (primeScale g Z)
  have hmem (p : ExteriorPrime K S) :
      p ∈ primeWindow K S g ∅ Z i ↔ p.val ∈ A := by
    simp only [mem_physicalPrimeWindow_iff_analytic, Finset.not_mem_empty,
      false_implies, implies_true, and_true, A]
  have hext :
      (∑ p ∈ primeWindow K S g ∅ Z i,
        primeCoefficient K (R.character u) p.val *
          W ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z)) =
      ∑ p ∈ A.filter (fun p => p ∉ S),
        primeCoefficient K (R.character u) p *
          W ((p.asIdeal.absNorm : ℝ) / primeScale g Z) := by
    apply Finset.sum_bij (fun p _ => p.val)
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(hmem p).mp hp, p.property⟩
    · intro p _ q _ hpq
      exact Subtype.ext hpq
    · intro p hp
      obtain ⟨hpA, hpS⟩ := Finset.mem_filter.mp hp
      exact ⟨⟨p, hpS⟩, (hmem ⟨p, hpS⟩).mpr hpA, rfl⟩
    · intro p _
      rfl
  rw [hext, Finset.sum_filter]
  unfold actualOriginalMaskedPrimeSum
  apply Finset.sum_congr rfl
  intro p _
  have hm := actual_row_primeCoefficient_mul_completeMask K S P R u p
  change primeCoefficient K (R.character u) p *
      W ((p.asIdeal.absNorm : ℝ) / primeScale g Z) *
        (if completeIdealCommonMask K S u.ideal.val p.asIdeal then 1 else 0) = _
  calc
    _ = W ((p.asIdeal.absNorm : ℝ) / primeScale g Z) *
        (primeCoefficient K (R.character u) p *
          (if completeIdealCommonMask K S u.ideal.val p.asIdeal then 1 else 0)) := by ring
    _ = _ := by rw [hm]; split_ifs <;> ring

/-- Conjugation changes only the complex profile power. -/
theorem conj_profilePower_conj_sub_one (z : ℂ) {y : ℝ} (hy : 0 < y) :
    conj (profilePower (conj z - 1) y) = (y : ℂ) ^ (z - 1) := by
  rw [profilePower, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, map_sub, map_one, conj_conj]
  exact profilePower_eq_cpow (z - 1) hy

/-- On the actual physical line the real profile is fixed before every
height, and the frequency in the positive row polynomial is z.im. -/
theorem profilePower_conj_sub_one_eq_fixed_frequency (z : ℂ)
    (hz : z.re = 17 / 50) (y : ℝ) :
    profilePower (conj z - 1) y =
      profilePower (-(33 / 50 : ℂ)) y *
        profilePower (-ExpansionInterfaces.Mellin.vertical 0 z.im) y := by
  have he : conj z - 1 = (-(33 / 50 : ℂ)) +
      (-ExpansionInterfaces.Mellin.vertical 0 z.im) := by
    apply Complex.ext <;> simp [ExpansionInterfaces.Mellin.vertical, hz] <;> ring
  simp only [profilePower, ← Complex.exp_add]
  rw [he]
  congr 1
  ring

theorem actualCompensationPrimeProfile_frequency (g : PrimeWindowGeometry)
    (i : Fin g.slots) (z : ℂ) (hz : z.re = 17 / 50) (y : ℝ) :
    (g.weight i).toFun y * profilePower (conj z - 1) y =
      actualCompensationPrimeProfile g i y *
        profilePower (-ExpansionInterfaces.Mellin.vertical 0 z.im) y := by
  rw [profilePower_conj_sub_one_eq_fixed_frequency z hz]
  simp only [actualCompensationPrimeProfile, mul_assoc]

/-- The common real window gives the exact conjugated, normalized main
prime slot. This identity precedes any estimate on either side. -/
theorem actualCompensationMainSlot_eq_normalized_masked
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z : ℝ) (hZ : 0 < Z)
    (z : ℂ) (i : Fin g.slots) :
    actualCompensationMainSlot K S P g ∅ u Z z i =
      (primeScale g Z : ℂ) ^ (z - 1 / 2) *
        conj ((Real.sqrt (primeScale g Z) : ℂ)⁻¹ *
          actualOriginalMaskedPrimeSum K S (R.character u) u.ideal.val
            (fun y => (g.weight i).toFun y * profilePower (conj z - 1) y)
            (primeScale g Z)
            ((analyticMomentPrimeWindow K g i).support 0 (primeScale g Z))) := by
  have hP : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  have hPc : (primeScale g Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hP.ne'
  have hsqrt : (Real.sqrt (primeScale g Z) : ℂ) =
      (primeScale g Z : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hP.le]
    norm_num
  have hscale : (primeScale g Z : ℂ) ^ (z - 1 / 2) *
      (Real.sqrt (primeScale g Z) : ℂ)⁻¹ =
        (primeScale g Z : ℂ) ^ (z - 1) := by
    rw [hsqrt, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hPc]
    congr 1
    ring
  rw [actualOriginalMaskedPrimeSum_eq_physicalWindow K S P R g u Z i,
    map_mul, map_inv₀, Complex.conj_ofReal, ← mul_assoc, hscale, map_sum,
    Finset.mul_sum]
  unfold actualCompensationMainSlot
  apply Finset.sum_congr rfl
  intro p _
  have hq : 0 < (p.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.val.ne_bot)
  have hreal : conj ((g.weight i).toFun
      ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z)) =
      (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) :=
    Complex.conj_eq_iff_im.mpr (g.real_valued i _)
  rw [map_mul, map_mul, hreal, conj_profilePower_conj_sub_one z (div_pos hq hP),
    Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hq.le hP.le,
    rowCharacterInput_character_eq_arithmetic]
  have hpow : (primeScale g Z : ℂ) ^ (z - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hPc)
  change (g.weight i).toFun _ * _ * _ = _
  simp only [Complex.ofReal_natCast]
  field_simp [hpow] <;> ring

/-- All slots use the original analytic windows and positive row
coefficients. The physical complex exponent belongs to the profile. -/
def compensationPrimeGeometry (g : PrimeWindowGeometry) (z : ℂ) : SlotGeometry K :=
  (momentPrimeGeometry K g).freezeTwists (fun _ => 0) (fun _ => conj z - 1)

variable (ω ψ : HeckeCharacter K)

/-- Exact identity with the existing shared moment-model primePolynomial. -/
theorem actualCompensationMainSlot_eq_shared_primePolynomial
    (a : PolynomialPresentation K ψ) (g : PrimeWindowGeometry) (V W : IdealTest K)
    (u : FrequencyRow K S) (Z : ℝ) (hZ : 0 < Z) (z : ℂ) (i : Fin g.slots) :
    actualCompensationMainSlot K S P g ∅ u Z z i =
      (primeScale g Z : ℂ) ^ (z - 1 / 2) *
        conj (primePolynomial
          (sharedMomentData K S P R ω ψ a (compensationPrimeGeometry K g z)
            (fun _ => 1) u.sector V W) i u.ideal.val Z 0) := by
  rw [shared_primePolynomial_eq_actualOriginalMaskedPrimeSum K S P R ω ψ, mul_one]
  exact actualCompensationMainSlot_eq_normalized_masked K S P R g u Z hZ z i

/-- The normalization retained by the moment interface contributes exactly
one half of a prime-window exponent, with no loss in the identity. -/
theorem norm_actualCompensationMainSlot_eq_shared_primePolynomial
    (a : PolynomialPresentation K ψ) (g : PrimeWindowGeometry) (V W : IdealTest K)
    (u : FrequencyRow K S) (Z : ℝ) (hZ : 0 < Z) (z : ℂ) (i : Fin g.slots) :
    ‖actualCompensationMainSlot K S P g ∅ u Z z i‖ =
      primeScale g Z ^ (z.re - 1 / 2) *
        ‖primePolynomial
          (sharedMomentData K S P R ω ψ a (compensationPrimeGeometry K g z)
            (fun _ => 1) u.sector V W) i u.ideal.val Z 0‖ := by
  rw [actualCompensationMainSlot_eq_shared_primePolynomial K S P R ω ψ a g V W
    u Z hZ z i, norm_mul, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZ _)]
  congr 2 <;> simp

end Expansion.Project

#print axioms Expansion.Project.actualOriginalMaskedPrimeSum_eq_physicalWindow
#print axioms Expansion.Project.profilePower_conj_sub_one_eq_fixed_frequency
#print axioms Expansion.Project.actualCompensationMainSlot_eq_shared_primePolynomial
#print axioms Expansion.Project.norm_actualCompensationMainSlot_eq_shared_primePolynomial
