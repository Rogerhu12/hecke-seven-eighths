import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.IdealPool

/-!
# The second divisor is paid by its actual frozen scalar

Each prime of the second squarefree divisor selects a nonempty subset of
all occurrences.  Its frozen plain divisors and frozen prime slots
therefore contain that divisor.  The exact central normalizations give
one inverse norm of this computed frozen ideal in each squared column.
The two Cauchy halves consequently supply the second divisor's own
harmonic factor; no first-transform divisor is substituted for it.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum WholeAllocation

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem actualIdealResidue_norm_le_one (C : A.GeneralArithmeticContext σ η hS)
    (I : Ideal (𝓞 F)) (h : A.R) :
    ‖actualIdealResidue (A := A) (σ := σ) I h‖ ≤ 1 := by
  by_cases hI : I ≠ 0 ∧ IsCoprime I A.cS
  · let J : A.Exterior := ⟨I, hI.1, Ideal.isCoprime_iff_sup_eq.mp hI.2⟩
    obtain ⟨a, u, ha, hua, hu⟩ := C.allowed_integral J
    letI : Finite (A.R ⧸ Ideal.span {a}) := by
      rw [ha.2]
      exact A.exteriorResidue_finite J
    letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
    have hb := finiteCharacter_norm_le_one (generatedIdealCharacter (σ := σ) J a ha)
      (Ideal.Quotient.mk _ h)
    rw [generatedIdealCharacter_mk] at hb
    change ‖actualIdealResidue (A := A) (σ := σ) J.val h‖ ≤ 1
    rw [actualIdealResidue_exterior]
    exact hb
  · simp only [actualIdealResidue, dif_neg hI, norm_zero, zero_le_one]

private theorem central_term_norm_sq_le (N B : ℝ) (hN : 0 < N)
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ^ 2 ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * (z * w)‖ ^ 2 ≤ B / N := by
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hp : ‖z‖ ^ 2 * ‖w‖ ^ 2 ≤ B := by
    simpa only [one_mul] using mul_le_mul hz2 hw (sq_nonneg _) zero_le_one
  calc
    _ = N⁻¹ * (‖z‖ ^ 2 * ‖w‖ ^ 2) := by
      simp only [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
        Real.sq_sqrt hN.le]
    _ ≤ N⁻¹ * B := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hN.le)
    _ = _ := by ring

namespace ActualColumnAllocation

variable {k : ℕ} (B : ActualColumnAllocation F k)

def frozenIdeal : Ideal (𝓞 F) :=
  (B.plainDivisor 0).val * (B.plainDivisor (Fin.succ 0)).val *
    ∏ i ∈ Finset.univ \ B.keep, (B.witness.2 i).asIdeal

theorem frozenIdeal_ne_zero : B.frozenIdeal ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (B.witness.2 i).ne_bot))

theorem frozenIdeal_norm : (Ideal.absNorm B.frozenIdeal : ℝ) =
    HeckeGeneral.Analysis.idealNorm F (B.plainDivisor 0) *
      HeckeGeneral.Analysis.idealNorm F (B.plainDivisor (Fin.succ 0)) *
        ∏ i ∈ Finset.univ \ B.keep, (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) := by
  simp only [frozenIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
    <;> rfl

/-- Nonempty occurrence choices force every actual divisor prime into
the computed frozen ideal, even when it selects several occurrences. -/
theorem divisor_dvd_frozenIdeal (hsq : Squarefree B.divisor)
    (ha : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2)) :
    B.divisor ∣ B.frozenIdeal := by
  apply (squarefree_dvd_iff_support B.divisor B.frozenIdeal hsq).mpr
  intro p
  have hselect : ∀ p : primeSupport B.divisor, (B.selection p).Nonempty :=
    (AllocationMass.mem_allocations _ _ _).mp ha
  obtain ⟨i, hi⟩ := hselect p
  have hinc (i : Fin (k + 2)) (hi : i ∈ B.selection p) :
      p.val ∣ occurrenceDivisor B.divisor B.selection i :=
    (occurrenceDivisor_dvd_iff B.divisor B.selection i _).mp dvd_rfl p hi
  have hslots : ∀ j : Fin k,
      occurrenceDivisor B.divisor B.selection j.succ.succ ∣ (B.witness.2 j).asIdeal := by
    have hm := B.witness_mem
    rw [paired_allocated_columns_eq_filter] at hm
    intro j
    exact (Finset.mem_filter.mp hm).2 j.succ.succ
  revert hi
  refine Fin.cases (fun hi => ?_) (fun j => Fin.cases (fun hi => ?_) (fun t hi => ?_) j) i
  · exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (hinc 0 hi) (B.plainDivisor (Fin.succ 0)).val) _
  · exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (hinc (Fin.succ 0) hi) (B.plainDivisor 0).val) _
  · have ht : t ∉ B.keep := by
      intro hkeep
      exact (Finset.mem_filter.mp hkeep).2 p hi
    have hprime := selected_prime_slot_eq B.divisor B.selection t.succ.succ p
      (B.witness.2 t) hi (hslots t)
    apply dvd_mul_of_dvd_right
    rw [hprime]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ht⟩)

/-- Squared frozen scalar with its exact original central denominators.
Only single-ideal/prime coefficient, profile and annulus bounds are used. -/
theorem scalar_norm_sq_le_frozen_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (T : FixedChildCharacters F k) (g h : A.R) (Z : ℝ) (hZ : 0 < Z)
    (length : Fin k → ℝ) (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (B.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ length i)
    (hprofile : ∀ i ∈ Finset.univ \ B.keep, ‖w i (B.witness.2 i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i) :
    ‖B.scalar (σ := σ) T g h Z length w‖ ^ 2 ≤
      (∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) /
        (Ideal.absNorm B.frozenIdeal : ℝ) := by
  have hplain (J : HeckeGeneral.Analysis.NonzeroIdeal F)
      (hj : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask J‖ ≤ 1) :
      ‖sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h J‖ ^ 2 ≤
        1 / HeckeGeneral.Analysis.idealNorm F J := by
    have hr := actualIdealResidue_norm_le_one C J.val (g * h)
    have hv : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val (g * h)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul hj hr (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simpa only [sourcePlainFrozen, mul_one, norm_one, one_pow] using
      central_term_norm_sq_le (HeckeGeneral.Analysis.idealNorm F J) 1
        (HeckeGeneral.Analysis.idealNorm_pos F J)
        (sourcePlainCoefficient T.plain T.plainTwist T.mask J *
          actualIdealResidue (A := A) (σ := σ) J.val (g * h)) 1 hv (by norm_num)
  have hslot (i : Fin k) (hi : i ∈ Finset.univ \ B.keep) :
      ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
        g h (w i) (Z ^ length i) (B.witness.2 i)‖ ^ 2 ≤
        (annulus i * profile i) / (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) := by
    have hr := actualIdealResidue_norm_le_one C (B.witness.2 i).asIdeal (g * h)
    have hv : ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (B.witness.2 i) *
        actualIdealResidue (A := A) (σ := σ) (B.witness.2 i).asIdeal (g * h)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hprime i hi) hr (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hp := central_term_norm_sq_le (Z ^ length i) (profile i)
      (Real.rpow_pos_of_pos hZ _) _ (w i (B.witness.2 i)) hv (hprofile i hi)
    change ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
      g h (w i) (Z ^ length i) (B.witness.2 i)‖ ^ 2 ≤ profile i / Z ^ length i at hp
    apply hp.trans
    have hnorm : (0 : ℝ) < Ideal.absNorm (B.witness.2 i).asIdeal :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr (B.witness.2 i).ne_bot))
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hZ _) hnorm).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hannulus i hi) (hP i)]
  calc
    _ = (‖sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h (B.plainDivisor 0)‖ ^ 2 *
        ‖sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h (B.plainDivisor (Fin.succ 0))‖ ^ 2) *
        ∏ i ∈ Finset.univ \ B.keep,
          ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
            g h (w i) (Z ^ length i) (B.witness.2 i)‖ ^ 2 := by
      simp only [scalar, FixedChildCharacters.frozenScalar, norm_mul, norm_prod,
        mul_pow, Finset.prod_pow, Finset.sdiff_eq_filter, Finset.mem_univ, true_and]
    _ ≤ (1 / HeckeGeneral.Analysis.idealNorm F (B.plainDivisor 0) *
        (1 / HeckeGeneral.Analysis.idealNorm F (B.plainDivisor (Fin.succ 0)))) *
        ∏ i ∈ Finset.univ \ B.keep,
          (annulus i * profile i) / (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) :=
      mul_le_mul
        (mul_le_mul (hplain _ hplain₁) (hplain _ hplain₂) (sq_nonneg _)
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le))
        (Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) hslot)
        (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le)
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le))
    _ = _ := by
      rw [B.frozenIdeal_norm, Finset.prod_div_distrib]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The second divisor receives its own inverse-norm factor. -/
theorem scalar_norm_sq_le_divisor
    (C : A.GeneralArithmeticContext σ η hS)
    (T : FixedChildCharacters F k) (g h : A.R) (Z : ℝ) (hZ : 0 < Z)
    (length : Fin k → ℝ) (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask (B.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (B.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * Z ^ length i)
    (hprofile : ∀ i ∈ Finset.univ \ B.keep, ‖w i (B.witness.2 i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hsq : Squarefree B.divisor)
    (ha : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2)) :
    ‖B.scalar (σ := σ) T g h Z length w‖ ^ 2 ≤
      (∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) / (Ideal.absNorm B.divisor : ℝ) := by
  apply (B.scalar_norm_sq_le_frozen_norm C T g h Z hZ length w annulus profile
    hplain₁ hplain₂ hprime hannulus hprofile hA hP).trans
  have hdiv := B.divisor_dvd_frozenIdeal hsq ha
  have hD : B.divisor ≠ 0 := by
    intro hz
    rw [hz, zero_dvd_iff] at hdiv
    exact B.frozenIdeal_ne_zero hdiv
  apply div_le_div_of_nonneg_left
    (Finset.prod_nonneg (fun i _ => mul_nonneg (hA i) (hP i)))
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)))
    (ideal_norm_le_of_dvd B.frozenIdeal_ne_zero hdiv)

end ActualColumnAllocation

/-- Apply the proved squared scalar bounds on the two sides of the
same second divisor.  The square roots pay one full inverse norm. -/
theorem paired_scalar_inverse_norm (left right : ℂ) (NL EL ER : ℝ)
    (hNL : 0 < NL) (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hleft : ‖left‖ ^ 2 ≤ EL / NL) (hright : ‖right‖ ^ 2 ≤ ER / NL) :
    ‖left‖ * ‖right‖ ≤ Real.sqrt EL * Real.sqrt ER / NL := by
  have hl := (le_div_iff₀ hNL).mp hleft
  have hr := (le_div_iff₀ hNL).mp hright
  have hp := mul_le_mul hl hr (mul_nonneg (sq_nonneg _) hNL.le) hEL
  have hs : (Real.sqrt EL * Real.sqrt ER) ^ 2 = EL * ER := by
    rw [mul_pow, Real.sq_sqrt hEL, Real.sq_sqrt hER]
  have hsquare : (‖left‖ * ‖right‖ * NL) ^ 2 ≤ (Real.sqrt EL * Real.sqrt ER) ^ 2 := by
    rw [hs]
    convert hp using 1 <;> ring
  exact (le_div_iff₀ hNL).mpr
    ((sq_le_sq₀ (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsquare)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.divisor_dvd_frozenIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.ActualColumnAllocation.scalar_norm_sq_le_divisor
#print axioms HeckeSkeleton.Moments.EngineStep.paired_scalar_inverse_norm

