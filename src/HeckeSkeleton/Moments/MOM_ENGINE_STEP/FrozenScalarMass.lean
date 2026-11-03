import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SupportSourceExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm

/-!
# Actual frozen factors retain their complete norm denominators

The two plain extractions and every frozen prime occurrence contribute
their original central normalization. Their product ideal is computed,
including multiplicities. Only original individual coefficient bounds,
prime annuli and profile bounds enter the proof.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {k : ℕ}

def frozenSourceIdeal (J₁ J₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (keep : Finset (Fin k)) (primes : Fin k → HeightOneSpectrum (𝓞 F)) : Ideal (𝓞 F) :=
  J₁.val * J₂.val * ∏ i ∈ Finset.univ \ keep, (primes i).asIdeal

theorem frozenSourceIdeal_ne_zero (J₁ J₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (keep : Finset (Fin k)) (primes : Fin k → HeightOneSpectrum (𝓞 F)) :
    frozenSourceIdeal J₁ J₂ keep primes ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (primes i).ne_bot))

theorem frozenSourceIdeal_norm (J₁ J₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (keep : Finset (Fin k)) (primes : Fin k → HeightOneSpectrum (𝓞 F)) :
    (Ideal.absNorm (frozenSourceIdeal J₁ J₂ keep primes) : ℝ) =
      HeckeGeneral.Analysis.idealNorm F J₁ * HeckeGeneral.Analysis.idealNorm F J₂ *
        ∏ i ∈ Finset.univ \ keep, (Ideal.absNorm (primes i).asIdeal : ℝ) := by
  simp only [frozenSourceIdeal, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
    <;> rfl

private theorem frozen_central_term_norm_sq_le (N B : ℝ) (hN : 0 < N)
    (z w : ℂ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ^ 2 ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * (z * w)‖ ^ 2 ≤ B / N := by
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hp : ‖z‖ ^ 2 * ‖w‖ ^ 2 ≤ B := by
    simpa only [one_mul] using mul_le_mul hz2 hw (sq_nonneg _) zero_le_one
  calc
    _ = N⁻¹ * (‖z‖ ^ 2 * ‖w‖ ^ 2) := by
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hN.le]
    _ ≤ N⁻¹ * B := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hN.le)
    _ = _ := by ring

theorem frozen_source_scalar_norm_sq_le
    (C : A.GeneralArithmeticContext σ η hS)
    (T : FixedChildCharacters F k) (g h : A.R)
    (J₁ J₂ : HeckeGeneral.Analysis.NonzeroIdeal F)
    (Z : ℝ) (hZ : 0 < Z) (length : Fin k → ℝ)
    (keep : Finset (Fin k)) (primes : Fin k → HeightOneSpectrum (𝓞 F))
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ) (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask J₁‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient T.plain T.plainTwist T.mask J₂‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ keep,
      ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (primes i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ keep,
      (Ideal.absNorm (primes i).asIdeal : ℝ) ≤ annulus i * Z ^ length i)
    (hprofile : ∀ i ∈ Finset.univ \ keep, ‖w i (primes i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i) :
    ‖T.frozenScalar (σ := σ) g h J₁ J₂ Z length keep primes w‖ ^ 2 ≤
      (∏ i ∈ Finset.univ \ keep, annulus i * profile i) /
        (Ideal.absNorm (frozenSourceIdeal J₁ J₂ keep primes) : ℝ) := by
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
      frozen_central_term_norm_sq_le (HeckeGeneral.Analysis.idealNorm F J) 1
        (HeckeGeneral.Analysis.idealNorm_pos F J)
        (sourcePlainCoefficient T.plain T.plainTwist T.mask J *
          actualIdealResidue (A := A) (σ := σ) J.val (g * h)) 1 hv (by norm_num)
  have hslot (i : Fin k) (hi : i ∈ Finset.univ \ keep) :
      ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
        g h (w i) (Z ^ length i) (primes i)‖ ^ 2 ≤
        (annulus i * profile i) / (Ideal.absNorm (primes i).asIdeal : ℝ) := by
    have hr := actualIdealResidue_norm_le_one C (primes i).asIdeal (g * h)
    have hv : ‖sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask (primes i) *
        actualIdealResidue (A := A) (σ := σ) (primes i).asIdeal (g * h)‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_mul (hprime i hi) hr (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hp := frozen_central_term_norm_sq_le (Z ^ length i) (profile i)
      (Real.rpow_pos_of_pos hZ _) _ (w i (primes i)) hv (hprofile i hi)
    change ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
      g h (w i) (Z ^ length i) (primes i)‖ ^ 2 ≤ profile i / Z ^ length i at hp
    apply hp.trans
    have hnorm : (0 : ℝ) < Ideal.absNorm (primes i).asIdeal :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero
        (Ideal.absNorm_eq_zero_iff.not.mpr (primes i).ne_bot))
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hZ _) hnorm).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hannulus i hi) (hP i)]
  calc
    _ = (‖sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h J₁‖ ^ 2 *
        ‖sourcePlainFrozen (σ := σ) T.plain T.plainTwist T.mask g h J₂‖ ^ 2) *
        ∏ i ∈ Finset.univ \ keep,
          ‖sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask
            g h (w i) (Z ^ length i) (primes i)‖ ^ 2 := by
      simp only [FixedChildCharacters.frozenScalar, norm_mul, norm_prod,
        mul_pow, Finset.prod_pow, Finset.sdiff_eq_filter, Finset.mem_univ, true_and]
    _ ≤ (1 / HeckeGeneral.Analysis.idealNorm F J₁ *
        (1 / HeckeGeneral.Analysis.idealNorm F J₂)) *
        ∏ i ∈ Finset.univ \ keep,
          (annulus i * profile i) / (Ideal.absNorm (primes i).asIdeal : ℝ) :=
      mul_le_mul
        (mul_le_mul (hplain _ hplain₁) (hplain _ hplain₂) (sq_nonneg _)
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le))
        (Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) hslot)
        (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
        (mul_nonneg
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le)
          (div_nonneg zero_le_one (HeckeGeneral.Analysis.idealNorm_pos F _).le))
    _ = _ := by
      rw [frozenSourceIdeal_norm J₁ J₂ keep primes, Finset.prod_div_distrib]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring


/-- The original frozen factors of one actual source support branch.
The bounds concern individual coefficients and profiles, never a whole
column or an allocated energy. -/
structure FrozenSourceAtoms (A : SArithmeticData F) (σ : F →+* ℂ)
    (H : Type*) (rows : Finset H) (k : ℕ) where
  plain₁ : HeckeGeneral.Analysis.NonzeroIdeal F
  plain₂ : HeckeGeneral.Analysis.NonzeroIdeal F
  keep : Finset (Fin k)
  primes : Fin k → HeightOneSpectrum (𝓞 F)
  characters : H → FixedChildCharacters F k
  factor : H → A.R
  residual : H → A.R
  base : ℝ
  base_pos : 0 < base
  length : Fin k → ℝ
  slotWeight : H → Fin k → HeightOneSpectrum (𝓞 F) → ℂ
  annulus : Fin k → ℝ
  profile : Fin k → ℝ
  annulus_nonneg : ∀ i, 0 ≤ annulus i
  profile_nonneg : ∀ i, 0 ≤ profile i
  plain₁_bound : ∀ h ∈ rows,
    ‖sourcePlainCoefficient (characters h).plain (characters h).plainTwist
      (characters h).mask plain₁‖ ≤ 1
  plain₂_bound : ∀ h ∈ rows,
    ‖sourcePlainCoefficient (characters h).plain (characters h).plainTwist
      (characters h).mask plain₂‖ ≤ 1
  prime_bound : ∀ h ∈ rows, ∀ i ∈ Finset.univ \ keep,
    ‖sourcePrimeCoefficient ((characters h).slot i) ((characters h).slotTwist i)
      (characters h).mask (primes i)‖ ≤ 1
  prime_annulus : ∀ i ∈ Finset.univ \ keep,
    (Ideal.absNorm (primes i).asIdeal : ℝ) ≤ annulus i * base ^ length i
  slot_bound : ∀ h ∈ rows, ∀ i ∈ Finset.univ \ keep,
    ‖slotWeight h i (primes i)‖ ^ 2 ≤ profile i

namespace FrozenSourceAtoms

variable {H : Type*} {rows : Finset H} (W : FrozenSourceAtoms A σ H rows k)

def value (h : H) : ℂ :=
  (W.characters h).frozenScalar (σ := σ) (W.factor h) (W.residual h)
    W.plain₁ W.plain₂ W.base W.length W.keep W.primes (W.slotWeight h)

def ideal : Ideal (𝓞 F) := frozenSourceIdeal W.plain₁ W.plain₂ W.keep W.primes

def envelope : ℝ := ∏ i ∈ Finset.univ \ W.keep, W.annulus i * W.profile i

theorem ideal_ne_zero : W.ideal ≠ 0 := frozenSourceIdeal_ne_zero _ _ _ _

theorem envelope_nonneg : 0 ≤ W.envelope :=
  Finset.prod_nonneg (fun i _ => mul_nonneg (W.annulus_nonneg i) (W.profile_nonneg i))

theorem norm_sq_le (C : A.GeneralArithmeticContext σ η hS) (h : H) (hh : h ∈ rows) :
    ‖W.value h‖ ^ 2 ≤ W.envelope / (Ideal.absNorm W.ideal : ℝ) :=
  frozen_source_scalar_norm_sq_le C (W.characters h) (W.factor h) (W.residual h)
    W.plain₁ W.plain₂ W.base W.base_pos W.length W.keep W.primes (W.slotWeight h)
    W.annulus W.profile (W.plain₁_bound h hh) (W.plain₂_bound h hh)
    (W.prime_bound h hh) W.prime_annulus (W.slot_bound h hh)
    W.annulus_nonneg W.profile_nonneg

theorem norm_le (C : A.GeneralArithmeticContext σ η hS) (h : H) (hh : h ∈ rows) :
    ‖W.value h‖ ≤ Real.sqrt W.envelope / Real.sqrt (Ideal.absNorm W.ideal : ℝ) := by
  have hs := Real.sqrt_le_sqrt (W.norm_sq_le C h hh)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div W.envelope_nonneg] using hs

end FrozenSourceAtoms

namespace SupportCartesianBranch

variable {S₁ S₂ : Finset (Ideal (𝓞 F))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 F))}
variable {P : Finset (Ideal (𝓞 F))} (b : SupportCartesianBranch S₁ S₂ S P)

/-- The actual frozen occurrences reconstruct the complete extracted
ideal. Repeated prime occurrences retain their multiplicities. -/
theorem frozenSourceIdeal_eq :
    frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 =
      b.plainExtract₁ * b.plainExtract₂ * ∏ i, b.slotExtract i := by
  change b.plainExtract₁ * b.plainExtract₂ *
    (∏ i ∈ Finset.univ \ b.keep, (b.witness.2 i).asIdeal) = _
  congr 1
  simp only [Finset.sdiff_eq_filter, Finset.prod_filter, Finset.mem_univ, true_and]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ b.keep
  · simp only [hi, not_true_eq_false, if_false]
    exact (Finset.mem_filter.mp hi).2.symm
  · simp only [hi, not_false_eq_true, if_true]
    have hn : b.slotExtract i ≠ 1 := by
      simpa only [keep, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hp := SupportCartesian.prime_fibre_frozen_mem (S i) P (b.slotExtract i) hn
      (b.witness.2 i) (b.witness_slots i)
    have he := (Finset.mem_filter.mp (b.witness_slots i)).2
    simpa only [supportExtract_prime _ (b.witness.2 i).prime P, if_pos hp] using he

end SupportCartesianBranch

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.frozen_source_scalar_norm_sq_le
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.frozenSourceIdeal_eq

