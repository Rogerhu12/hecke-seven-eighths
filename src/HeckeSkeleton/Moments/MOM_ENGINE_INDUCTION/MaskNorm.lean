import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MaskDeletion

/-!
# The norm of the genuine original deletion set

The fixed ideal depends only on the original finite set `S` and the
primes above 6.  Every prime deleted from the complete row `u` divides
this fixed ideal times `u` itself.  The squarefree product of the deletion
set therefore has norm at most a fixed constant times the original row
norm, including rows with redundant sixth powers.

This is the concrete norm input for `ReflectionMass.reflection_mass_subpower`.
A rowwise coefficient mass bound is not identified here with a common
row-independent measure; that analytic assembly is a separate obligation.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain HeckeGeneral.Analysis
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open scoped BigOperators Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- One fixed ideal accounting for all fixed prime exclusions. Repeated
prime factors in this ideal only enlarge the fixed norm constant. -/
def fixedRowDeletionIdeal (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    Ideal (𝓞 K) :=
  (∏ p ∈ S.toFinset, p.asIdeal) * Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K))

theorem fixedRowDeletionIdeal_ne_bot
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    fixedRowDeletionIdeal S ≠ ⊥ := by
  unfold fixedRowDeletionIdeal
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun p _ => p.ne_bot)
  · intro h
    have hz : (6 : 𝓞 K) = 0 := Ideal.span_singleton_eq_bot.mp h
    norm_num at hz

/-- Actual integral-ideal divisibility, with the whole original `u` on
the right and no assumed divisor or conductor estimate. -/
theorem completeRowDeletionProduct_dvd
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u : NonzeroIdeal K) :
    (∏ P ∈ completeRowDeletionPrimes S u, P) ∣ fixedRowDeletionIdeal S * u.val := by
  have hu : u.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero u
  have hM : fixedRowDeletionIdeal S * u.val ≠ ⊥ :=
    mul_ne_zero (fixedRowDeletionIdeal_ne_bot S) hu
  apply support_product_dvd hM
  intro P hP
  apply (prime_mem_support_iff _ _ hM (completeRowDeletionPrimes_prime S u P hP)).mpr
  change P ∣ ((∏ q ∈ S.toFinset, q.asIdeal) *
    Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K))) * u.val
  rcases Finset.mem_union.mp hP with hfixed | hrow
  · rcases Finset.mem_union.mp hfixed with hS | h6
    · obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hS
      have hp : p.asIdeal ∣ ∏ q ∈ S.toFinset, q.asIdeal :=
        Finset.dvd_prod_of_mem _ hpS
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp _) _
    · have h6zero : Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := by
        intro hz
        have hbad : (6 : 𝓞 K) = 0 := Ideal.span_singleton_eq_bot.mp hz
        norm_num at hbad
      have hp : P ∣ Ideal.span ({(6 : 𝓞 K)} : Set (𝓞 K)) :=
        (prime_mem_support_iff _ _ h6zero (support_prime h6)).mp h6
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp _) _
  · have hp : P ∣ u.val := (prime_mem_support_iff _ _ hu (support_prime hrow)).mp hrow
    exact dvd_mul_of_dvd_right hp _

/-- The fixed constant is strictly positive and chosen before the row. -/
theorem fixedRowDeletionIdeal_norm_pos
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] :
    0 < (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h =>
    fixedRowDeletionIdeal_ne_bot S (Ideal.absNorm_eq_zero_iff.mp h))

/-- The exact original deletion product costs only the original row norm
times the displayed fixed `S/6` constant. -/
theorem completeRowDeletionProduct_norm_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] (u : NonzeroIdeal K) :
    (Ideal.absNorm (∏ P ∈ completeRowDeletionPrimes S u, P) : ℝ) ≤
      (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) * idealNorm K u := by
  have hM : fixedRowDeletionIdeal S * u.val ≠ ⊥ :=
    mul_ne_zero (fixedRowDeletionIdeal_ne_bot S) (nonZeroDivisors.coe_ne_zero u)
  have hpos : 0 < Ideal.absNorm (fixedRowDeletionIdeal S * u.val) :=
    Nat.pos_of_ne_zero (fun h => hM (Ideal.absNorm_eq_zero_iff.mp h))
  have h := Nat.le_of_dvd hpos
    (map_dvd Ideal.absNorm (completeRowDeletionProduct_dvd S u))
  rw [map_mul] at h
  dsimp only [idealNorm]
  exact_mod_cast h

end HeckeSkeleton.Moments.EngineInduction
