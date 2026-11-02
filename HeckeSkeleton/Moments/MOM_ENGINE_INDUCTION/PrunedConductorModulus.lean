import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingRowConductor

/-!
# One actual modulus for the conductor and its remaining deletions

The full finite conductor may have arbitrary wild multiplicities. Only
the deletion set is squarefree, because it is an actual finite set of
prime ideals. Removing the primes already in the conductor makes its
product coprime to that entire conductor, not just to its radical.

If both pieces divide the same genuine modulus, their product divides
that modulus. This is the arithmetic step needed for a moving-row
recipe's displayed-support budget. It does not replace that modulus by
the product of independent norm bounds, and it supplies no row-character
identification, mask identity or final moment estimate as an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The actual conductor, with all its multiplicities, and the radical
of the genuinely redundant deletion primes use one common modulus. -/
theorem conductor_prunedDeletion_dvd
    (χ : HeckeCharacter K) (deletions : Finset (Ideal (𝓞 K)))
    (hprime : ∀ p ∈ deletions, Prime p) (modulus : NonzeroIdeal K)
    (hconductor : (finiteConductor K χ).val ∣ modulus.val)
    (hdeletion : ∀ p ∈ deletions, p ∣ modulus.val) :
    (finiteConductor K χ).val *
      (∏ p ∈ deletions \ primeSupport (finiteConductor K χ).val, p) ∣ modulus.val := by
  let E := deletions \ primeSupport (finiteConductor K χ).val
  have hC0 : (finiteConductor K χ).val ≠ ⊥ :=
    nonZeroDivisors.coe_ne_zero (finiteConductor K χ)
  have hM0 : modulus.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero modulus
  have hE : ∀ p ∈ E, Prime p := fun p hp => hprime p (Finset.mem_sdiff.mp hp).1
  have hD : (∏ p ∈ E, p) ∣ modulus.val := by
    apply support_product_dvd hM0
    intro p hp
    exact (prime_mem_support_iff modulus.val p hM0 (hE p hp)).mpr
      (hdeletion p (Finset.mem_sdiff.mp hp).1)
  have hcoprime : IsCoprime (∏ p ∈ E, p) (finiteConductor K χ).val := by
    apply (primeSupport_disjoint_iff (subset_product_nonzero E hE) hC0).mp
    have hf : normalizedFactors (∏ p ∈ E, p) = E.val := by
      simpa using normalizedFactors_prod_of_prime (m := E.val) hE
    have hs : primeSupport (∏ p ∈ E, p) = E := by
      simp only [primeSupport, hf, Finset.val_toFinset]
    rw [hs]
    exact Finset.disjoint_left.mpr (fun p hp hpc => (Finset.mem_sdiff.mp hp).2 hpc)
  exact hcoprime.symm.mul_dvd hconductor hD

/-- The functional-equation scale and the remaining deletion product
are bounded by the norm of that same modulus. The discriminant occurs
once, and no independent conductor-times-mask norm estimate is used. -/
theorem conductorScale_mul_prunedDeletion_norm_le
    (χ : HeckeCharacter K) (deletions : Finset (Ideal (𝓞 K)))
    (hprime : ∀ p ∈ deletions, Prime p) (modulus : NonzeroIdeal K)
    (hconductor : (finiteConductor K χ).val ∣ modulus.val)
    (hdeletion : ∀ p ∈ deletions, p ∣ modulus.val) :
    heckeConductorScale K χ *
        (Ideal.absNorm (∏ p ∈ deletions \ primeSupport (finiteConductor K χ).val, p) : ℝ) ≤
      ((NumberField.discr K).natAbs : ℝ) * idealNorm K modulus := by
  have hn := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors modulus)
    (map_dvd Ideal.absNorm
      (conductor_prunedDeletion_dvd χ deletions hprime modulus hconductor hdeletion))
  simp only [map_mul] at hn
  have hreal : (Ideal.absNorm (finiteConductor K χ).val : ℝ) *
      (Ideal.absNorm (∏ p ∈ deletions \ primeSupport (finiteConductor K χ).val, p) : ℝ) ≤
        idealNorm K modulus := by
    dsimp only [idealNorm]
    exact_mod_cast hn
  simpa only [heckeConductorScale, mul_assoc] using
    mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg (NumberField.discr K).natAbs)

/-- Genuine moving factors and the original remaining mask fit in the
same displayed-support modulus. Only the modulus used in this proof is
enlarged: the actual deletion set continues to use the original extra
ideal. Integer character exponents do not enlarge the displayed support. -/
theorem actualMovingConductor_remainingProduct_dvd {Index : Type*}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (β : HeckeCharacter K)
    (indices : Finset Index) (factor : Index → ExteriorIdeal K S)
    (factorSector : Index → SixthUnitClasses K S) (exponent : Index → ℤ)
    (displayed : NonzeroIdeal K)
    (hsupport : ∀ i ∈ indices, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val)
    (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S)
    (extra : NonzeroIdeal K) (hextra : extra.val ∣ displayed.val) :
    let χ := β * ((∏ i ∈ indices,
      completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
        completeIdealRowCharacter K S probe rows sector u.val)
    (finiteConductor K χ).val *
      (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
        primeSupport (finiteConductor K χ).val, p) ∣
      reflectionConductorBudget S β * u.val.val * displayed.val := by
  dsimp only
  let χ := β * ((∏ i ∈ indices,
    completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
      completeIdealRowCharacter K S probe rows sector u.val)
  have hM0 : reflectionConductorBudget S β * u.val.val * displayed.val ≠ ⊥ :=
    mul_ne_zero (mul_ne_zero (reflectionConductorBudget_ne_bot S β)
      (nonZeroDivisors.coe_ne_zero u.val)) (nonZeroDivisors.coe_ne_zero displayed)
  let modulus : NonzeroIdeal K :=
    ⟨reflectionConductorBudget S β * u.val.val * displayed.val,
      mem_nonZeroDivisors_of_ne_zero hM0⟩
  have hconductor : (finiteConductor K χ).val ∣ modulus.val := by
    apply (completeMovingRowCharacter_conductor_dvd S probe rows β indices factor
      factorSector exponent displayed hsupport sector u).trans
    refine ⟨fixedRowDeletionIdeal S, ?_⟩
    dsimp only [modulus, reflectionConductorBudget]
    simp only [Submonoid.coe_mul]
    ring
  have hbase : fixedRowDeletionIdeal S * u.val.val * extra.val ∣ modulus.val := by
    apply (mul_dvd_mul (dvd_refl (fixedRowDeletionIdeal S * u.val.val)) hextra).trans
    refine ⟨(finiteConductor K β).val * (sexticSConductorBudgetIdeal K S).val, ?_⟩
    dsimp only [modulus, reflectionConductorBudget]
    ring
  have hdeletion (p : Ideal (𝓞 K)) (hp : p ∈ remainingRowDeletionPrimes S u.val extra) :
      p ∣ modulus.val :=
    (Finset.dvd_prod_of_mem (fun q : Ideal (𝓞 K) => q) hp).trans
      ((remainingRowDeletionProduct_dvd S u.val extra).trans hbase)
  exact conductor_prunedDeletion_dvd χ (remainingRowDeletionPrimes S u.val extra)
    (remainingRowDeletionPrimes_prime S u.val extra) modulus hconductor hdeletion

/-- The actual moving-row FE scale times the original pruned deletion
product is linear in N(u) and in the one displayed-support norm. The
remaining ideal is already inside that displayed support and is not
charged a second time. -/
theorem actualMovingReflectionScale_remainingProduct_le {Index : Type*}
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (β : HeckeCharacter K)
    (indices : Finset Index) (factor : Index → ExteriorIdeal K S)
    (factorSector : Index → SixthUnitClasses K S) (exponent : Index → ℤ)
    (displayed : NonzeroIdeal K)
    (hsupport : ∀ i ∈ indices, (nonzeroIdealRadical K (factor i).val).val ∣ displayed.val)
    (sector : SixthUnitClasses K S) (u : ExteriorIdeal K S)
    (extra : NonzeroIdeal K) (hextra : extra.val ∣ displayed.val) :
    let χ := β * ((∏ i ∈ indices,
      completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
        completeIdealRowCharacter K S probe rows sector u.val)
    heckeConductorScale K χ *
        (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
          primeSupport (finiteConductor K χ).val, p) : ℝ) ≤
      reflectionConductorConstant S β * idealNorm K u.val * idealNorm K displayed := by
  dsimp only
  have hM0 : reflectionConductorBudget S β * u.val.val * displayed.val ≠ ⊥ :=
    mul_ne_zero (mul_ne_zero (reflectionConductorBudget_ne_bot S β)
      (nonZeroDivisors.coe_ne_zero u.val)) (nonZeroDivisors.coe_ne_zero displayed)
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hM0 (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm
      (actualMovingConductor_remainingProduct_dvd S probe rows β indices factor
        factorSector exponent displayed hsupport sector u extra hextra))
  simp only [map_mul] at hn
  let χ := β * ((∏ i ∈ indices,
    completeIdealRowCharacter K S probe rows (factorSector i) (factor i).val ^ exponent i) *
      completeIdealRowCharacter K S probe rows sector u.val)
  have hreal : (Ideal.absNorm (finiteConductor K χ).val : ℝ) *
      (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
        primeSupport (finiteConductor K χ).val, p) : ℝ) ≤
      (Ideal.absNorm (reflectionConductorBudget S β) : ℝ) *
        idealNorm K u.val * idealNorm K displayed := by
    dsimp only [χ, idealNorm]
    exact_mod_cast hn
  simpa only [heckeConductorScale, reflectionConductorConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg (NumberField.discr K).natAbs)

end HeckeSkeleton.Moments.EngineInduction
