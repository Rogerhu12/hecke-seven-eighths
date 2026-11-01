import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPaidCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualCharacters
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogMetadata

/-!
# The actual support of the paid literal source

The original effective moving support, the selected physical first
divisor, the first active radical, and the reduced pool factor pay the
entire new moving support.  The first phase's higher powers add no new
primes.  The chosen empty-mask unit is retained and has support norm one.

The passive deletion is deliberately absent from this remaining ideal:
`CanonicalLiteralPaidCharacters` transfers it to an independent finite
Mobius expansion.  In particular valuation six has no pool support cost.
No completed support window is an input to the actual four constructors.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalLiteralPhaseCalibration CanonicalLiteralActualCharacters
open CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

private theorem paid_primeSupport_mul (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    primeSupport (I * J) = primeSupport I ∪ primeSupport J := by
  simp only [primeSupport, normalizedFactors_mul hI hJ, Multiset.toFinset_add]

namespace OriginalMovingFactors

/-- Appending genuine factors only adds their displayed radical.  The
old remaining ideal is exteriorized once, exactly as in the old source. -/
theorem appendFactors_effectiveFullSupport_dvd
    (D E : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((D.appendFactors E).effectiveFullSupport remaining).val ∣
      (D.effectiveFullSupport remaining).val * E.support.val := by
  rw [← squarefree_support_product_self
    ((D.appendFactors E).effectiveFullSupport_squarefree remaining)]
  apply support_product_dvd
    (mul_ne_zero (D.effectiveFullSupport remaining).property.1 E.support.property.1)
  intro p hp
  rw [(D.appendFactors E).effectiveFullSupport_primes remaining,
    D.appendFactors_support_primes E] at hp
  rw [paid_primeSupport_mul _ _ (D.effectiveFullSupport remaining).property.1
    E.support.property.1, D.effectiveFullSupport_primes remaining]
  simp only [Finset.mem_union] at hp ⊢
  rcases hp with (hD | hE) | hremaining
  · exact Or.inl (Or.inl hD)
  · exact Or.inr hE
  · exact Or.inl (Or.inr hremaining)

theorem appendFactors_effectiveFullSupport_norm_le
    (D E : OriginalMovingFactors A P Rchar)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm ((D.appendFactors E).effectiveFullSupport remaining) ≤
      A.exteriorNorm (D.effectiveFullSupport remaining) * A.exteriorNorm E.support := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero (D.effectiveFullSupport remaining).property.1 E.support.property.1)
    (D.appendFactors_effectiveFullSupport_dvd E remaining)
  simpa only [map_mul, Nat.cast_mul] using h

end OriginalMovingFactors

namespace CanonicalLiteralPaidSupport

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- This uses the three actual singleton lists in their original order. -/
theorem moving_norm_le (F : FixedPhases A) (old : OriginalMovingFactors A P R)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) :
    A.exteriorNorm ((F.moving P R old).effectiveFullSupport remaining) ≤
      ((A.exteriorNorm (old.effectiveFullSupport remaining) *
        A.exteriorNorm (F.firstMoving P R).support) *
        A.exteriorNorm (F.poolMoving P R).support) *
        A.exteriorNorm (F.unitMoving P R).support := by
  have hfirst := old.appendFactors_effectiveFullSupport_norm_le (F.firstMoving P R) remaining
  have hpool := (old.appendFactors (F.firstMoving P R)).appendFactors_effectiveFullSupport_norm_le
    (F.poolMoving P R) remaining
  have hunit := ((old.appendFactors (F.firstMoving P R)).appendFactors
    (F.poolMoving P R)).appendFactors_effectiveFullSupport_norm_le
      (F.unitMoving P R) remaining
  exact hunit.trans (mul_le_mul_of_nonneg_right
    (hpool.trans (mul_le_mul_of_nonneg_right hfirst (by positivity))) (by positivity))

private theorem singleton_unit_norm (a : A.R)
    (ha : A.Generates (unitExterior A) a) :
    A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support = 1 := by
  change (Ideal.absNorm
    (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support.val : ℝ) = 1
  rw [OriginalMovingFactors.singleton_support _ _ ha 1]
  simp [unitExterior, commonRadical, primeSupport, ← Ideal.one_eq_top]

section FirstPhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem powerProduct_radical_mul_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (D : A.Exterior) :
    commonRadical (D.val * (primePowerProduct p e).val)
        (D.val * (primePowerProduct p e).val) ∣
      D.val * (primePowerProduct p (fun _ => 1)).val := by
  unfold commonRadical
  rw [Finset.inter_self]
  apply support_product_dvd (mul_ne_zero D.property.1
    (primePowerProduct p (fun _ => 1)).property.1)
  rw [paid_primeSupport_mul _ _ D.property.1 (primePowerProduct p e).property.1,
    paid_primeSupport_mul _ _ D.property.1
      (primePowerProduct p (fun _ => 1)).property.1,
    primePowerProduct_support p hp e he,
    primePowerProduct_support p hp (fun _ => 1) (fun _ => Nat.zero_lt_one)] <;>
    exact Finset.Subset.refl _

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)

theorem leftMoving_support_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.leftMoving C P R p m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal p m n).val := by
  rw [CanonicalLiteralFirstPhase.leftMoving_support]
  exact powerProduct_radical_mul_dvd (firstActivePrimes p m n)
    (firstActivePrimes_injective p hp m n)
    (CanonicalLiteralFirstPhase.leftExponent m n) (fun i => by
      simp only [CanonicalLiteralFirstPhase.leftExponent]; omega) D

theorem rightMoving_support_dvd (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    (CanonicalLiteralFirstPhase.rightMoving C P R p m n D δ hδ).support.val ∣
      D.val * (firstActiveIdeal p m n).val := by
  rw [CanonicalLiteralFirstPhase.rightMoving_support]
  exact powerProduct_radical_mul_dvd (firstActivePrimes p m n)
    (firstActivePrimes_injective p hp m n)
    (CanonicalLiteralFirstPhase.rightExponent m n) (fun i => by
      simp only [CanonicalLiteralFirstPhase.rightExponent]; omega) D

theorem leftMoving_norm_le (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.leftMoving C P R p m n D δ hδ).support ≤
      A.exteriorNorm D * A.exteriorNorm (firstActiveIdeal p m n) := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero D.property.1 (firstActiveIdeal p m n).property.1)
    (leftMoving_support_dvd P R C p hp m n D δ hδ)
  simpa only [map_mul, Nat.cast_mul] using h

theorem rightMoving_norm_le (p : ι → ExteriorPrime A)
    (hp : Function.Injective p) (m n : ι → ℕ)
    (D : A.Exterior) (δ : A.R) (hδ : A.Generates D δ) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.rightMoving C P R p m n D δ hδ).support ≤
      A.exteriorNorm D * A.exteriorNorm (firstActiveIdeal p m n) := by
  have h := HeckePort.Moments.norm_le_of_dvd
    (mul_ne_zero D.property.1 (firstActiveIdeal p m n).property.1)
    (rightMoving_support_dvd P R C p hp m n D δ hδ)
  simpa only [map_mul, Nat.cast_mul] using h

end FirstPhase

section ActualBlocks

variable [IsPrincipalIdealRing A.R]
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (D : Finset (HeightOneSpectrum A.R))
variable (old : OriginalMovingFactors A P R)
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The actual selected divisor and the original active radical give
the whole first-phase window. The chosen generator is not changed. -/
theorem left_first_window (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.leftMoving C P R b.primes
      b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)).support ≤
      Z ^ (idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  have h := leftMoving_norm_le P R C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    (originalFrequencyIdeal_generates _
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)
  rw [b.activeNorm_eq] at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _ (firstActiveRadical_ne_zero _ _),
        rpow_idealLogLength Z hZ _ (firstPhysicalDivisorIdeal (A := A) D).property.1]
      exact mul_comm _ _

theorem right_first_window (Z : ℝ) (hZ : 1 < Z) :
    A.exteriorNorm (CanonicalLiteralFirstPhase.rightMoving C P R b.primes
      b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
      (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)).support ≤
      Z ^ (idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  have h := rightMoving_norm_le P R C b.primes b.primes_injective
    b.leftMultiplicity b.rightMultiplicity (firstPhysicalDivisorIdeal (A := A) D)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
    (originalFrequencyIdeal_generates _
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).property)
  rw [b.activeNorm_eq] at h
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans hZ),
        rpow_idealLogLength Z hZ _ (firstActiveRadical_ne_zero _ _),
        rpow_idealLogLength Z hZ _ (firstPhysicalDivisorIdeal (A := A) D).property.1]
      exact mul_comm _ _

private theorem unamplified_window (firstIdeal : A.Exterior) (a : A.R)
    (ha : A.Generates firstIdeal a) (Z q firstCost : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤
      Z ^ firstCost) :
    A.exteriorNorm (((unamplifiedPhases firstIdeal a ha).moving P R old)
      .effectiveFullSupport remaining) ≤ Z ^ (q + firstCost) := by
  have hp : A.exteriorNorm ((unamplifiedPhases firstIdeal a ha).poolMoving P R).support = 1 :=
    singleton_unit_norm P R 1 (unitExterior_generates A)
  have hu : A.exteriorNorm ((unamplifiedPhases firstIdeal a ha).unitMoving P R).support = 1 :=
    singleton_unit_norm P R _ CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
  have h := moving_norm_le P R (unamplifiedPhases firstIdeal a ha) old remaining
  rw [hp, hu, mul_one, mul_one] at h
  exact h.trans (by
    rw [Real.rpow_add (zero_lt_one.trans hZ)]
    exact mul_le_mul hold hfirst (by positivity) (by positivity))

private theorem reduced_window (firstIdeal : A.Exterior) (a : A.R)
    (ha : A.Generates firstIdeal a) (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q firstCost : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q)
    (hfirst : A.exteriorNorm
      (OriginalMovingFactors.singleton (P := P) (R := R) ⟨a, ha.1⟩ 1).support ≤
      Z ^ firstCost) :
    A.exteriorNorm (((reducedPhases
      (amplifiedPhases C firstIdeal a ha p e.multiplicity) C p e).moving P R old)
      .effectiveFullSupport remaining) ≤
      Z ^ (q + firstCost + (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  let F := reducedPhases (amplifiedPhases C firstIdeal a ha p e.multiplicity) C p e
  have hu : A.exteriorNorm (F.unitMoving P R).support = 1 :=
    singleton_unit_norm P R _ CanonicalLiteralFixedPhases.emptyDivisorInverse_generates
  have hp : A.exteriorNorm (F.poolMoving P R).support =
      Z ^ ((e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) :=
    CanonicalLiteralPassivePhases.activeMoving_norm_eq_rpow P R C p e Z hZ
  have h := moving_norm_le P R F old remaining
  rw [hu, mul_one, hp] at h
  exact h.trans (by
    rw [Real.rpow_add (zero_lt_one.trans hZ), Real.rpow_add (zero_lt_one.trans hZ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hold hfirst (by positivity) (by positivity)) (by positivity))

/-- Direct and main, left side: only the original `q`, active `R`,
and selected physical `E` enter the actual paid support. -/
theorem unamplified_left (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  simpa only [add_assoc] using unamplified_window P R old remaining firstFixed _ hfirst
    Z q _ hZ hold (left_first_window P R C b D Z hZ)

theorem unamplified_right (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((unamplifiedPhases firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val) := by
  simpa only [add_assoc] using unamplified_window P R old remaining firstFixed _ hfirst
    Z q _ hZ hold (right_first_window P R C b D Z hZ)

/-- Pool, left side: the exact reduced factor adds the original
`movingMultiplicity * logNorm p`.  Valuation six adds zero. -/
theorem reduced_amplified_left (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((reducedPhases (amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst p e.multiplicity) C p e).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val +
        (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  simpa only [add_assoc] using reduced_window P R C old remaining firstFixed _ hfirst p e
    Z q _ hZ hold (left_first_window P R C b D Z hZ)

theorem reduced_amplified_right (firstFixed : A.Exterior)
    (hfirst : A.Generates firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes
      b.leftMultiplicity b.rightMultiplicity
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
    (p : ExteriorPrime A) (e : AmplifierValuation)
    (Z q : ℝ) (hZ : 1 < Z)
    (hold : A.exteriorNorm (old.effectiveFullSupport remaining) ≤ Z ^ q) :
    A.exteriorNorm (((reducedPhases (amplifiedPhases C firstFixed
      (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity b.rightMultiplicity
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
      hfirst p e.multiplicity) C p e).moving P R old).effectiveFullSupport remaining) ≤
      Z ^ (q + idealLogLength Z (firstActiveRadical DE.1 DE.2) +
        idealLogLength Z (firstPhysicalDivisorIdeal (A := A) D).val +
        (e.movingMultiplicity : ℝ) * idealLogLength Z p.val.asIdeal) := by
  simpa only [add_assoc] using reduced_window P R C old remaining firstFixed _ hfirst p e
    Z q _ hZ hold (right_first_window P R C b D Z hZ)

end ActualBlocks
end CanonicalLiteralPaidSupport
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMovingFactors.appendFactors_effectiveFullSupport_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.leftMoving_support_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.rightMoving_support_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.unamplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.unamplified_right
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.reduced_amplified_left
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPaidSupport.reduced_amplified_right
