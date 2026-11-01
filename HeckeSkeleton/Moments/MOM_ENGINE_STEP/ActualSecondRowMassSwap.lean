import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCorrelationColumnSwap

/-!
# The same actual row arithmetic after column exchange

Exchange of the two common columns negates the original frequency.  The
unit and nonunit frequency tests, their radicals, and the genuine gcd
generator are unchanged.  The residual element selected from the new
source is consequently the negative of the already selected old element;
its ideal is exactly the same.  This comparison does not choose another
residual ideal or assume equality of whole polynomials.

The row-mass data below exchange the original frozen atoms and conjugate
the original row profile.  Their original mask, radius, ideals, profile
bound and ideal fibres are preserved.  All resulting row bounds are
therefore equalities on the same source, with no new mass hypothesis.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- Negating the divided frequency keeps it a unit at the original
prime.  Both equal-depth conditions are retained literally. -/
@[simp] theorem unitFrequencySaving_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) :
    unitFrequencySaving C p n m (-h) ↔ unitFrequencySaving C p m n h := by
  by_cases hmn : m = n
  · subst n
    constructor
    · rintro ⟨_, hsix, k, hk, hkunit⟩
      refine ⟨rfl, hsix, -k, ?_, ?_⟩
      · simpa only [neg_neg, mul_neg] using congrArg Neg.neg hk
      · simpa only [dvd_neg] using hkunit
    · rintro ⟨_, hsix, k, hk, hkunit⟩
      refine ⟨rfl, hsix, -k, ?_, ?_⟩
      · simpa only [mul_neg] using congrArg Neg.neg hk
      · simpa only [dvd_neg] using hkunit
  · have hnm : n ≠ m := Ne.symm hmn
    simp only [unitFrequencySaving, hmn, hnm, false_and]

/-- Divisibility by the extra original prime power is unchanged by
negating the original frequency. -/
@[simp] theorem nonunitFrequencySaving_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) :
    nonunitFrequencySaving C p n m (-h) ↔ nonunitFrequencySaving C p m n h := by
  by_cases hmn : m = n
  · subst n
    simp only [nonunitFrequencySaving, dvd_neg]
  · have hnm : n ≠ m := Ne.symm hmn
    simp only [nonunitFrequencySaving, hmn, hnm, false_and]

section Radical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem unitFrequencyRadical_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    unitFrequencyRadical C p n m (-h) = unitFrequencyRadical C p m n h := by
  unfold unitFrequencyRadical
  congr 1
  funext i
  rw [unitFrequencySaving_swap_neg]

@[simp] theorem nonunitFrequencyRadical_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    nonunitFrequencyRadical C p n m (-h) = nonunitFrequencyRadical C p m n h := by
  unfold nonunitFrequencyRadical
  congr 1
  funext i
  rw [nonunitFrequencySaving_swap_neg]

@[simp] theorem nonunitFrequencyGenerator_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    nonunitFrequencyGenerator C p n m (-h) = nonunitFrequencyGenerator C p m n h := by
  unfold nonunitFrequencyGenerator
  congr 1
  funext i
  rw [nonunitFrequencySaving_swap_neg]

/-- The positive multiplicity-one contribution uses the very same
selected primes, not a smaller endpoint of a logarithmic window. -/
@[simp] theorem multiplicityOneNonunitPrimes_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    multiplicityOneNonunitPrimes C p n m (-h) =
      multiplicityOneNonunitPrimes C p m n h := by
  ext i
  simp only [multiplicityOneNonunitPrimes, Finset.mem_filter, Finset.mem_univ,
    true_and, nonunitFrequencySaving_swap_neg]
  tauto

@[simp] theorem multiplicityOneNonunitRadical_swap_neg
    (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
    (m n : ι → ℕ) (h : A.R) :
    multiplicityOneNonunitRadical C p n m (-h) =
      multiplicityOneNonunitRadical C p m n h := by
  unfold multiplicityOneNonunitRadical
  rw [multiplicityOneNonunitPrimes_swap_neg]

end Radical

namespace ActualSecondCorrelationRows

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (R : ActualSecondCorrelationRows A σ H ι)

@[simp] theorem swapColumns_unitFrequencyRadical
    (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    unitFrequencyRadical C R.swapColumns.primes R.swapColumns.leftMultiplicity
        R.swapColumns.rightMultiplicity (R.swapColumns.frequency h) =
      unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) :=
  unitFrequencyRadical_swap_neg C R.primes R.leftMultiplicity R.rightMultiplicity _

@[simp] theorem swapColumns_nonunitFrequencyRadical
    (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    nonunitFrequencyRadical C R.swapColumns.primes R.swapColumns.leftMultiplicity
        R.swapColumns.rightMultiplicity (R.swapColumns.frequency h) =
      nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) :=
  nonunitFrequencyRadical_swap_neg C R.primes R.leftMultiplicity R.rightMultiplicity _

@[simp] theorem swapColumns_multiplicityOneNonunitRadical
    (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    multiplicityOneNonunitRadical C R.swapColumns.primes R.swapColumns.leftMultiplicity
        R.swapColumns.rightMultiplicity (R.swapColumns.frequency h) =
      multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h) :=
  multiplicityOneNonunitRadical_swap_neg C R.primes R.leftMultiplicity R.rightMultiplicity _

@[simp] theorem swapColumns_factor
    (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    R.swapColumns.factor C h = R.factor C h := by
  change primePowerProductGenerator C R.primes
      (fun i => min (R.rightMultiplicity i) (R.leftMultiplicity i)) *
      nonunitFrequencyGenerator C R.primes R.rightMultiplicity R.leftMultiplicity
        (-R.frequency h) = _
  rw [nonunitFrequencyGenerator_swap_neg]
  have hm : (fun i => min (R.rightMultiplicity i) (R.leftMultiplicity i)) =
      (fun i => min (R.leftMultiplicity i) (R.rightMultiplicity i)) :=
    funext (fun i => min_comm _ _)
  rw [hm] <;> rfl

@[simp] theorem swapColumns_normFactor
    (C : A.GeneralArithmeticContext σ η hS) (h : H) :
    R.swapColumns.normFactor C h = R.normFactor C h := by
  change (Ideal.absNorm (gcd (primePowerProduct R.primes R.rightMultiplicity).val
      (primePowerProduct R.primes R.leftMultiplicity).val) : ℝ) *
      A.exteriorNorm (nonunitFrequencyRadical C R.primes R.rightMultiplicity
        R.leftMultiplicity (-R.frequency h)) = _
  rw [nonunitFrequencyRadical_swap_neg, gcd_comm] <;> rfl

private def mapFiniteCarrier {H : Type*} (s t : Finset H) (hst : s = t) (h : s) : t :=
  ⟨h.val, hst ▸ h.property⟩

private theorem mapFiniteCarrier_val {H : Type*} (s t : Finset H) (hst : s = t) (h : s) :
    (mapFiniteCarrier s t hst h).val = h.val := rfl

/-- Identity on the original live row label. The generic finite carrier
transport keeps the kernel from unfolding the complete correlation. -/
def swapLive (h : R.live) : R.swapColumns.live :=
  mapFiniteCarrier R.live R.swapColumns.live R.swapColumns_live.symm h

@[simp] theorem swapLive_val (h : R.live) : (R.swapLive h).val = h.val :=
  mapFiniteCarrier_val R.live R.swapColumns.live R.swapColumns_live.symm h

private theorem negative_residual_of_same_factor
    {T : Type*} [Ring T] [IsDomain T] (f g x y : T)
    (hg : g ≠ 0) (hx : f = g * x) (hy : -f = g * y) : y = -x := by
  apply mul_left_cancel₀ hg
  calc
    g * y = -f := hy.symm
    _ = -(g * x) := congrArg Neg.neg hx
    _ = g * -x := (mul_neg g x).symm

set_option maxHeartbeats 800000 in
/-- Uniqueness after cancellation proves the actual selected residual
element is negated. No new residual generator is selected in this proof. -/
theorem swapColumns_extractedRow_element
    (C : A.GeneralArithmeticContext σ η hS) (h : R.live) :
    (R.swapColumns.extractedRow C (R.swapLive h)).element =
      -(R.extractedRow C h).element := by
  have hg : R.factor C h.val ≠ 0 := by
    intro hz
    have he : R.frequency h.val = 0 :=
      (R.extractedRow C h).frequency.trans
        ((congrArg (fun z : A.R => z * (R.extractedRow C h).element) hz).trans
          (zero_mul _))
    exact (R.generates h.val (Finset.mem_filter.mp h.property).1).1 he
  have hfrequency : R.swapColumns.frequency (R.swapLive h).val = -R.frequency h.val := by
    rw [R.swapLive_val, R.swapColumns_frequency]
  have hfactor : R.swapColumns.factor C (R.swapLive h).val = R.factor C h.val := by
    rw [R.swapLive_val, R.swapColumns_factor]
  have hs : -R.frequency h.val = R.factor C h.val *
      (R.swapColumns.extractedRow C (R.swapLive h)).element :=
    hfrequency.symm.trans
      ((R.swapColumns.extractedRow C (R.swapLive h)).frequency.trans
        (congrArg (fun z : A.R => z *
          (R.swapColumns.extractedRow C (R.swapLive h)).element) hfactor))
  exact negative_residual_of_same_factor (R.frequency h.val) (R.factor C h.val)
    (R.extractedRow C h).element (R.swapColumns.extractedRow C (R.swapLive h)).element
    hg (R.extractedRow C h).frequency hs

/-- The selected residual ideal is exactly the original one. -/
@[simp] theorem swapColumns_extractedRow_ideal
    (C : A.GeneralArithmeticContext σ η hS) (h : R.live) :
    (R.swapColumns.extractedRow C (R.swapLive h)).ideal = (R.extractedRow C h).ideal := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  change A.extendIdeal (R.swapColumns.extractedRow C (R.swapLive h)).ideal =
    A.extendIdeal (R.extractedRow C h).ideal
  rw [← (R.swapColumns.extractedRow C (R.swapLive h)).generates.2,
    ← (R.extractedRow C h).generates.2, R.swapColumns_extractedRow_element C h,
    Ideal.span_singleton_neg]

@[simp] theorem swapColumns_extractedRow_momentIdeal
    (C : A.GeneralArithmeticContext σ η hS) (h : R.live) :
    (R.swapColumns.extractedRow C (R.swapLive h)).momentIdeal =
      (R.extractedRow C h).momentIdeal :=
  congrArg exteriorMomentIdeal (R.swapColumns_extractedRow_ideal C h)

end ActualSecondCorrelationRows

section RowMass

variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The true second Poisson scalar is real; its original radius and
mask are not replaced when the two columns exchange. -/
@[simp] theorem star_secondOrbitalScalar
    (radius : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R)) :
    star (secondOrbitalScalar (K := K) (S := A.Sf) radius mask) =
      secondOrbitalScalar (K := K) (S := A.Sf) radius mask := by
  simp [secondOrbitalScalar]

namespace ActualSecondRowMass

variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- Reuse every original atom and every original ideal fibre.  Positivity
of the original right common multiplicities is the only side condition;
it is the primitive common-support condition, not a row bound. -/
def swapColumns (hright : ∀ i, 0 < R.rightMultiplicity i) :
    ActualSecondRowMass R.swapColumns C kRight kLeft where
  leftAtoms := W.rightAtoms
  rightAtoms := W.leftAtoms
  left_ideal := W.right_ideal
  right_ideal := W.left_ideal
  radius := W.radius
  mask := W.mask
  rowProfile h := star (W.rowProfile h)
  profileBound := W.profileBound
  profileBound_nonneg := W.profileBound_nonneg
  profile_bound h hh := by
    simpa only [norm_star] using W.profile_bound h hh
  weight_eq h hh := by
    change star (R.weight h) =
      secondOrbitalScalar (K := K) (S := A.Sf) W.radius W.mask *
        star (W.rowProfile h) * W.rightAtoms.value h * star (W.leftAtoms.value h)
    rw [W.weight_eq h hh]
    simp only [star_mul', star_star, star_secondOrbitalScalar]
    ring
  unitIdeal := W.unitIdeal
  unit_ideal h hh := by
    rw [R.swapColumns_unitFrequencyRadical C h]
    exact W.unit_ideal h hh
  nonunitIdeal := W.nonunitIdeal
  nonunit_ideal h hh := by
    rw [R.swapColumns_nonunitFrequencyRadical C h]
    exact W.nonunit_ideal h hh
  left_positive := hright
  originalFiber := W.originalFiber
  original_fibers := W.original_fibers

variable (hright : ∀ i, 0 < R.rightMultiplicity i)

@[simp] theorem swapColumns_leftAtoms : (W.swapColumns hright).leftAtoms = W.rightAtoms := rfl

@[simp] theorem swapColumns_rightAtoms : (W.swapColumns hright).rightAtoms = W.leftAtoms := rfl

@[simp] theorem swapColumns_leftIdeal : (W.swapColumns hright).leftIdeal = W.rightIdeal := rfl

@[simp] theorem swapColumns_rightIdeal : (W.swapColumns hright).rightIdeal = W.leftIdeal := rfl

@[simp] theorem swapColumns_radius : (W.swapColumns hright).radius = W.radius := rfl

@[simp] theorem swapColumns_mask : (W.swapColumns hright).mask = W.mask := rfl

@[simp] theorem swapColumns_rowProfile (h : H) :
    (W.swapColumns hright).rowProfile h = star (W.rowProfile h) := rfl

@[simp] theorem swapColumns_profileBound :
    (W.swapColumns hright).profileBound = W.profileBound := rfl

@[simp] theorem swapColumns_unitIdeal : (W.swapColumns hright).unitIdeal = W.unitIdeal := rfl

@[simp] theorem swapColumns_nonunitIdeal :
    (W.swapColumns hright).nonunitIdeal = W.nonunitIdeal := rfl

@[simp] theorem swapColumns_originalFiber :
    (W.swapColumns hright).originalFiber = W.originalFiber := rfl

@[simp] theorem swapColumns_commonEnvelope :
    (W.swapColumns hright).commonEnvelope = W.commonEnvelope := by
  change W.profileBound * Real.sqrt W.rightAtoms.envelope * Real.sqrt W.leftAtoms.envelope =
    W.profileBound * Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope
  ring

@[simp] theorem swapColumns_commonDenominator :
    (W.swapColumns hright).commonDenominator = W.commonDenominator := by
  change Real.sqrt (Ideal.absNorm W.rightIdeal : ℝ) *
      Real.sqrt (Ideal.absNorm W.leftIdeal : ℝ) =
    Real.sqrt (Ideal.absNorm W.leftIdeal : ℝ) * Real.sqrt (Ideal.absNorm W.rightIdeal : ℝ)
  exact mul_comm _ _

@[simp] theorem swapColumns_correlationBound :
    (W.swapColumns hright).correlationBound = W.correlationBound := by
  change (Ideal.absNorm (gcd W.rightIdeal W.leftIdeal) : ℝ) /
      (Ideal.absNorm W.unitIdeal.val : ℝ) = _
  rw [gcd_comm] <;> rfl

/-- All complete-correlation and frozen-common costs are identical. -/
@[simp] theorem swapColumns_rowBound :
    (W.swapColumns hright).rowBound = W.rowBound := by
  simp only [rowBound, swapColumns_radius, swapColumns_mask,
    swapColumns_commonEnvelope, swapColumns_commonDenominator, swapColumns_correlationBound]

end ActualSecondRowMass
end RowMass

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.unitFrequencySaving_swap_neg
#print axioms HeckeSkeleton.Moments.EngineStep.multiplicityOneNonunitRadical_swap_neg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns_extractedRow_element
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapColumns_extractedRow_ideal
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.swapColumns
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.swapColumns_rowBound
