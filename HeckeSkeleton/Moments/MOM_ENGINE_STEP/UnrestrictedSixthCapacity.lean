import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SixthDeletionCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyClassStability

/-!
# Capacity from the original frequency pattern, including empty classes

An ordinary row class can be empty even when its original finite leaf is
live.  Its normalization must therefore be constructed before, and without,
an ordinary-row witness.  The original Boolean nonunit pattern supplies
the unit ideal directly: equal non-six-divisible multiplicities outside
that pattern contribute one copy of their original prime.

The complete sixth root fits with this ideal inside the original gcd for
every pattern, including unrealized and empty classes.  On every actual
nonzero correlation row the local frequency partition identifies the
computed ideal with the original unit-frequency radical.  These facts
construct the same capacity ledger from primitive prime data and original
scale windows.  Its equality with the existing row-anchored input is
literal equality of all data fields; no child is selected again.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unit ideal is computed from the original nonunit pattern.  No
row, selected child, or numerical saving is an input. -/
def secondPatternUnitIdeal (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (pattern : ι → Bool) : A.Exterior :=
  primePowerProduct p (fun i =>
    if m i = n i ∧ ¬6 ∣ m i ∧ pattern i = false then 1 else 0)

def secondPatternNonunitIdeal (p : ι → ExteriorPrime A) (pattern : ι → Bool) :
    A.Exterior :=
  primePowerProduct p (fun i => if pattern i = true then 1 else 0)

@[simp] theorem secondPatternUnitIdeal_swap
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (pattern : ι → Bool) :
    secondPatternUnitIdeal p n m pattern = secondPatternUnitIdeal p m n pattern := by
  unfold secondPatternUnitIdeal
  apply congrArg (primePowerProduct p)
  funext i
  by_cases he : m i = n i
  · simp only [he]
  · simp only [he, Ne.symm he, false_and, if_false]

/-- An arbitrary original pattern costs at most one copy of each
prime in addition to the complete sixth-root multiplicity. -/
theorem secondPatternUnitIdeal_mul_root_dvd_gcd
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool) :
    (secondPatternUnitIdeal p m n pattern).val * (secondSixthRootIdeal p m n).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val := by
  unfold secondPatternUnitIdeal secondSixthRootIdeal
  rw [← primePowerProduct_add]
  apply dvd_trans _ (primePowerProduct_min_dvd_gcd p m n)
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  apply pow_dvd_pow
  change (if m i = n i ∧ ¬6 ∣ m i ∧ pattern i = false then 1 else 0) +
    min (m i) (n i) / 6 ≤ min (m i) (n i)
  have hi := secondSixthRootBudget_exponent (m i) (n i) (hm i) (hn i)
  split_ifs <;> omega

theorem secondPatternUnitIdeal_dvd_gcd
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool) :
    (secondPatternUnitIdeal p m n pattern).val ∣
      gcd (primePowerProduct p m).val (primePowerProduct p n).val :=
  dvd_trans (dvd_mul_right _ _)
    (secondPatternUnitIdeal_mul_root_dvd_gcd p m n hm hn pattern)

private theorem unrestrictedSixth_log_mul (Z : ℝ) (I J : Ideal (𝓞 K))
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealLogLength Z (I * J) = idealLogLength Z I + idealLogLength Z J := by
  have hi : (Ideal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj : (Ideal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [idealLogLength, map_mul, Nat.cast_mul, Real.log_mul hi hj]
  ring

theorem secondPatternUnitIdeal_root_log_slack
    (Z : ℝ) (hZ : 1 < Z) (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool) :
    idealLogLength Z (secondPatternUnitIdeal p m n pattern).val +
        idealLogLength Z (secondSixthRootIdeal p m n).val ≤
      idealLogLength Z (gcd (primePowerProduct p m).val (primePowerProduct p n).val) := by
  rw [← unrestrictedSixth_log_mul Z _ _ (secondPatternUnitIdeal p m n pattern).property.1
    (secondSixthRootIdeal p m n).property.1]
  have hprod : (secondPatternUnitIdeal p m n pattern).val *
      (secondSixthRootIdeal p m n).val ≠ 0 :=
    mul_ne_zero (secondPatternUnitIdeal p m n pattern).property.1
      (secondSixthRootIdeal p m n).property.1
  have hnorm := ideal_norm_le_of_dvd
    (gcd_ne_zero_of_left (primePowerProduct p m).property.1)
    (secondPatternUnitIdeal_mul_root_dvd_gcd p m n hm hn pattern)
  have hpos : 0 < (Ideal.absNorm ((secondPatternUnitIdeal p m n pattern).val *
      (secondSixthRootIdeal p m n).val) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hprod (Ideal.absNorm_eq_zero_iff.mp hz))
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos hnorm) (Real.log_pos hZ).le

namespace ActualSecondCorrelationRows

variable {H : Type*} (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

/-- The original local correlation theorem identifies the pattern
ideal on each live row. It does not assert this complement on zero
correlation rows. -/
theorem secondPatternUnitIdeal_eq_live (pattern : ι → Bool) (h : R.live)
    (hpattern : actualNonunitPattern C R.primes R.leftMultiplicity
      R.rightMultiplicity (R.frequency h.val) = pattern) :
    secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern =
      unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h.val) := by
  rw [← hpattern]
  unfold secondPatternUnitIdeal unitFrequencyRadical
  apply congrArg (primePowerProduct R.primes)
  funext i
  rw [R.live_unitSaving_iff_nonunit_complement C h i]
  by_cases hn : nonunitFrequencySaving C (R.primes i)
      (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) <;>
    simp [actualNonunitPattern, hn]

theorem secondPatternNonunitIdeal_eq (pattern : ι → Bool) (h : H)
    (hpattern : actualNonunitPattern C R.primes R.leftMultiplicity
      R.rightMultiplicity (R.frequency h) = pattern) :
    secondPatternNonunitIdeal R.primes pattern =
      nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h) := by
  rw [← hpattern]
  unfold secondPatternNonunitIdeal nonunitFrequencyRadical
  apply congrArg (primePowerProduct R.primes)
  funext i
  simp only [actualNonunitPattern, decide_eq_true_eq]

end ActualSecondCorrelationRows

namespace OriginalNominalIdeals

/-- The same original second-common ideals and finite frequency
pattern produce the nominal ideal coordinates even for an empty class. -/
def ofSecondPattern
    (first opposite complementary : (Ideal (𝓞 K))⁰)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (pattern : ι → Bool) :
    OriginalNominalIdeals K where
  first := first
  opposite := opposite
  complementary := complementary
  second := ⟨(primePowerProduct p m).val,
    mem_nonZeroDivisors_of_ne_zero (primePowerProduct p m).property.1⟩
  secondOpposite := ⟨(primePowerProduct p n).val,
    mem_nonZeroDivisors_of_ne_zero (primePowerProduct p n).property.1⟩
  unitPart := ⟨(secondPatternUnitIdeal p m n pattern).val,
    mem_nonZeroDivisors_of_ne_zero (secondPatternUnitIdeal p m n pattern).property.1⟩
  nonunitPart := ⟨(secondPatternNonunitIdeal p pattern).val,
    mem_nonZeroDivisors_of_ne_zero (secondPatternNonunitIdeal p pattern).property.1⟩
  unit_dvd_gcd := secondPatternUnitIdeal_dvd_gcd p m n hm hn pattern

end OriginalNominalIdeals

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

/-- Both root slacks follow from primitive prime powers and the
computed original pattern ideal, with no row-nonemptiness hypothesis. -/
theorem sixthDeletion_slack_of_pattern
    (hZ : 1 < Z) (p : ι → ExteriorPrime A) (hp : Function.Injective p)
    (m n : ι → ℕ) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (pattern : ι → Bool)
    (hsecond : G.ideals.second.val = (primePowerProduct p m).val)
    (hopposite : G.ideals.secondOpposite.val = (primePowerProduct p n).val)
    (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal p m n pattern).val) :
    let r₆ := idealLogLength Z (secondSixthRootIdeal p m n).val
    0 ≤ r₆ ∧ G.skeleton.t₂ + r₆ ≤ G.skeleton.g₂ ∧
      G.secondRadical + r₆ ≤ G.halfSecond := by
  dsimp only
  have hroot := secondSixthRootIdeal_logLength_nonneg Z hZ p m n
  have hunitRoot := secondPatternUnitIdeal_root_log_slack Z hZ p m n hm hn pattern
  have hcommon := secondSixthRoot_common_log_slack_mean Z hZ p hp m n hm hn
  simpa only [skeleton, halfSecond, secondRadical, hsecond, hopposite, hunit] using
    And.intro hroot (And.intro hunitRoot hcommon)

end OriginalNominalGeometry

section Capacity

variable {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {G : OriginalNominalGeometry (K := K) a s.base step}
variable {p : ι → ExteriorPrime A} {m n : ι → ℕ}

namespace ActualAllocatedSource.Calibration.OriginalSixthLengthBinding

variable (B : D.OriginalSixthLengthBinding parent a step G
  (idealLogLength s.base (secondSixthRootIdeal p m n).val))

/-- Construct the actual capacity input before normalization or active
rectangle selection. The supplied calibration may have no ordinary rows. -/
def capacityInputOfPattern
    (hp : Function.Injective p) (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (pattern : ι → Bool)
    (hsecond : G.ideals.second.val = (primePowerProduct p m).val)
    (hopposite : G.ideals.secondOpposite.val = (primePowerProduct p n).val)
    (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal p m n pattern).val)
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    D.CapacityInput := by
  have hslack := G.sixthDeletion_slack_of_pattern s.base_gt_one p hp m n hm hn pattern
    hsecond hopposite hunit
  dsimp only at hslack
  exact {
    skeleton := G.skeleton.sixthDeletionSkeleton
      (idealLogLength s.base (secondSixthRootIdeal p m n).val)
    b₂ := G.halfSecond - idealLogLength s.base (secondSixthRootIdeal p m n).val
    p₂ := G.secondRadical
    boundary := G.boundary
    ell := G.tag.poolLength step
    gap := step
    delta := B.scales.error
    mesh := mesh
    supportError := G.supportError
    rawClipError := B.rawScaleError
    widthError := B.scales.error
    leftAnnulus := atoms.leftAnnulus
    rightAnnulus := atoms.rightAnnulus
    leftAnnulus_one := atoms.leftAnnulus_one
    rightAnnulus_one := atoms.rightAnnulus_one
    left_window := atoms.left_window
    right_window := atoms.right_window
    gap_pos := hstep
    kappa_pos := B.kappa_pos
    mesh_nonneg := hmesh
    mesh_bound := B.slots.fitsMesh hfit
    enlargement := G.enlargement_bound hstep.le
    unit_part := hslack.2.1
    actual_width := B.width_bounds.1
    delta_bound := B.scales.error_le_half_step
    principal_part := by linarith [hslack.2.2]
    boundary_nonneg := G.boundary_nonneg
    parent_capacity := B.parent_capacity
    common_part := by
      change G.skeleton.g₂ - (G.skeleton.t₂ +
        idealLogLength s.base (secondSixthRootIdeal p m n).val) ≤ G.skeleton.c₂
      have hc := G.common_length s.base_gt_one
      linarith [hslack.1]
    paid_shift := B.paid_shift
    raw_degree := B.raw_degree
    width_error := B.width_bounds.2
    budget_nonneg := by
      have hw := G.tag.removedLength_nonneg s.base s.base_gt_one
      have he := G.tag.poolLength_nonneg step hstep.le
      change 0 ≤ 6 * (G.tag.removedLength s.base + G.tag.poolLength step) +
        G.supportError + B.rawScaleError + B.scales.error
      exact add_nonneg
        (add_nonneg
          (add_nonneg (mul_nonneg (by norm_num) (add_nonneg hw he))
            G.supportError_nonneg) B.rawScaleError_nonneg) B.scales.error_nonneg
    charge_nonneg := by
      have hbp : 0 ≤ (G.halfSecond -
          idealLogLength s.base (secondSixthRootIdeal p m n).val) -
          G.secondRadical := by linarith [hslack.2.2]
      have hw := G.tag.removedLength_nonneg s.base s.base_gt_one
      have he := G.tag.poolLength_nonneg step hstep.le
      change 0 ≤ ((G.halfSecond - idealLogLength s.base
        (secondSixthRootIdeal p m n).val) - G.secondRadical + G.tag.removedLength s.base +
        G.boundary + G.tag.poolLength step) +
        (G.supportError + B.rawScaleError + B.scales.error) / 6 + D.parameters.κ * mesh
      exact add_nonneg
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg hbp hw) G.boundary_nonneg) he)
          (div_nonneg
            (add_nonneg (add_nonneg G.supportError_nonneg B.rawScaleError_nonneg)
              B.scales.error_nonneg) (by norm_num)))
        (mul_nonneg B.kappa_pos.le hmesh)
    primeBound := atoms.primeBound
    primeBound_nonneg := atoms.primeBound_nonneg
    prime_bound := atoms.prime_bound }

end ActualAllocatedSource.Calibration.OriginalSixthLengthBinding
end Capacity

section Compatibility

variable [IsPrincipalIdealRing A.R]
variable {ω ψ : HeckeCharacter K}
variable {V H Row : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k kLeft kRight : ℕ} {s : ActualAllocatedSource A V H k}
variable {D : s.Calibration (σ := σ) ω ψ}
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}
variable {G : OriginalNominalGeometry (K := K) a s.base step}
variable {R : ActualSecondCorrelationRows A σ Row ι}
variable {C : A.GeneralArithmeticContext σ η hS}

namespace ActualAllocatedSource.Calibration.OriginalSixthLengthBinding

variable (B : D.OriginalSixthLengthBinding parent a step G
  (idealLogLength s.base
    (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))

/-- Once an active ordinary source supplies its own witness, the
already constructed input is exactly the input used by the established
same-child mass theorem.  The witness only changes proof fields. -/
theorem capacityInputOfPattern_eq_actual
    (W : ActualSecondRowMass R C kLeft kRight)
    (hn : ∀ i, 0 < R.rightMultiplicity i) (pattern : ι → Bool) (h : R.rows)
    (hsecond : G.ideals.second.val = W.leftIdeal)
    (hopposite : G.ideals.secondOpposite.val = W.rightIdeal)
    (hpatternUnit : G.ideals.unitPart.val =
      (secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern).val)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    B.capacityInputOfPattern R.primes_injective W.left_positive hn pattern
        hsecond hopposite hpatternUnit hstep mesh hmesh hfit atoms =
      B.capacityInput W hn h hsecond hopposite hunit hstep mesh hmesh hfit atoms := rfl

end ActualAllocatedSource.Calibration.OriginalSixthLengthBinding
end Compatibility

namespace SecondSideNormalization

variable {ω ψ : HeckeCharacter K}
variable [IsPrincipalIdealRing A.R]
variable {H V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}

/-- A direct primitive entrance for each of the original four ordinary
rectangles. The same frame and calibration are retained, even if its
ordinary row set or its complete source is zero. Only the original
pattern, scale windows and individual profile bounds are required. -/
def ofOriginalSixthPattern
    (f : SecondSideFrame (V := V) C R Ray side k)
    (D : f.source.Calibration (σ := σ) ω ψ)
    (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
    (G : OriginalNominalGeometry (K := K) a f.source.base step)
    (B : D.OriginalSixthLengthBinding parent a step G
      (idealLogLength f.source.base
        (secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity).val))
    (hm : ∀ i, 0 < R.leftMultiplicity i) (hn : ∀ i, 0 < R.rightMultiplicity i)
    (pattern : ι → Bool)
    (hsecond : G.ideals.second.val = (primePowerProduct R.primes R.leftMultiplicity).val)
    (hopposite : G.ideals.secondOpposite.val =
      (primePowerProduct R.primes R.rightMultiplicity).val)
    (hunit : G.ideals.unitPart.val =
      (secondPatternUnitIdeal R.primes R.leftMultiplicity R.rightMultiplicity pattern).val)
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
    (heightDomain window : Set ℝ) (seminorms : Finset (ℕ × ℕ))
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin f.source.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i)
    (profiles : ∀ ξ, RawProfileWindow rowDomain heightDomain window seminorms
      (D.clippedData ξ) (amplitude ξ)) :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms where
  calibration := D
  capacity := B.capacityInputOfPattern R.primes_injective hm hn pattern
    hsecond hopposite hunit hstep mesh hmesh hfit atoms
  amplitude := amplitude
  amplitude_pos := hpos
  bounds := bounds
  bounds_nonneg := hbound
  factor := hfactor
  profile := profiles

end SecondSideNormalization

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.secondPatternUnitIdeal_mul_root_dvd_gcd
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.secondPatternUnitIdeal_eq_live
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalIdeals.ofSecondPattern
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.sixthDeletion_slack_of_pattern
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.capacityInputOfPattern
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalSixthLengthBinding.capacityInputOfPattern_eq_actual
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.ofOriginalSixthPattern
