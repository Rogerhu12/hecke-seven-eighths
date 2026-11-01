import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstSaving
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondSaving
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualNominalGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalExponent
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exceptional numerical fields from the actual original geometry

The first saving uses the original retained Gauss window, the actual
tag's prime window and the separately computed enlargement.  The second
saving uses the complete nonzero local correlations on an original live
row.  Its multiplicity-one nonunit radical is computed from the fixed
nonunit ideal and is proved equal to the actual radical on every row of
that class; its positive logarithmic term is never replaced by a lower
dyadic endpoint.

The original first allowance determines the intermediate normalization
exponent.  Consequently its remaining exponent is exactly the moving
length already paid by the original main or error tag.  Exact common
ideal lengths give zero row and width errors.  The final small remainder
is then a consequence of the original parent domain and the separate
support, divisor and volume error windows.

No first-saving, second-saving, final-remainder, energy or mass estimate
is a primitive input.  A live-row witness is required for the second
saving: an empty actual carrier is treated by its zero-source identity,
not by asserting a numerical correlation inequality on an empty class.
-/

noncomputable section
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

/-- Reversing the original first common pair does not change its active
radical, because the two original supports are the same. -/
theorem firstActiveRadical_swap_of_support_eq (D E : Ideal (𝓞 K))
    (h : primeSupport D = primeSupport E) :
    firstActiveRadical E D = firstActiveRadical D E := by
  unfold firstActiveRadical
  rw [← h]
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, ne_comm]
  · intro p hp
    rfl

/-- The actual right first normalizer is the left formula on the
oriented original pair, with its same common support. -/
theorem firstRightAllowance_eq_firstLeftAllowance_swap (Z total : ℝ)
    (D E : Ideal (𝓞 K)) (h : primeSupport D = primeSupport E) :
    firstRightAllowance Z total D E = firstLeftAllowance Z total E D := by
  unfold firstRightAllowance firstLeftAllowance
  rw [firstActiveRadical_swap_of_support_eq D E h]

namespace OriginalNominalTag

theorem movingLength_nonneg (tag : OriginalNominalTag K) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ tag.movingLength Z := by
  cases tag with
  | direct => exact le_rfl
  | main => exact le_rfl
  | error e p =>
    exact mul_nonneg (Nat.cast_nonneg _) (idealLogLength_nonneg Z hZ _ p.ne_bot)

/-- The main tag pays its pool length; an error pays its actual moving
prime norm.  The direct tag pays neither. -/
def exceptionalMovingLength (tag : OriginalNominalTag K) (Z step : ℝ) : ℝ :=
  tag.movingLength Z + tag.poolLength step

@[simp] theorem exceptionalMovingLength_direct (Z step : ℝ) :
    (OriginalNominalTag.direct : OriginalNominalTag K).exceptionalMovingLength Z step = 0 := by
  simp only [exceptionalMovingLength, movingLength, poolLength, add_zero]

@[simp] theorem exceptionalMovingLength_main (Z step : ℝ) :
    (OriginalNominalTag.main : OriginalNominalTag K).exceptionalMovingLength Z step = step / 3 := by
  simp only [exceptionalMovingLength, movingLength, poolLength, zero_add]

theorem exceptionalMovingLength_error (e : AmplifierValuation)
    (p : HeightOneSpectrum (𝓞 K)) (Z step : ℝ) :
    (OriginalNominalTag.error e p).exceptionalMovingLength Z step =
      (amplifierMovingExponent e.multiplicity : ℝ) * idealLogLength Z p.asIdeal := by
  cases e <;> simp [exceptionalMovingLength, movingLength, poolLength,
    AmplifierValuation.multiplicity, AmplifierValuation.movingMultiplicity,
    amplifierMovingExponent]

variable {A : SArithmeticData K}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z step eps : ℝ}

theorem pool_error_prime_upper
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (e : AmplifierValuation) (p : P.primes) :
    ∀ e' p', (OriginalNominalTag.error e p.val.val : OriginalNominalTag K) = .error e' p' →
      (Ideal.absNorm p'.asIdeal : ℝ) ≤ Z ^ (step / 3) := by
  intro e' p' h
  obtain ⟨he, hp⟩ := OriginalNominalTag.error.inj h
  subst e'
  subst p'
  exact P.norm_upper p.val p.property

/-- The actual main index already contains exactly this pool power. -/
theorem exceptionalMovingLength_main_index
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K)) (j : main.Index) :
    (OriginalNominalTag.main : OriginalNominalTag K).exceptionalMovingLength Z step =
      AmplifiedCommonIndex.movingLength P main error (.inl j) := by
  simp only [exceptionalMovingLength_main, AmplifiedCommonIndex.movingLength]

/-- The original error index retains the very same prime and valuation;
the three possible moving powers are one, zero and one. -/
theorem exceptionalMovingLength_error_index
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (main : TwoDivisorCommonBranch (K := K))
    (error : ℕ → ExteriorPrime A → TwoDivisorCommonBranch (K := K))
    (n : ({1, 6, 7} : Finset ℕ)) (p : P.primes) (e : AmplifierValuation)
    (he : e.multiplicity = n.val) (j : (error n.val p.val).Index) :
    (OriginalNominalTag.error e p.val.val).exceptionalMovingLength Z step =
      AmplifiedCommonIndex.movingLength P main error (.inr ⟨n, p, j⟩) := by
  rw [exceptionalMovingLength_error, he]
  rfl

end OriginalNominalTag

namespace ActualSecondRowMass

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- Restrict the fixed original nonunit ideal to the original primes
whose two common multiplicities are one.  There is no row choice. -/
def originalMultiplicityOneIdeal : A.Exterior :=
  primePowerProduct R.primes (fun i =>
    if R.leftMultiplicity i = 1 ∧ R.rightMultiplicity i = 1 then
      (normalizedFactors W.nonunitIdeal.val).count (R.primes i).val.asIdeal
    else 0)

/-- The original nonunit classification determines the exact same
multiplicity-one radical on every row, including before extraction. -/
theorem multiplicityOneRadical_eq (h : H) (hh : h ∈ R.rows) :
    multiplicityOneNonunitRadical C R.primes R.leftMultiplicity R.rightMultiplicity
        (R.frequency h) = W.originalMultiplicityOneIdeal := by
  apply Subtype.ext
  change (primePowerProduct R.primes (fun i =>
      if i ∈ multiplicityOneNonunitPrimes C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h) then 1 else 0)).val =
    (primePowerProduct R.primes (fun i =>
      if R.leftMultiplicity i = 1 ∧ R.rightMultiplicity i = 1 then
        (normalizedFactors W.nonunitIdeal.val).count (R.primes i).val.asIdeal
      else 0)).val
  apply congrArg (fun n : ι → ℕ => (primePowerProduct R.primes n).val)
  funext i
  have hc := primePowerProduct_count R.primes R.primes_injective
    (fun j => if nonunitFrequencySaving C (R.primes j) (R.leftMultiplicity j)
      (R.rightMultiplicity j) (R.frequency h) then 1 else 0) i
  change (normalizedFactors (nonunitFrequencyRadical C R.primes
      R.leftMultiplicity R.rightMultiplicity (R.frequency h)).val).count
        (R.primes i).val.asIdeal = _ at hc
  rw [W.nonunit_ideal h hh] at hc
  rw [hc]
  by_cases hm : R.leftMultiplicity i = 1 <;>
    by_cases hn : R.rightMultiplicity i = 1 <;>
    by_cases hv : nonunitFrequencySaving C (R.primes i) (R.leftMultiplicity i)
      (R.rightMultiplicity i) (R.frequency h) <;>
    simp only [multiplicityOneNonunitPrimes, Finset.mem_filter, Finset.mem_univ,
      hm, hn, hv, and_true, and_false, true_and, false_and, ite_true, ite_false]

def originalMultiplicityOneLength (Z : ℝ) : ℝ :=
  idealLogLength Z W.originalMultiplicityOneIdeal.val

theorem originalMultiplicityOneLength_nonneg (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ W.originalMultiplicityOneLength Z :=
  idealLogLength_nonneg Z hZ _ W.originalMultiplicityOneIdeal.property.1

/-- This is both the radical lower-window field and the exact identity
needed by the positive v-term of the second saving. -/
theorem rpow_originalMultiplicityOneLength (Z : ℝ) (hZ : 1 < Z)
    (h : H) (hh : h ∈ R.rows) :
    Z ^ W.originalMultiplicityOneLength Z = A.exteriorNorm
      (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h)) := by
  rw [W.multiplicityOneRadical_eq h hh]
  exact rpow_idealLogLength Z hZ W.originalMultiplicityOneIdeal.val
    W.originalMultiplicityOneIdeal.property.1

/-- A live original row proves the second saving for the fixed class.
The second positive-multiplicity condition belongs to the original
common-support dictionary. -/
theorem original_second_saving (Z : ℝ) (hZ : 1 < Z)
    (hright : ∀ i, 0 < R.rightMultiplicity i) (h : R.live) :
    let b₂ := (idealLogLength Z W.leftIdeal + idealLogLength Z W.rightIdeal) / 2
    2 * b₂ / 3 ≤ 2 * b₂ - 5 * idealLogLength Z (gcd W.leftIdeal W.rightIdeal) / 6 -
      idealLogLength Z (commonRadical W.leftIdeal W.rightIdeal) +
      idealLogLength Z W.unitIdeal.val + idealLogLength Z W.nonunitIdeal.val / 6 +
      2 * W.originalMultiplicityOneLength Z / 6 := by
  have hh : h.val ∈ R.rows := (Finset.mem_filter.mp h.property).1
  have hs := R.live_second_saving C Z hZ W.left_positive hright h
  dsimp only at hs ⊢
  rw [W.unit_ideal h.val hh, W.nonunit_ideal h.val hh,
    W.multiplicityOneRadical_eq h.val hh] at hs
  exact hs

end ActualSecondRowMass

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

private theorem allowance_positive_part (c d R : ℝ) :
    max (3 * c - 5 * d - R) 0 / 6 ≤ firstAllowance c d R := by
  have hb : 0 ≤ firstAllowance c d R := firstAllowance_nonneg c d R
  have hm := le_max_left ((3 * c - 5 * d - R) / 6) 0
  change (3 * c - 5 * d - R) / 6 ≤ firstAllowance c d R at hm
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
  exact max_le (by linarith) (by linarith)

/-- The active-radical inequality in the first ledger follows from the
original complementary support scale being at least one. -/
theorem original_support_exponent_nonneg (hZ : 1 < Z)
    (hsupport : 1 ≤ Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ)) :
    0 ≤ a.q + G.skeleton.E := by
  have he : Z ^ (a.q + G.skeleton.E) =
      Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ) := by
    change Z ^ (a.q + idealLogLength Z G.ideals.complementary.val) = _
    rw [Real.rpow_add (zero_lt_one.trans hZ), rpow_idealLogLength Z hZ _
      (nonZeroDivisors.coe_ne_zero G.ideals.complementary)]
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  simpa only [Real.rpow_zero, he] using hsupport

/-- The upper window of the retained original Gauss class preserves
the opposite common length with precisely the original support error. -/
theorem original_opposite_length (hZ : 1 < Z) :
    G.skeleton.d - G.supportError ≤ G.skeleton.shiftedCommon := by
  have hlog := Real.log_le_log G.retainedScale_pos G.retained_upper
  rw [Real.log_rpow (zero_lt_one.trans hZ)] at hlog
  have hk : G.retainedLength ≤ G.ideals.firstFrequency a Z + G.supportError :=
    (div_le_iff₀ (Real.log_pos hZ)).mpr (by nlinarith)
  rw [G.shiftedCommon_eq]
  change idealLogLength Z G.ideals.opposite.val - G.supportError ≤
    idealLogLength Z G.ideals.opposite.val + G.ideals.firstFrequency a Z - G.retainedLength
  linarith

theorem original_enlargement_upper (hstep : 0 ≤ step) :
    G.skeleton.g ≤ max (G.skeleton.shiftedCommon - G.skeleton.c -
      2 * G.skeleton.w + G.skeleton.wo) 0 + 2 * step := by
  have hp : G.tag.padding step ≤ 2 * step := by
    cases G.tag <;> simp only [OriginalNominalTag.padding] <;> linarith
  exact add_le_add le_rfl hp

theorem original_removed_length_upper (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hprime : ∀ e p, G.tag = .error e p →
      (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3)) :
    G.skeleton.w ≤ 7 * step / 3 := by
  cases ht : G.tag with
  | direct =>
    simp only [skeleton, ht, OriginalNominalTag.removedLength]
    linarith
  | main =>
    simp only [skeleton, ht, OriginalNominalTag.removedLength]
    linarith
  | error e p =>
    have hp : idealLogLength Z p.asIdeal ≤ step / 3 := by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      simpa only [rpow_idealLogLength Z hZ p.asIdeal p.ne_bot] using hprime e p ht
    change G.tag.removedLength Z ≤ _
    rw [ht]
    exact amplifier_error_length_le e (idealLogLength Z p.asIdeal) step
      (idealLogLength_nonneg Z hZ p.asIdeal p.ne_bot) hp

/-- The actual enlargement is a real scale, not the log of a newly
chosen ideal. Its literal max formula supplies the same scalar ledger
used by ActualFirstSaving, for every original main/direct/error tag. -/
theorem original_first_saving (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hsupport : 1 ≤ Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ))
    (hprime : ∀ e p, G.tag = .error e p →
      (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3)) :
    2 * (G.skeleton.c + G.skeleton.w) / 3 - 3 * step - 5 * G.supportError / 6 ≤
      firstSaving G.skeleton.c G.skeleton.shiftedCommon G.skeleton.w
        (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.wo G.boundary
        G.skeleton.g (G.tag.poolLength step) := by
  have hc : 0 ≤ G.skeleton.c :=
    idealLogLength_nonneg Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.first)
  have hR : 0 ≤ G.skeleton.R :=
    idealLogLength_nonneg Z hZ _ (firstActiveRadical_ne_zero _ _)
  have hs := G.original_support_exponent_nonneg hZ hsupport
  have hactive : G.skeleton.R ≤ G.skeleton.q + G.skeleton.R + G.skeleton.E := by
    change G.skeleton.R ≤ a.q + G.skeleton.R + G.skeleton.E
    linarith
  exact firstSaving_lower G.skeleton.c G.skeleton.d G.skeleton.shiftedCommon
    G.skeleton.w (G.skeleton.q + G.skeleton.R + G.skeleton.E) G.skeleton.R
    G.skeleton.wo G.boundary G.skeleton.g (G.tag.poolLength step) step G.supportError
    hc (G.tag.removedLength_nonneg Z hZ) (hR.trans hactive)
    (G.tag.movingLength_nonneg Z hZ) G.boundary_nonneg hstep G.supportError_nonneg
    hactive (allowance_positive_part _ _ _) (G.original_opposite_length hZ)
    (G.original_enlargement_upper hstep) (G.tag.poolLength_nonneg step hstep)
    (G.original_removed_length_upper hZ hstep hprime)

end OriginalNominalGeometry

namespace OriginalNominalGeometry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (W : ActualSecondRowMass R C kLeft kRight)

/-- The numerical label is computed from the original geometry and
the actual fixed row class. The intermediate exponent is the exact
first allowance. No descendant or terminal estimate enters it. -/
def exceptionalNumbers (vStar r₁ r₂ slotError firstProfile : ℝ) : ExceptionalOriginalNumbers where
  Aexp := G.skeleton.A
  c := G.skeleton.c
  d := G.skeleton.d
  R₀ := G.skeleton.R
  E₀ := G.skeleton.E
  K₀ := G.skeleton.Krow
  w := G.skeleton.w
  wo := G.skeleton.wo
  Bcommon := G.boundary
  g := G.skeleton.g
  ell := G.tag.poolLength step
  b₂ := (idealLogLength Z W.leftIdeal + idealLogLength Z W.rightIdeal) / 2
  p₂ := idealLogLength Z (commonRadical W.leftIdeal W.rightIdeal)
  g₂ := idealLogLength Z (gcd W.leftIdeal W.rightIdeal)
  t₂ := idealLogLength Z W.unitIdeal.val
  V₀ := idealLogLength Z W.nonunitIdeal.val
  v := W.originalMultiplicityOneLength Z
  vStar := vStar
  r₁ := r₁
  r₂ := r₂
  slotError := slotError
  stepσ := step
  δ := G.supportError
  parentWidth := G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E) -
    G.skeleton.c + G.boundary
  remaining := G.tag.exceptionalMovingLength Z step
  rowError := 0
  widthError := 0
  firstTotal := G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E)
  firstProfile := firstProfile

variable (vStar r₁ r₂ slotError firstProfile : ℝ)

/-- The same first allowance used by the original weighted Cauchy step.
On the original right branch its first common ideals are interchanged. -/
theorem exceptionalNumbers_normalizer_eq :
    Z ^ (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).parentWidth =
      firstLeftAllowance Z
        (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).firstTotal
        G.ideals.first.val G.ideals.opposite.val := rfl

/-- When the geometry was formed from this actual row mass, its second
coordinates agree literally with the exceptional coordinates. -/
theorem exceptionalNumbers_second_coordinates
    (hleft : G.ideals.second.val = W.leftIdeal)
    (hright : G.ideals.secondOpposite.val = W.rightIdeal)
    (hunit : G.ideals.unitPart.val = W.unitIdeal.val)
    (hnonunit : G.ideals.nonunitPart.val = W.nonunitIdeal.val) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.b₂ = G.halfSecond ∧ n.p₂ = G.secondRadical ∧
      n.g₂ = G.skeleton.g₂ ∧ n.t₂ = G.skeleton.t₂ ∧ n.V₀ = G.skeleton.V := by
  dsimp only [exceptionalNumbers, halfSecond, secondRadical, skeleton]
  rw [hleft, hright, hunit, hnonunit]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Directly fills ExceptionalLeafRawData.first_saving. The source
support scale and original error-prime window are the only extra
windows beyond the already computed geometry. -/
theorem exceptionalNumbers_first_saving (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hsupport : 1 ≤ Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ))
    (hprime : ∀ e p, G.tag = .error e p →
      (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3)) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    2 * (n.c + n.w) / 3 - 3 * n.stepσ - 5 * n.δ / 6 ≤
      firstSaving n.c (n.d + (2 * n.Aexp - n.c - n.d + n.R₀ + n.E₀ - a.m) - n.K₀)
        n.w (a.q + n.R₀ + n.E₀) n.wo n.Bcommon n.g n.ell := by
  exact G.original_first_saving hZ hstep hsupport hprime

/-- Directly fills ExceptionalLeafRawData.second_saving. The positive
v-term is the exact original multiplicity-one radical length. -/
theorem exceptionalNumbers_second_saving (hZ : 1 < Z)
    (hright : ∀ i, 0 < R.rightMultiplicity i) (h : R.live) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    2 * n.b₂ / 3 ≤ 2 * n.b₂ - 5 * n.g₂ / 6 - n.p₂ + n.t₂ + n.V₀ / 6 +
      (2 * n.v) / 6 :=
  W.original_second_saving Z hZ hright h

theorem exceptionalNumbers_v_nonneg (hZ : 1 < Z) :
    0 ≤ (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).v :=
  W.originalMultiplicityOneLength_nonneg Z hZ

theorem exceptionalNumbers_radical_window (hZ : 1 < Z) (h : H) (hh : h ∈ R.rows) :
    Z ^ (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).v ≤
      A.exteriorNorm (multiplicityOneNonunitRadical C R.primes R.leftMultiplicity
        R.rightMultiplicity (R.frequency h)) :=
  (W.rpow_originalMultiplicityOneLength Z hZ h hh).le

/-- Exact lengths need no upper-gcd or lower-unit dyadic error. -/
theorem exceptionalNumbers_gcd_window (hZ : 1 < Z) :
    (Ideal.absNorm (gcd W.leftIdeal W.rightIdeal) : ℝ) ≤
      Z ^ (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).g₂ :=
  (rpow_idealLogLength Z hZ (gcd W.leftIdeal W.rightIdeal)
    (gcd_ne_zero_of_left (primePowerProduct R.primes R.leftMultiplicity).property.1)).symm.le

theorem exceptionalNumbers_unit_window (hZ : 1 < Z) :
    Z ^ (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).t₂ ≤
      A.exteriorNorm W.unitIdeal :=
  (rpow_idealLogLength Z hZ W.unitIdeal.val W.unitIdeal.property.1).le

theorem exceptionalNumbers_dyad_window :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.g₂ - n.t₂ ≤ idealLogLength Z (gcd W.leftIdeal W.rightIdeal) -
      idealLogLength Z W.unitIdeal.val + n.rowError := by
  dsimp only [exceptionalNumbers]
  simp only [add_zero, le_refl]

/-- The original first allowance cancels exactly. Only the moving
power already present in the actual tag remains. -/
theorem exceptionalNumbers_remaining_window :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    (n.Aexp - n.c - n.w) + (a.q + n.R₀ + n.E₀) + n.w + n.Bcommon +
      n.wo + n.ell + n.rowError - n.parentWidth ≤ n.remaining := by
  dsimp only [exceptionalNumbers, OriginalNominalTag.exceptionalMovingLength, skeleton]
  linarith

/-- Literal second norm coordinates give zero width error on this
very row class. No bound on a chosen descendant occurs. -/
theorem exceptionalNumbers_width_window :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    ((2 * (n.Aexp - n.c - n.w) - n.K₀ - n.g - n.g₂ - n.V₀) +
      (a.q + n.R₀ + n.E₀ + n.wo + n.t₂ + n.V₀) +
      (n.b₂ - n.p₂ + n.w + n.Bcommon + n.ell)) -
      (secondCommonChildWidth Z (n.Aexp - n.c - n.w) (a.q + n.R₀ + n.E₀)
        n.wo n.K₀ n.g W.leftIdeal W.rightIdeal W.unitIdeal.val W.nonunitIdeal.val +
      secondCommonChildAllowance Z n.w n.Bcommon n.ell W.leftIdeal W.rightIdeal) ≤
      n.widthError := by
  dsimp only [exceptionalNumbers, secondCommonChildWidth, secondCommonChildAllowance]
  apply le_of_eq
  ring

/-- Directly fills ExceptionalLeafRawData.final_remainder for the
fixed loss padding+3*step+loss/2. The subsequent arithmetic sum uses
the reserved half, as in OriginalExceptionalExponent. -/
theorem exceptionalNumbers_final_remainder
    {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hpadding : 0 ≤ padding) (loss volumeLoss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16)
    (hvolume : volumeLoss ≤ loss / 16) (hslot : slotError ≤ loss / 16) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.remaining + n.widthError +
      (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ +
        5 * n.δ / 6 + volumeLoss + n.slotError) ≤
      (padding + 3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  apply ExceptionalOriginalNumbers.remainder_from_original_parent
    (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile)
    domain rfl hpadding step loss volumeLoss (G.tag.exceptionalMovingLength Z step) hloss
  · change G.tag.exceptionalMovingLength Z step ≤
      G.tag.exceptionalMovingLength Z step + loss / 16
    linarith
  · change 0 ≤ loss / 16
    linarith
  · exact le_rfl
  · exact hsupport
  · exact hvolume
  · exact hslot

/-- Read the intermediate exponent from the already chosen original
normalizer, retaining its actual first total. The discrepancy from the
geometric total is kept in remaining until its raw identity is proved. -/
def exceptionalNumbersAtNormalization (normalization total : ℝ) : ExceptionalOriginalNumbers :=
  { G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile with
    parentWidth := Real.log normalization / Real.log Z
    firstTotal := total
    remaining :=
      (G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E) - total) +
        G.tag.exceptionalMovingLength Z step }

/-- This denominator is the original normalizer itself. It can rewrite
the literal denominator in parentLeaf_weight_original_relative before
any exceptional estimate is applied. -/
theorem exceptionalNumbersAtNormalization_normalizer
    (normalization total : ℝ) (hZ : 1 < Z) (hN : 0 < normalization) :
    Z ^ (G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total).parentWidth = normalization :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hN

/-- The exact original first-allowance recipe, rather than a freely
selected exceptional exponent, proves the scalar cancellation. -/
theorem exceptionalNumbersAtNormalization_remaining_window
    (normalization total : ℝ) (hZ : 1 < Z)
    (hN : normalization = firstLeftAllowance Z total G.ideals.first.val G.ideals.opposite.val) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    (n.Aexp - n.c - n.w) + (a.q + n.R₀ + n.E₀) + n.w + n.Bcommon +
      n.wo + n.ell + n.rowError - n.parentWidth ≤ n.remaining := by
  have hp : Real.log normalization / Real.log Z =
      total - G.skeleton.c + G.boundary := by
    rw [hN]
    change Real.log (Z ^ (total - G.skeleton.c + G.boundary)) / Real.log Z = _
    rw [Real.log_rpow (zero_lt_one.trans hZ)]
    exact mul_div_cancel_right₀ _ (Real.log_pos hZ).ne'
  dsimp only [exceptionalNumbersAtNormalization, exceptionalNumbers]
  rw [hp]
  dsimp only [OriginalNominalTag.exceptionalMovingLength, skeleton]
  linarith

/-- The original total-length identity identifies all fields with the
computed geometric label. Both the actual normalizer and actual total
are supplied by the existing first source and are preserved here. -/
theorem exceptionalNumbersAtNormalization_eq
    (normalization total : ℝ) (hZ : 1 < Z)
    (hN : normalization = firstLeftAllowance Z total G.ideals.first.val G.ideals.opposite.val)
    (htotal : total = G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E)) :
    G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile normalization total =
      G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile := by
  have hp : Real.log normalization / Real.log Z =
      (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).parentWidth := by
    rw [hN, htotal]
    rw [← G.exceptionalNumbers_normalizer_eq W vStar r₁ r₂ slotError firstProfile]
    rw [Real.log_rpow (zero_lt_one.trans hZ)]
    exact mul_div_cancel_right₀ _ (Real.log_pos hZ).ne'
  simp only [exceptionalNumbersAtNormalization, htotal, hp, sub_self, zero_add]

theorem exceptionalNumbersAtNormalization_first_saving
    (normalization total : ℝ) (hZ : 1 < Z) (hstep : 0 ≤ step)
    (hsupport : 1 ≤ Z ^ a.q * (Ideal.absNorm G.ideals.complementary.val : ℝ))
    (hprime : ∀ e p, G.tag = .error e p →
      (Ideal.absNorm p.asIdeal : ℝ) ≤ Z ^ (step / 3)) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    2 * (n.c + n.w) / 3 - 3 * n.stepσ - 5 * n.δ / 6 ≤
      firstSaving n.c (n.d + (2 * n.Aexp - n.c - n.d + n.R₀ + n.E₀ - a.m) - n.K₀)
        n.w (a.q + n.R₀ + n.E₀) n.wo n.Bcommon n.g n.ell :=
  G.exceptionalNumbers_first_saving W vStar r₁ r₂ slotError firstProfile
    hZ hstep hsupport hprime

theorem exceptionalNumbersAtNormalization_second_saving
    (normalization total : ℝ) (hZ : 1 < Z)
    (hright : ∀ i, 0 < R.rightMultiplicity i) (h : R.live) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    2 * n.b₂ / 3 ≤ 2 * n.b₂ - 5 * n.g₂ / 6 - n.p₂ + n.t₂ + n.V₀ / 6 +
      (2 * n.v) / 6 :=
  G.exceptionalNumbers_second_saving W vStar r₁ r₂ slotError firstProfile hZ hright h

/-- The final field for the already chosen original normalizer. The
raw normalization and total identities are the same ones used in the
literal outer weight; there is no final-remainder premise. -/
theorem exceptionalNumbersAtNormalization_final_remainder
    (normalization total : ℝ) (hZ : 1 < Z)
    (hN : normalization = firstLeftAllowance Z total G.ideals.first.val G.ideals.opposite.val)
    (htotal : total = G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
    {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (hpadding : 0 ≤ padding) (loss volumeLoss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16)
    (hvolume : volumeLoss ≤ loss / 16) (hslot : slotError ≤ loss / 16) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    n.remaining + n.widthError +
      (max (n.Aexp - (a.m + a.q)) 0 + 3 * n.stepσ +
        5 * n.δ / 6 + volumeLoss + n.slotError) ≤
      (padding + 3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  rw [G.exceptionalNumbersAtNormalization_eq W vStar r₁ r₂ slotError firstProfile
    normalization total hZ hN htotal]
  exact G.exceptionalNumbers_final_remainder W vStar r₁ r₂ slotError firstProfile
    domain hpadding loss volumeLoss hloss hsupport hvolume hslot

end OriginalNominalGeometry

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.multiplicityOneRadical_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.original_second_saving
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.original_first_saving
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_first_saving
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_second_saving
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_width_window
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_final_remainder
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbersAtNormalization_remaining_window
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbersAtNormalization_final_remainder
