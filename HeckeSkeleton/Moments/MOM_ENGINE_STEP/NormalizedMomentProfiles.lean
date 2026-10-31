import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileSeminormNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput
import HeckeGeneral.Analysis.TInputSeparatedProfiles
import Mathlib.Algebra.BigOperators.Fin

/-!
# Actual child profiles divided by one positive radius

This is the producer's concrete normalized child.  Its radius is constant
across all original rows, the profile variable and the two rectangles.
The same arithmetic data, finite supports, rows and slot lengths are
retained.  All polynomial identities below follow from their literal
finite sums, including the complete centered subtraction.
-/

noncomputable section
open scoped Classical BigOperators ContDiff

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def normalizedIdealTest (W : IdealTest K) (B : ℝ) (hB : 0 < B) : IdealTest K where
  profile u t y := ((B⁻¹ : ℝ) : ℂ) * W.profile u t y
  support := W.support
  support_spec u t D I := by
    rw [W.support_spec]
    exact ⟨mul_ne_zero (by exact_mod_cast (inv_pos.mpr hB).ne'), right_ne_zero_of_mul⟩

def normalizedPrimeWindow (W : PrimeWindow K) (B : ℝ) (hB : 0 < B) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile t y := ((B⁻¹ : ℝ) : ℂ) * W.profile t y
  support := W.support
  support_spec t P p := by
    rw [W.support_spec]
    exact ⟨mul_ne_zero (by exact_mod_cast (inv_pos.mpr hB).ne'), right_ne_zero_of_mul⟩

def normalizedSlotGeometry (g : SlotGeometry K) (B : ℝ) (hB : 0 < B) : SlotGeometry K where
  slotCount := g.slotCount
  slots i := normalizedPrimeWindow (g.slots i) B hB

def normalizedMomentProfiles (d : MomentData K ω ψ) (B : ℝ) (hB : 0 < B) :
    MomentData K ω ψ :=
  { d with
    inverseTest := normalizedIdealTest d.inverseTest B hB
    plainTest₁ := normalizedIdealTest d.plainTest₁ B hB
    plainTest₂ := normalizedIdealTest d.plainTest₂ B hB
    geometry := normalizedSlotGeometry d.geometry B hB }

theorem normalizedMomentProfiles_invariants (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) :
    (normalizedMomentProfiles d B hB).rows = d.rows ∧
    (normalizedMomentProfiles d B hB).allowedRow = d.allowedRow ∧
    (normalizedMomentProfiles d B hB).commonMask = d.commonMask ∧
    (normalizedMomentProfiles d B hB).rowCharacter = d.rowCharacter ∧
    (normalizedMomentProfiles d B hB).theta = d.theta ∧
    (normalizedMomentProfiles d B hB).inverseBackground = d.inverseBackground ∧
    (normalizedMomentProfiles d B hB).plainBackground = d.plainBackground ∧
    (normalizedMomentProfiles d B hB).slotCoefficient = d.slotCoefficient ∧
    (normalizedMomentProfiles d B hB).geometry.slotCount = d.geometry.slotCount ∧
    (∀ i, ((normalizedMomentProfiles d B hB).geometry.slots i).length =
      (d.geometry.slots i).length) ∧
    (normalizedMomentProfiles d B hB).geometry.totalLength = d.geometry.totalLength ∧
    (∀ mesh, (normalizedMomentProfiles d B hB).geometry.fitsMesh mesh ↔
      d.geometry.fitsMesh mesh) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => Iff.rfl⟩

@[simp] theorem pairedRows_normalizedMomentProfiles (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (a : RealParameters) (Z : ℝ) :
    pairedRows (normalizedMomentProfiles d B hB) a Z = pairedRows d a Z := rfl

private theorem normalized_finite_sum {ι : Type*} (s : Finset ι)
    (p c : ℂ) (f g h : ι → ℂ) :
    p * (∑ i ∈ s, f i * (c * g i) * h i) =
      c * (p * ∑ i ∈ s, f i * g i * h i) := by
  calc
    _ = p * (c * ∑ i ∈ s, f i * g i * h i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by ring

theorem inversePolynomial_normalizedMomentProfiles (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (normalizedMomentProfiles d B hB) u D t =
      ((B⁻¹ : ℝ) : ℂ) * inversePolynomial d u D t := by
  exact normalized_finite_sum (d.inverseTest.support u t D)
    (Real.sqrt D : ℂ)⁻¹ ((B⁻¹ : ℝ) : ℂ)
    (fun I => (UniqueFactorizationMonoid.moebius I.val : ℂ) *
      heckeIdealCoefficient K d.inverseBackground I *
      heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction)
    (fun I => d.inverseTest.profile u t (idealNorm K I / D))
    (fun I => maskValue d u I.val)

theorem plainPolynomial_normalizedMomentProfiles (d : MomentData K ω ψ)
    (W : IdealTest K) (B : ℝ) (hB : 0 < B) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (normalizedMomentProfiles d B hB) (normalizedIdealTest W B hB) u N t =
      ((B⁻¹ : ℝ) : ℂ) * plainPolynomial d W u N t := by
  exact normalized_finite_sum (W.support u t N) (Real.sqrt N : ℂ)⁻¹ ((B⁻¹ : ℝ) : ℂ)
    (fun I => heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I)
    (fun I => W.profile u t (idealNorm K I / N)) (fun I => maskValue d u I.val)

theorem primePolynomial_normalizedMomentProfiles (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (normalizedMomentProfiles d B hB) i u Z t =
      ((B⁻¹ : ℝ) : ℂ) * primePolynomial d i u Z t := by
  exact normalized_finite_sum
    ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
    (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ ((B⁻¹ : ℝ) : ℂ)
    (fun p => primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p)
    (fun p => (d.geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length))
    (fun p => maskValue d u p.asIdeal)

theorem slotProduct_normalizedMomentProfiles (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct (normalizedMomentProfiles d B hB) u Z t =
      ((B⁻¹ : ℝ) : ℂ) ^ d.geometry.slotCount * slotProduct d u Z t := by
  change (∏ i : Fin d.geometry.slotCount,
    primePolynomial (normalizedMomentProfiles d B hB) i u Z t) = _
  simp only [primePolynomial_normalizedMomentProfiles, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] <;> rfl

/-- The whole centered difference has one exact amplitude factor. -/
theorem pairedStagePolynomial_normalizedMomentProfiles (centered : Bool)
    (d : MomentData K ω ψ) (B : ℝ) (hB : 0 < B)
    (u : NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ Z t : ℝ) :
    pairedStagePolynomial centered (normalizedMomentProfiles d B hB)
      u X₁ X₂ Y₁ Y₂ Z t =
      ((B⁻¹ : ℝ) : ℂ) ^ (d.geometry.slotCount + 2) *
        pairedStagePolynomial centered d u X₁ X₂ Y₁ Y₂ Z t := by
  have h₁ (N : ℝ) :
      plainPolynomial (normalizedMomentProfiles d B hB)
        (normalizedMomentProfiles d B hB).plainTest₁ u N t =
          ((B⁻¹ : ℝ) : ℂ) * plainPolynomial d d.plainTest₁ u N t :=
    plainPolynomial_normalizedMomentProfiles d d.plainTest₁ B hB u N t
  have h₂ (N : ℝ) :
      plainPolynomial (normalizedMomentProfiles d B hB)
        (normalizedMomentProfiles d B hB).plainTest₂ u N t =
          ((B⁻¹ : ℝ) : ℂ) * plainPolynomial d d.plainTest₂ u N t :=
    plainPolynomial_normalizedMomentProfiles d d.plainTest₂ B hB u N t
  simp only [pairedStagePolynomial, h₁, h₂, slotProduct_normalizedMomentProfiles, pow_add]
  split_ifs <;> ring

theorem pairedStageEnergy_normalizedMomentProfiles (centered : Bool)
    (d : MomentData K ω ψ) (a : RealParameters) (B : ℝ) (hB : 0 < B)
    (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered (normalizedMomentProfiles d B hB) a Z t Y₁ Y₂ =
      (B⁻¹) ^ ((d.geometry.slotCount + 2) * 2) *
        pairedStageEnergy centered d a Z t Y₁ Y₂ := by
  unfold pairedStageEnergy
  rw [pairedRows_normalizedMomentProfiles, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [pairedStagePolynomial_normalizedMomentProfiles, norm_mul, norm_pow,
    Complex.norm_of_nonneg (inv_nonneg.mpr hB.le), mul_pow, ← pow_mul]

theorem pairedEnergy_normalizedMomentProfiles (d : MomentData K ω ψ)
    (a : RealParameters) (B : ℝ) (hB : 0 < B) (Z t : ℝ) :
    pairedEnergy (normalizedMomentProfiles d B hB) a Z t =
      (B⁻¹) ^ ((d.geometry.slotCount + 2) * 2) * pairedEnergy d a Z t := by
  have h := pairedStageEnergy_normalizedMomentProfiles false d a B hB Z t 1 1
  simpa only [pairedStageEnergy_uncentered] using h

theorem normalizedPairedEnergy_profiles (d : MomentData K ω ψ)
    (a : RealParameters) (B : ℝ) (hB : 0 < B) (Z t : ℝ) :
    normalizedPairedEnergy (normalizedMomentProfiles d B hB) a Z t =
      (B⁻¹) ^ ((d.geometry.slotCount + 2) * 2) * normalizedPairedEnergy d a Z t := by
  unfold normalizedPairedEnergy
  rw [pairedEnergy_normalizedMomentProfiles, mul_div_assoc]

/-- Exact homogeneity, with the extracted factor on the original side. -/
theorem pairedEnergy_profile_factor (d : MomentData K ω ψ)
    (a : RealParameters) (B : ℝ) (hB : 0 < B) (Z t : ℝ) :
    pairedEnergy d a Z t = B ^ ((d.geometry.slotCount + 2) * 2) *
      pairedEnergy (normalizedMomentProfiles d B hB) a Z t := by
  rw [pairedEnergy_normalizedMomentProfiles, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hB.ne'), one_mul]

theorem normalizedPairedEnergy_profile_factor (d : MomentData K ω ψ)
    (a : RealParameters) (B : ℝ) (hB : 0 < B) (Z t : ℝ) :
    normalizedPairedEnergy d a Z t = B ^ ((d.geometry.slotCount + 2) * 2) *
      normalizedPairedEnergy (normalizedMomentProfiles d B hB) a Z t := by
  rw [normalizedPairedEnergy_profiles, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hB.ne'), one_mul]

theorem sqrt_normalizedPairedEnergy_profile_factor (d : MomentData K ω ψ)
    (a : RealParameters) (B : ℝ) (hB : 0 < B) (Z t : ℝ) :
    Real.sqrt (normalizedPairedEnergy d a Z t) = B ^ (d.geometry.slotCount + 2) *
      Real.sqrt (normalizedPairedEnergy (normalizedMomentProfiles d B hB) a Z t) := by
  conv_lhs => rw [normalizedPairedEnergy_profile_factor d a B hB Z t]
  rw [pow_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hB.le _)]

theorem normalizedIdealTest_profile_support (W : IdealTest K) (B : ℝ) (hB : 0 < B)
    (u : NonzeroIdeal K) (t : ℝ) :
    Function.support ((normalizedIdealTest W B hB).profile u t) =
      Function.support (W.profile u t) := by
  ext y
  change ((B⁻¹ : ℝ) : ℂ) * W.profile u t y ≠ 0 ↔ W.profile u t y ≠ 0
  exact ⟨right_ne_zero_of_mul, mul_ne_zero (by exact_mod_cast (inv_pos.mpr hB).ne')⟩

theorem normalizedPrimeWindow_profile_support (W : PrimeWindow K)
    (B : ℝ) (hB : 0 < B) (t : ℝ) :
    Function.support ((normalizedPrimeWindow W B hB).profile t) =
      Function.support (W.profile t) := by
  ext y
  change ((B⁻¹ : ℝ) : ℂ) * W.profile t y ≠ 0 ↔ W.profile t y ≠ 0
  exact ⟨right_ne_zero_of_mul, mul_ne_zero (by exact_mod_cast (inv_pos.mpr hB).ne')⟩

theorem normalizedIdealTest_smooth (W : IdealTest K) (B : ℝ) (hB : 0 < B)
    (u : NonzeroIdeal K) (t : ℝ) (h : ContDiff ℝ ∞ (W.profile u t)) :
    ContDiff ℝ ∞ ((normalizedIdealTest W B hB).profile u t) :=
  contDiff_const.mul h

theorem normalizedPrimeWindow_smooth (W : PrimeWindow K) (B : ℝ) (hB : 0 < B)
    (t : ℝ) (h : ContDiff ℝ ∞ (W.profile t)) :
    ContDiff ℝ ∞ ((normalizedPrimeWindow W B hB).profile t) :=
  contDiff_const.mul h

/-- Finite orders are chosen before the Fourier profile is normalized.
The same radius controls all rows and includes every actual prime slot. -/
def MomentProfileUnitBall (d : MomentData K ω ψ) (t : ℝ)
    (orders : Finset (ℕ × ℝ)) : Prop :=
  (∀ q ∈ orders, ∀ W ∈ [d.inverseTest, d.plainTest₁, d.plainTest₂], ∀ u,
    testSeminorm (W.profile u t) q.1 q.2 ≤ 1) ∧
  (∀ q ∈ orders, ∀ i,
    testSeminorm ((d.geometry.slots i).profile t) q.1 q.2 ≤ 1)

theorem normalizedMomentProfiles_unit_ball (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (t : ℝ) (orders : Finset (ℕ × ℝ))
    (hideal : ∀ q ∈ orders, ∀ W ∈ [d.inverseTest, d.plainTest₁, d.plainTest₂], ∀ u,
      testSeminorm (W.profile u t) q.1 q.2 ≤ B)
    (hprime : ∀ q ∈ orders, ∀ i,
      testSeminorm ((d.geometry.slots i).profile t) q.1 q.2 ≤ B) :
    MomentProfileUnitBall (normalizedMomentProfiles d B hB) t orders := by
  constructor
  · intro q hq W hW u
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact testSeminorm_normalized_le_one _ B hB q.1 q.2
        (hideal q hq d.inverseTest (by simp) u)
    · exact testSeminorm_normalized_le_one _ B hB q.1 q.2
        (hideal q hq d.plainTest₁ (by simp) u)
    · exact testSeminorm_normalized_le_one _ B hB q.1 q.2
        (hideal q hq d.plainTest₂ (by simp) u)
  · intro q hq i
    exact testSeminorm_normalized_le_one _ B hB q.1 q.2 (hprime q hq i)

/-- Measurability is required only for the radius and the actual numeric
energy.  No measurable space on `MomentData` is imposed. -/
theorem normalized_profile_family_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (D : X → MomentData K ω ψ) (n : ℕ)
    (hcount : ∀ x, (D x).geometry.slotCount = n)
    (B : X → ℝ) (hB : ∀ x, 0 < B x) (hB₁ : ∀ x, 1 ≤ B x)
    (hmeas : Measurable B) (a : RealParameters) (Z : ℝ) (t : X → ℝ)
    (hi : Integrable (fun x => normalizedPairedEnergy (D x) a Z (t x)) μ) :
    Integrable (fun x => normalizedPairedEnergy
      (normalizedMomentProfiles (D x) (B x) (hB x)) a Z (t x)) μ := by
  have heq :
      (fun x => normalizedPairedEnergy (normalizedMomentProfiles (D x) (B x) (hB x))
        a Z (t x)) =
      (fun x => (B x)⁻¹ ^ ((n + 2) * 2) * normalizedPairedEnergy (D x) a Z (t x)) := by
    funext x
    rw [normalizedPairedEnergy_profiles, hcount x]
  rw [heq]
  apply hi.norm.mono'
    ((hmeas.inv.pow _).aestronglyMeasurable.mul hi.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    have hinv : (B x)⁻¹ ≤ 1 := by
      simpa only [one_div] using (div_le_one (hB x)).mpr (hB₁ x)
    have hp : (B x)⁻¹ ^ ((n + 2) * 2) ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (hB x).le) hinv
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hB x).le) _)]
    exact mul_le_of_le_one_left (norm_nonneg _) hp

/-- Use the existing literal separated-profile constructor to make the
evaluated child time zero.  No new frequency or profile is selected. -/
def frozenMomentProfiles (d : MomentData K ω ψ) (t : ℝ) : MomentData K ω ψ :=
  d.separatedProfiles (fun _ => t) (fun _ => t) (fun _ => t)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => t) (fun _ => 0)

@[simp] theorem pairedRows_frozenMomentProfiles (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) :
    pairedRows (frozenMomentProfiles d t) a Z = pairedRows d a Z := rfl

theorem plainPolynomial_frozenMomentProfiles_left (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (frozenMomentProfiles d t) (frozenMomentProfiles d t).plainTest₁
      u N 0 = plainPolynomial d d.plainTest₁ u N t := by
  simp only [plainPolynomial, frozenMomentProfiles, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_zero, mul_one, maskValue] <;> rfl

theorem plainPolynomial_frozenMomentProfiles_right (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (frozenMomentProfiles d t) (frozenMomentProfiles d t).plainTest₂
      u N 0 = plainPolynomial d d.plainTest₂ u N t := by
  simp only [plainPolynomial, frozenMomentProfiles, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_zero, mul_one, maskValue] <;> rfl

theorem primePolynomial_frozenMomentProfiles (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (frozenMomentProfiles d t) i u Z 0 = primePolynomial d i u Z t := by
  simp only [primePolynomial, frozenMomentProfiles, MomentData.separatedProfiles,
    SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_zero, mul_one, maskValue] <;> rfl

theorem slotProduct_frozenMomentProfiles (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct (frozenMomentProfiles d t) u Z 0 = slotProduct d u Z t := by
  simp only [slotProduct, primePolynomial_frozenMomentProfiles]

theorem pairedEnergy_frozenMomentProfiles (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) :
    pairedEnergy (frozenMomentProfiles d t) a Z 0 = pairedEnergy d a Z t := by
  simp only [pairedEnergy, pairedRows_frozenMomentProfiles,
    plainPolynomial_frozenMomentProfiles_left, plainPolynomial_frozenMomentProfiles_right,
    slotProduct_frozenMomentProfiles]

theorem normalizedPairedEnergy_frozenMomentProfiles (d : MomentData K ω ψ)
    (a : RealParameters) (Z t : ℝ) :
    normalizedPairedEnergy (frozenMomentProfiles d t) a Z 0 =
      normalizedPairedEnergy d a Z t := by
  simp only [normalizedPairedEnergy, pairedEnergy_frozenMomentProfiles]

/-- The same actual profile unit ball is now expressed at the common
zero-time interface consumed by the next induction call. -/
theorem MomentProfileUnitBall.freeze_time (d : MomentData K ω ψ)
    (t : ℝ) (orders : Finset (ℕ × ℝ)) (h : MomentProfileUnitBall d t orders) :
    MomentProfileUnitBall (frozenMomentProfiles d t) 0 orders := by
  constructor
  · intro q hq W hW u
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
        profilePower_zero, mul_one] using h.1 q hq d.inverseTest (by simp) u
    · simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
        profilePower_zero, mul_one] using h.1 q hq d.plainTest₁ (by simp) u
    · simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
        profilePower_zero, mul_one] using h.1 q hq d.plainTest₂ (by simp) u
  · intro q hq i
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles, SlotGeometry.freezeTwists,
      PrimeWindow.freezeTwist, profilePower_zero, mul_one] using h.2 q hq i

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedStageEnergy_normalizedMomentProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedPairedEnergy_profile_factor
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedMomentProfiles_unit_ball
#print axioms HeckeSkeleton.Moments.EngineStep.normalized_profile_family_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedPairedEnergy_frozenMomentProfiles
#print axioms HeckeSkeleton.Moments.EngineStep.MomentProfileUnitBall.freeze_time
