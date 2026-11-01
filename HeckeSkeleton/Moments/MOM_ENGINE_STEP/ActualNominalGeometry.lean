import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMassBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

/-!
# The capacity ledger from original ideal norms and scale windows

The expansion is chosen from the original main, direct or valuation-error
tag. Its gap is the fixed step. Original ideal norms determine the common
lengths, the actual Gauss dyad determines the first row length, and separate
original row and support scales determine the two successor exponents.

Only original scale windows, individual slot identities and individual
analytic estimates are inputs. Neither a descendant width inequality nor
a capacity defect nor a chosen child occurs among the input fields.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

/-- The original branch tag, before either capacity deletion. -/
inductive OriginalNominalTag (K : Type) [Field K] [NumberField K] where
  | direct
  | main
  | error (valuation : AmplifierValuation) (prime : HeightOneSpectrum (𝓞 K))

namespace OriginalNominalTag

def removedLength (tag : OriginalNominalTag K) (Z : ℝ) : ℝ :=
  match tag with
  | .direct | .main => 0
  | .error e p => (e.multiplicity : ℝ) * idealLogLength Z p.asIdeal

def movingLength (tag : OriginalNominalTag K) (Z : ℝ) : ℝ :=
  match tag with
  | .direct | .main => 0
  | .error e p => (e.movingMultiplicity : ℝ) * idealLogLength Z p.asIdeal

def poolLength (tag : OriginalNominalTag K) (step : ℝ) : ℝ :=
  match tag with
  | .main => step / 3
  | .direct | .error _ _ => 0

def padding (tag : OriginalNominalTag K) (step : ℝ) : ℝ :=
  match tag with
  | .main => 2 * step
  | .direct | .error _ _ => step

theorem removedLength_nonneg (tag : OriginalNominalTag K) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ tag.removedLength Z := by
  cases tag with
  | direct => exact le_rfl
  | main => exact le_rfl
  | error e p =>
    exact mul_nonneg (Nat.cast_nonneg _) (idealLogLength_nonneg Z hZ _ p.ne_bot)

theorem poolLength_nonneg (tag : OriginalNominalTag K) (step : ℝ) (hstep : 0 ≤ step) :
    0 ≤ tag.poolLength step := by
  cases tag <;> simp only [poolLength] <;> positivity

end OriginalNominalTag

/-- Literal original ideal coordinates. On the right side the selected
and opposite second common ideals are interchanged. -/
structure OriginalNominalIdeals (K : Type) [Field K] [NumberField K] where
  first : (Ideal (𝓞 K))⁰
  opposite : (Ideal (𝓞 K))⁰
  complementary : (Ideal (𝓞 K))⁰
  second : (Ideal (𝓞 K))⁰
  secondOpposite : (Ideal (𝓞 K))⁰
  unitPart : (Ideal (𝓞 K))⁰
  nonunitPart : (Ideal (𝓞 K))⁰
  unit_dvd_gcd : unitPart.val ∣ gcd second.val secondOpposite.val

namespace OriginalNominalIdeals

/-- The frequency class of the actual common row record supplies its
unit-radical divisibility internally. The witness is an original row,
before normalization or either capacity choice. -/
def ofRowMass {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    [IsPrincipalIdealRing A.R] {H ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ActualSecondCorrelationRows A σ H ι}
    {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
    (W : ActualSecondRowMass R C kLeft kRight)
    (first opposite complementary : (Ideal (𝓞 K))⁰) (h : R.rows) :
    OriginalNominalIdeals K where
  first := first
  opposite := opposite
  complementary := complementary
  second := ⟨W.leftIdeal, mem_nonZeroDivisors_of_ne_zero
    (primePowerProduct R.primes R.leftMultiplicity).property.1⟩
  secondOpposite := ⟨W.rightIdeal, mem_nonZeroDivisors_of_ne_zero
    (primePowerProduct R.primes R.rightMultiplicity).property.1⟩
  unitPart := ⟨W.unitIdeal.val, mem_nonZeroDivisors_of_ne_zero W.unitIdeal.property.1⟩
  nonunitPart := ⟨W.nonunitIdeal.val, mem_nonZeroDivisors_of_ne_zero W.nonunitIdeal.property.1⟩
  unit_dvd_gcd := by
    change W.unitIdeal.val ∣ gcd W.leftIdeal W.rightIdeal
    rw [← W.unit_ideal h.val h.property]
    exact unitFrequencyRadical_dvd_gcd C R.primes R.leftMultiplicity
      R.rightMultiplicity W.left_positive (R.frequency h.val)

/-- The opposite side uses the same actual unit and nonunit ideals. -/
def swapSecond (I : OriginalNominalIdeals K) : OriginalNominalIdeals K where
  first := I.first
  opposite := I.opposite
  complementary := I.complementary
  second := I.secondOpposite
  secondOpposite := I.second
  unitPart := I.unitPart
  nonunitPart := I.nonunitPart
  unit_dvd_gcd := by simpa only [gcd_comm] using I.unit_dvd_gcd

def firstFrequency (I : OriginalNominalIdeals K) (a : RealParameters) (Z : ℝ) : ℝ :=
  2 * (a.n₁ + a.n₂ + a.z) - idealLogLength Z I.first.val -
    idealLogLength Z I.opposite.val +
    idealLogLength Z (firstActiveRadical I.first.val I.opposite.val) +
    idealLogLength Z I.complementary.val - a.m

private theorem logLength_le_of_dvd (Z : ℝ) (hZ : 1 < Z)
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) (h : I ∣ J) :
    idealLogLength Z I ≤ idealLogLength Z J := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [rpow_idealLogLength Z hZ I hI, rpow_idealLogLength Z hZ J hJ]
  exact norm_le_of_dvd hJ h

theorem unit_length (I : OriginalNominalIdeals K) (Z : ℝ) (hZ : 1 < Z) :
    idealLogLength Z I.unitPart.val ≤
      idealLogLength Z (gcd I.second.val I.secondOpposite.val) :=
  logLength_le_of_dvd Z hZ _ _ (nonZeroDivisors.coe_ne_zero I.unitPart)
    (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero I.second)) I.unit_dvd_gcd

theorem common_length (I : OriginalNominalIdeals K) (Z : ℝ) (hZ : 1 < Z) :
    idealLogLength Z (gcd I.second.val I.secondOpposite.val) -
      idealLogLength Z I.unitPart.val ≤ idealLogLength Z I.second.val := by
  have hg := logLength_le_of_dvd Z hZ
    (gcd I.second.val I.secondOpposite.val) I.second.val
    (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero I.second))
    (nonZeroDivisors.coe_ne_zero I.second) (gcd_dvd_left _ _)
  have hu := idealLogLength_nonneg Z hZ I.unitPart.val (nonZeroDivisors.coe_ne_zero _)
  linarith

theorem radical_length (I : OriginalNominalIdeals K) (Z : ℝ) (hZ : 1 < Z) :
    idealLogLength Z (commonRadical I.second.val I.secondOpposite.val) ≤
      (idealLogLength Z I.second.val + idealLogLength Z I.secondOpposite.val) / 2 := by
  have hd := commonRadical_dvd I.second.val I.secondOpposite.val
    (nonZeroDivisors.coe_ne_zero _) (nonZeroDivisors.coe_ne_zero _)
  have hl := logLength_le_of_dvd Z hZ _ _ (commonRadical_ne_zero _ _)
    (nonZeroDivisors.coe_ne_zero _) hd.1
  have hr := logLength_le_of_dvd Z hZ _ _ (commonRadical_ne_zero _ _)
    (nonZeroDivisors.coe_ne_zero _) hd.2
  linarith

end OriginalNominalIdeals

/-- Raw ideal coordinates and the retained original Gauss dyad. The
error-prime lower window is supplied by the same original prime pool. -/
structure OriginalNominalGeometry (a : RealParameters) (Z step : ℝ) where
  ideals : OriginalNominalIdeals K
  tag : OriginalNominalTag K
  retainedScale : ℝ
  retainedScale_pos : 0 < retainedScale
  supportError : ℝ
  supportError_nonneg : 0 ≤ supportError
  retained_upper : retainedScale ≤ Z ^ (ideals.firstFrequency a Z + supportError)
  error_prime_lower : ∀ e p, tag = .error e p →
    Z ^ (step / 6) ≤ (Ideal.absNorm p.asIdeal : ℝ)

namespace OriginalNominalGeometry

variable {a : RealParameters} {Z step : ℝ}
variable (G : OriginalNominalGeometry (K := K) a Z step)

def forMain (I : OriginalNominalIdeals K) (retainedScale supportError : ℝ)
    (hscale : 0 < retainedScale) (herr : 0 ≤ supportError)
    (hupper : retainedScale ≤ Z ^ (I.firstFrequency a Z + supportError)) :
    OriginalNominalGeometry (K := K) a Z step where
  ideals := I
  tag := .main
  retainedScale := retainedScale
  retainedScale_pos := hscale
  supportError := supportError
  supportError_nonneg := herr
  retained_upper := hupper
  error_prime_lower _ _ h := by cases h

def forDirect (I : OriginalNominalIdeals K) (retainedScale supportError : ℝ)
    (hscale : 0 < retainedScale) (herr : 0 ≤ supportError)
    (hupper : retainedScale ≤ Z ^ (I.firstFrequency a Z + supportError)) :
    OriginalNominalGeometry (K := K) a Z step where
  ideals := I
  tag := .direct
  retainedScale := retainedScale
  retainedScale_pos := hscale
  supportError := supportError
  supportError_nonneg := herr
  retained_upper := hupper
  error_prime_lower _ _ h := by cases h

/-- The original pool, with its already fixed prime label, proves the
only error-prime window used by the capacity ledger. -/
def forPoolError {A : SArithmeticData K}
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z (step / 3) eps)
    (e : AmplifierValuation) (p : P.primes)
    (I : OriginalNominalIdeals K) (retainedScale supportError : ℝ)
    (hscale : 0 < retainedScale) (herr : 0 ≤ supportError)
    (hupper : retainedScale ≤ Z ^ (I.firstFrequency a Z + supportError)) :
    OriginalNominalGeometry (K := K) a Z step where
  ideals := I
  tag := .error e p.val.val
  retainedScale := retainedScale
  retainedScale_pos := hscale
  supportError := supportError
  supportError_nonneg := herr
  retained_upper := hupper
  error_prime_lower e' p' he := by
    obtain ⟨he, hp⟩ := OriginalNominalTag.error.inj he
    subst e'
    subst p'
    simpa only [show (step / 3) / 2 = step / 6 by ring] using
      P.norm_lower p.val p.property

def retainedLength : ℝ := Real.log G.retainedScale / Real.log Z

def shiftedCommon : ℝ :=
  idealLogLength Z G.ideals.opposite.val + G.ideals.firstFrequency a Z - G.retainedLength

def enlargement : ℝ :=
  max (G.shiftedCommon - idealLogLength Z G.ideals.first.val -
    2 * G.tag.removedLength Z + G.tag.movingLength Z) 0 + G.tag.padding step

/-- Every entry is computed before normalization and slot deletion. -/
def skeleton : NominalChildGeometry where
  A := a.n₁ + a.n₂ + a.z
  m := a.m
  q := a.q
  c := idealLogLength Z G.ideals.first.val
  d := idealLogLength Z G.ideals.opposite.val
  R := idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val)
  E := idealLogLength Z G.ideals.complementary.val
  Krow := G.retainedLength
  w := G.tag.removedLength Z
  wo := G.tag.movingLength Z
  g := G.enlargement
  g₂ := idealLogLength Z (gcd G.ideals.second.val G.ideals.secondOpposite.val)
  t₂ := idealLogLength Z G.ideals.unitPart.val
  V := idealLogLength Z G.ideals.nonunitPart.val
  c₂ := idealLogLength Z G.ideals.second.val

def boundary : ℝ :=
  firstAllowance (idealLogLength Z G.ideals.first.val)
    (idealLogLength Z G.ideals.opposite.val)
    (idealLogLength Z (firstActiveRadical G.ideals.first.val G.ideals.opposite.val))

def halfSecond : ℝ :=
  (idealLogLength Z G.ideals.second.val + idealLogLength Z G.ideals.secondOpposite.val) / 2

def secondRadical : ℝ :=
  idealLogLength Z (commonRadical G.ideals.second.val G.ideals.secondOpposite.val)

@[simp] theorem parentWidth : G.skeleton.parentWidth = a.m + a.q := rfl

theorem shiftedCommon_eq : G.skeleton.shiftedCommon = G.shiftedCommon := rfl

theorem boundary_nonneg : 0 ≤ G.boundary := firstAllowance_nonneg _ _ _

private theorem retained_length_le (hZ : 1 < Z) :
    G.retainedLength ≤ G.ideals.firstFrequency a Z + G.supportError := by
  have h := Real.log_le_log G.retainedScale_pos G.retained_upper
  rw [Real.log_rpow (zero_lt_one.trans hZ)] at h
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr (by nlinarith)

theorem shiftedCommon_lower (hZ : 1 < Z) :
    -G.supportError ≤ G.skeleton.shiftedCommon := by
  have hd := idealLogLength_nonneg Z hZ G.ideals.opposite.val
    (nonZeroDivisors.coe_ne_zero _)
  have hk := G.retained_length_le hZ
  rw [G.shiftedCommon_eq]
  unfold shiftedCommon
  linarith

theorem enlargement_bound (hstep : 0 ≤ step) :
    G.skeleton.enlargementJ + step ≤ G.skeleton.g := by
  have hm := le_max_left G.skeleton.enlargementJ 0
  have hpad : step ≤ G.tag.padding step := by
    cases G.tag <;> simp only [OriginalNominalTag.padding] <;> linarith
  have hg : G.skeleton.g = max G.skeleton.enlargementJ 0 + G.tag.padding step := rfl
  rw [hg]
  linarith

theorem paid_shift (hZ : 1 < Z) (hmain : G.tag ≠ .direct) :
    G.skeleton.paidShift ≤
      6 * (G.skeleton.w + G.tag.poolLength step) + G.supportError := by
  have hc : 0 ≤ G.skeleton.c :=
    idealLogLength_nonneg Z hZ _ (nonZeroDivisors.coe_ne_zero _)
  have hD := G.shiftedCommon_lower hZ
  cases ht : G.tag with
  | direct => exact (hmain ht).elim
  | main =>
    apply G.skeleton.main_paid_shift step G.supportError
    · simp only [skeleton, ht, OriginalNominalTag.removedLength]
    · simp only [skeleton, ht, OriginalNominalTag.movingLength]
    · simp only [skeleton, enlargement, ht, OriginalNominalTag.removedLength,
        OriginalNominalTag.movingLength, OriginalNominalTag.padding,
        NominalChildGeometry.shiftedCommon, NominalChildGeometry.firstFrequency,
        OriginalNominalIdeals.firstFrequency, shiftedCommon, mul_zero, sub_zero, add_zero]
    · exact hc
    · exact hD
    · exact G.supportError_nonneg
  | error e p =>
    have hp0 := idealLogLength_nonneg Z hZ p.asIdeal p.ne_bot
    have hp : step / 6 ≤ idealLogLength Z p.asIdeal := by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      rw [rpow_idealLogLength Z hZ p.asIdeal p.ne_bot]
      exact G.error_prime_lower e p ht
    have hb := G.skeleton.error_paid_shift e (idealLogLength Z p.asIdeal) step
      G.supportError
      (by simp only [skeleton, ht, OriginalNominalTag.removedLength])
      (by simp only [skeleton, ht, OriginalNominalTag.movingLength])
      (by
        have hg : G.skeleton.g =
            max G.skeleton.enlargementJ 0 + G.tag.padding step := rfl
        simpa only [NominalChildGeometry.enlargementJ, ht, OriginalNominalTag.padding]
          using hg) hc hp0 hp hD G.supportError_nonneg
    simpa only [ht, OriginalNominalTag.poolLength] using hb

theorem unit_length (hZ : 1 < Z) : G.skeleton.t₂ ≤ G.skeleton.g₂ :=
  G.ideals.unit_length Z hZ

theorem common_length (hZ : 1 < Z) :
    G.skeleton.g₂ - G.skeleton.t₂ ≤ G.skeleton.c₂ :=
  G.ideals.common_length Z hZ

theorem radical_length (hZ : 1 < Z) : G.secondRadical ≤ G.halfSecond :=
  G.ideals.radical_length Z hZ

/-- The original second frequency cutoff, before dividing by the actual
gcd and nonunit radical. -/
def frequencyCenter : ℝ :=
  2 * (G.skeleton.A - G.skeleton.c - G.skeleton.w) -
    G.skeleton.Krow - G.skeleton.g

/-- The original moving-support scale, before adjoining the two actual
frequency radicals. -/
def supportCenter : ℝ :=
  G.skeleton.q + G.skeleton.R + G.skeleton.E + G.skeleton.wo

/-- Separate original scales and their dyadic windows. The identities
are the literal norm extractions in the two raw parameter dictionaries. -/
structure ScaleWindows (m q : ℝ) where
  rowScale : ℝ
  supportScale : ℝ
  rowScale_pos : 0 < rowScale
  supportScale_pos : 0 < supportScale
  rowError : ℝ
  supportError : ℝ
  rowError_nonneg : 0 ≤ rowError
  supportError_nonneg : 0 ≤ supportError
  error_small : 2 * (rowError + supportError) ≤ step
  row_lower : Z ^ (G.frequencyCenter - rowError) ≤ rowScale
  row_upper : rowScale ≤ Z ^ (G.frequencyCenter + rowError)
  support_lower : Z ^ (G.supportCenter - supportError) ≤ supportScale
  support_upper : supportScale ≤ Z ^ (G.supportCenter + supportError)
  row_parameter : Z ^ m = rowScale /
    ((Ideal.absNorm (gcd G.ideals.second.val G.ideals.secondOpposite.val) : ℝ) *
      (Ideal.absNorm G.ideals.nonunitPart.val : ℝ))
  support_parameter : Z ^ q = supportScale *
    ((Ideal.absNorm G.ideals.unitPart.val : ℝ) *
      (Ideal.absNorm G.ideals.nonunitPart.val : ℝ))

private theorem parameter_window_div
    {Z scale factor length center error exponent : ℝ}
    (hZ : 1 < Z) (hfactor : Z ^ length = factor)
    (hscale : Z ^ exponent = scale / factor)
    (hlower : Z ^ (center - error) ≤ scale)
    (hupper : scale ≤ Z ^ (center + error)) :
    center - length - error ≤ exponent ∧ exponent ≤ center - length + error := by
  have hf : factor ≠ 0 := by
    rw [← hfactor]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne'
  have he : Z ^ (exponent + length) = scale := by
    rw [Real.rpow_add (zero_lt_one.trans hZ), hfactor, hscale]
    exact div_mul_cancel₀ _ hf
  rw [← he] at hlower hupper
  have hl := (Real.rpow_le_rpow_left_iff hZ).mp hlower
  have hu := (Real.rpow_le_rpow_left_iff hZ).mp hupper
  constructor <;> linarith

private theorem parameter_window_mul
    {Z scale factor length center error exponent : ℝ}
    (hZ : 1 < Z) (hfactor : Z ^ length = factor)
    (hscale : Z ^ exponent = scale * factor)
    (hlower : Z ^ (center - error) ≤ scale)
    (hupper : scale ≤ Z ^ (center + error)) :
    center + length - error ≤ exponent ∧ exponent ≤ center + length + error := by
  have hf : factor ≠ 0 := by
    rw [← hfactor]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne'
  have he : Z ^ (exponent - length) = scale := by
    rw [Real.rpow_sub (zero_lt_one.trans hZ), hfactor, hscale]
    exact mul_div_cancel_right₀ _ hf
  rw [← he] at hlower hupper
  have hl := (Real.rpow_le_rpow_left_iff hZ).mp hlower
  have hu := (Real.rpow_le_rpow_left_iff hZ).mp hupper
  constructor <;> linarith

namespace ScaleWindows

variable {G} {m q : ℝ} (W : G.ScaleWindows m q)

def error : ℝ := W.rowError + W.supportError

theorem error_nonneg : 0 ≤ W.error :=
  add_nonneg W.rowError_nonneg W.supportError_nonneg

theorem error_le_half_step : W.error ≤ step / 2 := by
  have h := W.error_small
  change 2 * W.error ≤ step at h
  linarith

/-- Both width inequalities are derived from the separate original norm
windows. No inequality for a produced or normalized child is supplied. -/
theorem width_bounds (hZ : 1 < Z) :
    m + q ≤ G.skeleton.nominalWidth + W.error ∧
      G.skeleton.nominalWidth - (m + q) ≤ W.error := by
  have hrowFactor : Z ^ (G.skeleton.g₂ + G.skeleton.V) =
      (Ideal.absNorm (gcd G.ideals.second.val G.ideals.secondOpposite.val) : ℝ) *
        (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
    change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
    rw [Real.rpow_add (zero_lt_one.trans hZ),
      rpow_idealLogLength Z hZ _
        (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
      rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
  have hsupportFactor : Z ^ (G.skeleton.t₂ + G.skeleton.V) =
      (Ideal.absNorm G.ideals.unitPart.val : ℝ) *
        (Ideal.absNorm G.ideals.nonunitPart.val : ℝ) := by
    change Z ^ (idealLogLength Z _ + idealLogLength Z _) = _
    rw [Real.rpow_add (zero_lt_one.trans hZ),
      rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.unitPart),
      rpow_idealLogLength Z hZ _ (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
  obtain ⟨hrl, hru⟩ := parameter_window_div hZ hrowFactor W.row_parameter
    W.row_lower W.row_upper
  obtain ⟨hsl, hsu⟩ := parameter_window_mul hZ hsupportFactor W.support_parameter
    W.support_lower W.support_upper
  have hid : G.skeleton.nominalWidth =
      (G.frequencyCenter - (G.skeleton.g₂ + G.skeleton.V)) +
        (G.supportCenter + (G.skeleton.t₂ + G.skeleton.V)) := by
    dsimp only [NominalChildGeometry.nominalWidth, NominalChildGeometry.nominalRow,
      NominalChildGeometry.nominalSupport, frequencyCenter, supportCenter]
    ring
  rw [hid]
  dsimp only [error]
  constructor <;> linarith

end ScaleWindows

end OriginalNominalGeometry

namespace OriginalSlotDictionary

variable {ω ψ : HeckeCharacter K} {parent : MomentData K ω ψ}
variable {k : ℕ} {length : Fin k → ℝ}

/-- The original slot embedding also gives the pre-allocation total
length bound. This uses each original slot once. -/
theorem totalLength_le (raw : OriginalSlotDictionary parent length) :
    (∑ i, length i) ≤ parent.geometry.totalLength := by
  calc
    (∑ i, length i) = ∑ i, (parent.geometry.slots (raw.index i)).length :=
      Finset.sum_congr rfl (fun i _ => raw.length_eq i)
    _ = ∑ j ∈ Finset.univ.image raw.index, (parent.geometry.slots j).length := by
      rw [Finset.sum_image (fun _ _ _ _ h => raw.index.injective h)]
    _ ≤ ∑ j, (parent.geometry.slots j).length :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => (parent.geometry.slots j).length_pos.le)

end OriginalSlotDictionary

variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration

variable (D : s.Calibration (σ := σ) ω ψ)
variable (parent : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a s.base step)

/-- Original scale identities on this very calibration. In particular,
the direct case records the original empty source array, not a condition
on a later capacity child. -/
structure OriginalLengthBinding where
  slots : OriginalSlotDictionary parent s.length
  parent_z : a.z = parent.geometry.totalLength
  parent_region : 3 / 4 ≤ a.κ ∧ a.κ ≤ 1 ∧
    (a.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q)
  kappa : D.parameters.κ = a.κ
  direct_slots : G.tag = .direct → k = 0
  scales : G.ScaleWindows D.parameters.m D.parameters.q
  rawScaleError : ℝ
  rawScaleError_nonneg : 0 ≤ rawScaleError
  original_scale_product : s.scale₁ * s.scale₂ * s.base ^ s.beforeLength ≤
    s.base ^ (G.skeleton.rawDegree + rawScaleError)

/-- Individual original analytic inputs, independent of the numerical
capacity ledger and of every eventual removal choice. -/
structure OriginalCapacityAtoms where
  leftAnnulus : ℝ
  rightAnnulus : ℝ
  leftAnnulus_one : 1 ≤ leftAnnulus
  rightAnnulus_one : 1 ≤ rightAnnulus
  left_window : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₁.profile u (D.height ξ) x ≠ 0 → x ≤ leftAnnulus
  right_window : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
    (D.data ξ).plainTest₂.profile u (D.height ξ) x ≠ 0 → x ≤ rightAnnulus
  primeBound : V → Fin s.allocation.keep.card → ℝ
  primeBound_nonneg : ∀ ξ i, 0 ≤ primeBound ξ i
  prime_bound : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
    ∀ i : Fin s.allocation.keep.card,
    ‖primePolynomial (D.data ξ)
      (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i)
      u s.base (D.height ξ)‖ ^ 2 ≤
        primeBound ξ i * s.base ^ (D.parameters.κ * s.childLength i)

/-- The actual engine domain supplies the parent capacity with the full
permitted kappa interval. No use is made of the narrower shared PRegion. -/
def OriginalLengthBinding.ofDomain
    {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain centered parent a s.base Y₁ Y₂ floor padding)
    (slots : OriginalSlotDictionary parent s.length)
    (kappa : D.parameters.κ = a.κ)
    (direct_slots : G.tag = .direct → k = 0)
    (scales : G.ScaleWindows D.parameters.m D.parameters.q)
    (rawScaleError : ℝ) (herr : 0 ≤ rawScaleError)
    (hproduct : s.scale₁ * s.scale₂ * s.base ^ s.beforeLength ≤
      s.base ^ (G.skeleton.rawDegree + rawScaleError)) :
    D.OriginalLengthBinding parent a step G where
  slots := slots
  parent_z := domain.total_length
  parent_region := ⟨domain.kappa_lower, domain.kappa_upper, domain.capacity⟩
  kappa := kappa
  direct_slots := direct_slots
  scales := scales
  rawScaleError := rawScaleError
  rawScaleError_nonneg := herr
  original_scale_product := hproduct

namespace OriginalLengthBinding

variable {D parent a step G} (B : D.OriginalLengthBinding parent a step G)

include B

theorem before_length : s.beforeLength ≤ a.z := by
  rw [B.parent_z]
  exact B.slots.totalLength_le

theorem kappa_pos : 0 < D.parameters.κ := by
  rw [B.kappa]
  have hk := B.parent_region.1
  linarith

theorem parent_capacity : s.allocation.keep.card = 0 ∨
    G.skeleton.A + (6 * D.parameters.κ - 1) * s.beforeLength ≤
      G.skeleton.parentWidth := by
  rcases B.parent_region.2.2 with hz | hcap
  · left
    have hb : s.beforeLength ≤ 0 := by simpa only [hz] using B.before_length
    have hk : k = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hk
      let i : Fin k := ⟨0, hk⟩
      have hi : s.length i ≤ s.beforeLength :=
        Finset.single_le_sum (fun j _ => (s.length_pos j).le) (Finset.mem_univ i)
      exact (not_le_of_gt (s.length_pos i)) (hi.trans hb)
    have hcard := s.allocation.keep_card_le
    omega
  · right
    have hk : 0 ≤ 6 * a.κ - 1 := by linarith [B.parent_region.1]
    have hlen := mul_le_mul_of_nonneg_left B.before_length hk
    rw [B.kappa]
    change (a.n₁ + a.n₂ + a.z) + (6 * a.κ - 1) * s.beforeLength ≤ a.m + a.q
    linarith

theorem paid_shift : s.allocation.keep.card = 0 ∨
    G.skeleton.paidShift ≤
      6 * (G.skeleton.w + G.tag.poolLength step) + G.supportError := by
  by_cases hd : G.tag = .direct
  · left
    have hk := B.direct_slots hd
    have hcard := s.allocation.keep_card_le
    omega
  · exact Or.inr (G.paid_shift s.base_gt_one hd)

/-- The two quotient scale identities and the actual allocated-length
identity prove the raw degree inequality before clipping. -/
theorem raw_degree : D.parameters.n₁ + D.parameters.n₂ + D.parameters.z ≤
    G.skeleton.rawDegree - s.allocatedLength + B.rawScaleError := by
  have hz : 0 < s.base := zero_lt_one.trans s.base_gt_one
  have hN₁ := actual_momentIdeal_norm_one_le (s.allocation.plainDivisor 0)
  have hN₂ := actual_momentIdeal_norm_one_le (s.allocation.plainDivisor (Fin.succ 0))
  have hN₁pos := lt_of_lt_of_le zero_lt_one hN₁
  have hN₂pos := lt_of_lt_of_le zero_lt_one hN₂
  have hleft : s.base ^ D.parameters.n₁ ≤ s.scale₁ := by
    have he := (eq_div_iff hN₁pos.ne').mp D.left_scale
    calc
      _ = s.base ^ D.parameters.n₁ * 1 := (mul_one _).symm
      _ ≤ s.base ^ D.parameters.n₁ *
          HeckeGeneral.Analysis.idealNorm K (s.allocation.plainDivisor 0) :=
        mul_le_mul_of_nonneg_left hN₁ (Real.rpow_nonneg hz.le _)
      _ = _ := he
  have hright : s.base ^ D.parameters.n₂ ≤ s.scale₂ := by
    have he := (eq_div_iff hN₂pos.ne').mp D.right_scale
    calc
      _ = s.base ^ D.parameters.n₂ * 1 := (mul_one _).symm
      _ ≤ s.base ^ D.parameters.n₂ *
          HeckeGeneral.Analysis.idealNorm K (s.allocation.plainDivisor (Fin.succ 0)) :=
        mul_le_mul_of_nonneg_left hN₂ (Real.rpow_nonneg hz.le _)
      _ = _ := he
  have hp : s.base ^ (D.parameters.n₁ + D.parameters.n₂ + s.beforeLength) ≤
      s.base ^ (G.skeleton.rawDegree + B.rawScaleError) := by
    apply (le_trans _ B.original_scale_product)
    rw [Real.rpow_add hz, Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hleft hright (Real.rpow_nonneg hz.le _)
        ((Real.rpow_nonneg hz.le _).trans hleft)) (Real.rpow_nonneg hz.le _)
  have hn := (Real.rpow_le_rpow_left_iff s.base_gt_one).mp hp
  have hred := D.actual_length_reduction
  linarith

/-- This fills every capacity input from the same original calibration.
The step and parent mesh are used literally, before choosing a child. -/
def capacityInput (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    D.CapacityInput where
  skeleton := G.skeleton
  b₂ := G.halfSecond
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
  unit_part := G.unit_length s.base_gt_one
  actual_width := (B.scales.width_bounds s.base_gt_one).1
  delta_bound := B.scales.error_le_half_step
  principal_part := G.radical_length s.base_gt_one
  boundary_nonneg := G.boundary_nonneg
  parent_capacity := B.parent_capacity
  common_part := G.common_length s.base_gt_one
  paid_shift := B.paid_shift
  raw_degree := B.raw_degree
  width_error := (B.scales.width_bounds s.base_gt_one).2
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
    have hbp := sub_nonneg.mpr (G.radical_length s.base_gt_one)
    have hw := G.tag.removedLength_nonneg s.base s.base_gt_one
    have he := G.tag.poolLength_nonneg step hstep.le
    change 0 ≤ (G.halfSecond - G.secondRadical + G.tag.removedLength s.base +
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
  prime_bound := atoms.prime_bound

@[simp] theorem capacityInput_parentWidth
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    (B.capacityInput hstep mesh hmesh hfit atoms).skeleton.parentWidth = a.m + a.q := rfl

@[simp] theorem capacityInput_gap
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    (B.capacityInput hstep mesh hmesh hfit atoms).gap = step := rfl

/-- The existing same-family arithmetic mass proof receives its exact
norm-length identities from the same computed capacity input. -/
def normLengths
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms) :
    ActualCapacityNormLengths (B.capacityInput hstep mesh hmesh hfit atoms)
      s.base (G.skeleton.A - G.skeleton.c - G.skeleton.w)
      (G.skeleton.q + G.skeleton.R + G.skeleton.E)
      G.skeleton.wo G.skeleton.w G.skeleton.Krow G.skeleton.g (G.tag.poolLength step)
      G.ideals.second.val G.ideals.secondOpposite.val
      G.ideals.unitPart.val G.ideals.nonunitPart.val where
  base_eq := rfl
  degree_eq := rfl
  support_eq := rfl
  moving_eq := rfl
  removed_eq := rfl
  row_eq := rfl
  enlargement_eq := rfl
  gcd_eq := rfl
  unit_eq := rfl
  nonunit_eq := rfl
  common_eq := rfl
  radical_eq := rfl
  pool_eq := rfl

/-- Normalization is applied to this computed input and the existing
calibration. It does not replace the source or select a different child. -/
def normalizedCapacityData
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    D.NormalizedCapacityData :=
  (B.capacityInput hstep mesh hmesh hfit atoms).normalized amplitude hpos bounds hbound hfactor

@[simp] theorem normalizedCapacityData_parentWidth
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    (B.normalizedCapacityData hstep mesh hmesh hfit atoms amplitude hpos bounds hbound
      hfactor).geometry.parentWidth = a.m + a.q := rfl

@[simp] theorem normalizedCapacityData_gap
    (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
    (hfit : parent.geometry.fitsMesh mesh) (atoms : D.OriginalCapacityAtoms)
    (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
    (bounds : Fin s.allocation.keep.card → ℝ) (hbound : ∀ i, 0 ≤ bounds i)
    (hfactor : ∀ ξ i, atoms.primeBound ξ i = amplitude ξ ^ 2 * bounds i) :
    (B.normalizedCapacityData hstep mesh hmesh hfit atoms amplitude hpos bounds hbound
      hfactor).gap = step := rfl

end OriginalLengthBinding

end ActualAllocatedSource.Calibration

namespace ActualCapacityNormLengths

variable {cal : s.Calibration (σ := σ) ω ψ} {input : cal.CapacityInput}
variable {Z a₀ q wo w krow g ell : ℝ} {D E U N : Ideal (𝓞 K)}

/-- The shared pair-mass interface orders its two common ideals once.
This identity transport preserves the selected side's actual c₂ and
every parameter of the same capacity input. -/
def swap (L : ActualCapacityNormLengths input Z a₀ q wo w krow g ell D E U N) :
    ActualCapacityNormLengths input Z a₀ q wo w krow g ell E D U N where
  base_eq := L.base_eq
  degree_eq := L.degree_eq
  support_eq := L.support_eq
  moving_eq := L.moving_eq
  removed_eq := L.removed_eq
  row_eq := L.row_eq
  enlargement_eq := L.enlargement_eq
  gcd_eq := by simpa only [gcd_comm] using L.gcd_eq
  unit_eq := L.unit_eq
  nonunit_eq := L.nonunit_eq
  common_eq := by simpa only [add_comm] using L.common_eq
  radical_eq := by simpa only [commonRadical, Finset.inter_comm] using L.radical_eq
  pool_eq := L.pool_eq

end ActualCapacityNormLengths

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalIdeals.ofRowMass
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.ScaleWindows.width_bounds
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalLengthBinding.raw_degree
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalLengthBinding.capacityInput
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalLengthBinding.normLengths
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.OriginalLengthBinding.normalizedCapacityData
#print axioms HeckeSkeleton.Moments.EngineStep.ActualCapacityNormLengths.swap
