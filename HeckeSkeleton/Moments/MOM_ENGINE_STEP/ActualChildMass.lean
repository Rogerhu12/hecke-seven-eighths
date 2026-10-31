import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FrozenScalarMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedActualCapacityChild
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization

/-!
# Canonical arithmetic bounds for the actual capacity-child weight

Common extraction factors are computed from their original frozen atoms.
The row bound contains the complete correlation exactly once. The
second divisor receives its own inverse norm from its actual allocation
scalar. Residual ideal fibers are bounded by the original ideal fibers
after the nonunit support class has been fixed.

These bounds replace the three numerical fields of a raw calibration.
The remaining per-ideal/profile and length data are preserved. Thus the
cost of the actual produced child has an explicit arithmetic weight,
rather than an assumed bound for that cost.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open WholeAllocation CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ActualAllocatedSource

variable {k : ℕ} (s : ActualAllocatedSource A V H k)

/-- Raw windows on the actual frozen occurrences of the second divisor.
The complete source coefficient and its energy are not fields. -/
structure FrozenAtomBounds where
  annulus : Fin k → ℝ
  profile : Fin k → ℝ
  annulus_nonneg : ∀ i, 0 ≤ annulus i
  profile_nonneg : ∀ i, 0 ≤ profile i
  plain₁_bound : ∀ h ∈ s.rows,
    ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
      (s.characters h).mask (s.allocation.plainDivisor 0)‖ ≤ 1
  plain₂_bound : ∀ h ∈ s.rows,
    ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
      (s.characters h).mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1
  prime_bound : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
    ‖sourcePrimeCoefficient ((s.characters h).slot i) ((s.characters h).slotTwist i)
      (s.characters h).mask (s.allocation.witness.2 i)‖ ≤ 1
  prime_annulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
    (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤ annulus i * s.base ^ s.length i
  slot_bound : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
    ‖s.slotWeight h i (s.allocation.witness.2 i)‖ ^ 2 ≤ profile i
  divisor_squarefree : Squarefree s.allocation.divisor
  allocation_mem : s.allocation.selection ∈
    AllocationMass.idealAllocations s.allocation.divisor (k + 2)

namespace FrozenAtomBounds

variable {s} (W : s.FrozenAtomBounds)

def envelope : ℝ :=
  ∏ i ∈ Finset.univ \ s.allocation.keep, W.annulus i * W.profile i

def scalarBound : ℝ := W.envelope / (Ideal.absNorm s.allocation.divisor : ℝ)

theorem envelope_nonneg : 0 ≤ W.envelope :=
  Finset.prod_nonneg (fun i _ => mul_nonneg (W.annulus_nonneg i) (W.profile_nonneg i))

theorem divisor_ne_zero : s.allocation.divisor ≠ 0 := by
  have hd := s.allocation.divisor_dvd_frozenIdeal W.divisor_squarefree W.allocation_mem
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact s.allocation.frozenIdeal_ne_zero hd

theorem divisorNorm_pos : 0 < (Ideal.absNorm s.allocation.divisor : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr W.divisor_ne_zero))

theorem scalarBound_nonneg : 0 ≤ W.scalarBound :=
  div_nonneg W.envelope_nonneg W.divisorNorm_pos.le

theorem scalar_bound (C : A.GeneralArithmeticContext σ η hS)
    (h : H) (hh : h ∈ s.rows) :
    ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ W.scalarBound :=
  s.allocation.scalar_norm_sq_le_divisor C (s.characters h)
    (s.extractedFactor h) (s.row h).element s.base (zero_lt_one.trans s.base_gt_one)
    s.length (s.slotWeight h) W.annulus W.profile
    (W.plain₁_bound h hh) (W.plain₂_bound h hh) (W.prime_bound h hh)
    W.prime_annulus (W.slot_bound h hh) W.annulus_nonneg W.profile_nonneg
    W.divisor_squarefree W.allocation_mem

end FrozenAtomBounds
end ActualAllocatedSource

variable [IsPrincipalIdealRing A.R]
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)

/-- Per-row source factors, literal common ideals and original ideal
fibers. The unit/nonunit class is fixed in the original complex sum.
No row-energy, child-weight, recurrence or mass bound is supplied. -/
structure ActualSecondRowMass (kLeft kRight : ℕ) where
  leftAtoms : FrozenSourceAtoms A σ H R.rows kLeft
  rightAtoms : FrozenSourceAtoms A σ H R.rows kRight
  left_ideal : leftAtoms.ideal = (primePowerProduct R.primes R.leftMultiplicity).val
  right_ideal : rightAtoms.ideal = (primePowerProduct R.primes R.rightMultiplicity).val
  radius : {r : ℝ // 0 < r}
  mask : Finset (HeightOneSpectrum A.R)
  rowProfile : H → ℂ
  profileBound : ℝ
  profileBound_nonneg : 0 ≤ profileBound
  profile_bound : ∀ h ∈ R.rows, ‖rowProfile h‖ ≤ profileBound
  weight_eq : ∀ h ∈ R.rows, R.weight h =
    secondOrbitalScalar (K := F) (S := A.Sf) radius mask *
      rowProfile h * leftAtoms.value h * star (rightAtoms.value h)
  unitIdeal : A.Exterior
  unit_ideal : ∀ h ∈ R.rows,
    unitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) =
      unitIdeal
  nonunitIdeal : A.Exterior
  nonunit_ideal : ∀ h ∈ R.rows,
    nonunitFrequencyRadical C R.primes R.leftMultiplicity R.rightMultiplicity (R.frequency h) =
      nonunitIdeal
  left_positive : ∀ i, 0 < R.leftMultiplicity i
  originalFiber : ℕ
  original_fibers : ∀ I : Ideal (𝓞 F),
    (R.rows.filter (fun h => (R.originalIdeal h).val = I)).card ≤ originalFiber

namespace ActualSecondRowMass

variable {R C} {kLeft kRight : ℕ} (W : ActualSecondRowMass R C kLeft kRight)

def leftIdeal : Ideal (𝓞 F) := (primePowerProduct R.primes R.leftMultiplicity).val
def rightIdeal : Ideal (𝓞 F) := (primePowerProduct R.primes R.rightMultiplicity).val

def commonEnvelope : ℝ :=
  W.profileBound * Real.sqrt W.leftAtoms.envelope * Real.sqrt W.rightAtoms.envelope

def commonDenominator : ℝ :=
  Real.sqrt (Ideal.absNorm W.leftIdeal : ℝ) *
    Real.sqrt (Ideal.absNorm W.rightIdeal : ℝ)

def correlationBound : ℝ :=
  (Ideal.absNorm (gcd W.leftIdeal W.rightIdeal) : ℝ) /
    (Ideal.absNorm W.unitIdeal.val : ℝ)

/-- This contains the complete actual correlation once. -/
def rowBound : ℝ :=
  ‖secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask‖ *
    W.commonEnvelope / W.commonDenominator * W.correlationBound

theorem commonEnvelope_nonneg : 0 ≤ W.commonEnvelope :=
  mul_nonneg (mul_nonneg W.profileBound_nonneg (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem commonDenominator_nonneg : 0 ≤ W.commonDenominator :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem correlationBound_nonneg : 0 ≤ W.correlationBound :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem rowBound_nonneg : 0 ≤ W.rowBound :=
  mul_nonneg
    (div_nonneg (mul_nonneg (norm_nonneg _) W.commonEnvelope_nonneg) W.commonDenominator_nonneg)
    W.correlationBound_nonneg

theorem correlation_bound (h : H) (hh : h ∈ R.rows) :
    ‖R.correlation h‖ ≤ W.correlationBound := by
  have hc := actual_complete_correlation_gcd_radical_bound_of_generates
    C R.primes R.primes_injective R.leftMultiplicity R.rightMultiplicity
    W.left_positive R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
    (R.frequency h)
  simpa only [ActualSecondCorrelationRows.correlation, correlationBound, leftIdeal, rightIdeal,
    W.unit_ideal h hh] using hc

theorem row_bound (h : H) (hh : h ∈ R.rows) :
    ‖R.weight h * R.correlation h‖ ≤ W.rowBound := by
  have hl := W.leftAtoms.norm_le C h hh
  have hr := W.rightAtoms.norm_le C h hh
  rw [W.left_ideal] at hl
  rw [W.right_ideal] at hr
  have h₀ := mul_le_mul_of_nonneg_left (W.profile_bound h hh)
    (norm_nonneg (secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask))
  have h₁ := mul_le_mul h₀ hl (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) W.profileBound_nonneg)
  have h₂ := mul_le_mul h₁ hr (norm_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg _) W.profileBound_nonneg)
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have h₃ := mul_le_mul h₂ (W.correlation_bound h hh) (norm_nonneg _)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg _) W.profileBound_nonneg)
        (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  calc
    _ = ‖secondOrbitalScalar (K := F) (S := A.Sf) W.radius W.mask‖ *
        ‖W.rowProfile h‖ * ‖W.leftAtoms.value h‖ * ‖W.rightAtoms.value h‖ *
        ‖R.correlation h‖ := by
      rw [W.weight_eq h hh]
      simp only [norm_mul, norm_star]
    _ ≤ _ := h₃
    _ = W.rowBound := by
      unfold rowBound commonEnvelope commonDenominator leftIdeal rightIdeal
      ring

/-- Once the genuine nonunit support is fixed, an extracted ideal
determines the original ideal. Therefore extraction creates no new
ideal-fiber loss. -/
theorem extracted_fibers (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    ((Finset.univ : Finset R.live).filter
      (fun h => (R.extractedRow C h).momentIdeal = I)).card ≤ W.originalFiber := by
  let T : Finset R.live := Finset.univ.filter
    (fun h => (R.extractedRow C h).momentIdeal = I)
  let J : Ideal (𝓞 F) := gcd W.leftIdeal W.rightIdeal * W.nonunitIdeal.val * I.val
  have hm : T.image Subtype.val ⊆ R.rows.filter (fun h => (R.originalIdeal h).val = J) := by
    intro h hh
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
    have hxrow := (Finset.mem_filter.mp x.property).1
    have hi := (Finset.mem_filter.mp hx).2
    have hi' : (R.extractedRow C x).ideal.val = I.val :=
      congrArg (fun J : HeckeGeneral.Analysis.NonzeroIdeal F => J.val) hi
    refine Finset.mem_filter.mpr ⟨hxrow, ?_⟩
    rw [R.extractedRow_ideal_factor C x, W.nonunit_ideal x.val hxrow, hi']
    rfl
  calc
    _ = (T.image Subtype.val).card := (Finset.card_image_of_injective T Subtype.val_injective).symm
    _ ≤ (R.rows.filter (fun h => (R.originalIdeal h).val = J)).card := Finset.card_le_card hm
    _ ≤ W.originalFiber := W.original_fibers J

end ActualSecondRowMass

namespace SecondSideFrame

variable {R C} {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

theorem source_rows : f.source.rows = Finset.univ := by cases side <;> rfl

theorem source_row_weight (h : R.live) :
    f.source.weight h = R.weight h.val * R.correlation h.val := by cases side <;> rfl

theorem source_row_momentIdeal (h : R.live) :
    (f.source.row h).momentIdeal = (R.extractedRow C h).momentIdeal := by cases side <;> rfl

variable {ω ψ : HeckeCharacter F}
variable {kLeft kRight : ℕ}

/-- Replace the numerical weight and fiber fields by proved canonical
values. All original profile, arithmetic, support and length dictionaries
are retained, and capacity is subsequently produced for this calibration. -/
def arithmeticCalibration
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) : f.source.Calibration (σ := σ) ω ψ :=
  { cal with
    rowBound := W.rowBound
    rowBound_nonneg := W.rowBound_nonneg
    row_bound := fun h _ => by
      rw [f.source_row_weight]
      exact W.row_bound h.val (Finset.mem_filter.mp h.property).1
    scalarBound := B.scalarBound
    scalarBound_nonneg := B.scalarBound_nonneg
    scalar_bound := B.scalar_bound C
    fiberBound := W.originalFiber
    fibers := fun I => by
      simpa only [f.source_rows, f.source_row_momentIdeal] using W.extracted_fibers I }

theorem arithmeticCalibration_mass
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight) (B : f.source.FrozenAtomBounds) :
    (f.arithmeticCalibration cal W B).mass =
      W.rowBound * (B.envelope / (Ideal.absNorm f.source.allocation.divisor : ℝ)) *
        (W.originalFiber : ℝ) := rfl

/-- The cost is that of the actual constructed child. In particular its
correlation is already in rowBound, and its second-divisor density is
independent of the original Gauss normalization. -/
theorem arithmetic_child_cost
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight) (B : f.source.FrozenAtomBounds)
    {input : (f.arithmeticCalibration cal W B).CapacityInput}
    (child : (f.arithmeticCalibration cal W B).CapacityChild input)
    (bounds : Fin f.source.allocation.keep.card → ℝ) :
    child.envelopeFreeCost bounds =
      (W.rowBound * (B.envelope / (Ideal.absNorm f.source.allocation.divisor : ℝ)) *
        (W.originalFiber : ℝ)) *
        ((∏ i ∈ child.removed, bounds i) * f.source.base ^ input.exponent) := rfl

end SecondSideFrame

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.row_bound
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.extracted_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.arithmetic_child_cost

