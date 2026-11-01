import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding

/-!
# Reciprocal balancing of the two actual plain profiles

The two positive scale factors in a centered rectangle can be very
different, although their product is fixed by the original two plain
scales. Reciprocal multiplication of the two individual profiles keeps
each literal rectangle coefficient unchanged. No carrier, normalizer,
slot, character, location or Fourier variable is modified.

The balancing is performed before the actual normalized children are
chosen. Its factorization belongs to the original whole coefficient,
so the same stored leaf and its ordinary binding can be retained.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The reciprocal factors act only on the two displayed plain
weights. Their actual norm scales and all prime occurrences stay fixed. -/
def balancePlain (c : Bool → ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * (c r : ℂ)
    rightWeight := fun r I => d.rightWeight r I * (c r : ℂ)⁻¹ }

@[simp] theorem balancePlain_characters (c : Bool → ℝ) :
    (d.balancePlain c).characters = d.characters := rfl

@[simp] theorem balancePlain_normalizer (c : Bool → ℝ) :
    (d.balancePlain c).normalizer = d.normalizer := rfl

theorem balancePlain_rectangleLeftWeight (c : Bool → ℝ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.balancePlain c).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * (c r : ℂ) := by
  unfold rectangleLeftWeight balancePlain
  split_ifs <;> simp only [zero_mul]

/-- The equality is proved for each original column, including every
ramified zero and the absent comparison rectangle. -/
theorem balancePlain_term (c : Bool → ℝ) (hc : ∀ r, 0 < c r)
    (r : Bool) (i : AllocationColumn K k) :
    (d.balancePlain c).term r i = d.term r i := by
  have hcr : (c r : ℂ) ≠ 0 := by exact_mod_cast (hc r).ne'
  have he := CanonicalLiteralTransforms.bare_mul_weights d.characters
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r)
    (fun _ => (c r : ℂ)) (fun _ => (c r : ℂ)⁻¹)
    d.slotWeight (fun _ _ => 1) i
  have hw := funext (d.balancePlain_rectangleLeftWeight c r)
  unfold term
  rw [hw]
  change d.normalizer * rawBareSourceCoefficient d.characters
      (d.scale₁ r) (d.scale₂ r) d.base d.length
      (fun I => d.rectangleLeftWeight r I * (c r : ℂ))
      (fun I => d.rightWeight r I * (c r : ℂ)⁻¹) d.slotWeight i = _
  simpa only [mul_one, Finset.prod_const_one, mul_inv_cancel₀ hcr] using
    congrArg (fun z => d.normalizer * z) he

theorem balancePlain_whole (c : Bool → ℝ) (hc : ∀ r, 0 < c r)
    (i : AllocationColumn K k) :
    (d.balancePlain c).whole i = d.whole i := by
  rw [whole, d.balancePlain_term c hc false, d.balancePlain_term c hc true]
  rfl

/-- Actual support extraction and reciprocal balancing commute. The
original removed slots and the same witness are retained. -/
theorem balancePlain_extract (c : Bool → ℝ)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.balancePlain c).extract b = (d.extract b).balancePlain c := rfl

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- These are the actual scaled individual tests, not assumed new
profile representatives. Their finite supports are constructed by the
existing multiplication operation. -/
def balancePlain (c : Bool → ℝ) : (d.balancePlain c).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r) (fun _ => (c r : ℂ))
  right r := CanonicalLiteralProfileData.mulIdealTest (W.right r) (fun _ => (c r : ℂ)⁻¹)
  slot := W.slot
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.right_positive r)
  slot_positive := W.slot_positive
  left_frozen r u t y := congrArg (fun z => z * (c r : ℂ)) (W.left_frozen r u t y)
  right_frozen r u t y := congrArg (fun z => z * (c r : ℂ)⁻¹) (W.right_frozen r u t y)
  slot_frozen := W.slot_frozen
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) * (c r : ℂ) = _
    rw [W.left_eval, d.balancePlain_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / d.scale₂ r) * (c r : ℂ)⁻¹ = _
    rw [W.right_eval] <;> rfl
  slot_eval := W.slot_eval

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def balancePlain (W : d.SupportData excluded) (c : Bool → ℝ) :
    (d.balancePlain c).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem r I hI havoid := by
    rw [d.balancePlain_rectangleLeftWeight c r I] at hI
    exact W.left_mem r I (left_ne_zero_of_mul hI) havoid
  right_mem r I hI havoid := W.right_mem r I (left_ne_zero_of_mul hI) havoid
  slot_mem := W.slot_mem

end SupportData
end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralPlainBalance

/-- A positive balancing factor determined by the actual two scalar
profiles. No upper bound or replacement scale is selected here. -/
def ratio (left right : ℝ) : ℝ := Real.sqrt (right / left)

theorem ratio_pos {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    0 < ratio left right := Real.sqrt_pos.mpr (div_pos hr hl)

theorem left_mul_ratio {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    left * ratio left right = Real.sqrt (left * right) := by
  apply (sq_eq_sq₀ (mul_nonneg hl.le (ratio_pos hl hr).le)
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, ratio, Real.sq_sqrt (div_pos hr hl).le, Real.sq_sqrt (mul_pos hl hr).le]
  field_simp [hl.ne'] <;> ring

theorem right_mul_ratio_inv {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    right * (ratio left right)⁻¹ = Real.sqrt (left * right) := by
  apply (sq_eq_sq₀ (mul_nonneg hr.le (inv_nonneg.mpr (ratio_pos hl hr).le))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, inv_pow, ratio, Real.sq_sqrt (div_pos hr hl).le,
    Real.sq_sqrt (mul_pos hl hr).le]
  field_simp [hl.ne', hr.ne'] <;> ring

end CanonicalLiteralPlainBalance

namespace CanonicalLiteralRectangles

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}

/-- The balanced frames are a factorization of the same original
whole source. Both ordinary rectangles still have their original
allocation, locations, arithmetic rows and complete coefficients. -/
def balancedRectangles (R : ActualSecondCorrelationRows A σ H ι)
    (left : Atoms (K := K) k) (right : Atoms (K := K) l)
    (leftBalance rightBalance : Bool → ℝ)
    (hleftBalance : ∀ r, 0 < leftBalance r) (hrightBalance : ∀ r, 0 < rightBalance r)
    (IL : AllocationColumn K k → A.Exterior) (IR : AllocationColumn K l → A.Exterior)
    (hIL : ∀ i ∈ childCartesianColumns left.plain₁ left.plain₂ left.slots,
      (IL i).val = allocationColumnIdeal i)
    (hIR : ∀ j ∈ childCartesianColumns right.plain₁ right.plain₂ right.slots,
      (IR j).val = allocationColumnIdeal j)
    (b : liveSecondAllocationBranches (Ray := PUnit.{1})
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IR)
    (exceptional : H → Prop) (firstLeftSign firstRightSign : ℝ) :
    HybridOrdinaryRectangles R PUnit.{1}
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IL IR
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) left.whole right.whole
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.prime firstLeftSign))
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.prime firstRightSign)) b exceptional where
  leftTerms := (left.balancePlain leftBalance).term
  rightTerms := (right.balancePlain rightBalance).term
  left_difference i _ := by
    rw [left.balancePlain_term leftBalance hleftBalance false i,
      left.balancePlain_term leftBalance hleftBalance true i]
    rfl
  right_difference i _ := by
    rw [right.balancePlain_term rightBalance hrightBalance false i,
      right.balancePlain_term rightBalance hrightBalance true i]
    rfl
  leftFactors r := (left.balancePlain leftBalance).factors
    (R.restrictRows fun h => ¬exceptional h) .left b.val.2.1 IL hIL firstLeftSign r
  rightFactors r := (right.balancePlain rightBalance).factors
    (R.restrictRows fun h => ¬exceptional h) .right b.val.2.1 IR hIR firstRightSign r

end CanonicalLiteralRectangles

namespace ActualHybridLeaf.OrdinaryBinding

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {leaf : ActualHybridLeaf K H U V}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin leaf.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {T : Fin leaf.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
variable {IA : AllocationColumn K leaf.leftSlots → A.Exterior}
variable {IB : AllocationColumn K leaf.rightSlots → A.Exterior}
variable {rayLeft : AllocationColumn K leaf.leftSlots → Ray}
variable {rayRight : AllocationColumn K leaf.rightSlots → Ray}
variable {wholeLeft : AllocationColumn K leaf.leftSlots → ℂ}
variable {wholeRight : AllocationColumn K leaf.rightSlots → ℂ}
variable {x : H → AllocationColumn K leaf.leftSlots → WithLp 2 (U × V)}
variable {y : H → AllocationColumn K leaf.rightSlots → WithLp 2 (U × V)}
variable {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
variable {exceptional : H → Prop}
variable {B : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
  rayLeft rayRight wholeLeft wholeRight x y b exceptional}

/-- A different proved factorization of the same two whole coefficients
retains every original binding field. In particular balancing does not
change the stored leaf or either Fourier kernel. -/
def refactor (binding : leaf.OrdinaryBinding B)
    (B' : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight wholeLeft wholeRight x y b exceptional) :
    leaf.OrdinaryBinding B' where
  rows := binding.rows
  rows_zero := binding.rows_zero
  left := binding.left
  right := binding.right
  exceptional := binding.exceptional
  rowWeight := binding.rowWeight
  leftCoefficient := binding.leftCoefficient
  rightCoefficient := binding.rightCoefficient
  leftPoint := binding.leftPoint
  rightPoint := binding.rightPoint

end ActualHybridLeaf.OrdinaryBinding

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.balancePlain_term
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.balancePlain_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPlainBalance.left_mul_ratio
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPlainBalance.right_mul_ratio_inv
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.balancedRectangles
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.OrdinaryBinding.refactor
