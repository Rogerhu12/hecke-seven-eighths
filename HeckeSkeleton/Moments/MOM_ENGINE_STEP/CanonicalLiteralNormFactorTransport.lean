import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileFactorExtraction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles

/-!
# The factor extraction on an actual first-stage atom table

The scales of each direct, main and pool table are the actual scales
after its first support extraction. Thus its positive profile factors
can be computed from the table itself, before the second extraction.
This operation commutes with the existing atlas and deletion transport.

The complete original coefficient is preserved. The old first scalar
and the positive residual factor become one scalar in the first plain
profile, to be extracted by the existing literal leaf construction.
The original Gauss normalizer is unchanged and is paid only once.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : Atoms (K := K) k)

def normProfileLeftFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor (d.scale₁ false) (d.scale₁ r) δ₁ δ₂

def normProfileRightFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor (d.scale₂ false) (d.scale₂ r) δ₁ δ₂

def normProfileSlotFactor (δ₁ δ₂ : ℝ) (i : Fin k) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    (d.base ^ d.length i) (d.base ^ d.length i) δ₁ δ₂

def normProfileFactor (δ₁ δ₂ : ℝ) : ℝ :=
  d.scaleProduct false ^ (-1 / 2 + δ₁ + δ₂)

theorem normProfileFactor_pos (δ₁ δ₂ : ℝ) : 0 < d.normProfileFactor δ₁ δ₂ :=
  Real.rpow_pos_of_pos (d.scaleProduct_pos false) _

theorem normProfileLeftFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) :
    0 < d.normProfileLeftFactor δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos (d.scale₁_pos false) (d.scale₁_pos r) δ₁ δ₂

theorem normProfileRightFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) :
    0 < d.normProfileRightFactor δ₁ δ₂ r :=
  CanonicalLiteralProfileScalars.plainFactor_pos (d.scale₂_pos false) (d.scale₂_pos r) δ₁ δ₂

theorem normProfileSlotFactor_pos (δ₁ δ₂ : ℝ) (i : Fin k) :
    0 < d.normProfileSlotFactor δ₁ δ₂ i :=
  CanonicalLiteralProfileScalars.plainFactor_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _) δ₁ δ₂

theorem normProfileFactor_product (δ₁ δ₂ : ℝ) (r : Bool)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    CanonicalLiteralProfileFactorExtraction.product
        (d.normProfileLeftFactor δ₁ δ₂) (d.normProfileRightFactor δ₁ δ₂)
        (d.normProfileSlotFactor δ₁ δ₂) r = d.normProfileFactor δ₁ δ₂ := by
  have hplain := CanonicalLiteralProfileScalars.plainFactor_product_of_equal_product
    (d.scale₁_pos false) (d.scale₂_pos false) (d.scale₁_pos r) (d.scale₂_pos r)
    hproduct δ₁ δ₂
  have hslot (i : Fin k) : d.normProfileSlotFactor δ₁ δ₂ i =
      (d.base ^ d.length i) ^ (-1 / 2 + δ₁ + δ₂) := by
    unfold normProfileSlotFactor CanonicalLiteralProfileScalars.plainFactor
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)]
    congr 1
    unfold CanonicalLiteralProfileScalars.exponent
    ring
  unfold CanonicalLiteralProfileFactorExtraction.product
    normProfileLeftFactor normProfileRightFactor
  rw [hplain]
  simp_rw [hslot]
  rw [Real.finsetProd_rpow Finset.univ _
    (fun i _ => Real.rpow_nonneg (zero_le_one.trans d.base_gt_one.le) _) _]
  exact (Real.mul_rpow (mul_pos (d.scale₁_pos false) (d.scale₂_pos false)).le
    (Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (zero_le_one.trans d.base_gt_one.le) _)
    (-1 / 2 + δ₁ + δ₂)).symm

def divideNormFactors (δ₁ δ₂ : ℝ) : Atoms (K := K) k :=
  d.divideProfileFactors (d.normProfileLeftFactor δ₁ δ₂)
    (d.normProfileRightFactor δ₁ δ₂) (d.normProfileSlotFactor δ₁ δ₂)

def redistributeNormFactors (δ₁ δ₂ : ℝ) : Atoms (K := K) k :=
  (d.divideNormFactors δ₁ δ₂).scale (d.normProfileFactor δ₁ δ₂ : ℂ)

theorem redistributeNormFactors_whole (δ₁ δ₂ : ℝ)
    (hproduct : d.centered = true →
      d.scale₁ true * d.scale₂ true = d.scale₁ false * d.scale₂ false)
    (i : AllocationColumn K k) :
    (d.redistributeNormFactors δ₁ δ₂).whole i = d.whole i := by
  have hc : d.centered = true →
      d.normProfileLeftFactor δ₁ δ₂ true * d.normProfileRightFactor δ₁ δ₂ true =
        d.normProfileLeftFactor δ₁ δ₂ false * d.normProfileRightFactor δ₁ δ₂ false := by
    intro h
    exact (CanonicalLiteralProfileScalars.plainFactor_product_of_equal_product
      (d.scale₁_pos false) (d.scale₂_pos false) (d.scale₁_pos true) (d.scale₂_pos true)
      (hproduct h) δ₁ δ₂).trans
        (CanonicalLiteralProfileScalars.plainFactor_product_of_equal_product
          (d.scale₁_pos false) (d.scale₂_pos false) (d.scale₁_pos false) (d.scale₂_pos false)
          rfl δ₁ δ₂).symm
  have he := d.whole_eq_profileFactor_mul
    (d.normProfileLeftFactor δ₁ δ₂) (d.normProfileRightFactor δ₁ δ₂)
    (d.normProfileSlotFactor δ₁ δ₂) (d.normProfileLeftFactor_pos δ₁ δ₂)
    (d.normProfileRightFactor_pos δ₁ δ₂) (d.normProfileSlotFactor_pos δ₁ δ₂) hc i
  rw [d.normProfileFactor_product δ₁ δ₂ false rfl] at he
  rw [redistributeNormFactors, scale_whole]
  exact he.symm

@[simp] theorem redistributeNormFactors_characters (δ₁ δ₂ : ℝ) :
    (d.redistributeNormFactors δ₁ δ₂).characters = d.characters := rfl

@[simp] theorem redistributeNormFactors_normalizer (δ₁ δ₂ : ℝ) :
    (d.redistributeNormFactors δ₁ δ₂).normalizer = d.normalizer := rfl

/-- The first common scalar is combined with the residual factor,
as an exact atom-record identity. No nonzero source is required. -/
theorem scale_redistributeNormFactors (c : ℂ) (δ₁ δ₂ : ℝ) :
    (d.scale c).redistributeNormFactors δ₁ δ₂ =
      (d.divideNormFactors δ₁ δ₂).scale (c * (d.normProfileFactor δ₁ δ₂ : ℂ)) := by
  unfold redistributeNormFactors divideNormFactors divideProfileFactors
    normProfileLeftFactor normProfileRightFactor normProfileSlotFactor
    normProfileFactor scaleProduct scale
  congr 1
  funext r I
  ring

theorem redistributeNormFactors_onAtlas (δ₁ δ₂ : ℝ)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    (d.redistributeNormFactors δ₁ δ₂).onAtlas T count =
      (d.onAtlas T count).redistributeNormFactors δ₁ δ₂ := by
  cases count
  rfl

theorem redistributeNormFactors_deleteMask (δ₁ δ₂ : ℝ)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.redistributeNormFactors δ₁ δ₂).deleteMask M =
      (d.deleteMask M).redistributeNormFactors δ₁ δ₂ := rfl

section SecondInput

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)

theorem secondInput_redistributeNormFactors (δ₁ δ₂ : ℝ) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).redistributeNormFactors δ₁ δ₂ =
      d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ := rfl

end SecondInput

namespace ProfileData

variable {d} (W : d.ProfileData)

def divideNormFactors (δ₁ δ₂ : ℝ) : (d.divideNormFactors δ₁ δ₂).ProfileData :=
  W.divideProfileFactors (d.normProfileLeftFactor δ₁ δ₂)
    (d.normProfileRightFactor δ₁ δ₂) (d.normProfileSlotFactor δ₁ δ₂)

def redistributeNormFactors (δ₁ δ₂ : ℝ) : (d.redistributeNormFactors δ₁ δ₂).ProfileData :=
  (W.divideNormFactors δ₁ δ₂).scale (d.normProfileFactor δ₁ δ₂ : ℂ)

end ProfileData

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def divideNormFactors (W : d.SupportData excluded) (δ₁ δ₂ : ℝ) :
    (d.divideNormFactors δ₁ δ₂).SupportData excluded :=
  W.divideProfileFactors (d.normProfileLeftFactor δ₁ δ₂)
    (d.normProfileRightFactor δ₁ δ₂) (d.normProfileSlotFactor δ₁ δ₂)

def redistributeNormFactors (W : d.SupportData excluded) (δ₁ δ₂ : ℝ) :
    (d.redistributeNormFactors δ₁ δ₂).SupportData excluded :=
  (W.divideNormFactors δ₁ δ₂).scale (d.normProfileFactor δ₁ δ₂ : ℂ)

end SupportData
end CanonicalLiteralRectangles.Atoms

namespace CanonicalLiteralActualProfiles.ProfileSupport

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {excluded : Finset (Ideal (𝓞 K))}

/-- This is an internally constructed return value for the same
actual atlas. It is not a new profile-window hypothesis. -/
def redistributeNormFactors (E : ProfileSupport d excluded) (δ₁ δ₂ : ℝ) :
    ProfileSupport (d.redistributeNormFactors δ₁ δ₂) excluded where
  profiles := E.profiles.redistributeNormFactors δ₁ δ₂
  support := E.support.redistributeNormFactors δ₁ δ₂

end CanonicalLiteralActualProfiles.ProfileSupport
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.normProfileFactor_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributeNormFactors_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.scale_redistributeNormFactors
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributeNormFactors_onAtlas
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_redistributeNormFactors
