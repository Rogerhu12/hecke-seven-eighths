import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlasAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPlainBalance

/-!
# The two original constant scalars outside the profile family

The first common extraction and the pool reciprocity scalar are
independent of every remaining column. Their precise product is
separated from the actual two-stage atom table here. This equality is
proved from the individual profile operations, including all ramified
zeros and the complete centered subtraction.

Both scalars may vanish. No division is used in their normal form.
Only a genuinely nonzero original coefficient permits the inverse
rescaling used by the live normalization family. Atlas transport,
second common extraction and full deletion preserve the same scalar.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

theorem scale_scale (c e : ℂ) : (d.scale c).scale e = d.scale (c * e) := by
  unfold scale
  congr 1
  funext r I
  ring

theorem scale_one : d.scale 1 = d := by
  unfold scale
  simp only [one_mul]

theorem scale_inv_cancel (c : ℂ) (hc : c ≠ 0) :
    (d.scale c).scale c⁻¹ = d := by
  rw [d.scale_scale c c⁻¹, mul_inv_cancel₀ hc, d.scale_one]

theorem scale_addGauss (c : ℂ) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) :
    (d.scale c).addGauss G₁ G₂ G h₁ h₂ hG =
      (d.addGauss G₁ G₂ G h₁ h₂ hG).scale c := by
  unfold scale addGauss
  congr 1
  funext r I
  exact mul_assoc _ _ _

theorem scale_normPower (c : ℂ) (δ : ℝ) :
    (d.scale c).normPower δ = (d.normPower δ).scale c := by
  unfold scale normPower
  congr 1
  funext r I
  exact mul_assoc _ _ _

theorem scale_twoStageNorms (c : ℂ) (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ i, 0 < G i) (δ₁ δ₂ : ℝ) :
    (d.scale c).twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂ =
      (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).scale c := by
  unfold twoStageNorms
  rw [d.scale_addGauss, scale_normPower, scale_normPower, scale_normPower]

theorem scale_extract (c : ℂ) {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.scale c).extract b = (d.extract b).scale c := rfl

theorem scale_commonScalar (c : ℂ) {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.scale c).commonScalar b = d.commonScalar b := rfl

theorem scale_onAtlas (c : ℂ) {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    (d.scale c).onAtlas T count = (d.onAtlas T count).scale c := by
  cases count
  rfl

theorem scale_deleteMask (c : ℂ) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.scale c).deleteMask M = (d.deleteMask M).scale c := rfl

theorem scale_balancePlain (c : ℂ) (balance : Bool → ℝ) :
    (d.scale c).balancePlain balance = (d.balancePlain balance).scale c := by
  unfold scale balancePlain
  congr 1
  funext r I
  exact mul_assoc _ _ _

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

theorem scale_movingSingleton (c : ℂ) (I : A.Exterior) (a : A.R)
    (ha : A.Generates I a) :
    (d.scale c).movingSingleton P R I a ha =
      (d.movingSingleton P R I a ha).scale c := rfl

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- This table retains both Mellin factors, the actual Gauss scales
and all three original arithmetic phases. Only the two column-constant
profile multipliers are outside it. -/
def secondInputCore (firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) b.keep.card :=
  let e := d.extract b
  let n := e.twoStageNorms (e.scale₁ false) (e.scale₂ false)
    (fun i => e.base ^ e.length i) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _) δ₁ δ₂
  ((n.movingSingleton P R firstFixed firstElement hfirst).movingSingleton
    P R poolFixed poolElement hpool).movingSingleton P R unitFixed unitElement hunit

/-- The exact first common scalar times the original pool scalar.
The latter is also present on the main and direct paths with power one. -/
def secondInputScalar (power : A.Exterior) (firstElement : A.R) (δ₁ : ℝ) : ℂ :=
  d.commonScalar b * (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)

/-- An identity of the actual atom tables, proved before any sum or
norm. It therefore preserves every zero coefficient and works when
the extracted constant itself is zero. -/
theorem secondInput_eq_scale_core
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ =
      (d.secondInputCore P R b firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
          (d.secondInputScalar (σ := σ) b power firstElement δ₁) := by
  unfold secondInput secondInputCore secondInputScalar
  dsimp only [firstExtracted]
  rw [scale_twoStageNorms, scale_movingSingleton, scale_movingSingleton,
    scale_movingSingleton, scale_scale]

theorem secondInput_whole_eq_scalar_core
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (i : AllocationColumn K b.keep.card) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i =
      d.secondInputScalar (σ := σ) b power firstElement δ₁ *
        (d.secondInputCore P R b firstFixed poolFixed unitFixed
          firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i := by
  rw [d.secondInput_eq_scale_core P R b, scale_whole]

theorem secondInputScalar_ne_zero_of_whole_ne_zero
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (i : AllocationColumn K b.keep.card)
    (hne : (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).whole i ≠ 0) :
    d.secondInputScalar (σ := σ) b power firstElement δ₁ ≠ 0 := by
  rw [d.secondInput_whole_eq_scalar_core P R b] at hne
  exact left_ne_zero_of_mul hne

/-- Inverse rescaling is used only after a true live coefficient has
proved that the original constant is nonzero. -/
theorem secondInput_scale_inverse
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
    (hc : d.secondInputScalar (σ := σ) b power firstElement δ₁ ≠ 0) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale
        (d.secondInputScalar (σ := σ) b power firstElement δ₁)⁻¹ =
      d.secondInputCore P R b firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ := by
  rw [d.secondInput_eq_scale_core P R b, scale_inv_cancel _ _ hc]

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_eq_scale_core
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInputScalar_ne_zero_of_whole_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_scale_inverse
