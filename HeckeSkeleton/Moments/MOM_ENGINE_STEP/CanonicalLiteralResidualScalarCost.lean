import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstScalarCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralGaussScale
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileFactorExtraction

/-!
# Pay the complete first residual profile factor in the original scalar

The positive factor extracted from every retained original profile has
product `residualScale ^ (-1/2 + δ₁ + δ₂)`.  It must be charged once in
the original row scalar, before the normalized children are constructed.

The complete frozen ideal supplies the complementary square-root
denominator.  The actual pool power divides this same ideal, so its
tilt is paid without weakening the total original degree.  The final
seed theorem derives the residual scale lower bound directly from the
original prime window `(1,2)`; it assumes no child, kernel, or terminal
estimate.  Ordinary and centered sources use the same false-rectangle
scale, whose product is always the original `Z^(n₁+n₂)`.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralResidualScalarCost

/-- The full frozen norm pays the pool tilt while retaining the
original total degree.  The negative exponent reverses precisely the
actual residual-scale lower bound. -/
theorem residual_tilt_le
    {Z residual frozen power total δ₁ δ₂ : ℝ}
    (hZ : 0 < Z) (hresidual : 0 < residual) (hfrozen : 1 ≤ frozen)
    (hpower : 0 ≤ power) (hdivides : power ≤ frozen)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : Z ^ total ≤ residual * frozen) :
    residual ^ (-1 / 2 + δ₁ + δ₂) * power ^ δ₁ / Real.sqrt frozen ≤
      Z ^ (total * (-1 / 2 + δ₁ + δ₂)) := by
  have hfrozenpos : 0 < frozen := zero_lt_one.trans_le hfrozen
  have htilt : power ^ δ₁ ≤ frozen ^ (δ₁ + δ₂) :=
    (Real.rpow_le_rpow hpower hdivides hδ₁).trans
      (Real.rpow_le_rpow_of_exponent_le hfrozen (by linarith))
  calc
    _ ≤ residual ^ (-1 / 2 + δ₁ + δ₂) * frozen ^ (δ₁ + δ₂) /
        Real.sqrt frozen :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htilt (Real.rpow_nonneg hresidual.le _))
        (Real.sqrt_nonneg _)
    _ = (residual * frozen) ^ (-1 / 2 + δ₁ + δ₂) := by
      rw [mul_div_assoc, Real.sqrt_eq_rpow, ← Real.rpow_sub hfrozenpos]
      have he : δ₁ + δ₂ - 1 / 2 = -1 / 2 + δ₁ + δ₂ := by ring
      rw [he, ← Real.mul_rpow hresidual.le hfrozenpos.le]
    _ ≤ (Z ^ total) ^ (-1 / 2 + δ₁ + δ₂) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hZ _) hproduct (by linarith)
    _ = Z ^ (total * (-1 / 2 + δ₁ + δ₂)) := (Real.rpow_mul hZ.le _ _).symm

end CanonicalLiteralResidualScalarCost

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (C : A.GeneralArithmeticContext σ η htrace)

include C

/-- The newly extracted profile factor and the original common/pool
scalar are paid together.  The frozen denominator is not discarded
before this estimate. -/
theorem secondInputResidualScalar_norm_le_original_atoms
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (I power : A.Exterior) (firstElement : A.R) (δ₁ δ₂ total : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hpower : power.val ∣ I.val)
    (hmask : d.characters.MaskIndicator) (cap : ℕ) (B : ℝ)
    (hcap : k ≤ cap) (hB : 1 ≤ B)
    (hcost : ∀ i ∈ Finset.univ \ b.keep, d.primeAtomCost i (b.witness.2 i) ≤ B)
    (hscale : d.base ^ (total - idealLogLength d.base I.val) ≤
      (d.extract b).scaleProduct false) :
    ‖(d.twoStageProfileFactor b δ₁ δ₂ : ℂ) *
        d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤
      Real.sqrt (B ^ cap) * d.base ^ (total * (-1 / 2 + δ₁ + δ₂)) := by
  have hz : 0 < d.base := zero_lt_one.trans d.base_gt_one
  have hnorm : A.exteriorNorm power ≤ (Ideal.absNorm I.val : ℝ) :=
    ideal_norm_le_of_dvd I.property.1 hpower
  have hone : (1 : ℝ) ≤ Ideal.absNorm I.val := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)
  have hproduct : d.base ^ total ≤
      (d.extract b).scaleProduct false * (Ideal.absNorm I.val : ℝ) := by
    calc
      _ = d.base ^ (total - idealLogLength d.base I.val) *
          (Ideal.absNorm I.val : ℝ) := by
        rw [← rpow_idealLogLength d.base d.base_gt_one I.val I.property.1,
          ← Real.rpow_add hz, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)
  have htilt := CanonicalLiteralResidualScalarCost.residual_tilt_le
    hz ((d.extract b).scaleProduct_pos false) hone (A.exteriorNorm_pos power).le
    hnorm hδ₁ hδ₂ hδ hproduct
  change ‖(((d.extract b).scaleProduct false ^ (-1 / 2 + δ₁ + δ₂) : ℝ) : ℂ) *
    d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤ _
  rw [norm_mul, Complex.norm_of_nonneg
    (Real.rpow_nonneg ((d.extract b).scaleProduct_pos false).le _)]
  change (d.extract b).scaleProduct false ^ (-1 / 2 + δ₁ + δ₂) *
      ‖d.secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤ _
  calc
    _ ≤ (d.extract b).scaleProduct false ^ (-1 / 2 + δ₁ + δ₂) *
        (Real.sqrt (B ^ cap) * A.exteriorNorm power ^ δ₁ /
          Real.sqrt (Ideal.absNorm I.val : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (d.secondInputScalar_norm_le_original_atoms C b I power firstElement δ₁
          hI hmask cap B hcap hB hcost)
        (Real.rpow_nonneg ((d.extract b).scaleProduct_pos false).le _)
    _ = Real.sqrt (B ^ cap) *
        ((d.extract b).scaleProduct false ^ (-1 / 2 + δ₁ + δ₂) *
          A.exteriorNorm power ^ δ₁ / Real.sqrt (Ideal.absNorm I.val : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htilt (Real.sqrt_nonneg _)

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

/-- This is the same scale product whose factors have just been
extracted.  The original open prime window proves the lower bound,
including repeated removed occurrences and the zero-slot case. -/
theorem literalOriginalAtoms_extract_scaleProduct_lower
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots support)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {B : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) B)
    (hprime : ∀ i, Function.support (profiles.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2) :
    Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength -
      idealLogLength Z
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)) ≤
      ((seed).extract b).scaleProduct false := by
  have hp (i) (_hi : i ∈ Finset.univ \ b.keep) :
      (seed).base ^ (seed).length i ≤ (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) := by
    have hslot := (Finset.mem_filter.mp (b.witness_slots i)).1
    change b.witness.2 i ∈
      (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorSlots i at hslot
    exact profiles.primeScale_le_norm_of_open_prime_window Z t (zero_lt_one.trans hZ)
      hprime i (b.witness.2 i) (Finset.mem_filter.mp hslot).1
  have hproduct : (seed).scale₁ false * (seed).scale₂ false = (seed).base ^ (a.n₁ + a.n₂) :=
    (Real.rpow_add (zero_lt_one.trans hZ) a.n₁ a.n₂).symm
  have h := b.residualGaussScale_lower_one (seed).base (seed).base_gt_one (seed).length
    ((seed).scale₁ false) ((seed).scale₂ false) (a.n₁ + a.n₂)
    ((seed).scale₁_pos false).le ((seed).scale₂_pos false).le hproduct hp
  simpa only [SlotGeometry.totalLength] using h

variable (C : A.GeneralArithmeticContext σ η htrace)

include C

/-- The complete scalar cost from raw individual profiles.  No
moving quantity is hidden in the fixed original atom budget. -/
theorem literalOriginalAtoms_residualScalar_norm_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (original.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots support)
    (I power : A.Exterior) (firstElement : A.R) (δ₁ δ₂ : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (hpower : power.val ∣ I.val) :
    ‖((seed).twoStageProfileFactor b δ₁ δ₂ : ℂ) *
        (seed).secondInputScalar (σ := σ) b power firstElement δ₁‖ ≤
      Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap) *
        Z ^ ((a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (-1 / 2 + δ₁ + δ₂)) := by
  apply (seed).secondInputResidualScalar_norm_le_original_atoms C b I power firstElement
    δ₁ δ₂ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) hδ₁ hδ₂ hδ hI hpower
    (Q.literalSourceCharacters_maskIndicator ξ) cap
    (CanonicalLiteralFirstScalarCost.atomBudget annulus B) hcap
    (CanonicalLiteralFirstScalarCost.atomBudget_one annulus B)
  · intro i _
    exact (Q.literalOriginalAtoms_primeAtomCost_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original hzero ht annulus hannulus hwindow i (b.witness.2 i)).trans
      (CanonicalLiteralFirstScalarCost.atomBudget_atom annulus B)
  · simpa only [hI] using Q.literalOriginalAtoms_extract_scaleProduct_lower
      ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ b original hprime

/-- Both literal column scalars restore the full original decay.
The only loss is the two explicitly chosen Mellin tilts. -/
theorem literalOriginalAtoms_residualScalar_pair_norm_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ i, Function.support (original.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    {supportL supportR : Finset (Ideal (𝓞 K))}
    (bL : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots supportL)
    (bR : SupportCartesianBranch (seed).plain₁ (seed).plain₂ (seed).slots supportR)
    (IL IR powerL powerR : A.Exterior) (elementL elementR : A.R) (δ₁ δ₂ : ℝ)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (hIL : frozenSourceIdeal bL.plainDivisor₁ bL.plainDivisor₂ bL.keep bL.witness.2 = IL.val)
    (hIR : frozenSourceIdeal bR.plainDivisor₁ bR.plainDivisor₂ bR.keep bR.witness.2 = IR.val)
    (hpowerL : powerL.val ∣ IL.val) (hpowerR : powerR.val ∣ IR.val) :
    ‖((seed).twoStageProfileFactor bL δ₁ δ₂ : ℂ) *
        (seed).secondInputScalar (σ := σ) bL powerL elementL δ₁‖ *
      ‖((seed).twoStageProfileFactor bR δ₁ δ₂ : ℂ) *
        (seed).secondInputScalar (σ := σ) bR powerR elementR δ₁‖ ≤
      (CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap *
        Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) +
          2 * (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (δ₁ + δ₂)) := by
  have hL := Q.literalOriginalAtoms_residualScalar_norm_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ C original hzero ht hprime annulus hannulus hwindow cap hcap
    bL IL powerL elementL δ₁ δ₂ hδ₁ hδ₂ hδ hIL hpowerL
  have hR := Q.literalOriginalAtoms_residualScalar_norm_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ C original hzero ht hprime annulus hannulus hwindow cap hcap
    bR IR powerR elementR δ₁ δ₂ hδ₁ hδ₂ hδ hIR hpowerR
  have h := mul_le_mul hL hR (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hZ.le) _))
  apply h.trans_eq
  calc
    _ = (Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap) *
        Real.sqrt ((CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap)) *
      (Z ^ ((a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (-1 / 2 + δ₁ + δ₂)) *
        Z ^ ((a.n₁ + a.n₂ + (data ξ).geometry.totalLength) * (-1 / 2 + δ₁ + δ₂))) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt (pow_nonneg
        (zero_le_one.trans (CanonicalLiteralFirstScalarCost.atomBudget_one annulus B)) cap),
        ← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 2
      ring

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralResidualScalarCost.residual_tilt_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInputResidualScalar_norm_le_original_atoms
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_extract_scaleProduct_lower
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_residualScalar_pair_norm_le
