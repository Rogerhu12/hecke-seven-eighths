import ThetaGlobal.GlobalAngular
import ThetaGlobal.GlobalProjectRadial
import HeckeGeneral.Characters.InfinityType
import DedekindZetaZeroFree.Theta.Periods.OddUpperAverageVanishing

/-!
# Actual complex rotations and the compact sheet-quotient integral

The local rotation below has actual Hecke-character value `-1` for every
nonzero angular weight, including even weights.  The inverse local period
character has the same value.  The rotation lies in the sixth powers, so
it preserves the power-class cutoff and every Hilbert twist.

`quotient_weighted_constantTerm_zero` applies the existing invariant
sheet Haar construction to this rotation.  Its remaining radial hypothesis
is a pointwise law for the chosen constant-term function, not an assumed
vanishing integral or a reflection theorem.

Project-facing source; see the separate compilation-status report.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalProjectAngular

open NumberField HeckeGeneral.Characters
open DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open MeasureTheory
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

def complexRotation (θ : HeckeCharacter F) (v : InfinitePlace F) (hv : v.IsComplex) :
    v.Completionˣ :=
  complexUnitsToCompletion hv (complexCircleEmbedding
    (GlobalAngular.angularRotation (heckeComplexWeight F v hv θ)))

theorem complexRotation_norm (θ : HeckeCharacter F)
    (v : InfinitePlace F) (hv : v.IsComplex) :
    ‖(complexRotation θ v hv : v.Completion)‖ = 1 := by
  rw [complexRotation, norm_complexUnitsToCompletion, norm_complexCircleEmbedding]

/-- Exact value `-1`, so the existing odd-integral theorem applies even
when the angular weight itself is even. -/
theorem complexRotation_character (θ : HeckeCharacter F)
    (v : InfinitePlace F) (hv : v.IsComplex)
    (hk : heckeComplexWeight F v hv θ ≠ 0) :
    (infiniteComponent F v θ (complexRotation θ v hv) : ℂ) = -1 := by
  have hk' : (heckeComplexWeight F v hv θ : ℝ) ≠ 0 := by exact_mod_cast hk
  have he : (heckeComplexWeight F v hv θ : ℝ) *
      (Real.pi / (heckeComplexWeight F v hv θ : ℝ)) = Real.pi := by
    rw [mul_comm, div_mul_cancel₀ _ hk']
  change (complexHeckeComponent F v hv θ (complexCircleEmbedding
    (GlobalAngular.angularRotation (heckeComplexWeight F v hv θ))) : ℂ) = -1
  rw [complexCharacter_circle]
  change ((GlobalAngular.angularRotation (heckeComplexWeight F v hv θ) ^
    heckeComplexWeight F v hv θ : Circle) : ℂ) = -1
  rw [GlobalAngular.angularRotation, ← Circle.exp_intCast_mul, he,
    Circle.coe_exp, Complex.exp_pi_mul_I]

theorem complexRotation_inverse_character (θ : HeckeCharacter F)
    (v : InfinitePlace F) (hv : v.IsComplex)
    (hk : heckeComplexWeight F v hv θ ≠ 0) :
    (infiniteComponent F v θ (complexRotation θ v hv) : ℂ)⁻¹ = -1 := by
  rw [complexRotation_character θ v hv hk]
  norm_num

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

def sheetWeight (L : R.A.G →* ℂ) (B : Subgroup R.A.V) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ B then 1 else 0) * (L y)⁻¹

theorem sheetWeight_rotation (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (w : InfinitePlace F) (z : w.Completionˣ)
    (hL : L (IdeleInsertion.infiniteInsertion R.A w z) = -1) (y : R.A.G) :
    sheetWeight R L B (IdeleInsertion.infiniteInsertion R.A w z * y) =
      -sheetWeight R L B y := by
  unfold sheetWeight
  rw [map_mul, IdeleInsertion.insertion_class_eq_one R, one_mul, map_mul, hL]
  simp only [neg_one_mul, inv_neg]
  ring

/-- Exact compact-quotient angular cancellation with the actual sheet
measure.  Descent is recorded by `hprojection`; radial covariance is
recorded by `hconstant`. -/
theorem quotient_weighted_constantTerm_zero
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (L : R.A.G →* ℂ) (B : Subgroup R.A.V)
    (z : w.Completionˣ) (hz : ‖(z : w.Completion)‖ = 1)
    (hL : L (IdeleInsertion.infiniteInsertion R.A w z) = -1)
    (constantTerm : R.A.G → ℂ) (f : SheetQuotient R.A l → ℂ)
    (hf : Integrable f (sheetQuotientHaar R.A w μG l))
    (hprojection : ∀ y : Sheet R.A l,
      f (sheetProjection R.A l y) = sheetWeight R L B y.val * constantTerm y.val)
    (hconstant : ∀ y, constantTerm (IdeleInsertion.infiniteInsertion R.A w z * y) =
      constantTerm y) :
    (∫ q, f q ∂sheetQuotientHaar R.A w μG l) = 0 := by
  let t : R.A.G1 := ⟨IdeleInsertion.infiniteInsertion R.A w z,
    IdeleInsertion.norm_insertion_one R w z hz⟩
  apply IdeleInsertion.quotient_integral_zero_of_odd R.A w μG l t f hf
  intro y y' hy'
  rw [hprojection, hprojection]
  change sheetWeight R L B y'.val * constantTerm y'.val =
    -(sheetWeight R L B y.val * constantTerm y.val)
  rw [hy', sheetWeight_rotation R L B w z hL, hconstant]
  ring

end ThetaGlobal.GlobalProjectAngular
