import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCentralCoefficientBound
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

/-!
# Sharp original coefficients from the actual moving arithmetic recipe

The fixed moving character and both original deletion ideals remain in
the arithmetic atoms. Their norms are bounded internally from the actual
Hecke coefficients and the zero-or-one coprimality mask. Only the original
individual profile bounds are used to obtain the centered whole-column
bound, with its exact negative central exponent.

The finite Schwartz orders and slot cap precede the original moving
profiles. The last theorem takes their single-profile seminorm windows;
it takes no column, terminal, parent-source or child-mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}

private theorem original_moving_arithmetic_profile_norm_le
    (c f : ℂ) (B : ℝ) (hc : ‖c‖ ≤ 1) (hf : ‖f‖ ≤ B) :
    ‖c * f‖ ≤ B := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hc hf (norm_nonneg _) zero_le_one

namespace CompleteMovingRowRecipe

variable (Q : CompleteMovingRowRecipe A P R data)

theorem arithmeticAtoms_left_norm_le_one (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ‖(Q.arithmeticAtoms ξ).leftArithmetic I‖ ≤ 1 := by
  change ‖heckeIdealCoefficient K ((data ξ).plainBackground *
    (Q.correction * Q.moving.character)) I *
      (if IsCoprime I.val Q.arithmeticMask.val then (1 : ℂ) else 0)‖ ≤ 1
  by_cases hI : IsCoprime I.val Q.arithmeticMask.val
  · simpa only [if_pos hI, mul_one] using
      norm_heckeIdealCoefficient_le_one K
        ((data ξ).plainBackground * (Q.correction * Q.moving.character)) I
  · simp only [if_neg hI, mul_zero, norm_zero, zero_le_one]

theorem arithmeticAtoms_right_norm_le_one (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ‖(Q.arithmeticAtoms ξ).rightArithmetic I‖ ≤ 1 :=
  Q.arithmeticAtoms_left_norm_le_one ξ I

theorem arithmeticAtoms_prime_norm_le_one (ξ : X)
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    ‖(Q.arithmeticAtoms ξ).primeArithmetic i p‖ ≤ 1 := by
  change ‖primeCoefficient K ((data ξ).slotCoefficient i *
    (Q.correction * Q.moving.character)) p *
      (if IsCoprime p.asIdeal Q.arithmeticMask.val then (1 : ℂ) else 0)‖ ≤ 1
  by_cases hp : IsCoprime p.asIdeal Q.arithmeticMask.val
  · simpa only [if_pos hp, mul_one] using
      norm_primeCoefficient_le_one K
        ((data ξ).slotCoefficient i * (Q.correction * Q.moving.character)) p
  · simp only [if_neg hp, mul_zero, norm_zero, zero_le_one]

/-- The central normalization is paid by the original two plain scales
and every original slot. The actual arithmetic atoms are constructed by
the moving-row recipe, including their fixed moving character and masks. -/
theorem coefficient_norm_le_original_profiles
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (B : ℝ) (hB : 1 ≤ B)
    (hleft : ∀ x, ‖W.left ξ t x‖ ≤ B)
    (hright : ∀ x, ‖W.right ξ t x‖ ≤ B)
    (hprime : ∀ i x, ‖((data ξ).geometry.slots i).profile t x‖ ≤ B)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).Column)
    (hv : v ∈ (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).columns) :
    ‖(((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).values Y₁ Y₂).coefficient
        centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) / 2) := by
  exact ParentConstantAtoms.coefficient_norm_le_original_central_cap
    ((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t)
    cap hcap B hB hZ
    (fun comparison I _ => original_moving_arithmetic_profile_norm_le _ _ B
      (Q.arithmeticAtoms_left_norm_le_one ξ I)
      (hleft (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))))
    (fun comparison I _ => original_moving_arithmetic_profile_norm_le _ _ B
      (Q.arithmeticAtoms_right_norm_le_one ξ I)
      (hright (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))))
    (fun i p _ => original_moving_arithmetic_profile_norm_le _ _ B
      (Q.arithmeticAtoms_prime_norm_le_one ξ i p)
      (hprime i ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length)))
    centered hY₁ hcomparison v hv

/-- Finite seminorms of the individual original profiles suffice. The
two literal centered rectangles and all original prime occurrences are
retained by the preceding theorem. No hypothesis concerns their product. -/
theorem coefficient_norm_le_original_seminorms
    (W : NormProfileRecipe data) (ξ : X)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (hZ : 0 < Z)
    (cap : ℕ) (hcap : (data ξ).geometry.slotCount ≤ cap)
    (orders : Finset (ℕ × ℕ)) (B : ℝ) (hB : 1 ≤ B)
    (left right : 𝓢(ℝ, ℂ)) (prime : Fin (data ξ).geometry.slotCount → 𝓢(ℝ, ℂ))
    (hleft : ∀ x, W.left ξ t x = left x)
    (hright : ∀ x, W.right ξ t x = right x)
    (hprime : ∀ i x, ((data ξ).geometry.slots i).profile t x = prime i x)
    (hleftBound : (OriginalProfileAtomBounds.profileOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) left ≤ B)
    (hrightBound : (OriginalProfileAtomBounds.profileOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) right ≤ B)
    (hprimeBound : ∀ i, (OriginalProfileAtomBounds.profileOrders orders).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (prime i) ≤ B)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).Column)
    (hv : v ∈ (((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).raw Y₁ Y₂).columns) :
    ‖(((Q.arithmeticAtoms ξ).constantAtoms (W.at ξ) a Z t).values Y₁ Y₂).coefficient
        centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + (data ξ).geometry.totalLength) / 2) := by
  apply Q.coefficient_norm_le_original_profiles W ξ a Z t Y₁ Y₂ hZ cap hcap B hB
    (fun x => ?_) (fun x => ?_) (fun i x => ?_) centered hY₁ hcomparison v hv
  · rw [hleft]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders left x).trans hleftBound
  · rw [hright]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders right x).trans hrightBound
  · rw [hprime]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (prime i) x).trans (hprimeBound i)

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.arithmeticAtoms_left_norm_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.arithmeticAtoms_prime_norm_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.coefficient_norm_le_original_profiles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.coefficient_norm_le_original_seminorms
