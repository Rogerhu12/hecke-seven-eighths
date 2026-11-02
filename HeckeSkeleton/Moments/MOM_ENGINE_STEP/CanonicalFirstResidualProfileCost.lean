import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralResidualScalarCost

/-!
# The original first Poisson weight and the residual profile scalar

The first row weight alone does not contain the original total-degree
decay. That decay is supplied by the positive profile factors extracted
before constructing either normalized child. This file combines the
two literal quantities, preserving both the actual mask divisor and
the active Gauss modulus.

The resulting main exponent is `m - total - mask - active`, exactly
`(m + q) - (total + q + mask + active)`. The two Mellin tilts remain
explicit, and the final theorem derives the column-scalar estimate
from the original individual profile windows and frozen ideals.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalFirstResidualProfileCost

/-- All moving powers left after the two exact main exponents cancel. -/
def tiltError (m total mask active δ₁ δ₂ : ℝ) : ℝ :=
  δ₁ * (mask + active - m) + 2 * total * (δ₁ + δ₂)

theorem combined_exponent (m q total mask active δ₁ δ₂ : ℝ) :
    (m - mask - active + δ₁ * (mask + active - m)) +
        (-total + 2 * total * (δ₁ + δ₂)) =
      (m + q) - (total + q + mask + active) +
        tiltError m total mask active δ₁ δ₂ := by
  unfold tiltError
  ring

/-- Original numerical length bounds pay the small tilts uniformly.
The actual mask and active lengths have not been replaced inside the
main exponent. -/
theorem tiltError_le {m total mask active bound δ₁ δ₂ : ℝ}
    (hm : 0 ≤ m) (hbound : 0 ≤ bound)
    (htotal : total ≤ bound) (hmask : mask ≤ bound) (hactive : active ≤ bound)
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) :
    tiltError m total mask active δ₁ δ₂ ≤ 4 * bound * (δ₁ + δ₂) := by
  have hfirst : δ₁ * (mask + active - m) ≤ δ₁ * (2 * bound) :=
    mul_le_mul_of_nonneg_left (by linarith) hδ₁
  have hsecond : 2 * total * (δ₁ + δ₂) ≤ 2 * bound * (δ₁ + δ₂) :=
    mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hδ₁ hδ₂)
  have hremaining : 0 ≤ bound * δ₂ := mul_nonneg hbound hδ₂
  unfold tiltError
  nlinarith

/-- A scalar combination used only after the individual first-column
scalars have been proved from their original atoms. -/
theorem combined_profile_le
    {Z m q total mask active δ₁ δ₂ field atomCost pairCost : ℝ}
    (hZ : 0 < Z) (hfield : 0 ≤ field)
    (hpair : pairCost ≤ atomCost * Z ^ (-total + 2 * total * (δ₁ + δ₂))) :
    (field * Z ^ (m - mask - active + δ₁ * (mask + active - m))) * pairCost ≤
      (field * atomCost) *
        Z ^ ((m + q) - (total + q + mask + active) +
          tiltError m total mask active δ₁ δ₂) := by
  calc
    _ ≤ (field * Z ^ (m - mask - active + δ₁ * (mask + active - m))) *
        (atomCost * Z ^ (-total + 2 * total * (δ₁ + δ₂))) :=
      mul_le_mul_of_nonneg_left hpair
        (mul_nonneg hfield (Real.rpow_nonneg hZ.le _))
    _ = (field * atomCost) *
        (Z ^ (m - mask - active + δ₁ * (mask + active - m)) *
          Z ^ (-total + 2 * total * (δ₁ + δ₂))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZ, combined_exponent m q total mask active δ₁ δ₂]

end CanonicalFirstResidualProfileCost

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalFirstLog

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The exact first Poisson profile weight on its original divisor.
Both norm identities concern actual arithmetic elements. -/
theorem rowWeightBound_eq_original_lengths
    (r : OrbitalGaussColumn K S Γ) (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (Z m mask active δ : ℝ) (hZ : 0 < Z)
    (hradius : radius.val = Z ^ (-m))
    (hmask : (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ mask)
    (hactive : (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      ⟨r.modulus, r.nonzero⟩).val = Z ^ active) :
    rowWeightBound r radius D δ =
      orbitalFieldFactor K * Z ^ (m - mask - active + δ * (mask + active - m)) := by
  rw [rowWeightBound_eq]
  change orbitalFieldFactor K *
      (radius.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val) ^ (δ - 1) *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨r.modulus, r.nonzero⟩).val ^ (δ - 1) = _
  rw [hradius, hmask, hactive, ← Real.rpow_add hZ,
    ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le, mul_assoc, ← Real.rpow_add hZ]
  have he : (-m + mask) * (δ - 1) + active * (δ - 1) =
      m - mask - active + δ * (mask + active - m) := by ring
  rw [he]

/-- Combine the actual first Poisson weight with the complete scalar
pair. The scalar estimate is derived from raw atoms at the public
original-source entry point below. -/
theorem rowWeightBound_mul_scalarPair_le
    (r : OrbitalGaussColumn K S Γ) (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (Z m q total mask active δ₁ δ₂ atomCost : ℝ) (leftScalar rightScalar : ℂ)
    (hZ : 0 < Z) (hradius : radius.val = Z ^ (-m))
    (hmask : (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ mask)
    (hactive : (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      ⟨r.modulus, r.nonzero⟩).val = Z ^ active)
    (hpair : ‖leftScalar‖ * ‖rightScalar‖ ≤
      atomCost * Z ^ (-total + 2 * total * (δ₁ + δ₂))) :
    rowWeightBound r radius D δ₁ * (‖leftScalar‖ * ‖rightScalar‖) ≤
      (orbitalFieldFactor K * atomCost) *
        Z ^ ((m + q) - (total + q + mask + active) +
          CanonicalFirstResidualProfileCost.tiltError m total mask active δ₁ δ₂) := by
  rw [rowWeightBound_eq_original_lengths r radius D Z m mask active δ₁
    hZ hradius hmask hactive]
  exact CanonicalFirstResidualProfileCost.combined_profile_le hZ
    (orbitalFieldFactor_nonneg K) hpair

end CanonicalFirstLog

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

/-- The first profile cost is proved from the actual original source.
The two complete frozen ideals, including any pool powers, supply the
scalar pair; no estimate for a whole transformed source is an input. -/
theorem literalOriginalAtoms_first_combined_profile_le
    (C : A.GeneralArithmeticContext σ η htrace)
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
    (hpowerL : powerL.val ∣ IL.val) (hpowerR : powerR.val ∣ IR.val)
    (r : OrbitalGaussColumn K A.Sf Γ) (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum A.R)) (m q mask active : ℝ)
    (hradius : radius.val = Z ^ (-m))
    (hmask : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val = Z ^ mask)
    (hactive : (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨r.modulus, r.nonzero⟩).val = Z ^ active) :
    CanonicalFirstLog.rowWeightBound r radius D δ₁ *
        (‖((seed).twoStageProfileFactor bL δ₁ δ₂ : ℂ) *
            (seed).secondInputScalar (σ := σ) bL powerL elementL δ₁‖ *
          ‖((seed).twoStageProfileFactor bR δ₁ δ₂ : ℂ) *
            (seed).secondInputScalar (σ := σ) bR powerR elementR δ₁‖) ≤
      (orbitalFieldFactor K * (CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap) *
        Z ^ ((m + q) -
          (a.n₁ + a.n₂ + (data ξ).geometry.totalLength + q + mask + active) +
          CanonicalFirstResidualProfileCost.tiltError m
            (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂) := by
  have hpair := Q.literalOriginalAtoms_residualScalar_pair_norm_le
    ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ C original hzero ht hprime
    annulus hannulus hwindow cap hcap bL bR IL IR powerL powerR elementL elementR
    δ₁ δ₂ hδ₁ hδ₂ hδ hIL hIR hpowerL hpowerR
  exact CanonicalFirstLog.rowWeightBound_mul_scalarPair_le r radius D
    Z m q (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) mask active δ₁ δ₂
    ((CanonicalLiteralFirstScalarCost.atomBudget annulus B) ^ cap) _ _
    (zero_lt_one.trans hZ) hradius hmask hactive hpair

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstResidualProfileCost.tiltError_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstResidualProfileCost.combined_profile_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.rowWeightBound_eq_original_lengths
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFirstLog.rowWeightBound_mul_scalarPair_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_first_combined_profile_le
