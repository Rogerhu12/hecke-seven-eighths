import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalOriginalPointwise

/-!
# Integrate the two actual original exceptional source estimates

The original first scalar pair and profile are paid together. The
second magnitude is normalized by the same actual first allowance,
and then integrated against both stored kernels. The original theta
partition and dependent arithmetic index are preserved throughout.

These internal source-estimate inputs are proved by the literal
six-case factories, not hypotheses of the final engine theorem.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance canonicalExceptionalOriginalIntegralCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}


namespace ActualDirectFirstSource.SecondStages

variable {s : ActualDirectFirstSource (E := ℝ) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := ℝ) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.CoverHybridPredicates L)
local notation "normalization" => s.canonicalNormalization hZ total
variable (i : R.liveLeaves L exceptional normalization)
local notation "leaf" => R.parentLeaf L exceptional normalization i.val
local notation "labels" => R.arithmeticLabels L hcap exceptional normalization
local notation "j" => R.originalIndex L hcap exceptional normalization i
variable (extract : (leaf).ConstantAtomExtraction)
variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
local notation "outerLeaf" => extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar
variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))

/-- Integrate the proved actual first-profile and second-source bounds
on the same stored parent. The two original Fourier kernels remain
explicit and the original arithmetic index is unchanged. -/
theorem exceptionalCost_of_original_source
    (hpredicate : (leaf).exceptional = characters.exceptional)
    (parentWidth firstCost secondCost remaining lower tilt : ℝ) (order : ℕ)
    (hfirstCost : 0 ≤ firstCost) (hsecondCost : 0 ≤ secondCost)
    (hfirst : (s.pieces i.val.1 i.val.2.1).weightBound *
        (‖leftScalar‖ * ‖rightScalar‖) ≤
      firstCost * Z ^ (parentWidth - total i.val.1 i.val.2.1 + tilt))
    (hsecond : ∀ thetaPair : theta × theta, ∀ z : ℝ × ℝ,
      ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z /
          R.firstAllowanceAt L total i.val ≤
        (secondCost *
          (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order) *
            Z ^ remaining /
          (Ideal.absNorm (commonRadical (R.commonLabel L i.val).1
            (R.commonLabel L i.val).2) : ℝ) * Z ^ (-lower)) :
    (leaf).exceptionalCost / Z ^ parentWidth ≤
      R.originalScalarAt L i.val *
        (((theta.card : ℝ) ^ 2 * firstCost * secondCost * (1 + 2 * Real.pi) ^ order *
          CanonicalExceptionalPaidIntegral.fourierFactor order order
            (leaf).firstKernel (leaf).secondKernel) * Z ^ (remaining + tilt) *
              (labels).carrier.exceptionalDyadWeight Z lower j) := by
  let coefficient := R.originalScalarAt L i.val *
    (firstCost * secondCost * Z ^ (remaining + tilt) *
      (labels).carrier.exceptionalDyadWeight Z lower j)
  have hindex := (labels).carrier.exceptionalDyadWeight_nonneg
    Z lower (zero_lt_one.trans hZ).le j
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (R.originalScalarAt_nonneg L i.val)
      (mul_nonneg
        (mul_nonneg (mul_nonneg hfirstCost hsecondCost)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hindex)
  have hheight : 0 ≤ (1 + 2 * Real.pi) ^ order := by positivity
  have hpoint : ∀ thetaPair : theta × theta, ∀ z : ℝ × ℝ,
      (((‖leftScalar‖ * ‖rightScalar‖) * (leaf).weight) / Z ^ parentWidth) *
          ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z ≤
        (coefficient * (1 + 2 * Real.pi) ^ order) *
          ((1 + ‖z.1‖) ^ order * (1 + ‖z.2‖) ^ order) := by
    intro thetaPair z
    have hp := R.stripOuter_theta_pointwise L hcap hZ total exceptional i extract
      leftScalar rightScalar hleftScalar hrightScalar characters thetaPair z
      parentWidth firstCost
      (secondCost *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order)
      remaining lower tilt hfirstCost hfirst (hsecond thetaPair z)
    rw [extract.stripOuter_weight leftScalar rightScalar hleftScalar hrightScalar] at hp
    have hg := CanonicalLiteralExceptionalWindows.fourierHeight_polynomial
      order (WithLp.toLp 2 z)
    simp only [WithLp.ofLp_toLp] at hg
    calc
      _ ≤ coefficient *
          (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order :=
        hp.trans_eq (by dsimp only [coefficient]; ring)
      _ ≤ coefficient * ((1 + 2 * Real.pi) ^ order *
          (1 + ‖z.1‖) ^ order * (1 + ‖z.2‖) ^ order) :=
        mul_le_mul_of_nonneg_left hg hcoefficient
      _ = _ := by ring

  have hb := CanonicalExceptionalPaidIntegral.theta_cost_le_of_strip_outer_majorant
    order order (coefficient * (1 + 2 * Real.pi) ^ order)
    (mul_nonneg hcoefficient hheight) leaf extract leftScalar rightScalar
    hleftScalar hrightScalar characters hpredicate Z parentWidth hpoint
  exact hb.trans_eq (by dsimp only [coefficient]; ring)

end ActualDirectFirstSource.SecondStages

namespace ActualFirstSource.SecondStages

variable {s : ActualFirstSource (E := ℝ) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}
variable (R : s.SecondStages (E := ℝ) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)
variable {cap : ℕ} (hcap : L.slotCount ≤ cap) (hZ : 1 < Z)
variable (total : ∀ v : s.CommonLabel, ((s.block v).mask s.mask).powerset → ℝ)
variable (exceptional : R.CoverHybridPredicates L)
local notation "normalization" => s.canonicalNormalization hZ total
variable (i : R.liveLeaves L exceptional normalization)
local notation "leaf" => R.parentLeaf L exceptional normalization i.val
local notation "labels" => R.arithmeticLabels L hcap exceptional normalization
local notation "j" => (labels).index i
variable (extract : (leaf).ConstantAtomExtraction)
variable (leftScalar rightScalar : ℂ) (hleftScalar : leftScalar ≠ 0)
variable (hrightScalar : rightScalar ≠ 0)
local notation "outerLeaf" => extract.stripOuter leftScalar rightScalar hleftScalar hrightScalar
variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))

/-- Integrate the proved actual first-profile and second-source bounds
on the same stored parent. The two original Fourier kernels remain
explicit and the original arithmetic index is unchanged. -/
theorem exceptionalCost_of_original_source
    (hpredicate : (leaf).exceptional = characters.exceptional)
    (parentWidth firstCost secondCost remaining lower tilt : ℝ) (order : ℕ)
    (hfirstCost : 0 ≤ firstCost) (hsecondCost : 0 ≤ secondCost)
    (hfirst : (s.pools i.val.1 i.val.2.1).weightBound *
        (‖leftScalar‖ * ‖rightScalar‖) ≤
      firstCost * Z ^ (parentWidth - total i.val.1 i.val.2.1 + tilt))
    (hsecond : ∀ thetaPair : theta × theta, ∀ z : ℝ × ℝ,
      ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z /
          R.firstAllowanceAt L total i.val ≤
        (secondCost *
          (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order) *
            Z ^ remaining /
          (Ideal.absNorm (commonRadical (R.commonLabel L i.val).1
            (R.commonLabel L i.val).2) : ℝ) * Z ^ (-lower)) :
    (leaf).exceptionalCost / Z ^ parentWidth ≤
      R.originalScalarAt L i.val *
        (((theta.card : ℝ) ^ 2 * firstCost * secondCost * (1 + 2 * Real.pi) ^ order *
          CanonicalExceptionalPaidIntegral.fourierFactor order order
            (leaf).firstKernel (leaf).secondKernel) * Z ^ (remaining + tilt) *
              (labels).carrier.exceptionalDyadWeight Z lower j) := by
  let coefficient := R.originalScalarAt L i.val *
    (firstCost * secondCost * Z ^ (remaining + tilt) *
      (labels).carrier.exceptionalDyadWeight Z lower j)
  have hindex := (labels).carrier.exceptionalDyadWeight_nonneg
    Z lower (zero_lt_one.trans hZ).le j
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (R.originalScalarAt_nonneg L i.val)
      (mul_nonneg
        (mul_nonneg (mul_nonneg hfirstCost hsecondCost)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) hindex)
  have hheight : 0 ≤ (1 + 2 * Real.pi) ^ order := by positivity
  have hpoint : ∀ thetaPair : theta × theta, ∀ z : ℝ × ℝ,
      (((‖leftScalar‖ * ‖rightScalar‖) * (leaf).weight) / Z ^ parentWidth) *
          ((outerLeaf).thetaClassLeaf characters thetaPair).exceptionalIntegrand z ≤
        (coefficient * (1 + 2 * Real.pi) ^ order) *
          ((1 + ‖z.1‖) ^ order * (1 + ‖z.2‖) ^ order) := by
    intro thetaPair z
    have hp := R.stripOuter_theta_pointwise L hcap hZ total exceptional i extract
      leftScalar rightScalar hleftScalar hrightScalar characters thetaPair z
      parentWidth firstCost
      (secondCost *
        (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order)
      remaining lower tilt hfirstCost hfirst (hsecond thetaPair z)
    rw [extract.stripOuter_weight leftScalar rightScalar hleftScalar hrightScalar] at hp
    have hg := CanonicalLiteralExceptionalWindows.fourierHeight_polynomial
      order (WithLp.toLp 2 z)
    simp only [WithLp.ofLp_toLp] at hg
    calc
      _ ≤ coefficient *
          (1 + CanonicalLiteralExceptionalWindows.fourierHeight (WithLp.toLp 2 z)) ^ order :=
        hp.trans_eq (by dsimp only [coefficient]; ring)
      _ ≤ coefficient * ((1 + 2 * Real.pi) ^ order *
          (1 + ‖z.1‖) ^ order * (1 + ‖z.2‖) ^ order) :=
        mul_le_mul_of_nonneg_left hg hcoefficient
      _ = _ := by ring

  have hb := CanonicalExceptionalPaidIntegral.theta_cost_le_of_strip_outer_majorant
    order order (coefficient * (1 + 2 * Real.pi) ^ order)
    (mul_nonneg hcoefficient hheight) leaf extract leftScalar rightScalar
    hleftScalar hrightScalar characters hpredicate Z parentWidth hpoint
  exact hb.trans_eq (by dsimp only [coefficient]; ring)

end ActualFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.exceptionalCost_of_original_source
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.exceptionalCost_of_original_source
