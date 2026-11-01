import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralChartCoefficients

/-!
# The two stored chart coordinates give the actual atom locations

The second common ideal and the genuine pool power are fixed for the
leaf.  Their logarithms form one row translation.  After that
translation the two stored coordinates are exactly the sum of the two
plain and every retained prime location.  The two sides retain their
different first-coordinate signs, and neither Fourier variable or
Fourier measure is changed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Characters MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (left : Finset ι) (right : Finset κ)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (c : ι → ℂ) (e : κ → ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (rowLabelCount : ℕ)
variable (rowLabel : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
  Fin (rowLabelCount + 1))
variable (hleft : ∀ i ∈ b.leftColumns left,
  IsCoprime (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
variable (hright : ∀ j ∈ b.rightColumns right,
  IsCoprime (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val)
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)

namespace SecondBlockProfileChart

/-- The canonical left second coordinate, combined with the original
first-coordinate norm, is the literal atom location plus one computed
row translation. The input ideal identity is `ideal_product` of the
actual residual Cartesian reindex. -/
theorem canonicalLog_left_jointLocation
    (power : A.Exterior) (firstSign : ℝ)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (i : ι) {k : ℕ} (j : AllocationColumn K k)
    (hplain₁ : j.1.1 ≠ 0) (hplain₂ : j.1.2 ≠ 0)
    (hideal : (b.leftResidual i).val = allocationColumnIdeal j) :
    WithLp.toLp 2
      (-firstSign * Real.log (A.exteriorNorm
          (ExteriorIdealEuler.mul power (b.secondLeftIdeal i))),
        (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e
          finiteTest hlc hcs radius D rowLabelCount rowLabel hleft hright δ hδ hδhalf)
            .leftPoint q i) =
      WithLp.toLp 2
          (-firstSign * Real.log (A.exteriorNorm
              (ExteriorIdealEuler.mul power b.commonLeftIdeal)),
            Real.log (CanonicalSecondLogChart.rowRadius radius D q).val -
              Real.log (A.exteriorNorm b.commonLeftIdeal)) +
        rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) j := by
  change WithLp.toLp 2
      (-firstSign * Real.log (Ideal.absNorm
        (power.val * (b.commonLeftIdeal.val * (b.leftResidual i).val)) : ℝ),
        Real.log (CanonicalSecondLogChart.rowRadius radius D q).val -
          Real.log (Ideal.absNorm (b.commonLeftIdeal.val * (b.leftResidual i).val) : ℝ)) = _
  apply CanonicalLiteralLocations.actual_product_locations
    firstSign (Real.log (CanonicalSecondLogChart.rowRadius radius D q).val)
    j hplain₁ hplain₂ _ _
    (power.val * b.commonLeftIdeal.val) b.commonLeftIdeal.val
    (mul_ne_zero power.property.1 b.commonLeftIdeal.property.1) b.commonLeftIdeal.property.1
  · rw [hideal, mul_assoc]
  · rw [hideal]

/-- The stored right column uses the negative of its first location
when entering its ordinary energy. The actual right second coordinate
has no row-radius translation; the whole sign is retained here. -/
theorem canonicalLog_right_jointLocation
    (power : A.Exterior) (firstSign : ℝ)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (i : κ) {k : ℕ} (j : AllocationColumn K k)
    (hplain₁ : j.1.1 ≠ 0) (hplain₂ : j.1.2 ≠ 0)
    (hideal : (b.rightResidual i).val = allocationColumnIdeal j) :
    WithLp.toLp 2
      (firstSign * Real.log (A.exteriorNorm
          (ExteriorIdealEuler.mul power (b.secondRightIdeal i))),
        (canonicalLogWithCoefficients hΓ μv hDiff ν b C left right φ c e
          finiteTest hlc hcs radius D rowLabelCount rowLabel hleft hright δ hδ hδhalf)
            .rightPoint q i) =
      WithLp.toLp 2
          (firstSign * Real.log (A.exteriorNorm
              (ExteriorIdealEuler.mul power b.commonRightIdeal)),
            -Real.log (A.exteriorNorm b.commonRightIdeal)) +
        rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) j := by
  have he := CanonicalLiteralLocations.actual_product_locations
    (-firstSign) 0 j hplain₁ hplain₂
    (power.val * (b.commonRightIdeal.val * (b.rightResidual i).val))
    (b.commonRightIdeal.val * (b.rightResidual i).val)
    (power.val * b.commonRightIdeal.val) b.commonRightIdeal.val
    (mul_ne_zero power.property.1 b.commonRightIdeal.property.1) b.commonRightIdeal.property.1
    (by rw [hideal, mul_assoc]) (by rw [hideal])
  simpa only [neg_neg, zero_sub, neg_mul] using he

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalLog_left_jointLocation
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.canonicalLog_right_jointLocation
