import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussNumerators

/-!
# The exact post-pool frozen ideals of the six original Gauss sources

The original whole column is reconstructed from the first common ideal,
the complete pool prime power, and the actual residual ideal. These are
identities on the unchanged actual column carriers.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
namespace HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open MeasureTheory HeckePort.Moments HeckePort.Moments.Support
variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}

namespace ActualGaussSource
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η htrace}
variable {ι α : Type*} (G : ActualGaussSource C ι)

structure OriginalPostIdeal (ideal : α → A.Exterior) (index : ι → α) where
  frozen : Ideal (𝓞 K)
  frozen_ne_zero : frozen ≠ 0
  reconstruct : ∀ i ∈ G.columns, (ideal (index i)).val = frozen * (G.ideal i).val

namespace OriginalPostIdeal
variable {G} {ideal : α → A.Exterior} {index : ι → α}
variable (W : G.OriginalPostIdeal ideal index)

include W in
theorem norm_le_original (i : ι) (hi : i ∈ G.columns) :
    A.exteriorNorm (G.ideal i) ≤ A.exteriorNorm (ideal (index i)) := by
  apply ideal_norm_le_of_dvd (ideal (index i)).property.1
  exact ⟨W.frozen, by rw [W.reconstruct i hi, mul_comm]⟩

theorem lower (Z total : ℝ) (hZ : 1 < Z) (i : ι) (hi : i ∈ G.columns)
    (hfull : Z ^ total ≤ A.exteriorNorm (ideal (index i))) :
    Z ^ (total - idealLogLength Z W.frozen) ≤ A.exteriorNorm (G.ideal i) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < (Ideal.absNorm W.frozen : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr W.frozen_ne_zero))
  have he : A.exteriorNorm (ideal (index i)) =
      (Ideal.absNorm W.frozen : ℝ) * A.exteriorNorm (G.ideal i) := by
    change (Ideal.absNorm (ideal (index i)).val : ℝ) = _
    rw [W.reconstruct i hi, map_mul, Nat.cast_mul] <;> rfl
  rw [Real.rpow_sub hz, rpow_idealLogLength Z hZ W.frozen W.frozen_ne_zero]
  apply (div_le_iff₀ hn).mpr
  simpa only [he, mul_comm] using hfull

theorem upper (Z total : ℝ) (hZ : 1 < Z) (i : ι) (hi : i ∈ G.columns)
    (hfull : A.exteriorNorm (ideal (index i)) ≤ Z ^ total) :
    A.exteriorNorm (G.ideal i) ≤ Z ^ (total - idealLogLength Z W.frozen) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < (Ideal.absNorm W.frozen : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr W.frozen_ne_zero))
  have he : A.exteriorNorm (ideal (index i)) =
      (Ideal.absNorm W.frozen : ℝ) * A.exteriorNorm (G.ideal i) := by
    change (Ideal.absNorm (ideal (index i)).val : ℝ) = _
    rw [W.reconstruct i hi, map_mul, Nat.cast_mul] <;> rfl
  rw [Real.rpow_sub hz, rpow_idealLogLength Z hZ W.frozen W.frozen_ne_zero]
  apply (le_div_iff₀ hn).mpr
  simpa only [he, mul_comm] using hfull

end OriginalPostIdeal
end ActualGaussSource

section CanonicalFirst

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
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
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}

local notation "chart" => FirstBlockProfileChart.canonicalLogWithCoefficients
  hΓ μv ν b C left right φ c e finiteTest hlc hcs radius D δ hδ hδhalf


namespace FirstBlockDirectData

variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)


def canonicalLeftOriginalPostIdeal :
    (p.leftData.directSource (p.leftDivisorCoefficient S χ)).OriginalPostIdeal fullI id where
  frozen := DE.1
  frozen_ne_zero := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i ∈ b.leftColumns left := by
      simpa only [DirectGaussData.directSource, p.left_columns] using hi
    have he := b.left_reconstruct left i hi'
    rw [b.common_left] at he
    simpa only [p.left_ideal] using he

def canonicalRightOriginalPostIdeal :
    (p.rightData.directSource (p.rightDivisorCoefficient S χ)).OriginalPostIdeal fullJ id where
  frozen := DE.2
  frozen_ne_zero := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i ∈ b.rightColumns right := by
      simpa only [DirectGaussData.directSource, p.right_columns] using hi
    have he := b.right_reconstruct right i hi'
    rw [b.common_right] at he
    simpa only [p.right_ideal] using he

end FirstBlockDirectData

namespace FirstBlockPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {base ell eps : ℝ}
variable {pool : PowerScaleExteriorPool A bad base ell eps}
variable (p : FirstBlockPoolData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C left right φ c e
    finiteTest hlc hcs radius D δ hδ hδhalf) pool M X hX)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)


def canonicalLeftMainOriginalPostIdeal :
    ((p.divisorPools.leftData S).mainSource (p.leftDivisorCoefficient S χ)).OriginalPostIdeal fullI id where
  frozen := DE.1
  frozen_ne_zero := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i ∈ b.leftColumns left := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.left_columns S, p.left_columns] using hi
    have he := b.left_reconstruct left i hi'
    rw [b.common_left] at he
    simpa only [p.divisorPools.left_ideal S, p.left_ideal] using he

def canonicalLeftPoolOriginalPostIdeal (prime : ExteriorPrime A) (n : ℕ) :
    ((p.divisorPools.leftData S).residualSource prime n
      (p.leftDivisorCoefficient S χ)).OriginalPostIdeal fullI (fun i => i.val) where
  frozen := DE.1 * (powerIdeal prime n).val
  frozen_ne_zero := by
    apply mul_ne_zero _ (powerIdeal prime n).property.1
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i.val ∈ b.leftColumns left := by
      simpa only [p.divisorPools.left_columns S, p.left_columns] using
        (Finset.mem_filter.mp i.property).1
    have he := b.left_reconstruct left i.val hi'
    rw [b.common_left] at he
    have hp := ((p.divisorPools.leftData S).residualPresentation prime n i).reconstructed
    rw [p.divisorPools.left_ideal S, p.left_ideal] at hp
    change (fullI i.val).val = (DE.1 * (powerIdeal prime n).val) *
      ((p.divisorPools.leftData S).residualPresentation prime n i).residual.val
    rw [he, hp, mul_assoc]

def canonicalRightMainOriginalPostIdeal :
    ((p.divisorPools.rightData S).mainSource (p.rightDivisorCoefficient S χ)).OriginalPostIdeal fullJ id where
  frozen := DE.2
  frozen_ne_zero := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i ∈ b.rightColumns right := by
      simpa only [FirstGaussPoolData.mainSource, p.divisorPools.right_columns S, p.right_columns] using hi
    have he := b.right_reconstruct right i hi'
    rw [b.common_right] at he
    simpa only [p.divisorPools.right_ideal S, p.right_ideal] using he

def canonicalRightPoolOriginalPostIdeal (prime : ExteriorPrime A) (n : ℕ) :
    ((p.divisorPools.rightData S).residualSource prime n
      (p.rightDivisorCoefficient S χ)).OriginalPostIdeal fullJ (fun i => i.val) where
  frozen := DE.2 * (powerIdeal prime n).val
  frozen_ne_zero := by
    apply mul_ne_zero _ (powerIdeal prime n).property.1
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  reconstruct i hi := by
    have hi' : i.val ∈ b.rightColumns right := by
      simpa only [p.divisorPools.right_columns S, p.right_columns] using
        (Finset.mem_filter.mp i.property).1
    have he := b.right_reconstruct right i.val hi'
    rw [b.common_right] at he
    have hp := ((p.divisorPools.rightData S).residualPresentation prime n i).reconstructed
    rw [p.divisorPools.right_ideal S, p.right_ideal] at hp
    change (fullJ i.val).val = (DE.2 * (powerIdeal prime n).val) *
      ((p.divisorPools.rightData S).residualPresentation prime n i).residual.val
    rw [he, hp, mul_assoc]

end FirstBlockPoolData

end CanonicalFirst
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalPostIdeal.lower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalPostIdeal.upper
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussSource.OriginalPostIdeal.norm_le_original
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalLeftOriginalPostIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockDirectData.canonicalRightOriginalPostIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftMainOriginalPostIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightMainOriginalPostIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalLeftPoolOriginalPostIdeal
#print axioms HeckeSkeleton.Moments.EngineStep.FirstBlockPoolData.canonicalRightPoolOriginalPostIdeal
