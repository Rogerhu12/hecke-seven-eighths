import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SignedDirectFirstSource

/-!
# Signs of the actual first-source terminal costs

The original dual zero is a sum of norms. Each truncation mass retains
its actual Mobius norm, Poisson factor, residue mass and positive dual
radius. These definitions give the signs needed by the final parent
conclusion without replacing either terminal by a different quantity.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]

namespace ParentPeriodicPair

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)} [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

theorem truncationMass_nonneg (p : ParentPeriodicPair K S Γ)
    (M : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (radius : {r : ℝ // 0 < r}) : 0 ≤ p.truncationMass M radius := by
  unfold truncationMass sIntegerMaskedTruncationMass
  apply Finset.sum_nonneg
  intro D _
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (sIntegerPeriodicResidueL1_nonneg K (S : Set (HeightOneSpectrum (𝓞 K)))
        p.modulus p.modulus_ne_zero _))
    (add_nonneg zero_le_one (inv_nonneg.mpr
      (sIntegerMaskDualRadius K S p.modulus p.modulus_ne_zero radius
        (sIntegerMaskGenerator K _ D)).property.le))

end ParentPeriodicPair

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K} {centered : Bool} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

namespace ActualDirectFirstSource

variable (s : ActualDirectFirstSource (E := E) hΓ μv C Z finiteTest
  centered d a t Y₁ Y₂ X hX)

theorem dualZeroCost_nonneg
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
      HeckeGeneral.Characters.localDifferentExponent K v = 0) :
    0 ≤ s.dualZeroCost hDiff := by
  unfold dualZeroCost
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tailCost_nonneg (seminorms : Finset (ℕ × ℕ)) : 0 ≤ s.tailCost seminorms := by
  unfold tailCost
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (apply_nonneg _ _)
    (((s.source v).pairs i j).truncationMass_nonneg (s.source v).mask s.radius)

end ActualDirectFirstSource
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.truncationMass_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.dualZeroCost_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.tailCost_nonneg
