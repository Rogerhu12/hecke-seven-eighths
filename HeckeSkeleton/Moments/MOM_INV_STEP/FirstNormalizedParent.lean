import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLiveProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedSource

/-!
# The literal normalized canonical parent and its actual live sources

This interface starts with the original squared orbital series. Its
two positive terms are the actual normalized arithmetic sources which
are passed to the second Poisson transform, and its error is exactly
the physical principal restoration and complete localized tail of
that first transform. Normalization is moved through both Cauchy roots
by an equality, without charging the physical scalar a second time.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedParent

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalBlock CanonicalNormPools FirstParentRows FirstOuterCenters
open scoped Classical BigOperators nonZeroDivisors

theorem roots_scale (a x y : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a * x) * Real.sqrt (a * y) =
      a * (Real.sqrt x * Real.sqrt y) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha]
  calc
    _ = (Real.sqrt a * Real.sqrt a) * (Real.sqrt x * Real.sqrt y) := by ring
    _ = _ := by rw [Real.mul_self_sqrt ha]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

include hallowed ν μ in
/-- All constants precede the original source and both common center
assignments. The two sources and the first errors are constructed from
the parent; no comparison with a proposed parent energy is a premise. -/
theorem exists_parent_source_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (a p : ℕ) (ε massEps : ℝ) (hε : 0 < ε) (hmassEps : 0 < massEps) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ ι : Type*} [Fintype ι], ∀ (T : FirstParentEnergy.Data K S (σ := σ)),
      T.localTest = h →
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
        (Z r ell V tau : ℝ) (hZ : 0 < Z) (L : Finset Ext) (w : Ext → ℝ)
        (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (F : {r : ℝ // 0 < r}) (R : OuterIndex K S D T → {r : ℝ // 0 < r})
        (Aweight : ℝ), 0 ≤ Aweight →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, height K Sset f ≤ F.val) →
      (∀ o, (rowCap K S (cubeDilation K S (outerAnchor K S D T o).1
        (outerAnchor K S D T o).2 o.1.val o.2.1.val) F
          (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ o)).val ≤ (R o).val) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ a) →
      (∀ b ∈ T.cubes, ∀ f ∈ L,
        ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset → UnramifiedAt K G q) →
      T.columns.base ^ T.columns.length = T.scale.val → 1 < T.columns.base →
      T.columns.cutoff = W →
      (∀ k ∈ T.columns.slots, ∀ q ∈ T.columns.primeLists k, Prime q) →
      Z ^ (-r - 2 * ell - V) * (∑ f ∈ L, w f * ‖FirstCappedProduction.parent K S D Γ T f‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest * Aweight) *
        (Real.sqrt (FirstNormalizedSource.total K S D Γ T
          (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ) L grid centers
          false R massEps ε Z r ell V Θ ψ G hν hG W hW m) *
         Real.sqrt (FirstNormalizedSource.total K S D Γ T
          (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ) L grid centers
          true R massEps ε Z r ell V Θ ψ G hν hG W hW m)) +
        Z ^ (-r - 2 * ell - V) *
          ∑ f ∈ L, w f * FirstCappedProduction.actualError K S D Γ hΓ μv T f Z tau := by
  obtain ⟨s, C, hC, hb⟩ := FirstLiveProduction.exists_parent_free_bound
    K S D Γ hΓ hallowed μv ν μ h hlc hcs a p ε massEps hε hmassEps m
  refine ⟨s, C, hC, ?_⟩
  intro σ ι _ T hlocal Θ ψ G hν hG hcal Z r ell V tau hZ L w grid centers W hW F R Aweight
    hAw hw0 hF hcap hw hβ hGunramified hscale hbase hcut hprime
  have hp := hb T hlocal Θ ψ G hν hG hcal Z tau hZ L w grid centers W hW F R Aweight
    hAw hw0 hF hcap hw hβ hGunramified hscale hbase hcut hprime
  have hleft := FirstNormalizedSource.total_eq_normalized_freeTotal K S D Γ T
    (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ) L grid centers false
    R massEps ε Z r ell V Θ ψ G hν hG W hW m hZ.le
  have hright := FirstNormalizedSource.total_eq_normalized_freeTotal K S D Γ T
    (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ) L grid centers true
    R massEps ε Z r ell V Θ ψ G hν hG W hW m hZ.le
  apply (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hZ.le _)).trans_eq
  rw [mul_add, hleft, hright, roots_scale _ _ _ (Real.rpow_nonneg hZ.le _)]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormalizedParent

end
