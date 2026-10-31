import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRetained
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedFreeEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedReduction

/-!
# The whole canonical parent reduced to prescribed free inverse energies

Both Cauchy roots come from the same complete original old-label and
arithmetic source. The old rows are eliminated at the prescribed physical
cap using the proved divisor fiber estimate and the genuine orbital
majorant. The parent identity and its principal and infinite-tail errors
are the actual Poisson terms.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalBlock CanonicalPoissonSplit FirstParentRows FirstOuterCenters CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

private theorem roots_common_factor (C L R : ℝ) (hC : 0 ≤ C) :
    Real.sqrt (C * L) * Real.sqrt (C * R) =
      C * (Real.sqrt L * Real.sqrt R) := by
  rw [Real.sqrt_mul hC, Real.sqrt_mul hC]
  calc
    (Real.sqrt C * Real.sqrt L) * (Real.sqrt C * Real.sqrt R) =
        (Real.sqrt C * Real.sqrt C) * (Real.sqrt L * Real.sqrt R) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hC]

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
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Varch" => mixedEmbedding.euclidean.mixedSpace K

/-- Complete first production with constants chosen before the source,
original prime lists, norm windows, and both common center assignments. -/
theorem exists_retained_free_bound
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
        (Z tau : ℝ) (hZ : 0 < Z) (L : Finset Ext) (w : Ext → ℝ)
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
      (∑ f ∈ L, w f * ‖FirstLocalizedRetained.retained K S D Γ μv hΓ T f Z tau‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ Varch ℂ) T.archTest * Aweight) *
        (Real.sqrt (FirstCappedFreeEnergy.freeTotal K S D Γ T Θ ψ G hν hG
          grid centers W hW m false R massEps ε) *
         Real.sqrt (FirstCappedFreeEnergy.freeTotal K S D Γ T Θ ψ G hν hG
          grid centers W hW m true R massEps ε)) := by
  obtain ⟨s, C, hC, hb⟩ := FirstCappedFreeEnergy.exists_rawTotal_free_bound
    K S D Γ hΓ hallowed μv ν h hlc hcs a p ε massEps hε hmassEps m
  refine ⟨s, C, hC, ?_⟩
  intro σ ι _ T hlocal Θ ψ G hν hG hcal Z tau hZ L w grid centers W hW F R Aweight
    hAw hw0 hF hcap hw hβ hGunramified hscale hbase hcut hprime
  have hraw := hb T hlocal Θ ψ G hν hG
    (FirstLocalizedCutoff.sourceCutoff K S D T Z tau hZ) L w grid centers W hW F R
    Aweight hAw hw0 hF hcap hw hβ hGunramified hscale hbase hcut hprime
  have hfirst := FirstLocalizedRetained.weighted_retained_norm_le
    K S D Γ μv ν hΓ hallowed G T hcal L w hw0 Z tau hZ
  apply hfirst.trans
  apply (mul_le_mul (Real.sqrt_le_sqrt (hraw false)) (Real.sqrt_le_sqrt (hraw true))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  exact roots_common_factor _ _ _ (by positivity)

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]
variable {σ : Type*}

def parent (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext) : ℂ :=
  canonicalCubeEnergy K S D Γ T.columns f T.cubes (FirstParentEnergy.columnPool K S T)
    T.archTest T.localTest T.mask T.radius

def actualError (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext) (Z tau : ℝ) : ℝ :=
  (2 * ‖canonicalPrincipalSource K S D Γ hΓ T.columns f T.cubes
      (FirstParentEnergy.columnPool K S T) T.archTest T.localTest T.locallyConstant
      T.compactSupport T.mask T.radius‖ +
    ‖canonicalPrincipal K S D Γ hΓ μv T.columns f T.cubes
      (FirstParentEnergy.columnPool K S T) T.archTest T.localTest T.locallyConstant
      T.compactSupport T.mask T.radius‖) +
    ‖FirstLocalizedTail.sourceSubsetTail K S D Γ hΓ μv T.columns f
      ((T.cubes ×ˢ FirstParentEnergy.columnPool K S T) ×ˢ
        (T.cubes ×ˢ FirstParentEnergy.columnPool K S T))
      T.archTest T.localTest T.locallyConstant T.compactSupport T.mask
      T.radius T.scale Z tau‖

/-- The original orbital parent, with its true infinite-frequency tail
and physical primitive principal terms. No source identity is assumed. -/
include ν μ in
theorem parent_norm_le_retained_and_error
    (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext) (Z tau : ℝ) :
    ‖parent K S D Γ T f‖ ≤
      ‖FirstLocalizedRetained.retained K S D Γ μv hΓ T f Z tau‖ +
        actualError K S D Γ hΓ μv T f Z tau := by
  have hb := FirstLocalizedReduction.parent_norm_le_retained_and_errors
    K S D Γ hΓ μv ν μ T.columns f T.cubes (FirstParentEnergy.columnPool K S T)
    (fun n hn => dyadicPool_squarefree K Sset hn) T.archTest T.localTest
    T.locallyConstant T.compactSupport T.mask T.radius T.scale Z tau
  simpa only [parent, actualError, FirstLocalizedRetained.retained, add_assoc] using hb

include ν μ in
theorem weighted_parent_le_retained_and_errors
    (T : FirstParentEnergy.Data K S (σ := σ)) (L : Finset Ext)
    (w : Ext → ℝ) (hw : ∀ f ∈ L, 0 ≤ w f) (Z tau : ℝ) :
    (∑ f ∈ L, w f * ‖parent K S D Γ T f‖) ≤
      (∑ f ∈ L, w f * ‖FirstLocalizedRetained.retained K S D Γ μv hΓ T f Z tau‖) +
      ∑ f ∈ L, w f * actualError K S D Γ hΓ μv T f Z tau := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro f hf
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (parent_norm_le_retained_and_error K S D Γ hΓ μv ν μ T f Z tau) (hw f hf)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction

end

