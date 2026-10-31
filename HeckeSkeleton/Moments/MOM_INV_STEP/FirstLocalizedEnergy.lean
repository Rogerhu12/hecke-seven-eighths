import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterCenters

/-!
# Complete first positive energies with frozen arithmetic frequency cutoffs

The cutoff is one positive function of the actual cube/extraction/divisor
index. It precedes every old label and Γ sector. The source energies are
the literal full-Möbius energies of the actual first Poisson source;
their common density estimate is constructed from the original test.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open FirstParentRows FirstOuterCenters FirstNormPoolEnergy FirstColumnAssembly
  FirstPositiveSource FirstCenteredPositiveEnergy FirstCommonEnvelope FirstPoissonNormalization
  CanonicalNormPools CommonKernel
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
variable {σ ι : Type*} [Fintype ι]

abbrev LocalizedIndex (T : FirstParentEnergy.Data K S (σ := σ))
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) :=
  Σ o : OuterIndex K S D T, FirstDualTruncation.sectorCutoff K S D Γ (H o).val

def divisor (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) :
    NonzeroRingElements OS := sIntegerMaskGenerator K Sset o.2.2.2.val

def maskWeight (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) : ℝ :=
  ‖(UniqueFactorizationMonoid.moebius (IdealMobiusMask.primeProduct o.2.2.2.val) : ℂ)‖ *
    outerFactor K S D T.radius (divisor K S D T o)
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val

theorem maskWeight_nonneg (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) :
    0 ≤ maskWeight K S D T o :=
  mul_nonneg (norm_nonneg _) (outerFactor_nonneg K S D T.radius (divisor K S D T o) _ _ _ _)

def radialScale (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) : ℝ :=
  FirstCommonEnvelope.radialScale K S D T.radius (divisor K S D T o)
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val
    (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val false)
    (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val true)

theorem radialScale_pos (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) :
    0 < radialScale K S D T o :=
  FirstCommonEnvelope.radialScale_pos K S D T.radius (divisor K S D T o) _ _ _ _ _ _

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def profile (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T)
    (z : Ext × Sector) : CanonicalFirstEnergy.Profile K S :=
  FirstParentRetained.profile K S D μv ν T.archTest T.localTest T.locallyConstant
    T.compactSupport T.radius (divisor K S D T o)
    (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val z.1
    (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val false)
    (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val true)

def rawTotal (G : HeckeCharacter K) (T : FirstParentEnergy.Data K S (σ := σ))
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
    (side : Bool) : ℝ :=
  ∑ o : OuterIndex K S D T, maskWeight K S D T o *
    ∑ f ∈ L, pairWeight K S T.columns o.1.val o.2.1.val w f *
      ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
        sourceEnergy K S D Γ T.columns G (profile K S D Γ μv ν T o z.val) T.scale
          (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
          (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
          (divisor K S D T o).val z.val.2

theorem rawTotal_nonneg (G : HeckeCharacter K) (T : FirstParentEnergy.Data K S (σ := σ))
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
    (hw : ∀ f ∈ L, 0 ≤ w f) (side : Bool) :
    0 ≤ rawTotal K S D Γ μv ν G T H L w side := by
  apply Finset.sum_nonneg
  intro o ho
  apply mul_nonneg (maskWeight_nonneg K S D T o)
  apply Finset.sum_nonneg
  intro f hf
  apply mul_nonneg
    (mul_nonneg (mul_nonneg (hw f hf) (norm_nonneg _)) (norm_nonneg _))
  apply Finset.sum_nonneg
  intro z hz
  exact FirstParentEnergy.positiveEnergy_nonneg K S Γ _ _ _ _ _ _

def centeredTotal (T : FirstParentEnergy.Data K S (σ := σ))
    (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
    (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
    (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
    (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
    (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
    (ε : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  ∑ o : OuterIndex K S D T, (maskWeight K S D T o * radialScale K S D T o ^ ε) *
    ∑ f ∈ L, pairWeight K S T.columns o.1.val o.2.1.val w f *
      ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
        centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
          (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
          (FirstOuterCenters.Centering.at K S D T grid centers side o)
          (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
          (divisor K S D T o).val z.val.2 W hW (frequencyEnvelope m)

variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hallowed hΓ in
/-- The entire localized first positive source is controlled by actual
centered inverse columns. The common density constant is uniform in
the original labels, arithmetic cutoffs and complete center grid. -/
theorem exists_centeredTotal_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v)) (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ₀ ι₀ : Type*} [Fintype ι₀], ∀ (T : FirstParentEnergy.Data K S (σ := σ₀)),
      T.localTest = h →
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ),
      (∀ f ∈ L, 0 ≤ w f) →
      ∀ (grid : ι₀ → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2),
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p) →
      T.columns.base ^ T.columns.length = T.scale.val → 1 < T.columns.base →
      T.columns.cutoff = W →
      (∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p) →
      ∀ side : Bool,
        rawTotal K S D Γ μv ν G T H L w side ≤
          (A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest) *
            centeredTotal K S D Γ T Θ ψ G hν hG H L w grid centers W hW ε m side := by
  obtain ⟨s, A, hA, hb⟩ := exists_first_density_common_envelope K S D Γ μv ν h hlc hcs ε hε m
  refine ⟨s, A, hA, ?_⟩
  intro σ₀ ι₀ _ T hlocal Θ ψ G hν hG H L w hw grid centers W hW
    hGunramified hCX hZ hCW hprime side
  subst h
  let Aφ := A * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest
  have hAφ : 0 ≤ Aφ := mul_nonneg hA (apply_nonneg _ _)
  have hpoint (o : OuterIndex K S D T) (f : Ext)
      (z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val) :
      sourceEnergy K S D Γ T.columns G (profile K S D Γ μv ν T o z.val) T.scale
        (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
        (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
        (divisor K S D T o).val z.val.2 ≤
      (Aφ * radialScale K S D T o ^ ε) *
        centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
          (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
          (FirstOuterCenters.Centering.at K S D T grid centers side o)
          (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
          (divisor K S D T o).val z.val.2 W hW (frequencyEnvelope m) := by
    apply sourceEnergy_le_of_density_bound K S D Γ T.columns Θ ψ G hν hG T.scale
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
      (FirstOuterCenters.Centering.at K S D T grid centers side o)
      (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
      (divisor K S D T o).val z.val.2 W hW hΓ hallowed hGunramified hCX hZ hCW hprime
      (profile K S D Γ μv ν T o z.val) (frequencyEnvelope m)
      (frequencyEnvelope_integrable m) (frequencyEnvelope_nonneg m)
      (Aφ * radialScale K S D T o ^ ε)
      (mul_nonneg hAφ (Real.rpow_nonneg (radialScale_pos K S D T o).le ε))
    intro η
    exact hb T.archTest T.radius (divisor K S D T o)
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val z.val.1
      (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val false)
      (residualScale K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
        o.1.val o.2.1.val true) η
  unfold rawTotal centeredTotal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  calc
    _ ≤ maskWeight K S D T o *
        ((Aφ * radialScale K S D T o ^ ε) *
          ∑ f ∈ L, pairWeight K S T.columns o.1.val o.2.1.val w f *
            ∑ z : FirstDualTruncation.sectorCutoff K S D Γ (H o).val,
              centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
                (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side
                (FirstOuterCenters.Centering.at K S D T grid centers side o)
                (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z.val.1)
                (divisor K S D T o).val z.val.2 W hW (frequencyEnvelope m)) := by
      apply mul_le_mul_of_nonneg_left _ (maskWeight_nonneg K S D T o)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro f hf
      have hpf : 0 ≤ pairWeight K S T.columns o.1.val o.2.1.val w f :=
        mul_nonneg (mul_nonneg (hw f hf) (norm_nonneg _)) (norm_nonneg _)
      have hz := Finset.sum_le_sum (s := Finset.univ)
        (fun z (_ : z ∈ Finset.univ) => hpoint o f z)
      rw [← Finset.mul_sum] at hz
      exact (mul_le_mul_of_nonneg_left hz hpf).trans_eq (by ring)
    _ = _ := by ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedEnergy

end
