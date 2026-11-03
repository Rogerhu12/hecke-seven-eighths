import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedFreeEnergy

/-!
# Production estimate for the whole localized first positive source

The common Fourier bound, genuine centered Mellin expansion and actual
old-label fiber bound are composed here. All constants precede the
original source, every arithmetic cutoff and the finite center grid.
The right side consists of the free positive inverse energies that
enter the second Poisson pass.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedProduction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open FirstParentRows FirstOuterCenters FirstLocalizedEnergy FirstLocalizedFreeEnergy
  CanonicalNormPools
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

include hallowed hΓ in
theorem exists_rawTotal_free_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (a p : ℕ) (ε massEps : ℝ) (hε : 0 < ε) (hmassEps : 0 < massEps) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ {σ ι : Type*} [Fintype ι], ∀ (T : FirstParentEnergy.Data K S (σ := σ)),
      T.localTest = h →
      ∀ (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
        (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
        (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (L : Finset Ext) (w : Ext → ℝ)
        (grid : ι → {r : ℝ // 0 < r}) (centers : FirstOuterCenters.Centering K S D T grid)
        (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
        (F : {r : ℝ // 0 < r}) (Aweight : ℝ), 0 ≤ Aweight →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, height K Sset f ≤ F.val) →
      (∀ f ∈ L, w f ≤ Aweight * ((idealDivisors f.val.val).card : ℝ) ^ a) →
      (∀ b ∈ T.cubes, ∀ f ∈ L,
        ‖T.columns.labelWeight b f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset → UnramifiedAt K G q) →
      T.columns.base ^ T.columns.length = T.scale.val → 1 < T.columns.base →
      T.columns.cutoff = W →
      (∀ k ∈ T.columns.slots, ∀ q ∈ T.columns.primeLists k, Prime q) →
      ∀ side : Bool,
        rawTotal K S D Γ μv ν G T H L w side ≤
          (C * s.sup (schwartzSeminormFamily ℝ V ℂ) T.archTest * Aweight) *
            freeTotal K S D Γ T Θ ψ G hν hG H grid centers W hW m side F massEps ε := by
  obtain ⟨s, A, hA, hsource⟩ := exists_centeredTotal_bound K S D Γ μv ν hallowed hΓ
    h hlc hcs ε hε m
  obtain ⟨B, hB, hfiber⟩ := exists_centeredTotal_free_bound K S D Γ hΓ hallowed
    a p massEps hmassEps
  refine ⟨s, A * B, mul_nonneg hA (zero_le_one.trans hB), ?_⟩
  intro σ ι _ T hlocal Θ ψ G hν hG H L w grid centers W hW F Aweight hAweight
    hw0 hF hw hβ hGunramified hscale hbase hcut hprime side
  have h₁ := hsource T hlocal Θ ψ G hν hG H L w hw0 grid centers W hW
    hGunramified hscale hbase hcut hprime side
  have h₂ := hfiber T Θ ψ G hν hG H L w grid centers W hW F Aweight hAweight
    hF hw hβ ε m side
  exact h₁.trans ((mul_le_mul_of_nonneg_left h₂
    (mul_nonneg hA (apply_nonneg _ _))).trans_eq (by ring))

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedProduction

end

