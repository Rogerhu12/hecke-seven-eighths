import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolRawFourierStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFamilyIntegrability

/-!
# Integrating the genuine raw second source

Each actual transformed row is complex linear in its original profile.
The first Fourier parameter therefore multiplies each complete pair by
its literal unit Gram phase.  Finite physical rows give integrability
against the original positive Fourier measure; no finite support in the
continuous Fourier variable and no post-Cauchy energy bound are used.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments

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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Arch" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- True profile linearity of an arbitrary actual periodic Poisson row.
It retains its full residue weight and every mask factor. -/
theorem ParentPeriodicPair.transformedRow_profile_smul
    (p : ParentPeriodicPair K A.Sf Γ) (a : ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R)) (q : Q) :
    ({ p with profile := a • p.profile } : ParentPeriodicPair K A.Sf Γ).
        transformedRow μv hDiff finiteTest radius D q =
      a * p.transformedRow μv hDiff finiteTest radius D q := by
  unfold ParentPeriodicPair.transformedRow sIntegerPeriodicFourierProfileTerm
  dsimp only [ParentPeriodicPair.dualRadius]
  rw [engine_traceSchwartzFourier_smul, sUnitOrbitalProfile_tensor_smul, smul_eq_mul]
  ring

theorem FirstCommonCharacterBlock.secondPair_transformedRow_smul
    {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (profiles : ι → κ → SchwartzMap Arch ℂ) (u : ι → κ → ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (q : Q) (i : ι) (j : κ) :
    (b.secondPair hΓ hDiff C (fun i j => u i j • profiles i j) i j).
        transformedRow μv hDiff finiteTest radius D q =
      u i j * (b.secondPair hΓ hDiff C profiles i j).
        transformedRow μv hDiff finiteTest radius D q := by
  have hp :
      b.secondPair hΓ hDiff C (fun i j => u i j • profiles i j) i j =
        { b.secondPair hΓ hDiff C profiles i j with
          profile := u i j • (b.secondPair hΓ hDiff C profiles i j).profile } := rfl
  rw [hp, ParentPeriodicPair.transformedRow_profile_smul]

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

theorem withMultiplier_transformedRow
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) (u : ι → ℂ)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (q : Q) (i j : ι) :
    (((s.withMultiplier u).sources DE).pairs i j).
        transformedRow μv hDiff finiteTest s.radius D.val q =
      (u i * star (u j)) * ((s.sources DE).pairs i j).
        transformedRow μv hDiff finiteTest s.radius D.val q := by
  have hp :
      (fun i j => ((u i * G.coefficient i) * star (u j * G.coefficient j)) • s.profile) =
        (fun i j => (u i * star (u j)) •
          ((G.coefficient i * star (G.coefficient j)) • s.profile)) := by
    funext i j
    rw [smul_smul, star_mul]
    congr 1
    ring
  change ((canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal
      DE.val DE.property).secondPair hΓ hDiff C
        (fun i j => ((u i * G.coefficient i) * star (u j * G.coefficient j)) • s.profile) i j).
      transformedRow μv hDiff finiteTest s.radius D.val q = _
  rw [hp]
  exact FirstCommonCharacterBlock.secondPair_transformedRow_smul _ _ _ _ _ _ _ _ _

/-- A single literal pair row is a bounded continuous Gram phase times
the same original row.  The actual Fourier measure is finite. -/
theorem phase_transformedRow_integrable
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (F : SchwartzMap W ℂ) (x : ι → W)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) (q : Q) (i j : ι) :
    Integrable (fun ξ : W =>
      (((s.withMultiplier (fun i => jointPhase ξ (x i))).sources DE).pairs i j).
        transformedRow μv hDiff finiteTest s.radius D.val q) (actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  let a := ((s.sources DE).pairs i j).transformedRow μv hDiff finiteTest s.radius D.val q
  have hc : Continuous (fun ξ : W => jointPhase ξ (x i) * star (jointPhase ξ (x j))) :=
    (continuous_jointPhase (x i)).mul (continuous_jointPhase (x j)).star
  have hi : Integrable (fun ξ : W => a * (jointPhase ξ (x i) * star (jointPhase ξ (x j))))
      (actualFourierMeasure F) := by
    apply (integrable_const a).mul_bdd (c := 1) hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by simp only [norm_mul, norm_star, norm_jointPhase, one_mul, le_refl]
  apply hi.congr
  exact Filter.Eventually.of_forall fun ξ => by
    rw [s.withMultiplier_transformedRow]
    exact mul_comm _ _

def rawPhaseNonzeroCost
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest) (x : ι → W) (ξ : W) : ℝ :=
  (s.withMultiplier (fun i => jointPhase ξ (x i))).rawNonzeroCost

/-- The finite carrier consists of actual physical dual rows.  The
continuous Fourier parameter still ranges over the whole space. -/
theorem rawPhaseNonzeroCost_integrable
    (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
    (F : SchwartzMap W ℂ) (x : ι → W) :
    Integrable (s.rawPhaseNonzeroCost x) (actualFourierMeasure F) := by
  change Integrable (fun ξ : W =>
    ∑ DE, ∑ D : s.mask.powerset,
      ‖∑ q ∈ (s.sources DE).rows,
        ∑ i ∈ (s.sources DE).leftColumns, ∑ j ∈ (s.sources DE).rightColumns,
          (((s.withMultiplier (fun i => jointPhase ξ (x i))).sources DE).pairs i j).
            transformedRow μv hDiff finiteTest s.radius D.val q‖) (actualFourierMeasure F)
  apply integrable_finsetSum
  intro DE _
  apply integrable_finsetSum
  intro D _
  apply Integrable.norm
  exact integrable_finsetSum _ (fun q _ =>
    integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => s.phase_transformedRow_integrable F x DE D q i j)))

namespace TerminalCalibration

variable {s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Z Lmax Nsave decay : ℝ}

theorem rawPhaseCost_integrable
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => (T.fourierPhase x ξ).rawCost ε Cerror Czero)
      (actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change Integrable (fun ξ => (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.rawPhaseNonzeroCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))) (actualFourierMeasure F)
  exact (((integrable_const _).add (s.rawPhaseNonzeroCost_integrable F x)).add
    (integrable_const _)).const_mul (s.fiber : ℝ)

theorem integral_rawPhaseCost
    (T : s.TerminalCalibration sTail sZero k Z Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    (∫ ξ, (T.fourierPhase x ξ).rawCost ε Cerror Czero ∂actualFourierMeasure F) =
      (s.fiber : ℝ) *
        ((actualFourierMeasure F).real Set.univ *
          (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
            Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave)) +
          ∫ ξ, s.rawPhaseNonzeroCost x ξ ∂actualFourierMeasure F) := by
  letI := actualFourierMeasure_finite F
  change (∫ ξ, (s.fiber : ℝ) *
    (Czero * (T.windows.multiplicity * T.zeroAmplitude) * Z ^ (T.productExponent * ε) +
      s.rawPhaseNonzeroCost x ξ +
      Cerror * (T.windows.multiplicity * T.tailAmplitude) * Z ^ (-Nsave))
        ∂actualFourierMeasure F) = _
  rw [integral_const_mul,
    integral_add ((integrable_const _).add (s.rawPhaseNonzeroCost_integrable F x)) (integrable_const _),
    integral_add (integrable_const _) (s.rawPhaseNonzeroCost_integrable F x),
    integral_const, integral_const]
  simp only [smul_eq_mul]
  ring

end TerminalCalibration
end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest}
variable {sTail sZero : Finset (ℕ × ℕ)} {k : ℕ} {Lmax Nsave decay : ℝ}

theorem ActualPoolStages.TerminalCalibration.rawPhaseCost_integrable
    (T : s.TerminalCalibration sTail sZero k Lmax Nsave decay)
    (F : SchwartzMap W ℂ) (x : ι → W) (ε Cerror Czero : ℝ) :
    Integrable (fun ξ => T.rawPhaseCost x ξ ε Cerror Czero) (actualFourierMeasure F) := by
  unfold ActualPoolStages.TerminalCalibration.rawPhaseCost
  apply Integrable.const_mul
  apply Integrable.add
  · apply Integrable.add
    · apply Integrable.add
      · exact (T.main.rawPhaseCost_integrable F x ε Cerror Czero).const_mul d.multiplicity
      · exact integrable_finsetSum _ (fun p _ =>
          ((T.one p).rawPhaseCost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)
    · exact integrable_finsetSum _ (fun p _ =>
        ((T.six p).rawPhaseCost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)
  · exact integrable_finsetSum _ (fun p _ =>
      ((T.seven p).rawPhaseCost_integrable F (fun i => x i.val) ε Cerror Czero).const_mul _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.transformedRow_profile_smul
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.withMultiplier_transformedRow
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.rawPhaseNonzeroCost_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualPoolStages.TerminalCalibration.rawPhaseCost_integrable
