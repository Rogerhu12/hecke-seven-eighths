import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussStage

/-!
# A second positive row ball with no additional row avoidance mask

The Gauss energy already contains the original complete column
coefficients.  Its positive row majorant may therefore use the empty
row avoidance mask.  This is a choice of the majorant in the proved
Gauss-stage theorem, made before either second common ideal is chosen.
The original source, its columns and every mask in its coefficients
remain unchanged.

The empty mask has one divisor.  Its chosen generator need not be the
element one, but it is a unit and its actual arithmetic norm is one.
Thus no extra mask norm enters the physical frequency cutoff.  The
unit phase itself is retained by the original second chart.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

section EmptyMask

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

theorem empty_mask_generator_dvd_one :
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅).val ∣ 1 := by
  change IdealMobiusMask.maskGenerator ∅ ∣ 1
  rw [IdealMobiusMask.maskGenerator_dvd_iff]
  simp [IdealMobiusMask.primeProduct]

theorem empty_mask_generator_coprime
    (a : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    IsCoprime a
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅).val :=
  IsCoprime.of_isCoprime_of_dvd_right isCoprime_one_right
    (empty_mask_generator_dvd_one S)

/-- A norm identity, not an unjustified equality between chosen units. -/
theorem empty_mask_generator_norm :
    (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅)).val = 1 := by
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm]
  have hspan : Ideal.span
      ({(sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅).val} :
        Set (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) = ⊤ := by
    change Ideal.span {IdealMobiusMask.maskGenerator ∅} = ⊤
    unfold IdealMobiusMask.maskGenerator
    rw [Submodule.IsPrincipal.span_singleton_generator]
    simp [IdealMobiusMask.primeProduct]
  rw [hspan]
  simp

theorem empty_mask_divisor_eq_empty
    (D : (∅ : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))).powerset) :
    D.val = ∅ :=
  Finset.eq_empty_of_subset_empty (Finset.mem_powerset.mp D.property)

variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}

/-- The true inverse dual radius has exactly the radius and modulus
norm factors when the independently chosen row majorant is unmasked. -/
theorem ParentPeriodicPair.inverse_dualRadius_empty
    (p : ParentPeriodicPair K S Γ) (r : {r : ℝ // 0 < r}) :
    ((p.dualRadius r ∅).val)⁻¹ = r.val *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨p.modulus, p.modulus_ne_zero⟩).val := by
  change (((r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) ∅)).val) *
      (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        ⟨p.modulus, p.modulus_ne_zero⟩).val)⁻¹)⁻¹ = _
  rw [inv_inv, empty_mask_generator_norm, mul_one]

end EmptyMask

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
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

namespace ActualGaussStage

variable {hΓ μv hDiff ν}

/-- Construct the second stage from the very original Gauss source.
No avoidance or column coprimality premise is needed for its new row
ball.  Masks already present in G.coefficient are retained literally. -/
def canonicalUnmaskedRowBall
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {ι : Type*} (G : ActualGaussSource C ι)
    (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
    (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
    {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1)) :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G (rowBallFiniteFamily K A.Sf 1) :=
  canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
    δ hδ hδhalf G retainedScale Z g hscale hZ ∅ cutoff hcutoff hnorm
    (by intro h hh p hp; exact False.elim (Finset.not_mem_empty p hp))
    (fun i _ => empty_mask_generator_coprime A.Sf (G.generator i))
    support dimension width (fun DE _ => character DE) (fun DE _ => dyad DE)

section Projections

variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ]
variable (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

@[simp] theorem canonicalUnmaskedRowBall_mask :
    (canonicalUnmaskedRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      support dimension width character dyad).mask = ∅ := rfl

@[simp] theorem canonicalUnmaskedRowBall_radius :
    (canonicalUnmaskedRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      support dimension width character dyad).radius.val =
        (retainedScale * Z ^ g)⁻¹ := rfl

@[simp] theorem canonicalUnmaskedRowBall_profile :
    (canonicalUnmaskedRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      support dimension width character dyad).profile =
        CanonicalRowBall.archTest K A.Sf 1 := rfl

theorem canonicalUnmaskedRowBall_source_profile
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (i j : ι) :
    (((canonicalUnmaskedRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
      support dimension width character dyad).sources DE).pairs i j).profile =
        (G.coefficient i * star (G.coefficient j)) •
          CanonicalRowBall.archTest K A.Sf 1 := rfl

end Projections

end ActualGaussStage

variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The original uniform Poisson theorem bounds this constructed
majorant of the same G.energy, with no input energy comparison. -/
theorem canonical_unmasked_gauss_stage_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B Drecipe)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ
      (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {ι : Type*} (G : ActualGaussSource C ι),
    ∀ retainedScale Z g : ℝ, ∀ (hscale : 0 < retainedScale) (hZ : 0 < Z),
    ∀ cutoff : ℝ, ∀ hcutoff : 1 ≤ cutoff,
    ∀ hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g,
    ∀ {Θ : Type*} [Fintype Θ],
    ∀ (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ),
    ∀ (character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ),
    ∀ (dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1)),
      G.energy hDiff ≤
        (ActualGaussStage.canonicalUnmaskedRowBall
          (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
          δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
          support dimension width character dyad).cost seminorms Ctail decay := by
  obtain ⟨seminorms, Ctail, hC, hbound⟩ :=
    actual_gauss_stage_bound (E := ℝ) (ν := ν) (μ := μ) hΓ μv hDiff C Drecipe hD
      (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro ι G retainedScale Z g hscale hZ cutoff hcutoff hnorm Θ _ support dimension width character dyad
  exact hbound G _

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.empty_mask_generator_norm
#print axioms HeckeSkeleton.Moments.EngineStep.ParentPeriodicPair.inverse_dualRadius_empty
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalUnmaskedRowBall
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_unmasked_gauss_stage_bound
