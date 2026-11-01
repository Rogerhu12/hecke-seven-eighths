import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalBlockRowSectors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.LiveSourceConditions
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogTiltWindows

/-!
# The literal row profile of a live original source is bounded by one

A nonempty original physical row set and its original norm calibration
force the retained scale times its enlargement to be at least one. The
canonical primal radius is its reciprocal. The empty row-mask generator
has norm one, while every original subgroup orbit has norm at least one.
Thus the exact negative Mellin row tilt is bounded by one at every dual
row, before the ordinary/exceptional partition.

The final wrapper obtains physical nonemptiness from the actual fibre
leaf. It does not infer it from a bare unscaled leaf or from a nonzero
normalized descendant, and it does not replace an already chosen N.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.Support WholeAllocation

variable {K : Type} [Field K] [NumberField K]

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
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
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


namespace CanonicalSecondLogChart

/-- This applies to the actual empty-mask generator; its element is
not identified with one, only its proved norm is used. -/
theorem unmasked_rowTilt_norm_le_one
    (r : {r : ℝ // 0 < r}) (hr : r.val ≤ 1)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖(((rowRadius r (∅ : Finset (HeightOneSpectrum A.R)) q).val ^ (-δ) : ℝ) : ℂ)‖ ≤ 1 := by
  have hwindow : r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅)).val ≤
      (1 : ℝ) ^ (0 : ℝ) := by
    rw [sIntegerMaskGenerator_empty_norm K A.Sf, mul_one, Real.rpow_zero]
    exact hr
  simpa only [zero_mul, Real.one_rpow] using
    rowTilt_norm_le_of_norm_window r ∅ q (Z := 1) (B := 0) (δ := δ)
      (by norm_num) hδ hwindow

end CanonicalSecondLogChart

namespace ActualGaussStage

variable {hΓ μv hDiff ν}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad

include hnorm in
/-- The lower bound comes from one genuine original nonzero ideal,
not from a dual-row window or a completed child bound. -/
theorem retainedScale_enlargement_one_of_physical_rows (hrows : G.rows.Nonempty) :
    1 ≤ retainedScale * Z ^ g := by
  obtain ⟨h, hh⟩ := hrows
  have hone : 1 ≤ A.exteriorNorm (originalFrequencyIdeal h) := by
    change (1 : ℝ) ≤ Ideal.absNorm (originalFrequencyIdeal h).val
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (originalFrequencyIdeal h).property.1)
  exact hone.trans (hnorm h hh)

/-- All original support and coefficient gates retain exactly this
row factor. Only the fixed finite sector classifier was enlarged. -/
@[simp] theorem canonicalSector_prepared_weight
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((stage).supported.gated.charts DE D).weight q =
      (((CanonicalSecondLogChart.rowRadius
        (CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ) D.val q).val ^ (-δ) : ℝ) : ℂ) := rfl

/-- The actual original source supplies a constant-one row-profile
window for every dual row, with no label or cutoff dependence. -/
theorem canonicalSector_prepared_weight_norm_le_one
    (hrows : G.rows.Nonempty)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : (∅ : Finset (HeightOneSpectrum A.R)).powerset)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ‖((stage).supported.gated.charts DE D).weight q‖ ≤ 1 := by
  have hproduct := retainedScale_enlargement_one_of_physical_rows
    G retainedScale Z g hnorm hrows
  have hr : (CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ).val ≤ 1 := by
    have hp : 0 < retainedScale * Z ^ g := mul_pos hscale (Real.rpow_pos_of_pos hZ g)
    have hdiv : (1 : ℝ) / (retainedScale * Z ^ g) ≤ 1 :=
      (div_le_iff₀ hp).mpr (by simpa only [one_mul] using hproduct)
    simpa only [CanonicalRowBall.gaussRadius, one_div] using hdiv
  rw [canonicalSector_prepared_weight, emptyMask_divisor_eq D]
  exact CanonicalSecondLogChart.unmasked_rowTilt_norm_le_one
    (CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ) hr q δ hδ.le

variable (LC RC : SourceCartesianCover G.columns G.ideal)
variable (exceptional : (canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoverHybridPredicates LC RC)
variable (F : SchwartzMap ℝ ℂ) (x : ι → ℝ)
variable (leaf : (canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ hδ hδhalf G retainedScale Z g hscale hZ cutoff hcutoff hnorm
  dimension width character dyad).supported.gated.CoveredLeafKey LC RC)

/-- This is the constant-one profile window for the same literal
covered leaf. Original physical nonemptiness is recovered internally
from its existing fibre multiplier and its actual `Live` condition. -/
theorem canonicalSector_fiberLeaf_rowProfile_one
    (hlive : ((stage).supported.gated.fiberCoveredLeaf LC RC exceptional F x leaf).Live) :
    ∀ q ∈ (leaf.1.chart.actualRows ∅ cutoff hcutoff leaf.1.rowLabel).rows,
      ‖leaf.1.chart.weight q‖ ≤ 1 := by
  have hrows := ((stage).supported_gated_fiberLeaf_live LC RC exceptional F x leaf hlive).1
  intro q _
  exact canonicalSector_prepared_weight_norm_le_one P δ hδ hδhalf G retainedScale Z g
    hscale hZ cutoff hcutoff hnorm dimension width character dyad hrows
    leaf.1.1 leaf.1.2.1 q

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.unmasked_rowTilt_norm_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalSector_prepared_weight_norm_le_one
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalSector_fiberLeaf_rowProfile_one
