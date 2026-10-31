import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredPositiveEnergy

/-!
# Production first-parent bound with one fixed center grid

The left-hand side is the whole literal retained parent. Both energies
on the right contain all original cube pairs, extraction keys, mask
divisors and Γ sectors, the full overlap Möbius pool, the original
squared assigned marks and the genuine Fourier/Mellin measures.

Each displayed inverse family uses the same grid center at its center
index. The pointwise density comparison is constructed from the actual
orbital Fourier kernel; it is not an input to the production theorem.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentProduction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open FirstParentEnergy FirstNormPoolEnergy FirstMobiusGeometry FirstColumnAssembly
  FirstPositiveSource FirstCenteredPositiveEnergy FirstCommonEnvelope CanonicalFirstEnergy
  CommonKernel
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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {σ ι : Type*} [Fintype ι]

/-- One common grid precedes every actual row and source label. The
assignment records only proved annular membership of extracted norms. -/
structure Centering (T : FirstParentEnergy.Data K S (σ := σ))
    (grid : ι → {r : ℝ // 0 < r}) where
  assignment : ∀ side : Bool, ∀ i : FirstParentEnergy.Index K S D Γ T,
    overlapPool K S T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false → ι
  lower : ∀ side i e, (grid (assignment side i e)).val ≤
    extractedHeight K S (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val side
      (overlapIdeal K S D T.scale (selectedAnchor K S D Γ T i).1
        (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false e)
  upper : ∀ side i e, extractedHeight K S
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val side
      (overlapIdeal K S D T.scale (selectedAnchor K S D Γ T i).1
        (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false e) ≤
    2 * (grid (assignment side i e)).val

def Centering.at (T : FirstParentEnergy.Data K S (σ := σ))
    (grid : ι → {r : ℝ // 0 < r}) (centers : Centering K S D Γ T grid)
    (side : Bool) (i : FirstParentEnergy.Index K S D Γ T) :
    FirstCenteredPositiveEnergy.Centering K S D ι T.scale
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val side where
  center := grid
  assignment := centers.assignment side i
  lower := centers.lower side i
  upper := centers.upper side i

def radialScale (T : FirstParentEnergy.Data K S (σ := σ))
    (i : FirstParentEnergy.Index K S D Γ T) : ℝ :=
  FirstCommonEnvelope.radialScale K S D T.radius (selectedDivisor K S D Γ T i)
    (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val
    (residualScale K S T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false)
    (residualScale K S T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val true)

variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (grid : ι → {r : ℝ // 0 < r}) (centers : Centering K S D Γ T grid)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)

def centeredTotal (ε : ℝ) (m : ℕ) (side : Bool) : ℝ :=
  ∑ i : FirstParentEnergy.Index K S D Γ T,
    FirstParentEnergy.outerWeight K S D Γ T i *
      (radialScale K S D Γ T i ^ ε *
        FirstCenteredPositiveEnergy.centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
          (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
          i.1.val i.2.1.val side (Centering.at K S D Γ T grid centers side i)
          (CanonicalIdealRow.ofExterior K S T.label)
          (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
          (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 W hW (frequencyEnvelope m))

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

def originalSideTotal (side : Bool) : ℝ :=
  if side then FirstParentEnergy.totalRight K S D Γ μv ν G T
  else FirstParentEnergy.totalLeft K S D Γ μv ν G T

theorem left_energy_source (i : FirstParentEnergy.Index K S D Γ T) :
    FirstParentEnergy.leftEnergy K S D Γ μv ν G T i =
    sourceEnergy K S D Γ T.columns G (selectedProfile K S D Γ μv ν T i) T.scale
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val false (CanonicalIdealRow.ofExterior K S T.label)
      (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 := rfl

theorem right_energy_source (i : FirstParentEnergy.Index K S D Γ T) :
    FirstParentEnergy.rightEnergy K S D Γ μv ν G T i =
    sourceEnergy K S D Γ T.columns G (selectedProfile K S D Γ μv ν T i) T.scale
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val true (CanonicalIdealRow.ofExterior K S T.label)
      (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 := rfl

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed hΓ in
private theorem side_total_le
    (hGunramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G p)
    (hCX : T.columns.base ^ T.columns.length = T.scale.val)
    (hZ : 1 < T.columns.base) (hCW : T.columns.cutoff = W)
    (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
    (ε : ℝ) (m : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hdensity : ∀ i : FirstParentEnergy.Index K S D Γ T, ∀ η : LogPlane,
      ‖(selectedProfile K S D Γ μv ν T i).density K S Γ η‖ ≤
        (A * radialScale K S D Γ T i ^ ε) * frequencyEnvelope m η)
    (side : Bool) :
    originalSideTotal K S D Γ T G μv ν side ≤
      A * centeredTotal K S D Γ T Θ ψ G hν hG grid centers W hW ε m side := by
  have hpoint (i : FirstParentEnergy.Index K S D Γ T) :
      sourceEnergy K S D Γ T.columns G (selectedProfile K S D Γ μv ν T i) T.scale
        (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
        i.1.val i.2.1.val side (CanonicalIdealRow.ofExterior K S T.label)
        (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
        (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 ≤
      (A * radialScale K S D Γ T i ^ ε) *
        FirstCenteredPositiveEnergy.centeredEnergy K S D Γ T.columns Θ ψ G hν hG T.scale
          (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
          i.1.val i.2.1.val side (Centering.at K S D Γ T grid centers side i)
          (CanonicalIdealRow.ofExterior K S T.label)
          (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
          (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 W hW (frequencyEnvelope m) := by
    have hrad : 0 < radialScale K S D Γ T i :=
      FirstCommonEnvelope.radialScale_pos K S D T.radius (selectedDivisor K S D Γ T i)
        _ _ _ _ _ _
    exact sourceEnergy_le_of_density_bound K S D Γ T.columns Θ ψ G hν hG T.scale
      (selectedAnchor K S D Γ T i).1 (selectedAnchor K S D Γ T i).2
      i.1.val i.2.1.val side (Centering.at K S D Γ T grid centers side i)
      (CanonicalIdealRow.ofExterior K S T.label)
      (CanonicalIdealRow.ofExterior K S i.2.2.2.2.val.1)
      (selectedDivisor K S D Γ T i).val i.2.2.2.2.val.2 W hW hΓ hallowed
      hGunramified hCX hZ hCW hprime (selectedProfile K S D Γ μv ν T i)
      (frequencyEnvelope m) (frequencyEnvelope_integrable m) (frequencyEnvelope_nonneg m)
      (A * radialScale K S D Γ T i ^ ε)
      (mul_nonneg hA (Real.rpow_nonneg hrad.le ε)) (hdensity i)
  unfold originalSideTotal centeredTotal
  rw [Finset.mul_sum]
  cases side
  · simp only [Bool.false_eq_true, if_false, FirstParentEnergy.totalLeft]
    apply Finset.sum_le_sum
    intro i hi
    rw [left_energy_source K S D Γ T G μv ν]
    exact (mul_le_mul_of_nonneg_left (hpoint i)
      (outerWeight_nonneg K S D Γ T i)).trans_eq (by ring)
  · simp only [if_true, FirstParentEnergy.totalRight]
    apply Finset.sum_le_sum
    intro i hi
    rw [right_energy_source K S D Γ T G μv ν]
    exact (mul_le_mul_of_nonneg_left (hpoint i)
      (outerWeight_nonneg K S D Γ T i)).trans_eq (by ring)

include hallowed hΓ ν in
/-- The complete literal retained first parent is controlled by two
positive energies of actual inverse columns at fixed centers. The
finite seminorm family and constant are selected before the original
Schwartz test, every arithmetic source, the finite center grid and its
assignments. The common Fourier density estimate is proved from the
orbital kernel and is not a premise. -/
theorem exists_canonicalRetained_centered_bound
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ₀ ι₀ : Type*} [Fintype ι₀],
      ∀ (T₀ : FirstParentEnergy.Data K S (σ := σ₀)), T₀.localTest = h →
      ∀ (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ G₀ : HeckeCharacter K),
      ∀ (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ T₀.columns.background) (hG₀ : G₀ ∈ Θ₀),
      ∀ (grid₀ : ι₀ → {r : ℝ // 0 < r}) (centers₀ : Centering K S D Γ T₀ grid₀),
      ∀ (W₀ : SchwartzMap ℝ ℂ) (hW₀ : tsupport W₀ ⊆ Set.Icc (1 : ℝ) 2),
        (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K G₀ p) →
        T₀.columns.base ^ T₀.columns.length = T₀.scale.val →
        1 < T₀.columns.base → T₀.columns.cutoff = W₀ →
        (∀ k ∈ T₀.columns.slots, ∀ p ∈ T₀.columns.primeLists k, Prime p) →
        ThetaCalibrationInput K Sset D T₀.columns.lambda G₀ →
        ‖FirstDualTruncation.canonicalRetained K S D Γ hΓ μv
          T₀.columns T₀.label T₀.cubes (FirstParentEnergy.columnPool K S T₀)
          T₀.archTest T₀.localTest T₀.locallyConstant T₀.compactSupport
          T₀.mask T₀.radius T₀.frequencyBound‖ ≤
        (A * s.sup (schwartzSeminormFamily ℝ V ℂ) T₀.archTest) *
          (Real.sqrt (centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
            grid₀ centers₀ W₀ hW₀ ε m false) *
           Real.sqrt (centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
            grid₀ centers₀ W₀ hW₀ ε m true)) := by
  obtain ⟨s, A, hA, hb⟩ := exists_first_density_common_envelope
    K S D Γ μv ν h hlc hcs ε hε m
  refine ⟨s, A, hA, ?_⟩
  intro σ₀ ι₀ _ T₀ hlocal Θ₀ ψ₀ G₀ hν₀ hG₀ grid₀ centers₀ W₀ hW₀
    hGunramified hCX hZ hCW hprime hcal
  subst h
  let M := A * s.sup (schwartzSeminormFamily ℝ V ℂ) T₀.archTest
  have hM : 0 ≤ M := mul_nonneg hA (apply_nonneg _ _)
  have hdensity (i : FirstParentEnergy.Index K S D Γ T₀) (η : LogPlane) :
      ‖(selectedProfile K S D Γ μv ν T₀ i).density K S Γ η‖ ≤
        (M * radialScale K S D Γ T₀ i ^ ε) * frequencyEnvelope m η := by
    exact hb T₀.archTest T₀.radius (selectedDivisor K S D Γ T₀ i)
      (selectedAnchor K S D Γ T₀ i).1 (selectedAnchor K S D Γ T₀ i).2
      i.1.val i.2.1.val i.2.2.2.2.val.1
      (residualScale K S T₀.scale (selectedAnchor K S D Γ T₀ i).1
        (selectedAnchor K S D Γ T₀ i).2 i.1.val i.2.1.val false)
      (residualScale K S T₀.scale (selectedAnchor K S D Γ T₀ i).1
        (selectedAnchor K S D Γ T₀ i).2 i.1.val i.2.1.val true) η
  have hleft : FirstParentEnergy.totalLeft K S D Γ μv ν G₀ T₀ ≤
      M * centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀ grid₀ centers₀ W₀ hW₀ ε m false :=
    side_total_le K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀ grid₀ centers₀ W₀ hW₀ μv ν hΓ hallowed
      hGunramified hCX hZ hCW hprime ε m M hM hdensity false
  have hright : FirstParentEnergy.totalRight K S D Γ μv ν G₀ T₀ ≤
      M * centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀ grid₀ centers₀ W₀ hW₀ ε m true :=
    side_total_le K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀ grid₀ centers₀ W₀ hW₀ μv ν hΓ hallowed
      hGunramified hCX hZ hCW hprime ε m M hM hdensity true
  refine (FirstParentEnergy.canonicalRetained_norm_le K S D Γ μv ν hΓ
    hallowed G₀ T₀ hcal).trans ?_
  calc
    _ ≤ Real.sqrt (M * centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
          grid₀ centers₀ W₀ hW₀ ε m false) *
        Real.sqrt (M * centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
          grid₀ centers₀ W₀ hW₀ ε m true) :=
      mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hM, Real.sqrt_mul hM]
      have hs : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM
      calc
        _ = (Real.sqrt M * Real.sqrt M) *
          (Real.sqrt (centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
            grid₀ centers₀ W₀ hW₀ ε m false) *
           Real.sqrt (centeredTotal K S D Γ T₀ Θ₀ ψ₀ G₀ hν₀ hG₀
            grid₀ centers₀ W₀ hW₀ ε m true)) := by ring
        _ = _ := by rw [hs]

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentProduction

end

