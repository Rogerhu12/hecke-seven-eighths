import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualGaussStage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre

/-!
# Original row coordinates for the constructed Gauss stage

The classifier of the actual canonical stage is the encoding of its
original nonunit-prime subset, finite character class and bounded
dyadic coordinates.  Its `OriginalFibreRows` witness is constructed
below from that literal code.  No size bound for the declared chart
label type is an input.

The remaining arithmetic inputs identify the primes of the original
mask and row support with divisors of their original nonzero ideals,
and give the two original ideal norm windows.  A frequency norm bound
is neither used as a substitute for these identities nor used to
choose a new row partition.  The uniform row-image constant is chosen
before the scale, row set and all values of the original classifier.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}

namespace OriginalGaussRowClassifier

/-- The original support ideal, rather than the size of the frequency
set or the declared label codomain, pays for its Boolean coordinate. -/
theorem labels_uniform_subpower {Θ : Type*} [Fintype Θ]
    (dimension width : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ (support : Finset (HeightOneSpectrum (𝓞 K))) (rowIdeal : Ideal (𝓞 K)),
      rowIdeal ≠ 0 → (Ideal.absNorm rowIdeal : ℝ) ≤ Z ^ B →
      (∀ p ∈ support, p.asIdeal ∣ rowIdeal) →
      ∀ (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
        (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
          Fin dimension → Fin (width + 1))
        (rows : Finset (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)),
        ((rows.image (label support dimension width character dyad)).card : ℝ) ≤
          C * Z ^ ε := by
  obtain ⟨Cm, hCm, hmask⟩ := original_mask_labels_subpower (K := K) B ε hB hε
  let fixed : ℝ := (Fintype.card Θ : ℝ) * ((width + 1 : ℕ) : ℝ) ^ dimension
  have hfixed : 0 ≤ fixed := by dsimp [fixed]; positivity
  refine ⟨Cm * (fixed + 1), mul_pos hCm (by linarith), ?_⟩
  intro Z hZ support rowIdeal hrow hnorm hdiv character dyad rows
  let primes : OriginalMaskPrimeData support rowIdeal :=
    { prime := id
      injective := fun _ _ _ _ he => he
      divides := hdiv }
  have hs : (2 : ℝ) ^ support.card ≤ Cm * Z ^ ε := by
    simpa only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat] using
      hmask Z hZ support rowIdeal hrow hnorm primes
  have hc : ((rows.image (label support dimension width character dyad)).card : ℝ) ≤
      ((2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension : ℕ) : ℝ) := by
    exact_mod_cast labels_card_le support dimension width character dyad rows
  calc
    _ ≤ (2 : ℝ) ^ support.card * fixed := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, fixed, mul_assoc] using hc
    _ ≤ (Cm * Z ^ ε) * fixed := mul_le_mul_of_nonneg_right hs hfixed
    _ ≤ (Cm * Z ^ ε) * (fixed + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
        (mul_nonneg hCm.le (Real.rpow_nonneg (zero_le_one.trans hZ) ε))
    _ = (Cm * (fixed + 1)) * Z ^ ε := by ring

end OriginalGaussRowClassifier

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable {ν : Measure (FiniteAdeleRing (𝓞 K) K)} [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace ActualGaussStage

variable (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
variable {ι : Type*} (G : ActualGaussSource C ι)
variable (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
variable (mask : Finset (HeightOneSpectrum A.R)) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
variable (hnorm : ∀ h ∈ G.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (havoid : ∀ h ∈ G.rows, ∀ p ∈ mask, h ∉ p.asIdeal)
variable (hcolumn : ∀ i ∈ G.columns, IsCoprime (G.generator i)
  (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask).val)
variable {Θ : Type*} [Fintype Θ]
variable (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

/-- The code is the one used by the actual constructed charts.  Every
classifier equality below holds on all original orbits, hence also on
the exact finite source rows used by the covered-leaf fibre proof. -/
def canonicalRowBallOriginalFibreRows
    (B : ℝ) (maskIdeal rowIdeal : Ideal (𝓞 K))
    (hmaskIdeal : maskIdeal ≠ 0) (hrowIdeal : rowIdeal ≠ 0)
    (maskPrimes : OriginalMaskPrimeData mask maskIdeal)
    (row_divides : ∀ p ∈ support, p.asIdeal ∣ rowIdeal)
    (mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (row_norm : (Ideal.absNorm rowIdeal : ℝ) ≤ Z ^ B) :
    (canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).OriginalFibreRows
        Θ dimension width B Z where
  support _ := support
  maskIdeal := maskIdeal
  rowIdeal _ := rowIdeal
  mask_nonzero := hmaskIdeal
  row_nonzero _ := hrowIdeal
  maskPrimes := maskPrimes
  row_divides _ := row_divides
  mask_norm := mask_norm
  row_norm _ := row_norm
  code DE D := OriginalGaussRowClassifier.code support dimension width
    (character DE D) (dyad DE D)
  encode _ _ := OriginalGaussRowClassifier.encode support dimension width
  row_label _ _ _ _ := rfl

/-- No extra class is inserted between the original coordinates and
the actual row label.  Equality of actual labels determines the whole
original code, not merely a bound for the physical frequency. -/
theorem canonicalRowBall_rowLabel_eq_iff
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset)
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    ((canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).charts DE D).rowLabel q =
    ((canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).charts DE D).rowLabel q' ↔
      OriginalGaussRowClassifier.nonunitSupport support q =
        OriginalGaussRowClassifier.nonunitSupport support q' ∧
        character DE D q = character DE D q' ∧ dyad DE D q = dyad DE D q' := by
  simpa only [canonicalRowBall_rowLabel] using
    OriginalGaussRowClassifier.label_eq_iff support dimension width
      (character DE D) (dyad DE D) q q'

/-- This counts precisely the labels present in the actual finite
second source.  The unused value in its `Fin (count + 1)` carrier is
never charged. -/
theorem canonicalRowBall_actualRowLabels_card_le
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).actualRowLabels DE D).card ≤
      2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension := by
  apply actualRowLabels_card_le _ _ _ support dimension width
    (OriginalGaussRowClassifier.code support dimension width (character DE D) (dyad DE D))
    (OriginalGaussRowClassifier.encode support dimension width)
  intro q _
  rfl

end ActualGaussStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussRowClassifier.labels_uniform_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBallOriginalFibreRows
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBall_rowLabel_eq_iff
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBall_actualRowLabels_card_le
