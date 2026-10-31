import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalFibreRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyClassStability

/-!
# Canonical second charts with their actual common-block row classes

Each common block uses its own complete original prime set.  The first
row coordinate records the genuine nonunit divided-frequency condition,
including equal multiplicities, nonprincipal depth and the extra prime
power.  It is not the divisibility of the unextracted frequency by one
prime.  The remaining coordinates are the original finite character and
dyadic classifiers.

The stage has the same source, positive profile, radius, physical rows,
fibre, complete coefficients and full-log kernel as the canonical row-ball
construction.  Only its per-block row partition is specified here.  The
row-support ideal in its fibre certificate is the actual first common
ideal of that block; its norm window follows from an original column
window.  There is no norm bound for a union of all column supports.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}

namespace FirstCommonCharacterBlock

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock fullI fullJ DE)

/-- All original common primes, including primes whose two characters
have equal exponents.  No active-radical restriction is made. -/
def originalPrimeSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
  Finset.univ.image (fun i => (b.primes i).val)

theorem originalPrimeSupport_ideal_image :
    b.originalPrimeSupport.image (fun p => p.asIdeal) = primeSupport DE.1 := by
  rw [← b.common_left,
    primePowerProduct_support b.primes b.primes_injective b.leftMultiplicity b.left_positive]
  simp only [originalPrimeSupport, Finset.image_image, Function.comp_def]

theorem originalPrimeSupport_divides (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ b.originalPrimeSupport) : p.asIdeal ∣ DE.1 := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact b.originalCommonPrimeData.divides i (Finset.mem_univ i)

/-- The actual divided-frequency selection at this block's original
multiplicities.  The image remains a subset of its complete prime set. -/
def dividedNonunitSupport (C : A.GeneralArithmeticContext σ η htrace) (h : A.R) :
    b.originalPrimeSupport.powerset :=
  ⟨(Finset.univ.filter (fun i => nonunitFrequencySaving C (b.primes i)
      (b.leftMultiplicity i) (b.rightMultiplicity i) h)).image (fun i => (b.primes i).val),
    Finset.mem_powerset.mpr (Finset.image_subset_image (Finset.filter_subset _ _))⟩

@[simp] theorem prime_mem_dividedNonunitSupport
    (C : A.GeneralArithmeticContext σ η htrace) (h : A.R) (i : Fin b.primeCount) :
    (b.primes i).val ∈ (b.dividedNonunitSupport C h).val ↔
      nonunitFrequencySaving C (b.primes i)
        (b.leftMultiplicity i) (b.rightMultiplicity i) h := by
  change (b.primes i).val ∈ (Finset.univ.filter (fun j => nonunitFrequencySaving C
    (b.primes j) (b.leftMultiplicity j) (b.rightMultiplicity j) h)).image
      (fun j => (b.primes j).val) ↔ _
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    have hji : j = i := b.primes_injective (Subtype.ext he)
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩

theorem nonunitSaving_iff_of_dividedSupport_eq
    (C : A.GeneralArithmeticContext σ η htrace) (h h' : A.R)
    (he : b.dividedNonunitSupport C h = b.dividedNonunitSupport C h')
    (i : Fin b.primeCount) :
    nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i) h ↔
      nonunitFrequencySaving C (b.primes i)
        (b.leftMultiplicity i) (b.rightMultiplicity i) h' := by
  have hm : (b.primes i).val ∈ (b.dividedNonunitSupport C h).val ↔
      (b.primes i).val ∈ (b.dividedNonunitSupport C h').val := by rw [he]
  simpa only [prime_mem_dividedNonunitSupport] using hm

theorem nonunitRadical_eq_of_dividedSupport_eq
    (C : A.GeneralArithmeticContext σ η htrace) (h h' : A.R)
    (he : b.dividedNonunitSupport C h = b.dividedNonunitSupport C h') :
    nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity h =
      nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity h' := by
  unfold nonunitFrequencyRadical
  congr 1
  funext i
  rw [b.nonunitSaving_iff_of_dividedSupport_eq C h h' he i]

end FirstCommonCharacterBlock

namespace OriginalBlockGaussRowClassifier

variable {Γ : Subgroup A.U}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (b : FirstCommonCharacterBlock fullI fullJ DE)

def code {Θ : Type*} (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    OriginalFiniteFibre.RowCode b.originalPrimeSupport Θ dimension width :=
  (b.dividedNonunitSupport C (-q.out.val), character q, dyad q)

def label {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    Fin (Fintype.card (OriginalFiniteFibre.RowCode b.originalPrimeSupport
      Θ dimension width) + 1) :=
  OriginalGaussRowClassifier.encode b.originalPrimeSupport dimension width
    (code C b dimension width character dyad q)

theorem label_eq_iff {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    label C b dimension width character dyad q = label C b dimension width character dyad q' ↔
      b.dividedNonunitSupport C (-q.out.val) = b.dividedNonunitSupport C (-q'.out.val) ∧
        character q = character q' ∧ dyad q = dyad q' := by
  change OriginalGaussRowClassifier.encode b.originalPrimeSupport dimension width
    (code C b dimension width character dyad q) =
      OriginalGaussRowClassifier.encode b.originalPrimeSupport dimension width
        (code C b dimension width character dyad q') ↔ _
  rw [(OriginalGaussRowClassifier.encode_injective
    b.originalPrimeSupport dimension width).eq_iff]
  simp only [code, Prod.mk.injEq]

/-- This is the exact per-prime hypothesis consumed by the live-row
unit/nonunit, factor and norm-factor stability theorems. -/
theorem nonunitSaving_iff_of_label_eq {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (he : label C b dimension width character dyad q =
      label C b dimension width character dyad q') (i : Fin b.primeCount) :
    nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
        (-q.out.val) ↔
      nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
        (-q'.out.val) :=
  b.nonunitSaving_iff_of_dividedSupport_eq C _ _
    ((label_eq_iff C b dimension width character dyad q q').mp he).1 i

theorem nonunitRadical_eq_of_label_eq {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
    (character : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
      Fin dimension → Fin (width + 1))
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (he : label C b dimension width character dyad q =
      label C b dimension width character dyad q') :
    nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val) =
      nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-q'.out.val) :=
  b.nonunitRadical_eq_of_dividedSupport_eq C _ _
    ((label_eq_iff C b dimension width character dyad q q').mp he).1

end OriginalBlockGaussRowClassifier

variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0}
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
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)
variable (character : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
  mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

/-- Construct the same row-ball stage with a genuine divided-frequency
classifier on each complete common block.  The complete source and all
continuous analytic data are unchanged. -/
def canonicalRowBallByBlock :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G (rowBallFiniteFamily K A.Sf 1) :=
  { canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn ∅ dimension width character dyad with
    charts DE D :=
      let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
      { (canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
          δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
          hnorm havoid hcolumn b.originalPrimeSupport dimension width character dyad).charts DE D with
        rowLabel := OriginalBlockGaussRowClassifier.label C b dimension width
          (character DE D) (dyad DE D) } }

@[simp] theorem canonicalRowBallByBlock_profile :
    (canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).profile =
      CanonicalRowBall.archTest K A.Sf 1 := rfl

@[simp] theorem canonicalRowBallByBlock_radius :
    (canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).radius =
      CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ := rfl

@[simp] theorem canonicalRowBallByBlock_fiber :
    (canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).fiber =
      engineOrbitMultiplicity (Γ := Γ) G.rows := rfl

@[simp] theorem canonicalRowBallByBlock_rowLabel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).charts DE D).rowLabel =
      OriginalBlockGaussRowClassifier.label C
        (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
        dimension width (character DE D) (dyad DE D) := rfl

@[simp] theorem canonicalRowBallByBlock_kernel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).charts DE D).kernel =
      canonicalRowBallKernel (Γ := Γ) μv ν δ hδ hδ1 := rfl

/-- Equality of the actual chart labels fixes the genuine local
nonunit flags used by the live-row arithmetic extraction. -/
theorem canonicalRowBallByBlock_nonunitSaving_iff_of_rowLabel_eq
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset)
    (q q' : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (he :
      ((canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
        δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
        hnorm havoid hcolumn dimension width character dyad).charts DE D).rowLabel q =
      ((canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
        δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
        hnorm havoid hcolumn dimension width character dyad).charts DE D).rowLabel q') :
    let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
    ∀ i : Fin b.primeCount,
      nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
          (-q.out.val) ↔
        nonunitFrequencySaving C (b.primes i) (b.leftMultiplicity i) (b.rightMultiplicity i)
          (-q'.out.val) := by
  dsimp only
  exact OriginalBlockGaussRowClassifier.nonunitSaving_iff_of_label_eq C
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    dimension width (character DE D) (dyad DE D) q q'
    (by simpa only [canonicalRowBallByBlock_rowLabel] using he)

/-- Every row-support divisor and its norm bound are proved from the
actual common block and the original retained-column window. -/
def canonicalRowBallByBlockOriginalFibreRows
    (B : ℝ) (maskIdeal : Ideal (𝓞 K)) (hmaskIdeal : maskIdeal ≠ 0)
    (maskPrimes : OriginalMaskPrimeData mask maskIdeal)
    (mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (column_norm : ∀ i ∈ G.columns, (Ideal.absNorm (G.ideal i).val : ℝ) ≤ Z ^ B) :
    (canonicalRowBallByBlock (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn dimension width character dyad).OriginalFibreRows
        Θ dimension width B Z where
  support DE :=
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).originalPrimeSupport
  maskIdeal := maskIdeal
  rowIdeal DE := DE.val.1
  mask_nonzero := hmaskIdeal
  row_nonzero DE := (actual_common_pair_properties _ _ _ _ DE).1
  maskPrimes := maskPrimes
  row_divides DE :=
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).originalPrimeSupport_divides
  mask_norm := mask_norm
  row_norm DE := (actual_common_pair_norm G.columns G.columns
    (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) (Z ^ B)
    (fun i _ => (G.ideal i).property.1) (fun i _ => (G.ideal i).property.1)
    column_norm column_norm DE).1
  code DE D := OriginalBlockGaussRowClassifier.code C
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property)
    dimension width (character DE D) (dyad DE D)
  encode DE _ := OriginalGaussRowClassifier.encode
    (canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property).originalPrimeSupport
    dimension width
  row_label _ _ _ _ := rfl

end ActualGaussStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.originalPrimeSupport_ideal_image
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.originalPrimeSupport_divides
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalBlockGaussRowClassifier.nonunitSaving_iff_of_label_eq
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalBlockGaussRowClassifier.nonunitRadical_eq_of_label_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBallByBlock
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBallByBlockOriginalFibreRows
