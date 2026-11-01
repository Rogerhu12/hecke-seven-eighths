import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalGaussOrbitRows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoverCardinality

/-!
# A constructed actual second Gauss stage

The positive original test is the fixed normalized row-ball tensor.
The radius is the inverse of the original retained scale times its
prescribed power of Z, before any mask divisor is selected.  Original
element norms and prime avoidance prove the Gauss calibration.  Its
finite multiplicity is the computed multiplicity of the actual rows.

Every common block and every mask divisor uses the same full-log-axis
Fourier kernel.  The whole original coefficients, both norm tilts and
the inverse row-radius tilt remain in the resulting chart.  The row
partition is an encoding of its actual nonunit prime subset, original
finite character class and original bounded dyadic coordinates.
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

namespace CanonicalRowBall

/-- This radius is chosen from the original scale window, with no
dependence on either later common block or mask divisor. -/
def gaussRadius (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z) :
    {r : ℝ // 0 < r} :=
  ⟨(retainedScale * Z ^ g)⁻¹,
    inv_pos.mpr (mul_pos hscale (Real.rpow_pos_of_pos hZ g))⟩

@[simp] theorem gaussRadius_val (retainedScale Z g : ℝ)
    (hscale : 0 < retainedScale) (hZ : 0 < Z) :
    (gaussRadius retainedScale Z g hscale hZ).val =
      (retainedScale * Z ^ g)⁻¹ := rfl

end CanonicalRowBall

section Arithmetic

variable [IsPrincipalIdealRing A.R]

/-- The submask generator divides the generator of the same original
full mask. This is proved from membership in the actual prime ideals. -/
theorem original_submask_generator_dvd
    {D M : Finset (HeightOneSpectrum A.R)} (hDM : D ⊆ M) :
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val ∣
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M).val := by
  change IdealMobiusMask.maskGenerator D ∣ IdealMobiusMask.maskGenerator M
  rw [IdealMobiusMask.maskGenerator_dvd_iff]
  apply (IdealMobiusMask.mem_primeProduct D _).mpr
  intro p hp
  exact (IdealMobiusMask.mem_primeProduct M _).mp
    ((IdealMobiusMask.maskGenerator_dvd_iff M _).mp (dvd_refl _)) p (hDM hp)

/-- Regrouping into a common ideal changes the generator only within
its original principal ideal. Original full-column mask coprimality
therefore supplies every actual regrouped column and every submask. -/
theorem generated_original_submask_coprime
    {I : A.Exterior} {a b : A.R} (ha : A.Generates I a) (hb : A.Generates I b)
    {D M : Finset (HeightOneSpectrum A.R)} (hDM : D ⊆ M)
    (hmask : IsCoprime a
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) M).val) :
    IsCoprime b (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val := by
  have hspan : Ideal.span {a} = Ideal.span {b} := ha.2.trans hb.2.symm
  have hba : b ∣ a := Ideal.span_singleton_le_span_singleton.mp hspan.le
  exact (hmask.of_isCoprime_of_dvd_left hba).of_isCoprime_of_dvd_right
    (original_submask_generator_dvd hDM)

theorem engineElementOrbit_avoids_of_original
    (h : A.R) (hh : h ≠ 0) (M : Finset (HeightOneSpectrum A.R))
    (havoid : ∀ p ∈ M, h ∉ p.asIdeal) :
    sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ M
      (engineElementOrbit (Γ := Γ) h) = 1 := by
  rw [engineElementOrbit, dif_pos hh, sIntegerOrbitAvoidanceMask_mk]
  exact if_pos havoid

end Arithmetic

namespace OriginalGaussRowClassifier

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- Raw prime divisibility of the negative second Poisson frequency.
This does not classify the frequency after division by a common prime
power; a divided-frequency classifier uses `nonunitFrequencySaving`. -/
def nonunitSupport (support : Finset (HeightOneSpectrum (𝓞 K))) (q : Q) :
    support.powerset :=
  ⟨support.filter (fun p => p.asIdeal ∣
      (ProbeOrbitNormSum.principalExterior A
        ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val),
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

@[simp] theorem mem_nonunitSupport
    (support : Finset (HeightOneSpectrum (𝓞 K))) (q : Q)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ (nonunitSupport support q).val ↔ p ∈ support ∧ p.asIdeal ∣
      (ProbeOrbitNormSum.principalExterior A
        ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val :=
  Finset.mem_filter

def code {Θ : Type*} (support : Finset (HeightOneSpectrum (𝓞 K)))
    (dimension width : ℕ) (character : Q → Θ)
    (dyad : Q → Fin dimension → Fin (width + 1)) (q : Q) :
    OriginalFiniteFibre.RowCode support Θ dimension width :=
  (nonunitSupport support q, character q, dyad q)

/-- The finite encoding has one unused value only because the existing
chart API uses `Fin (rowLabelCount + 1)`. It does not refine any row code. -/
def encode {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (c : OriginalFiniteFibre.RowCode support Θ dimension width) :
    Fin (Fintype.card (OriginalFiniteFibre.RowCode support Θ dimension width) + 1) :=
  (Fintype.equivFin _ c).castSucc

theorem encode_injective {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ) :
    Function.Injective (encode (Θ := Θ) support dimension width) := by
  intro c c' he
  exact (Fintype.equivFin _).injective (Fin.castSucc_injective _ he)

def label {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (character : Q → Θ) (dyad : Q → Fin dimension → Fin (width + 1)) (q : Q) :
    Fin (Fintype.card (OriginalFiniteFibre.RowCode support Θ dimension width) + 1) :=
  encode support dimension width (code support dimension width character dyad q)

theorem label_eq_iff {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (character : Q → Θ) (dyad : Q → Fin dimension → Fin (width + 1)) (q q' : Q) :
    label support dimension width character dyad q =
      label support dimension width character dyad q' ↔
      nonunitSupport support q = nonunitSupport support q' ∧
        character q = character q' ∧ dyad q = dyad q' := by
  change encode support dimension width (code support dimension width character dyad q) =
    encode support dimension width (code support dimension width character dyad q') ↔ _
  rw [(encode_injective support dimension width).eq_iff]
  simp only [code, Prod.mk.injEq]

/-- Only the image of the original finite coordinates is counted. -/
theorem labels_card_le {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (character : Q → Θ) (dyad : Q → Fin dimension → Fin (width + 1)) (rows : Finset Q) :
    (rows.image (label support dimension width character dyad)).card ≤
      2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension :=
  OriginalFiniteFibre.row_image_card_le_coordinates rows
    (label support dimension width character dyad) support dimension width
    (code support dimension width character dyad) (encode support dimension width)
    (fun _ _ => rfl)

end OriginalGaussRowClassifier

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

namespace ActualGaussStage

/-- This fixed kernel precedes all moving rows, coefficients, scales,
common ideals, masks and dyadic classifier values. -/
def canonicalRowBallKernel (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) : 𝓢(ℝ, ℂ) :=
  CanonicalSecondLogChart.kernel (Γ := Γ) μv ν (rowBallFiniteFamily K A.Sf 1)
    (rowBallFiniteFamily_locallyConstant K A.Sf 1)
    (rowBallFiniteFamily_compactSupport K A.Sf 1)
    δ hδ hδ1 (CanonicalRowBall.archTest K A.Sf 1)

variable {hΓ μv hDiff ν}

/-- Direct and pooled actual Gauss sources enter the same constructor.
The premises concern their original individual norms, prime avoidance,
full-column masks and finite classifier coordinates only. -/
def canonicalRowBall
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {ι : Type*} (G : ActualGaussSource C ι)
    (retainedScale Z g : ℝ) (hscale : 0 < retainedScale) (hZ : 0 < Z)
    (mask : Finset (HeightOneSpectrum A.R)) (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
    (hnorm : ∀ h ∈ G.rows,
      A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
    (havoid : ∀ h ∈ G.rows, ∀ p ∈ mask, h ∉ p.asIdeal)
    (hcolumn : ∀ i ∈ G.columns, IsCoprime (G.generator i)
      (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) mask).val)
    {Θ : Type*} [Fintype Θ]
    (support : Finset (HeightOneSpectrum (𝓞 K))) (dimension width : ℕ)
    (character : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
    (dyad : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      mask.powerset → SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
        Fin dimension → Fin (width + 1)) :
    ActualGaussStage (E := ℝ) hΓ μv hDiff G (rowBallFiniteFamily K A.Sf 1) where
  profile := CanonicalRowBall.archTest K A.Sf 1
  radius := CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ
  mask := mask
  cutoff := cutoff
  cutoff_one := hcutoff
  fiber := engineOrbitMultiplicity (Γ := Γ) G.rows
  calibration := by
    apply CanonicalRowBall.chart G.rows (engineElementOrbit (Γ := Γ))
      (CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ) 1 mask
      (engineOrbitMultiplicity (Γ := Γ) G.rows)
    · intro h hh
      have he := engineElementOrbit_norm_of_generates (Γ := Γ)
        (originalFrequencyIdeal h) h (originalFrequencyIdeal_generates h (G.row_nonzero h hh))
      change (retainedScale * Z ^ g)⁻¹ *
        (sIntegerOrbitNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
          (engineElementOrbit (Γ := Γ) h)).val ≤ 1
      rw [he]
      exact (mul_le_mul_of_nonneg_left (hnorm h hh)
        (inv_nonneg.mpr (mul_pos hscale (Real.rpow_pos_of_pos hZ g)).le)).trans_eq
          (inv_mul_cancel₀ (mul_pos hscale (Real.rpow_pos_of_pos hZ g)).ne')
    · intro h hh
      exact engineElementOrbit_avoids_of_original h (G.row_nonzero h hh) mask (havoid h hh)
    · exact engineOrbit_fibre_le_multiplicity G.rows
  charts DE D := by
    let b := canonicalFirstCommonBlock C G.columns G.columns G.ideal G.ideal DE.val DE.property
    refine SecondBlockProfileChart.canonicalLogWithCoefficients hΓ μv hDiff ν b C
      G.columns G.columns (CanonicalRowBall.archTest K A.Sf 1) G.coefficient G.coefficient
      (rowBallFiniteFamily K A.Sf 1)
      (rowBallFiniteFamily_locallyConstant K A.Sf 1)
      (rowBallFiniteFamily_compactSupport K A.Sf 1)
      (CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ) D.val
      (Fintype.card (OriginalFiniteFibre.RowCode support Θ dimension width))
      (OriginalGaussRowClassifier.label support dimension width
        (character DE D) (dyad DE D)) ?_ ?_ δ hδ hδ1
    · intro i hi
      have hgen := b.secondLeft_generates C i
      rw [b.secondLeftIdeal_eq G.columns i hi] at hgen
      exact generated_original_submask_coprime (G.generates i) hgen
        (Finset.mem_powerset.mp D.property) (hcolumn i (Finset.mem_filter.mp hi).1)
    · intro j hj
      have hgen := b.secondRight_generates C j
      rw [b.secondRightIdeal_eq G.columns j hj] at hgen
      exact generated_original_submask_coprime (G.generates j) hgen
        (Finset.mem_powerset.mp D.property) (hcolumn j (Finset.mem_filter.mp hj).1)

section Projections

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

@[simp] theorem canonicalRowBall_radius :
    (canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).radius =
      CanonicalRowBall.gaussRadius retainedScale Z g hscale hZ := rfl

@[simp] theorem canonicalRowBall_fiber :
    (canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).fiber =
      engineOrbitMultiplicity (Γ := Γ) G.rows := rfl

@[simp] theorem canonicalRowBall_kernel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).charts DE D).kernel =
      canonicalRowBallKernel (Γ := Γ) μv ν δ hδ hδ1 := rfl

@[simp] theorem canonicalRowBall_rowLabel
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) (D : mask.powerset) :
    ((canonicalRowBall (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
      δ hδ hδ1 G retainedScale Z g hscale hZ mask cutoff hcutoff
      hnorm havoid hcolumn support dimension width character dyad).charts DE D).rowLabel =
      OriginalGaussRowClassifier.label support dimension width
        (character DE D) (dyad DE D) := rfl

end Projections

end ActualGaussStage

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_submask_generator_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.generated_original_submask_coprime
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussRowClassifier.label_eq_iff
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalGaussRowClassifier.labels_card_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBall
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.canonicalRowBall_kernel
