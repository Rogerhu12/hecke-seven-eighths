import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildSectors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFrequencyClassStability
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualMovingFrequencyFactors
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S4: the finite classifier of the original second Poisson rows

The code records only the actual nonunit pattern and the unit sector of
the original extracted frequency. The arithmetic extraction is defined
before the row carrier and the Fourier chart, so there is no circular
dependence on the classifier. Its cardinality is exactly the bound in
the S4 contract. The existing `actualRows` uses the same extraction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments
open MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

theorem common_active_of_coefficients
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) (right : Finset κ)
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (c : ι → ℂ) (d : κ → ℂ) (i : ι) (j : κ)
    (hi : i ∈ b.leftColumns left) (hj : j ∈ b.rightColumns right)
    (hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val)
    (hci : c i ≠ 0) (hdj : d j ≠ 0) :
    DE ∈ commonSupportPool (left.filter (fun i => c i ≠ 0))
      (right.filter (fun j => d j ≠ 0))
      (fun i => (fullI i).val) (fun j => (fullJ j).val) := by
  have he : commonSupportLabel (fullI i).val (fullJ j).val = DE := by
    apply (commonSupportLabel_eq_iff (fullI i).val (fullJ j).val DE.1 DE.2
      (commonSupportPool_support_eq left right _ _ DE hDE)).mpr
    refine ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2, ?_⟩
    simpa only [b.left_residual, b.right_residual] using hcop
  unfold commonSupportPool
  exact Finset.mem_image.mpr ⟨(i, j),
    Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hci⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hdj⟩⟩, he⟩

theorem coefficient_zero_of_inactive
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (left : Finset ι) (right : Finset κ)
    (hDE : DE ∈ commonSupportPool left right
      (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (c : ι → ℂ) (d : κ → ℂ) (i : ι) (j : κ)
    (hi : i ∈ b.leftColumns left) (hj : j ∈ b.rightColumns right)
    (hcop : IsCoprime (b.leftResidual i).val (b.rightResidual j).val)
    (hinactive : DE ∉ commonSupportPool (left.filter (fun i => c i ≠ 0))
      (right.filter (fun j => d j ≠ 0))
      (fun i => (fullI i).val) (fun j => (fullJ j).val)) :
    c i = 0 ∨ d j = 0 := by
  by_cases hci : c i = 0
  · exact Or.inl hci
  · by_cases hdj : d j = 0
    · exact Or.inr hdj
    · exact False.elim (hinactive
        (common_active_of_coefficients b left right hDE c d i j hi hj hcop hci hdj))

def originalRowCorrelation (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : ℂ :=
  generatedIdealCorrelation (σ := σ) b.commonLeftIdeal b.commonRightIdeal
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _) (-q.out.val)

def originalRowFactor (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : A.R :=
  primePowerProductGenerator C b.primes
      (fun i => min (b.leftMultiplicity i) (b.rightMultiplicity i)) *
    nonunitFrequencyGenerator C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val)

def originalRowNormFactor (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : ℝ :=
  (Ideal.absNorm (gcd b.commonLeftIdeal.val b.commonRightIdeal.val) : ℝ) *
    A.exteriorNorm
      (nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val))

def originalRowExtraction (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (hc : originalRowCorrelation b C q ≠ 0) :
    ActualChildRow
      (ProbeOrbitNormSum.principalExterior A ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩)
      (-q.out.val) (originalRowFactor b C q) (originalRowNormFactor b C q) :=
  Classical.choice (exists_actual_extracted_child_row_of_generates C b.primes
    b.primes_injective b.leftMultiplicity b.rightMultiplicity
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (ProbeOrbitNormSum.principalExterior A ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩)
    (-q.out.val)
    (ProbeOrbitNormSum.principalExterior_generates A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩) hc)

def originalRowSector (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) :=
  if hc : originalRowCorrelation b C q ≠ 0 then
    (originalRowExtraction b C q hc).sector P
  else 1

local instance sectorFintype :
    Fintype (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
  Fintype.ofFinite _

abbrev RowCode (b : FirstCommonCharacterBlock fullI fullJ DE) :=
  (Fin b.primeCount → Bool) ×
    SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))

def rowLabelCount (b : FirstCommonCharacterBlock fullI fullJ DE) : ℕ :=
  Fintype.card (RowCode b)

theorem rowLabelCount_eq (b : FirstCommonCharacterBlock fullI fullJ DE) :
    rowLabelCount b = 2 ^ b.primeCount *
      Nat.card (SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) := by
  simp [rowLabelCount, RowCode, Nat.card_eq_fintype_card]

def rowCode (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) : RowCode b :=
  (actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val),
    originalRowSector b C P q)

def rowLabel (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    Fin (rowLabelCount b + 1) :=
  (Fintype.equivFin (RowCode b) (rowCode b C P q)).castSucc

theorem rowCode_eq_of_label_eq (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q r : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (h : rowLabel b C P q = rowLabel b C P r) :
    rowCode b C P q = rowCode b C P r :=
  (Fintype.equivFin (RowCode b)).injective (Fin.castSucc_injective _ h)

theorem pattern_eq_of_label_eq (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q r : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (h : rowLabel b C P q = rowLabel b C P r) :
    actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-q.out.val) =
      actualNonunitPattern C b.primes b.leftMultiplicity b.rightMultiplicity (-r.out.val) :=
  congrArg Prod.fst (rowCode_eq_of_label_eq b C P q r h)

theorem sector_eq_of_label_eq (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η htrace)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (q r : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (h : rowLabel b C P q = rowLabel b C P r) :
    originalRowSector b C P q = originalRowSector b C P r :=
  congrArg Prod.snd (rowCode_eq_of_label_eq b C P q r h)

section Charts

variable [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

theorem actualRows_sector_eq_original
    (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
      profiles finiteTest radius D)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h : (chart.actualRows M X hX label).live) :
    ((chart.actualRows M X hX label).extractedRow C h).sector P =
      originalRowSector b C P h.val := by
  have hc : originalRowCorrelation b C h.val ≠ 0 :=
    (Finset.mem_filter.mp h.property).2
  rw [originalRowSector, dif_pos hc]
  rfl

theorem actualRows_sector_stable
    (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
      profiles finiteTest radius D)
    (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (hlabel : ∀ q r, chart.rowLabel q = chart.rowLabel r →
      originalRowSector b C P q = originalRowSector b C P r)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1))
    (h k : (chart.actualRows M X hX label).live) :
    ((chart.actualRows M X hX label).extractedRow C h).sector P =
      ((chart.actualRows M X hX label).extractedRow C k).sector P := by
  rw [actualRows_sector_eq_original chart P M X hX label h,
    actualRows_sector_eq_original chart P M X hX label k]
  apply hlabel
  have hh : chart.rowLabel h.val = label :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).2
  have hk : chart.rowLabel k.val = label :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp k.property).1).2
  exact hh.trans hk.symm

end Charts

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.SecondTransformPrivate
