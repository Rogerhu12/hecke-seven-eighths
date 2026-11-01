import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondChartAllocation
import HeckeGeneral.Arithmetic.SIntegerOrbits

/-!
# The actual second rows retain exactly the original unit sectors

A fixed nonzero principal ideal has at most the subgroup index many
orbits of generators.  We inject any finite original row fibre directly
into these generator orbits.  Equality there is the very same subgroup
orbit relation, so no representative or sector is discarded.

For the actual second chart, `principalExterior_generates` identifies
the local ideal of the original negative Poisson frequency.  Negation
does not change its principal ideal.  Consequently the fibre bound is
the fixed `Γ.index`, independently of every chart, cutoff, row label,
common ideal, and subsequent restriction of the finite row set.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.MobiusRegroup MeasureTheory

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The map uses the actual representative as a generator of its
actual ideal.  Its injectivity is the original subgroup orbit relation,
and does not require a principal ideal hypothesis on the whole ring. -/
theorem finite_nonzero_orbit_ideal_fibre_le_index
    (Γ : Subgroup Rˣ) [Γ.FiniteIndex]
    (rows : Finset (MulAction.orbitRel.Quotient Γ (NonzeroRingElements R)))
    (I : Ideal R) (hI : I ≠ 0) :
    (rows.filter (fun q => Ideal.span {q.out.val} = I)).card ≤ Γ.index := by
  letI : NeZero I := ⟨hI⟩
  let fibre := rows.filter (fun q => Ideal.span {q.out.val} = I)
  let sector : fibre → GeneratorOrbits Γ I := fun q =>
    Quotient.mk _ ⟨q.val.out.val, (Finset.mem_filter.mp q.property).2⟩
  have hinjective : Function.Injective sector := by
    intro q q' hsector
    change (Quotient.mk _
      (⟨q.val.out.val, (Finset.mem_filter.mp q.property).2⟩ : PrincipalGenerators I) :
        GeneratorOrbits Γ I) =
      Quotient.mk _ (⟨q'.val.out.val, (Finset.mem_filter.mp q'.property).2⟩ :
        PrincipalGenerators I) at hsector
    obtain ⟨u, hu⟩ := Quotient.exact hsector
    have hrel : MulAction.orbitRel Γ (NonzeroRingElements R) q.val.out q'.val.out := by
      refine ⟨u, Subtype.ext ?_⟩
      exact congrArg (fun a : PrincipalGenerators I => a.val) hu
    apply Subtype.ext
    exact (Quotient.out_eq q.val).symm.trans
      ((Quotient.sound hrel).trans (Quotient.out_eq q'.val))
  have hcard : Nat.card fibre ≤ Γ.index :=
    (Nat.card_le_card_of_injective sector hinjective).trans
      (card_generatorOrbits_le_index Γ I)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, fibre] using hcard

end Domain

variable {K : Type} [Field K] [NumberField K]
variable (A : SArithmeticData K)
variable (Γ : Subgroup A.U) [Γ.FiniteIndex]

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

/-- The original negative frequency determines the same principal
ideal as its actual orbit representative. -/
theorem original_orbit_principal_ideal (q : Q) :
    Ideal.span {q.out.val} =
      A.extendIdeal (ProbeOrbitNormSum.principalExterior A
        ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩) := by
  simpa only [Ideal.span_singleton_neg] using
    (ProbeOrbitNormSum.principalExterior_generates A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).2

/-- Any finite subset of the actual orbit rows has at most `Γ.index`
rows of a fixed exterior ideal.  The negative Poisson sign is retained
in the original-ideal map, then removed only from its principal span. -/
theorem finite_original_orbit_exterior_fibre_le_index
    (rows : Finset Q) (I : A.Exterior) :
    (rows.filter (fun q => (ProbeOrbitNormSum.principalExterior A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val = I.val)).card ≤ Γ.index := by
  have hsubset : rows.filter (fun q => (ProbeOrbitNormSum.principalExterior A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val = I.val) ⊆
      rows.filter (fun q => Ideal.span {q.out.val} = A.extendIdeal I) := by
    intro q hq
    obtain ⟨hrow, hideal⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨hrow, ?_⟩
    have hext : ProbeOrbitNormSum.principalExterior A
        ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩ = I := Subtype.ext hideal
    rw [original_orbit_principal_ideal A Γ q, hext]
  have hcard := finite_nonzero_orbit_ideal_fibre_le_index
    (sIntegerUnitSubgroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    rows (A.extendIdeal I) (A.extendIdeal_ne_zero I)
  rw [sIntegerUnitSubgroup_index] at hcard
  exact (Finset.card_le_card hsubset).trans hcard

/-- The arbitrary-ideal version includes the empty zero-ideal fibre.
This is the exact quantifier needed by `ActualSecondRowMass.original_fibers`. -/
theorem finite_original_orbit_ideal_fibre_le_index
    (rows : Finset Q) (I : Ideal (𝓞 K)) :
    (rows.filter (fun q => (ProbeOrbitNormSum.principalExterior A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val = I)).card ≤ Γ.index := by
  by_cases hnonempty : (rows.filter (fun q => (ProbeOrbitNormSum.principalExterior A
      ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩).val = I)).Nonempty
  · obtain ⟨q, hq⟩ := hnonempty
    have hI := (Finset.mem_filter.mp hq).2
    rw [← hI]
    exact finite_original_orbit_exterior_fibre_le_index A Γ rows
      (ProbeOrbitNormSum.principalExterior A ⟨-q.out.val, neg_ne_zero.mpr q.out.property⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty]
    exact Nat.zero_le _

variable {A Γ}
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η htrace} {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)

/-- The actual chart's original fibre bound, with no new source
assumption.  This populates `originalFiber := Γ.index` directly. -/
theorem actualRows_original_fibers
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) (I : Ideal (𝓞 K)) :
    ((chart.actualRows M X hX label).rows.filter
      (fun q => ((chart.actualRows M X hX label).originalIdeal q).val = I)).card ≤ Γ.index := by
  exact finite_original_orbit_ideal_fibre_le_index A Γ
    (chart.actualRows M X hX label).rows I

/-- Arbitrary later row restrictions inherit this same fixed fibre
bound; no new sector or count is charged after exceptional partition. -/
theorem actualRows_restrict_original_fibers
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) (p : Q → Prop) (I : Ideal (𝓞 K)) :
    (((chart.actualRows M X hX label).rows.filter p).filter
      (fun q => ((chart.actualRows M X hX label).originalIdeal q).val = I)).card ≤ Γ.index := by
  exact finite_original_orbit_ideal_fibre_le_index A Γ
    ((chart.actualRows M X hX label).rows.filter p) I

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.finite_nonzero_orbit_ideal_fibre_le_index
#print axioms HeckeSkeleton.Moments.EngineStep.finite_original_orbit_ideal_fibre_le_index
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_original_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.actualRows_restrict_original_fibers
