import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondStage

/-!
# Split the genuine second rows before Cauchy

The exceptional rows must be separated on the original transformed sum.
Splitting two already formed square-root row energies would create mixed
exceptional/nonexceptional terms.  Here the nonexceptional carrier uses
one Cauchy estimate, while each exceptional row retains its own complete
left and right polynomials and the same Fourier kernel.  Consequently a
single-row cost has exactly the product needed by the exceptional count.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments MeasureTheory
open UniqueFactorizationMonoid

private theorem norm_sum_partition_singletons {H : Type*}
    (rows : Finset H) (exceptional : H → Prop) (f : H → ℂ) :
    ‖∑ h ∈ rows, f h‖ ≤
      ‖∑ h ∈ rows.filter (fun h => ¬ exceptional h), f h‖ +
        ∑ h ∈ rows.filter exceptional, ‖f h‖ := by
  have he : (∑ h ∈ rows, f h) =
      (∑ h ∈ rows.filter (fun h => ¬ exceptional h), f h) +
        ∑ h ∈ rows.filter exceptional, f h := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : exceptional h <;> simp [hh]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Singleton Cauchy has no cross-row terms and retains the product of
the two actual complete columns on that same row. -/
theorem singleton_joint_sqrt_product {H I J : Type*}
    (h : H) (left : Finset I) (right : Finset J) (q : H → ℂ)
    (c : H → I → ℂ) (d : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy {h} left q c x ξ) *
      Real.sqrt (jointColumnEnergy {h} right q d y ξ) =
        ‖q h‖ * ‖jointFourierColumn left (c h) (x h) ξ‖ *
          ‖jointFourierColumn right (d h) (y h) ξ‖ := by
  simp only [jointColumnEnergy, Finset.sum_singleton,
    Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  have hs : Real.sqrt ‖q h‖ * Real.sqrt ‖q h‖ = ‖q h‖ := by
    nlinarith [Real.sq_sqrt (norm_nonneg (q h))]
  calc
    _ = (Real.sqrt ‖q h‖ * Real.sqrt ‖q h‖) *
        ‖jointFourierColumn left (c h) (x h) ξ‖ *
          ‖jointFourierColumn right (d h) (y h) ξ‖ := by ring
    _ = _ := by rw [hs]

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "MV" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

variable {hΓ μv hDiff}
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η htrace}
variable {left : Finset ι} {right : Finset κ}
variable {profiles : ι → κ → SchwartzMap MV ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right
  profiles finiteTest radius D)

/-- The original complete second kernel restricted only in its row
carrier.  All column supports, generators, masks and coefficients stay
literal, including a centered coefficient when the source has one. -/
def kernelCostOn (rows : Finset Q) : ℝ :=
  let a := fun i => generatedOriginalColumn (σ := σ) hΓ (b.secondLeftIdeal i)
    (engineAllowedGenerator C b.commonLeftIdeal * b.leftGenerator i)
    (b.secondLeft_generates C i)
  let a' := fun j => generatedOriginalColumn (σ := σ) hΓ (b.secondRightIdeal j)
    (engineAllowedGenerator C b.commonRightIdeal * b.rightGenerator j)
    (b.secondRight_generates C j)
  let δ := (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val
  secondResidualKernelCost PUnit chart.kernel rows (fun t => -t.out.val)
    (b.leftColumns left) (b.rightColumns right)
    b.commonLeftIdeal b.commonRightIdeal b.leftResidual b.rightResidual
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun t => secondOrbitalScalar radius D * chart.weight t)
    (fun i => chart.leftCoefficient i * (a i).divisorPhase δ)
    (fun j => chart.rightCoefficient j * (a' j).divisorPhase δ)
    chart.leftPoint chart.rightPoint

theorem classKernelCost_eq_on
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (label : Fin (chart.rowLabelCount + 1)) :
    chart.classKernelCost M X hX label = chart.kernelCostOn
      ((b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows.filter
        (fun t => chart.rowLabel t = label)) := rfl

/-- The original finite row labels remain outside Cauchy.  Summing
their separate costs is the definition of the complete chart cost. -/
theorem kernelCost_eq_on
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X) :
    chart.kernelCost M X hX =
      ∑ label : Fin (chart.rowLabelCount + 1), chart.kernelCostOn
        ((b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX).rows.filter
          (fun t => chart.rowLabel t = label)) := rfl

theorem kernel_bound_on
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (rows : Finset Q) :
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ‖∑ t ∈ rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
        chart.kernelCostOn rows := by
  obtain ⟨hDa, hEa, hDb, hEb⟩ := b.second_coprimalities hsupport
  exact actual_second_source_kernel_bound (hΓ := hΓ) (hS := hDiff)
    (Ray := PUnit) (μv := μv) chart.kernel rows
    (b.leftColumns left) (b.rightColumns right)
    b.commonLeftIdeal b.commonRightIdeal b.leftResidual b.rightResidual
    b.secondLeftIdeal b.secondRightIdeal (fun _ => rfl) (fun _ => rfl)
    (engineAllowedGenerator C b.commonLeftIdeal) (engineAllowedGenerator C b.commonRightIdeal)
    b.leftGenerator b.rightGenerator
    (engineAllowedGenerator_generates C _) (engineAllowedGenerator_generates C _)
    b.left_generates b.right_generates (b.secondLeft_generates C) (b.secondRight_generates C)
    hDa hEa hDb hEb (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => (1 : Circle))
    (fun i j hc => by simpa only [Circle.coe_one] using
      b.secondPhase_one hΓ C hsupport hleft hright i j hc)
    profiles finiteTest radius D chart.left_mask chart.right_mask
    chart.weight chart.leftCoefficient chart.rightCoefficient chart.leftPoint chart.rightPoint
    (fun t _ i hi j hj hc => chart.profile t i hi j hj hc)

/-- The exceptional predicate is chosen before both Fourier variables.
Each exceptional row is kept paired before its own triangle estimate. -/
def partitionedKernelCost (rows : Finset Q) (exceptional : Q → Prop) : ℝ :=
  chart.kernelCostOn (rows.filter (fun t => ¬ exceptional t)) +
    ∑ t ∈ rows.filter exceptional, chart.kernelCostOn {t}

theorem kernel_bound_partitioned
    (hsupport : primeSupport DE.1 = primeSupport DE.2)
    (hleft : ∀ i, ∃ u : Kˣ, (u : K) = (b.leftGenerator i : K) ∧
      A.IsAllowed C.correction.B u)
    (hright : ∀ j, ∃ u : Kˣ, (u : K) = (b.rightGenerator j : K) ∧
      A.IsAllowed C.correction.B u)
    (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X)
    (exceptional : Q → Prop) :
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
      (source.pairs i j).transformedRow μv hDiff finiteTest radius D t‖ ≤
        chart.partitionedKernelCost source.rows exceptional := by
  dsimp only
  let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
  apply (norm_sum_partition_singletons source.rows exceptional _).trans
  apply add_le_add
  · exact chart.kernel_bound_on hsupport hleft hright M X hX _
  · apply Finset.sum_le_sum
    intro t _
    simpa only [Finset.sum_singleton] using
      chart.kernel_bound_on hsupport hleft hright M X hX {t}

end SecondBlockProfileChart

variable (hΓ μv hDiff)

/-- The common physical cutoff and the zero frequency are unchanged by
the row partition.  The split is made on each genuine transformed sum,
before any Cauchy estimate of its nonzero rows. -/
theorem canonical_second_block_transform_partitioned_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    {ι κ : Type*} (left : Finset ι) (right : Finset κ)
    (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior)
    (DE : commonSupportPool left right (fun i => (fullI i).val) (fun j => (fullJ j).val))
    (profiles : ι → κ → SchwartzMap MV ℂ)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (M : Finset (HeightOneSpectrum A.R)) (radius : {r : ℝ // 0 < r})
    (X : ℝ) (hX : 1 ≤ X) :
    let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
    let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
    ∀ charts : ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff b C left right profiles
        finiteTest radius D.val,
    ∀ exceptional : M.powerset → Q → Prop,
    ‖source.transform μv hDiff finiteTest‖ ≤
      ‖source.zeroTerm μv hDiff finiteTest‖ +
        ∑ D : M.powerset,
          (charts D).partitionedKernelCost source.rows (exceptional D) := by
  dsimp only
  intro charts exceptional
  let b := canonicalFirstCommonBlock C left right fullI fullJ DE.val DE.property
  let source := b.secondFiniteSource hΓ hDiff C left right profiles M radius X hX
  change ‖source.transform μv hDiff finiteTest‖ ≤ _
  rw [source.transform_eq_common_rows μv hDiff finiteTest]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ D ∈ M.powerset,
        ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D t‖ :=
      norm_sum_le _ _
    _ = ∑ D : M.powerset,
        ‖∑ t ∈ source.rows, ∑ i ∈ source.leftColumns, ∑ j ∈ source.rightColumns,
          (source.pairs i j).transformedRow μv hDiff finiteTest source.radius D.val t‖ :=
      (Finset.sum_coe_sort _ _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D _
      exact (charts D).kernel_bound_partitioned
        (commonSupportPool_support_eq left right (fun i => (fullI i).val)
          (fun j => (fullJ j).val) DE.val DE.property)
        (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).1
        (canonicalFirstCommonBlock_allowed C left right fullI fullJ DE.val DE.property).2
        M X hX (exceptional D)

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
/-- The original whole Gauss source reaches the exceptional/nonexceptional
partition before Cauchy.  Tail constants still precede every source and
partition; the true zero and the common physical tail are unchanged. -/
theorem gauss_second_stage_partitioned_bound
    (C : A.GeneralArithmeticContext σ η htrace)
    (Drecipe : ComparisonPoissonCoefficientData K A)
    (hD : GlobalPairCancel.HasArithmeticRecipes A σ htrace C.correction.B Drecipe)
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
    (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
    (decay : ℝ) (hdecay : 1 < decay) (order : ℕ)
    (horder : Module.finrank ℤ (traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) < order)
    (hdegree : (Module.finrank ℚ K : ℝ) * decay ≤ order) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Ctail : ℝ, 0 ≤ Ctail ∧
    ∀ {H ι : Type*} (rows : Finset H) (rowMap : H → Q) (weight : H → ℝ)
      (columns : Finset ι) (c : ι → ℂ) (fullI : ι → A.Exterior)
      (afull : ι → A.R) (hafull : ∀ i, A.Generates (fullI i) (afull i))
      (hfull : ∀ i ∈ columns, ∃ u : Kˣ, (u : K) = (afull i : K) ∧ A.IsAllowed C.correction.B u)
      (φ : SchwartzMap MV ℂ) (radius : {r : ℝ // 0 < r})
      (M : Finset (HeightOneSpectrum A.R)) (X : ℝ) (hX : 1 ≤ X),
    let profiles := fun i j => (c i * star (c j)) • φ
    let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
        (fun j => (fullI j).val) =>
      canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
    let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C
      columns columns profiles M radius X hX
    ∀ charts : ∀ DE, ∀ D : M.powerset,
      SecondBlockProfileChart (E := E) hΓ μv hDiff (blocks DE) C columns columns profiles
        finiteTest radius D.val,
    ∀ exceptional : ∀ DE, M.powerset → Q → Prop,
    ∀ B : ℕ, GaussEnergyChart rows rowMap weight φ
      (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M B →
    weightedEnergy rows weight
      (fun h => ∑ i ∈ columns, c i *
        (generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)).orbit hDiff (rowMap h)) ≤
      (B : ℝ) * ∑ DE,
        (‖(sources DE).zeroTerm μv hDiff finiteTest‖ +
          (∑ D : M.powerset, (charts DE D).partitionedKernelCost (sources DE).rows (exceptional DE D)) +
          Ctail * X ^ (1 - decay) *
            ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
              seminorms.sup (schwartzSeminormFamily ℂ MV ℂ) ((sources DE).pairs i j).profile *
                ((sources DE).pairs i j).truncationMass M radius) := by
  obtain ⟨seminorms, Ctail, hC, htail⟩ := finite_source_uniform_bound
    (K := K) (S := A.Sf) (Γ := Γ) ν μv μ hDiff finiteTest hlc hcs
    decay hdecay order horder hdegree
  refine ⟨seminorms, Ctail, hC, ?_⟩
  intro H ι rows rowMap weight columns c fullI afull hafull hfull φ radius M X hX
  dsimp only
  intro charts exceptional B cal
  let profiles := fun i j => (c i * star (c j)) • φ
  let blocks := fun DE : commonSupportPool columns columns (fun i => (fullI i).val)
      (fun j => (fullI j).val) =>
    canonicalFirstCommonBlock C columns columns fullI fullI DE.val DE.property
  let sources := fun DE => (blocks DE).secondFiniteSource hΓ hDiff C
    columns columns profiles M radius X hX
  let series := fun DE => ∑ i ∈ (sources DE).leftColumns, ∑ j ∈ (sources DE).rightColumns,
    ((sources DE).pairs i j).maskedSeries (sIntegerFiniteTestFunction K A.Sf finiteTest) radius M
  have hp := gauss_energy_orbital_source_bound hDiff rows rowMap weight columns c
    (fun i => generatedOriginalColumn (σ := σ) hΓ (fullI i) (afull i) (hafull i)) φ
    (sIntegerFiniteTestFunction K A.Sf finiteTest)
    (continuous_sIntegerFiniteTestFunction K A.Sf finiteTest hlc)
    (hasCompactSupport_sIntegerFiniteTestFunction K A.Sf finiteTest hcs) radius M B cal
  rw [common_support_gauss_sources hΓ hDiff C Drecipe hD columns columns fullI fullI
    afull afull hafull hafull hfull hfull] at hp
  change weightedEnergy rows weight _ ≤ (B : ℝ) * (∑ DE, series DE).re at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro DE _
  have ht := htail (sources DE)
  have hk := canonical_second_block_transform_partitioned_bound hΓ μv hDiff C columns columns fullI fullI
    DE profiles finiteTest M radius X hX (charts DE) (exceptional DE)
  have hre := Complex.re_le_norm (series DE - (sources DE).transform μv hDiff finiteTest)
  rw [Complex.sub_re] at hre
  have hfinite := Complex.re_le_norm ((sources DE).transform μv hDiff finiteTest)
  change (series DE).re ≤ _
  change ‖series DE - (sources DE).transform μv hDiff finiteTest‖ ≤ _ at ht
  exact ((sub_le_iff_le_add.mp (hre.trans ht)).trans
    (add_le_add le_rfl (hfinite.trans hk))).trans_eq (add_comm _ _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.singleton_joint_sqrt_product
#print axioms HeckeSkeleton.Moments.EngineStep.SecondBlockProfileChart.kernel_bound_partitioned
#print axioms HeckeSkeleton.Moments.EngineStep.canonical_second_block_transform_partitioned_bound

#print axioms HeckeSkeleton.Moments.EngineStep.gauss_second_stage_partitioned_bound

