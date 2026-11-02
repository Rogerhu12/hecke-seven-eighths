import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsOriginalMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Coefficients of the literal first Cauchy family

The inverse residual norm in the canonical logarithmic chart makes
its coefficient multiplier contractive. The complete original centered
coefficient is retained, and the finite character factors have norm at
most one. Consequently the active physical carrier embeds in the
original active carrier before any second transform.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

universe u v w

/-- A projection with fixed codomain transports through the literal
heterogeneous source equalities, once its index equality is supplied. -/
theorem dependent_projection_eq {α : Sort u} {β : α → Sort v} {γ : Sort w}
    (project : (a : α) → β a → γ) {a b : α} {x : β a} {y : β b}
    (hab : a = b) (hxy : HEq x y) : project a x = project b y := by
  cases hab
  cases eq_of_heq hxy
  rfl

variable {K : Type} [Field K] [NumberField K]

theorem exteriorNorm_one_le {A : SArithmeticData K} (I : A.Exterior) :
    1 ≤ A.exteriorNorm I := by
  change (1 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
    (fun h => I.property.1 (Ideal.absNorm_eq_zero_iff.mp h)))

theorem first_left_divisorFactor_norm_le
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (a r : OrbitalGaussColumn K S Γ)
    (delta : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    ‖firstLeftDivisorFactor a r delta‖ ≤ 1 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    r.modulus r.nonzero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {a.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {r.modulus})
  unfold firstLeftDivisorFactor
  rw [norm_mul, norm_mul]
  exact (mul_le_mul
    (mul_le_mul (finiteCharacter_norm_le_one a.character _)
      (finiteCharacter_norm_le_one a.character _) (norm_nonneg _) zero_le_one)
    (finiteCharacter_norm_le_one r.character _) (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num)

theorem first_right_divisorFactor_norm_le
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (a r : OrbitalGaussColumn K S Γ)
    (delta : Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) :
    ‖firstRightDivisorFactor a r delta‖ ≤ 1 := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    a.modulus a.nonzero
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K)))
    r.modulus r.nonzero
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {a.modulus})
  letI := Fintype.ofFinite ((Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K) ⧸
    Ideal.span {r.modulus})
  unfold firstRightDivisorFactor
  rw [norm_mul, norm_mul, norm_star]
  exact (mul_le_mul
    (mul_le_mul (finiteCharacter_norm_le_one a.character _)
      (finiteCharacter_norm_le_one a.character _) (norm_nonneg _) zero_le_one)
    (finiteCharacter_norm_le_one r.character _) (norm_nonneg _) (by norm_num)).trans_eq
      (by norm_num)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem first_chart_project_eq (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset)
    {W : Type*}
    (project : (profiles : F.source.Column → F.source.Column →
        SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) →
      FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
        (Arithmetic.localMeasures (K := K)) (F.source.block v)
        (Arithmetic.context c) F.source.columns F.source.columns profiles
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) F.source.radius D.val → W) :
    project F.source.profiles (F.source.charts v D) =
      project F.originalProfile (F.canonicalChart v D) :=
  dependent_projection_eq project hF.profile (hF.chart v D)

theorem first_chart_leftCoefficient_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    ‖(F.source.charts v D).leftCoefficient i‖ ≤ ‖F.coefficient i‖ := by
  have he := first_chart_project_eq F hF v D (fun _ chart => chart.leftCoefficient)
  rw [he]
  change ‖F.coefficient i *
      (((((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i)) ^
        p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) : ℂ))‖ ≤ _
  rw [CanonicalFirstLog.scaledNormalizedTiltScalar_norm
    ((Arithmetic.data c).exteriorNorm_pos _) p.tilt]
  have hpower : (Arithmetic.data c).exteriorNorm ((F.source.block v).leftResidual i) ^
      (p.tilt - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (exteriorNorm_one_le ((F.source.block v).leftResidual i))
      (show p.tilt - 1 ≤ 0 by linarith [p.tilt_half])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (norm_nonneg _)

theorem first_chart_rightCoefficient_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    ‖(F.source.charts v D).rightCoefficient i‖ ≤ ‖F.coefficient i‖ := by
  have he := first_chart_project_eq F hF v D (fun _ chart => chart.rightCoefficient)
  rw [he]
  change ‖F.coefficient i *
      (((((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i)) ^
        p.tilt : ℝ) : ℂ) /
        ((Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) : ℂ))‖ ≤ _
  rw [CanonicalFirstLog.scaledNormalizedTiltScalar_norm
    ((Arithmetic.data c).exteriorNorm_pos _) p.tilt]
  have hpower : (Arithmetic.data c).exteriorNorm ((F.source.block v).rightResidual i) ^
      (p.tilt - 1) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (exteriorNorm_one_le ((F.source.block v).rightResidual i))
      (show p.tilt - 1 ≤ 0 by linarith [p.tilt_half])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower (norm_nonneg _)

theorem first_piece_leftCoefficient_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    ‖(F.source.pieces v D).originalLeftCoefficient i‖ ≤ ‖F.coefficient i‖ := by
  unfold FirstBlockDirectData.originalLeftCoefficient
  dsimp only
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (first_left_divisorFactor_norm_le _ _ _)
    (norm_nonneg _)).trans
      (by simpa only [mul_one] using first_chart_leftCoefficient_norm_le F hF v D i)

theorem first_piece_rightCoefficient_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) (i : F.source.Column) :
    ‖(F.source.pieces v D).originalRightCoefficient i‖ ≤ ‖F.coefficient i‖ := by
  unfold FirstBlockDirectData.originalRightCoefficient
  dsimp only
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (first_right_divisorFactor_norm_le _ _ _)
    (norm_nonneg _)).trans
      (by simpa only [mul_one] using first_chart_rightCoefficient_norm_le F hF v D i)

theorem first_key_phase_norm {F : FirstPresentation call p} (key : FirstCauchyKey F) :
    ‖FirstCauchyKey.phase key‖ = 1 := by
  unfold FirstCauchyKey.phase
  split_ifs <;> exact Circle.norm_coe _

theorem first_key_coefficient_norm_le
    (F : FirstPresentation call p) (hF : F.Realizes)
    (key : FirstCauchyKey F) (i : F.source.Column) :
    ‖FirstCauchyKey.coefficient key i‖ ≤ ‖F.coefficient i‖ := by
  unfold FirstCauchyKey.coefficient
  split_ifs with hdiv hside
  · rw [norm_mul, first_key_phase_norm, mul_one]
    exact first_piece_rightCoefficient_norm_le F hF key.1 key.2.1 i
  · rw [norm_mul, first_key_phase_norm, mul_one]
    exact first_piece_leftCoefficient_norm_le F hF key.1 key.2.1 i
  · simpa only [norm_zero] using norm_nonneg (F.coefficient i)

theorem first_key_coefficient_ne_zero
    (F : FirstPresentation call p) (hF : F.Realizes)
    (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : FirstCauchyKey.coefficient key i ≠ 0) : F.coefficient i ≠ 0 := by
  intro hz
  have h := first_key_coefficient_norm_le F hF key i
  rw [hz, norm_zero] at h
  exact hi (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem first_key_mem_original {F : FirstPresentation call p}
    (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) : i ∈ F.source.columns := by
  unfold FirstCauchyKey.data at hi
  split_ifs at hi with hside
  · rw [(FirstCauchyKey.piece key).right_columns] at hi
    exact (Finset.mem_filter.mp hi).1
  · rw [(FirstCauchyKey.piece key).left_columns] at hi
    exact (Finset.mem_filter.mp hi).1

theorem first_key_coefficient_bound
    (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (horders : originalOrders ⊆ input.orders)
    (key : FirstCauchyKey F) (i : F.source.Column)
    (hi : i ∈ (FirstCauchyKey.data key).columns) :
    ‖FirstCauchyKey.coefficient key i‖ ≤ 2 * input.amplitude ^ (c.geometry.slots + 2) :=
  (first_key_coefficient_norm_le F hF key i).trans
    (first_coefficient_norm_le F hF input horders i (first_key_mem_original key i hi))

theorem first_key_activeColumns_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (key : FirstCauchyKey F) :
    (((FirstCauchyKey.data key).columns.filter
      (fun i => FirstCauchyKey.coefficient key i ≠ 0)).card : ℝ) ≤
        (idealCountConstant K * call.base ^ originalColumnExponent c) ^
          (c.geometry.slots + 2) := by
  have hsub : (FirstCauchyKey.data key).columns.filter
      (fun i => FirstCauchyKey.coefficient key i ≠ 0) ⊆ firstActiveColumns F := by
    intro i hi
    have him := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨first_key_mem_original key i him.1,
        first_key_coefficient_ne_zero F hF key i him.2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (firstActiveColumns_card F hF input hlarge)

theorem first_family_coefficient_bound
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (horders : originalOrders ⊆ input.orders) (i : Fin family.count) :
    ∀ j ∈ (family.source i).source.columns,
      ‖(family.source i).source.coefficient j‖ ≤
        2 * input.amplitude ^ (c.geometry.slots + 2) := by
  have he := dependent_projection_eq
    (fun (Column : Type) (source : ActualGaussSource (Arithmetic.context c) Column) =>
      ∀ j ∈ source.columns, ‖source.coefficient j‖ ≤
        2 * input.amplitude ^ (c.geometry.slots + 2))
    (hf.column i) (hf.source i)
  rw [he]
  exact fun j hj => first_key_coefficient_bound F hF input horders (family.index i) j hj

theorem first_family_activeColumns_card
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hf : family.Realizes)
    (input : ProfileInput call) (hlarge : originalThreshold c call.frame ≤ call.base)
    (i : Fin family.count) :
    (((family.source i).source.columns.filter
      (fun j => (family.source i).source.coefficient j ≠ 0)).card : ℝ) ≤
        (idealCountConstant K * call.base ^ originalColumnExponent c) ^
          (c.geometry.slots + 2) := by
  have he := dependent_projection_eq
    (fun (Column : Type) (source : ActualGaussSource (Arithmetic.context c) Column) =>
      ((source.columns.filter (fun j => source.coefficient j ≠ 0)).card : ℝ))
    (hf.column i) (hf.source i)
  rw [he]
  exact first_key_activeColumns_card F hF input hlarge (family.index i)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_key_coefficient_norm_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_coefficient_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.first_family_activeColumns_card
