import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeMellinInduction
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeDataReflectionFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchParameterTransport

/-!
# Assembling the actual recipe reflection family with Mellin strict calls

The reflection preparation is executed here, rather than supplied as a
completed local reduction. Its literal root, base coefficient ledgers,
positive reflection kernels and universal quarter labels form the local
scalar certificates. The two real parameter spaces occupy fixed summands
of one common space. Only coefficient and height budgets are enlarged.

The remaining strict callback contains actual Mellin profiles and labelled
canonical outputs, never a parent moment or local scalar bound. Its
constants precede every scale, height, original index and node.

The prepared universal family now contains the original per-slot mesh.
Its genuine reflection factory proves that primitive for each literal
child before creating the child label. An additional data-only dictionary
Q is retained in every source and child label, using its literal
constructor-preservation proof. The strict callback therefore receives
Q, the original mesh, the fixed exponent `2 * c.family.B - 1`, actual
arithmetic and ranked profile invariants. The exponent is preserved by
Mellin preprocessing and equal-product comparison, and canonical strict
outputs retain it through their actual left/right kappa identities.
It must still construct the canonical output for the
literal Mellin input. This module does not claim that this remaining
producer or the original three targets have already been completed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

private theorem height_budget_mono {C C' H H' T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hCC' : C ≤ C') (hHH' : H ≤ H') :
    C * (1 + T) ^ H ≤ C' * (1 + T) ^ H' :=
  mul_le_mul hCC' (Real.rpow_le_rpow_of_exponent_le (by linarith) hHH')
    (Real.rpow_nonneg (by linarith) H) (hC.trans hCC')

private def terminal_enlarge_budget {residual U T C H C' H' floor padding sigma boundary : ℝ}
    (out : TerminalComponents.{u} residual U T C H floor padding sigma boundary)
    (hbudget : C * (1 + T) ^ H ≤ C' * (1 + T) ^ H') :
    TerminalComponents.{u} residual U T C' H' floor padding sigma boundary where
  Label := out.Label
  terms := out.terms
  coefficient := out.coefficient
  exponent := out.exponent
  coefficient_nonneg := out.coefficient_nonneg
  estimate := out.estimate
  mass := out.mass.trans hbudget
  ledger := out.ledger

private def strict_enlarge_budget {Ω : Type u} [MeasurableSpace Ω]
    {sigma W : ℝ} {S : PolynomialSystem.{u} K ω ψ sigma W} {x : S.Label}
    {U T C H C' H' beta delta : ℝ}
    {admissible : MomentData K ω ψ → RealParameters → Prop}
    (out : MellinStrictBranchAt (Ω := Ω) S x U T C H beta delta admissible)
    (hbudget : C * (1 + T) ^ H ≤ C' * (1 + T) ^ H') :
    MellinStrictBranchAt (Ω := Ω) S x U T C' H' beta delta admissible where
  cap := out.cap
  order := out.order
  weight := out.weight
  lower := out.lower
  upper := out.upper
  weight_nonneg := out.weight_nonneg
  lower_pos := out.lower_pos
  interval := out.interval
  profileBudget := out.profileBudget
  profileBudget_one_le := out.profileBudget_one_le
  slot_cap := out.slot_cap
  profiles := out.profiles
  engineCoefficient := out.engineCoefficient
  engineControl := out.engineControl
  outputs := out.outputs
  budget := out.budget.trans hbudget

private def short_enlarge_budget {Ω : Type u} [MeasurableSpace Ω]
    {sigma W : ℝ} {S : PolynomialSystem.{u} K ω ψ sigma W} {x : S.Label}
    {U boundary delta beta C control C' control' : ℝ}
    (out : ShortReflectionBranchAt (Ω := Ω) S x U boundary delta beta C control)
    (hU : 0 ≤ U) (hbudget : C * control ≤ C' * control') :
    ShortReflectionBranchAt (Ω := Ω) S x U boundary delta beta C' control' where
  output := out.output
  terminal := out.terminal.trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hU beta))
  mass := out.mass.trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hU delta))

private def outer_enlarge_budget {Ω : Type u} [MeasurableSpace Ω]
    {sigma W : ℝ} {S : PolynomialSystem.{u} K ω ψ sigma W} {x : S.Label}
    {U padding delta beta C control C' control' : ℝ}
    (out : OuterReflectionBranchAt (Ω := Ω) S x U padding delta beta C control)
    (hU : 0 ≤ U) (hbudget : C * control ≤ C' * control') :
    OuterReflectionBranchAt (Ω := Ω) S x U padding delta beta C' control' where
  output := out.output
  terminal := out.terminal.trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hU beta))
  mass := out.mass.trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hU delta))

namespace Source

variable {c : TargetContext K}
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

/-- The strict producer and the real dyadic reflection parameters share
one fixed space; no frequency-dependent measure bind is used. -/
abbrev RecipeMellinParameter := (ℝ × ℝ) ⊕ ((ℕ × Bool) × ℝ)

/-- The exact remaining strict producer obligation on the prepared
family. It supplies actual per-frequency canonical outputs with their
literal child labels and pure profile/coefficient budgets.

The concrete data predicate Q, original per-slot mesh and original
fixed cancellation exponent are already primitive invariants of every
node in this family. Supplying its canonical producing theorem remains
a separate obligation; no finished energy estimate is a field here. -/
structure RecipeMellinStrictFamily
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (Q : MomentData K c.family.omega (targetCharacter K c) → Prop)
    (ground : ℕ) (engine reflection : ℕ → ℕ) (A Cp Hp lower upper : ℝ) where
  coefficient : ℝ
  heightDegree : ℝ
  threshold : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  heightDegree_nonneg : 0 ≤ heightDegree
  outputs : ∀ Z : ℝ, threshold ≤ Z → ∀ T : ℝ, 0 ≤ T →
    ∀ i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T,
    let S := recipeDataReflectionSystem c Q ground engine reflection
      A Cp Hp lower upper (momentBaseFor i) T
    ∀ x : S.Label,
    EngineStep.PairedEngineDomain (S.node x).centered (S.node x).data
      (S.node x).parameters (momentBaseFor i)
      (momentBaseFor i ^ (S.node x).comparison₁)
      (momentBaseFor i ^ (S.node x).comparison₂)
      (16 * recipeInductionSigma c) (recipeInductionSigma c / 16) →
    Nonempty (MellinStrictBranchAt (Ω := RecipeMellinParameter) S x (momentBaseFor i) T
      coefficient heightDegree (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
      (admissibleOfInvariant (recipeDataReflectionPrimitive c Q ground engine reflection
        (recipeInductionSigma c) (recipeInductionSigma c / 16)
        A Cp Hp lower upper (momentBaseFor i) T)))

/-- Every non-strict input is constructed from the actual prepared
reflection family. The same original root is retained, including when
`indexMap` selects its zero-slot version. -/
def RecipeDataReflectionFamilyData.scalarCertificate
    {R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)}
    {Q : MomentData K c.family.omega (targetCharacter K c) → Prop}
    {ground : ℕ} {engine reflection : ℕ → ℕ} {A Cp Hp lower upper Cr Hr Z T : ℝ}
    {indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T}
    {s : SixthUnitClasses K (places K c)}
    (prepared : RecipeDataReflectionFamilyData R Q ground engine reflection
      A Cp Hp lower upper Cr Hr (indexMap Z T i) s)
    (strict : RecipeMellinStrictFamily R Q ground engine reflection A Cp Hp lower upper)
    (hCr : 0 ≤ Cr) (hT : 0 ≤ T) (hZ : strict.threshold ≤ Z)
    (hbase : momentBaseFor (indexMap Z T i) = momentBaseFor i) :
    RecipeScalarLocalCertificate.{0} R indexMap
      (max Cr strict.coefficient) (max Hr strict.heightDegree) i s := by
  let j := indexMap Z T i
  let S := recipeDataReflectionSystem c Q ground engine reflection
    A Cp Hp lower upper (momentBaseFor j) T
  let primitive := recipeDataReflectionPrimitive c Q ground engine reflection
    (recipeInductionSigma c) (recipeInductionSigma c / 16)
    A Cp Hp lower upper (momentBaseFor j) T
  let C := max Cr strict.coefficient
  let H := max Hr strict.heightDegree
  have hreflection : Cr * (1 + T) ^ Hr ≤ C * (1 + T) ^ H :=
    height_budget_mono hT hCr (le_max_left _ _) (le_max_left _ _)
  have hstrict : strict.coefficient * (1 + T) ^ strict.heightDegree ≤ C * (1 + T) ^ H :=
    height_budget_mono hT strict.coefficient_nonneg (le_max_right _ _) (le_max_right _ _)
  have hσ : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  have hr : 0 ≤ sourceReserve c.family.lamA :=
    (moment_mesh_engine_bounds c.family.lamA_pos).2.1.le
  have hU : 0 ≤ momentBaseFor j := (zero_lt_one.trans prepared.scale).le
  let localInputs : MellinCoreRecursionInput (Ω := RecipeMellinParameter) S
      (momentBaseFor j) T C H (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
      (16 * recipeInductionSigma c) (recipeInductionSigma c / 16)
      (sourceReserve c.family.lamA) ((1 + T) ^ H) (admissibleOfInvariant primitive) := {
    geometry := universalPolynomialSystem_geometry primitive (recipeInductionSigma c) 2
      (recipeInductionSigma c / 16) c.geometry.slots hσ
    scale := prepared.scale
    coefficient_nonneg := hCr.trans (le_max_left _ _)
    height_nonneg := hT
    floor_nonneg := by positivity
    padding_nonneg := by positivity
    boundary_nonneg := hr
    boundary_le_floor :=
      (recipe_reflection_comparison_floor c.family.lamA_pos (le_refl _)).1
    terminal_budget := le_rfl
    original_profile_bound := le_rfl
    node_admissible := fun x => x.down.property.admissible
    engine := fun x _hadmissible hdomain =>
      strict_enlarge_budget (Classical.choice (strict.outputs Z hZ T hT j x hdomain)) hstrict
    baseComponents := fun x hwidth hlength =>
      terminal_enlarge_budget (Classical.choice (prepared.base x hwidth hlength)) hreflection
    shortReflection := fun x hwidth hcore hordinary hlarge hshort =>
      short_enlarge_budget
        ((Classical.choice (prepared.shortReflection x hwidth hcore hordinary hlarge hshort)).inrParameter
          (Ω' := ℝ × ℝ) ((0, false), 0)) hU hreflection
    outerReflection := fun x hnoncore hzero hordinary =>
      outer_enlarge_budget
        ((Classical.choice (prepared.outerReflection x hnoncore hzero hordinary)).inrParameter
          (Ω' := ℝ × ℝ) ((0, false), 0)) hU hreflection
    quarterLabels := fun x _hwidth hcore _hordinary _hlarge hleft hright =>
      universalQuarterLabels primitive (recipeInductionSigma c) 2
        (recipeInductionSigma c / 16) c.geometry.slots hσ x hcore hleft.le hright.le }
  exact {
    system := S
    root := prepared.source.root
    root_eq := prepared.source.root_eq
    parameterSpace := RecipeMellinParameter
    parameterMeasurable := inferInstance
    originalControl := (1 + T) ^ H
    admissible := admissibleOfInvariant primitive
    localInputs := by simpa only [j, hbase] using localInputs }

private def scalarInput_from_reflectionFamilies
    {R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c)}
    {Q : MomentData K c.family.omega (targetCharacter K c) → Prop}
    {ground : ℕ} {engine reflection : ℕ → ℕ} {A Cp Hp lower upper Cr Hr Zr : ℝ}
    (strict : RecipeMellinStrictFamily R Q ground engine reflection A Cp Hp lower upper)
    (hCr : 0 ≤ Cr) (hHr : 0 ≤ Hr) (hZr : 1 ≤ Zr)
    (indexMap : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T →
        SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (eligible : ∀ Z T,
      SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T → Prop)
    (hbase : ∀ Z T (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T),
      momentBaseFor (indexMap Z T i) = momentBaseFor i)
    (families : ∀ Z : ℝ, Zr ≤ Z → ∀ T : ℝ, 0 ≤ T →
      ∀ i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T,
      eligible Z T i → ∀ s : SixthUnitClasses K (places K c),
      Nonempty (RecipeDataReflectionFamilyData R Q ground engine reflection
        A Cp Hp lower upper Cr Hr (indexMap Z T i) s)) :
    RecipeScalarLocalInput.{0} R indexMap eligible where
  heightDegree := max Hr strict.heightDegree
  ceiling := 1
  heightDegree_nonneg := hHr.trans (le_max_left _ _)
  ceiling_pos := by norm_num
  families := by
    intro τ _hτ _hceiling
    refine ⟨max Zr strict.threshold, max Cr strict.coefficient,
      hZr.trans (le_max_left _ _), hCr.trans (le_max_left _ _), ?_⟩
    intro Z hZ i _hbin heligible s
    have hZr' : Zr ≤ Z := (le_max_left _ _).trans hZ
    have hZs : strict.threshold ≤ Z := (le_max_right _ _).trans hZ
    have hT : 0 ≤ Z ^ τ := Real.rpow_nonneg (zero_le_one.trans (hZr.trans hZr')) τ
    obtain ⟨prepared⟩ := families Z hZr' (Z ^ τ) hT i heligible s
    exact ⟨prepared.scalarCertificate strict hCr hT hZs (hbase Z (Z ^ τ) i)⟩

/-- Run the real source and reflection preparation, then assemble all
local inputs around only the explicit remaining strict producer. The
additional Q inputs are concrete source dictionaries and their literal
fixed-line preservation, not an intermediate analytic conclusion. The
same common degree and constants work for the original unrestricted
zero-slot projection and the capacity-eligible positive projection.
This is a construction of certificates, not a claim that the strict
canonical producing callback has been proved. -/
theorem recipeMellinFamily_preparation
    (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (Q : MomentData K c.family.omega (targetCharacter K c) → Prop)
    (hQpreserved : FixedLineDataPreserved Q)
    (hQroot : ∀ (Z T : ℝ)
      (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
      (s : SixthUnitClasses K (places K c)), Q (recipeRoot R i s).data)
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    {lengthBound : ℝ} (hgeom : R.MomentGeometry lengthBound)
    (hprofiles : WholeMomentProfileControlFor (recipeMomentModels K c R))
    (w : InfinitePlace K) (hψ : heckeRadialParameter K w (targetCharacter K c) = 0) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ 1 / 2 ∧ 2 ≤ upper ∧ lower < upper ∧
      ∃ decay : ℝ, 1 < decay ∧ ∃ reflection : ℕ → ℕ,
      (∀ J, J ≤ reflection J ∧ 1 ≤ reflection J) ∧
      ∀ (ground : ℕ) (engine : ℕ → ℕ), 1 ≤ ground →
      ∃ Cp Hp : ℝ, 0 < Cp ∧ 0 ≤ Hp ∧
      ∀ strict : RecipeMellinStrictFamily R Q ground engine reflection decay Cp Hp lower upper,
      Nonempty (RecipeScalarLocalInput.{0} R (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
      ((∀ j : Fin R.family.presentationCount,
          FiniteOrder (R.family.presentation j).plainBackground →
            (R.family.presentation j).plainBackground⁻¹ ∈ (R.family.presentation j).theta) →
        Nonempty (RecipeScalarLocalInput.{0} R (fun _ _ i => i)
          (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty))) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
      decay, hdecay, reflection, hreflection, preparation⟩ :=
    recipeDataReflectionFamily_preparation R Q hQpreserved hQroot hcomplex hgeom hprofiles w hψ
  refine ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
    decay, hdecay, reflection, hreflection, ?_⟩
  intro ground engine hground
  obtain ⟨Cp, Hp, Cr, Hr, Zr, hCp, hHp, hCr, hHr, hZr, families⟩ :=
    preparation ground engine hground
  refine ⟨Cp, Hp, hCp, hHp, ?_⟩
  intro strict
  constructor
  · exact ⟨scalarInput_from_reflectionFamilies strict hCr hHr hZr
      (fun _ _ i => i.noSlots) (fun _ _ _ => True) (fun _ _ _ => rfl)
      (fun Z hZ T hT i _heligible s => (families Z hZ T hT i s).1)⟩
  · intro hfinite
    exact ⟨scalarInput_from_reflectionFamilies strict hCr hHr hZr
      (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)
      (fun _ _ _ => rfl)
      (fun Z hZ T hT i heligible s => (families Z hZ T hT i s).2 hfinite heligible.1)⟩

end Source

end HeckeSkeleton.Moments.EngineInduction
