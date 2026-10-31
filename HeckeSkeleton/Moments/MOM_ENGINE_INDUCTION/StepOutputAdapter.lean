import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ChildStepCompatibility
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BranchedIntegralRecursion
import HeckeGeneral.Analysis.TInputSeparatedProfiles

/-!
# Consuming the canonical complete engine output

`EngineStep.PairedEngineConclusion` is imported from the provider's exact
`fabcb58e` source.  Its production remains the engine theorem's obligation;
this module does not assert that the record is inhabited.

The provider permits a different twist at each continuous child parameter.
We freeze that time into the actual test profiles, with no additional
complex power.  This preserves both plain polynomials, the entire slot
product, all original row and mask data, and every geometric length.  All
nodes can consequently be evaluated at the common interface time zero.

The AM--GM adapter retains the four actual terminal contributions and the
provider's full positive kernels.  It assumes no child moment estimate.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open scoped BigOperators Classical

universe u v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Evaluate every actual profile at one time, retaining its original
character and mask and introducing no extra power twist. -/
def freezeMomentTime (d : MomentData K ω ψ) (time : ℝ) : MomentData K ω ψ :=
  d.separatedProfiles (fun _ => time) (fun _ => time) (fun _ => time)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => time) (fun _ => 0)

@[simp] theorem freezeMomentTime_rows (d : MomentData K ω ψ) (time : ℝ)
    (a : RealParameters) (U : ℝ) :
    pairedRows (freezeMomentTime d time) a U = pairedRows d a U := rfl

@[simp] theorem freezeMomentTime_slotCount (d : MomentData K ω ψ) (time : ℝ) :
    (freezeMomentTime d time).geometry.slotCount = d.geometry.slotCount := rfl

@[simp] theorem freezeMomentTime_totalLength (d : MomentData K ω ψ) (time : ℝ) :
    (freezeMomentTime d time).geometry.totalLength = d.geometry.totalLength := rfl

@[simp] theorem freezeMomentTime_fitsMesh (d : MomentData K ω ψ) (time mesh : ℝ) :
    (freezeMomentTime d time).geometry.fitsMesh mesh ↔ d.geometry.fitsMesh mesh := Iff.rfl

@[simp] theorem freezeMomentTime_plainPolynomial₁ (d : MomentData K ω ψ)
    (time : ℝ) (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial (freezeMomentTime d time) (freezeMomentTime d time).plainTest₁ u N 0 =
      plainPolynomial d d.plainTest₁ u N time := by
  simp only [freezeMomentTime, plainPolynomial, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_zero, mul_one, maskValue]

@[simp] theorem freezeMomentTime_plainPolynomial₂ (d : MomentData K ω ψ)
    (time : ℝ) (u : NonzeroIdeal K) (N : ℝ) :
    plainPolynomial (freezeMomentTime d time) (freezeMomentTime d time).plainTest₂ u N 0 =
      plainPolynomial d d.plainTest₂ u N time := by
  simp only [freezeMomentTime, plainPolynomial, MomentData.separatedProfiles,
    IdealTest.freezeTwist, profilePower_zero, mul_one, maskValue]

@[simp] theorem freezeMomentTime_primePolynomial (d : MomentData K ω ψ)
    (time : ℝ) (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (U : ℝ) :
    primePolynomial (freezeMomentTime d time) i u U 0 = primePolynomial d i u U time := by
  simp only [freezeMomentTime, primePolynomial, MomentData.separatedProfiles,
    SlotGeometry.freezeTwists, PrimeWindow.freezeTwist, profilePower_zero, mul_one, maskValue]
  rfl

@[simp] theorem freezeMomentTime_slotProduct (d : MomentData K ω ψ)
    (time : ℝ) (u : NonzeroIdeal K) (U : ℝ) :
    slotProduct (freezeMomentTime d time) u U 0 = slotProduct d u U time := by
  unfold slotProduct
  apply Finset.prod_congr rfl
  intro i _
  exact freezeMomentTime_primePolynomial d time i u U

@[simp] theorem freezeMomentTime_pairedEnergy (d : MomentData K ω ψ)
    (time : ℝ) (a : RealParameters) (U : ℝ) :
    pairedEnergy (freezeMomentTime d time) a U 0 = pairedEnergy d a U time := by
  simp only [pairedEnergy, freezeMomentTime_rows, freezeMomentTime_plainPolynomial₁,
    freezeMomentTime_plainPolynomial₂, freezeMomentTime_slotProduct]

/-- Both rectangles of the same node are frozen together. -/
def Node.freezeTime (n : Node K ω ψ) (time : ℝ) : Node K ω ψ :=
  { n with data := freezeMomentTime n.data time }

@[simp] theorem Node.freezeTime_width (n : Node K ω ψ) (time : ℝ) :
    (n.freezeTime time).width = n.width := rfl

@[simp] theorem Node.freezeTime_plainPair (n : Node K ω ψ)
    (time : ℝ) (u : NonzeroIdeal K) (U : ℝ) :
    (n.freezeTime time).plainPair u U 0 = n.plainPair u U time := by
  simp only [Node.freezeTime, Node.plainPair, freezeMomentTime_plainPolynomial₁,
    freezeMomentTime_plainPolynomial₂]

@[simp] theorem Node.freezeTime_energy (n : Node K ω ψ) (time U : ℝ) :
    (n.freezeTime time).energy U 0 = n.energy U time := by
  simp only [Node.energy, Node.freezeTime, Node.plainPair, freezeMomentTime_rows,
    freezeMomentTime_plainPolynomial₁, freezeMomentTime_plainPolynomial₂,
    freezeMomentTime_slotProduct]

@[simp] theorem Node.freezeTime_normalizedEnergy (n : Node K ω ψ) (time U : ℝ) :
    (n.freezeTime time).normalizedEnergy U 0 = n.normalizedEnergy U time := by
  simp only [Node.normalizedEnergy, Node.freezeTime_energy, Node.freezeTime_width]

/-- The provider's centered parent is exactly the node coefficient. -/
theorem Node.energy_eq_pairedStageEnergy (n : Node K ω ψ) (U t : ℝ) :
    n.energy U t = EngineStep.pairedStageEnergy n.centered n.data n.parameters
      U t (U ^ n.comparison₁) (U ^ n.comparison₂) := rfl

/-- A variable child twist has the same normalized energy at time zero
after freezing its actual profiles. -/
theorem ordinary_freezeMomentTime_normalizedEnergy (d : MomentData K ω ψ)
    (a : RealParameters) (U time : ℝ) :
    (Node.ordinary (freezeMomentTime d time) a).normalizedEnergy U 0 =
      EngineStep.normalizedPairedEnergy d a U time := by
  unfold Node.normalizedEnergy EngineStep.normalizedPairedEnergy
  rw [Node.ordinary_energy, freezeMomentTime_pairedEnergy]
  rfl

/-- Only an abbreviation of the provider's canonical output type, for
the literal node at the common interface time zero. -/
abbrev Node.EngineOutput {Ω : Type v} [MeasurableSpace Ω]
    (n : Node K ω ψ) (U σ δ β C control : ℝ) :=
  EngineStep.PairedEngineConclusion (Ω := Ω) n.centered n.data n.parameters
    U 0 (U ^ n.comparison₁) (U ^ n.comparison₂) σ δ β C control

/-- Linearize the actual output while retaining the four original
terminal contributions rather than renaming them as a base case. -/
theorem engineOutput_linearized_terminals {Ω : Type v} [MeasurableSpace Ω]
    {n : Node K ω ψ} {U σ δ β C control : ℝ}
    (out : n.EngineOutput (Ω := Ω) U σ δ β C control) (hU : 0 < U) :
    n.normalizedEnergy U 0 ≤ out.firstZero + out.secondZero + out.exceptional + out.tail +
      ∑ b, ((∫ ξ, EngineStep.normalizedPairedEnergy
        (out.leftData b ξ) (out.leftParameters b) U (out.leftTwist b ξ) ∂out.kernel b) +
        ∫ ξ, EngineStep.normalizedPairedEnergy
          (out.rightData b ξ) (out.rightParameters b) U (out.rightTwist b ξ) ∂out.kernel b) / 2 := by
  apply out.parent.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro b _
  have hpoint (ξ : Ω) :
      Real.sqrt (EngineStep.normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) U
        (out.leftTwist b ξ)) *
      Real.sqrt (EngineStep.normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) U
        (out.rightTwist b ξ)) ≤
      (EngineStep.normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) U
        (out.leftTwist b ξ) +
       EngineStep.normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) U
        (out.rightTwist b ξ)) / 2 := by
    have hl := EngineStep.normalizedPairedEnergy_nonneg
      (out.leftData b ξ) (out.leftParameters b) U (out.leftTwist b ξ) hU
    have hr := EngineStep.normalizedPairedEnergy_nonneg
      (out.rightData b ξ) (out.rightParameters b) U (out.rightTwist b ξ) hU
    nlinarith [sq_nonneg
      (Real.sqrt (EngineStep.normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b) U
        (out.leftTwist b ξ)) -
       Real.sqrt (EngineStep.normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b) U
        (out.rightTwist b ξ))), Real.sq_sqrt hl, Real.sq_sqrt hr]
  have hi := integral_mono (out.cauchy_integrable b)
    (((out.left_integrable b).add (out.right_integrable b)).div_const 2) hpoint
  rw [integral_div] at hi
  simp only [Pi.add_apply] at hi
  rw [integral_add (out.left_integrable b) (out.right_integrable b)] at hi
  exact hi

/-- Put one literal engine output in the induction schedule. The child
labels must denote the actual frozen models, and a zero-slot parent must
have zero-slot children. No measurable structure on labels or child map
is required. Width decrease comes from the canonical output itself. -/
def engineOutputToBranchedAt {Ω : Type v} [MeasurableSpace Ω]
    {σ W U δ β C control : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W)
    (x : S.Label)
    (out : (S.node x).EngineOutput (Ω := Ω) U σ δ β C control)
    (hU : 0 < U)
    (left right : Fin out.branches → Ω → S.Label)
    (hleft : ∀ b ξ, S.node (left b ξ) =
      Node.ordinary (freezeMomentTime (out.leftData b ξ) (out.leftTwist b ξ))
        (out.leftParameters b))
    (hright : ∀ b ξ, S.node (right b ξ) =
      Node.ordinary (freezeMomentTime (out.rightData b ξ) (out.rightTwist b ξ))
        (out.rightParameters b))
    (hzeroLeft : ∀ b, (S.node x).parameters.z = 0 → (out.leftParameters b).z = 0)
    (hzeroRight : ∀ b, (S.node x).parameters.z = 0 → (out.rightParameters b).z = 0) :
    BranchedIntegralAt (Ω := Ω)
      (fun y => (S.node y).normalizedEnergy U 0) S.schedule x where
  branches := out.branches
  kernel := out.kernel
  finite := out.finite_kernel
  left := left
  right := right
  remainder := out.firstZero + out.secondZero + out.exceptional + out.tail
  left_integrable b := by
    simpa only [hleft, ordinary_freezeMomentTime_normalizedEnergy] using out.left_integrable b
  right_integrable b := by
    simpa only [hright, ordinary_freezeMomentTime_normalizedEnergy] using out.right_integrable b
  left_earlier b := Filter.Eventually.of_forall fun ξ => by
    apply S.earlier_of_width_drop (left b ξ) x
    · rw [hleft b ξ]
      change (out.leftParameters b).m + (out.leftParameters b).q + σ / 2 ≤
        (S.node x).parameters.m + (S.node x).parameters.q
      linarith [out.left_width b]
    · intro hz
      rw [hleft b ξ]
      exact hzeroLeft b hz
  right_earlier b := Filter.Eventually.of_forall fun ξ => by
    apply S.earlier_of_width_drop (right b ξ) x
    · rw [hright b ξ]
      change (out.rightParameters b).m + (out.rightParameters b).q + σ / 2 ≤
        (S.node x).parameters.m + (S.node x).parameters.q
      linarith [out.right_width b]
    · intro hz
      rw [hright b ξ]
      exact hzeroRight b hz
  estimate := by
    simpa only [hleft, hright, ordinary_freezeMomentTime_normalizedEnergy] using
      engineOutput_linearized_terminals out hU

/-- Assemble engine outputs only on a family where each node has such an
output. For a system with base or reflection cases, use the local adapter
above together with `BranchedIntegralStep.ofLocal`. -/
def engineOutputsToBranchedStep {Ω : Type v} [MeasurableSpace Ω]
    {σ W U δ β C : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W)
    (control : S.Label → ℝ)
    (outputs : ∀ x, (S.node x).EngineOutput (Ω := Ω) U σ δ β C (control x))
    (hU : 0 < U)
    (left right : ∀ x, Fin (outputs x).branches → Ω → S.Label)
    (hleft : ∀ x b ξ, S.node (left x b ξ) =
      Node.ordinary (freezeMomentTime ((outputs x).leftData b ξ) ((outputs x).leftTwist b ξ))
        ((outputs x).leftParameters b))
    (hright : ∀ x b ξ, S.node (right x b ξ) =
      Node.ordinary (freezeMomentTime ((outputs x).rightData b ξ) ((outputs x).rightTwist b ξ))
        ((outputs x).rightParameters b))
    (hzeroLeft : ∀ x b,
      (S.node x).parameters.z = 0 → ((outputs x).leftParameters b).z = 0)
    (hzeroRight : ∀ x b,
      (S.node x).parameters.z = 0 → ((outputs x).rightParameters b).z = 0) :
    BranchedIntegralStep (Ω := Ω)
      (fun y => (S.node y).normalizedEnergy U 0) S.schedule :=
  BranchedIntegralStep.ofLocal fun x =>
    engineOutputToBranchedAt S x (outputs x) hU (left x) (right x)
      (hleft x) (hright x) (hzeroLeft x) (hzeroRight x)

/-- The canonical terminal and complete kernel-mass conclusions give the
closed recurrence once their original-profile control is uniform. This
assumes no bound for a recursive child or for the final parent moment. -/
def engineOutputsToClosedParentReduction {Ω : Type u} [MeasurableSpace Ω]
    {σ W U T δ β C H : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W)
    (control : S.Label → ℝ)
    (outputs : ∀ x, (S.node x).EngineOutput (Ω := Ω) U σ δ β C (control x))
    (hU : 0 < U) (hC : 0 ≤ C)
    (hcontrol : ∀ x, control x ≤ (1 + T) ^ H)
    (left right : ∀ x, Fin (outputs x).branches → Ω → S.Label)
    (hleft : ∀ x b ξ, S.node (left x b ξ) =
      Node.ordinary (freezeMomentTime ((outputs x).leftData b ξ) ((outputs x).leftTwist b ξ))
        ((outputs x).leftParameters b))
    (hright : ∀ x b ξ, S.node (right x b ξ) =
      Node.ordinary (freezeMomentTime ((outputs x).rightData b ξ) ((outputs x).rightTwist b ξ))
        ((outputs x).rightParameters b))
    (hzeroLeft : ∀ x b,
      (S.node x).parameters.z = 0 → ((outputs x).leftParameters b).z = 0)
    (hzeroRight : ∀ x b,
      (S.node x).parameters.z = 0 → ((outputs x).rightParameters b).z = 0) :
    ClosedParentReduction K S U T 0 C H β δ where
  reduction := .branched Ω inferInstance
    (engineOutputsToBranchedStep S control outputs hU left right hleft hright
      hzeroLeft hzeroRight)
  terminal x := by
    change (outputs x).firstZero + (outputs x).secondZero + (outputs x).exceptional +
      (outputs x).tail ≤ C * (1 + T) ^ H * U ^ β
    exact (outputs x).terminals.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcontrol x) hC)
        (Real.rpow_nonneg hU.le β))
  mass x := by
    change (∑ b, ((outputs x).kernel b).real Set.univ) ≤ C * (1 + T) ^ H * U ^ δ
    exact (outputs x).mass.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcontrol x) hC)
        (Real.rpow_nonneg hU.le δ))

end HeckeSkeleton.Moments.EngineInduction
