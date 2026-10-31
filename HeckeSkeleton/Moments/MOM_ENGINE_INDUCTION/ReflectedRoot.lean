import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Induction
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# One outer ordinary reflection after the core induction

An unrestricted zero-slot source need not have an earlier padded-core
child in the two-stage rank: both may occupy the same width band and the
later stage. The consumer here first proves the bound for a closed core
system, then integrates it once against the original reflection measure.
No additional recursive edge or fictitious decrease is introduced.

The reflection inequality, its actual child polynomials, integrability,
terminal components and kernel mass remain obligations of the reflection
producer. In particular, this file does not prove the conductor-over-scale
reflection formula. The extra mass exponent is charged once, with the
core mesh and the original source row width unchanged.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

universe u v w

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- A genuine outer reflection on the original parameter space. The
children belong to a separately closed core system, so no earlier-state
field is appropriate here. Normalization uses each node's actual width. -/
structure OuterReflectionAt {σ W : ℝ} (parent : Node K ω ψ)
    (core : PolynomialSystem.{u} K ω ψ σ W) (U t : ℝ)
    (Ω : Type v) [MeasurableSpace Ω] where
  kernel : Measure Ω
  finite : IsFiniteMeasure kernel
  child : Ω → core.Label
  remainder : ℝ
  integrable : Integrable (fun ξ => (core.node (child ξ)).normalizedEnergy U t) kernel
  estimate : parent.normalizedEnergy U t ≤ remainder +
    ∫ ξ, (core.node (child ξ)).normalizedEnergy U t ∂kernel

/-- Consume an already proved core bound once. This theorem has no
recursive hypothesis and its kernel exponent is not multiplied by depth. -/
theorem OuterReflectionAt.power_bound
    {σ W U t : ℝ} {parent : Node K ω ψ}
    {core : PolynomialSystem.{u} K ω ψ σ W}
    {Ω : Type v} [MeasurableSpace Ω]
    (out : OuterReflectionAt parent core U t Ω)
    (T coreC coreH C H β e δ : ℝ)
    (hU : 1 ≤ U) (hT : 0 ≤ T) (hcoreC : 0 ≤ coreC) (hcoreH : 0 ≤ coreH)
    (hC : 0 ≤ C) (hexponent : β ≤ e + δ)
    (hcore : ∀ x, (core.node x).normalizedEnergy U t ≤
      coreC * U ^ e * (1 + T) ^ coreH)
    (hterminal : out.remainder ≤ C * (1 + T) ^ H * U ^ β)
    (hmass : out.kernel.real Set.univ ≤ C * (1 + T) ^ H * U ^ δ) :
    parent.normalizedEnergy U t ≤
      (C * (1 + coreC)) * U ^ (e + δ) * (1 + T) ^ (coreH + H) := by
  letI : IsFiniteMeasure out.kernel := out.finite
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hTpos : 0 < 1 + T := by linarith
  have hheight : 1 ≤ (1 + T) ^ coreH := Real.one_le_rpow (by linarith) hcoreH
  have hcore_nonneg : 0 ≤ coreC * U ^ e * (1 + T) ^ coreH := by positivity
  have hi := integral_mono_ae out.integrable
    (integrable_const (coreC * U ^ e * (1 + T) ^ coreH))
    (Filter.Eventually.of_forall fun ξ => hcore (out.child ξ))
  simp only [integral_const, smul_eq_mul] at hi
  have hi' : (∫ ξ, (core.node (out.child ξ)).normalizedEnergy U t ∂out.kernel) ≤
      (C * coreC) * U ^ (e + δ) * (1 + T) ^ (coreH + H) := by
    apply (hi.trans (mul_le_mul_of_nonneg_right hmass hcore_nonneg)).trans_eq
    rw [Real.rpow_add hUpos e δ, Real.rpow_add hTpos coreH H]
    ring
  have ht : out.remainder ≤ C * U ^ (e + δ) * (1 + T) ^ (coreH + H) := by
    calc
      out.remainder ≤ C * (1 + T) ^ H * U ^ β := hterminal
      _ ≤ C * (1 + T) ^ H * U ^ (e + δ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexponent)
          (by positivity)
      _ ≤ (C * (1 + T) ^ H * U ^ (e + δ)) * (1 + T) ^ coreH := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hheight
            (by positivity : 0 ≤ C * (1 + T) ^ H * U ^ (e + δ))
      _ = _ := by
        rw [Real.rpow_add hTpos coreH H]
        ring
  apply (out.estimate.trans (add_le_add ht hi')).trans_eq
  ring

variable {Index : ℝ → ℝ → Type v} {Sector : Type w}

/-- The actual unrestricted source and one already closed core system.
The original source is not required to be a node in that system. The
outer reflection certificate contains no completed moment bound. -/
structure ReflectedRootCertificate
    (F : SourceFamily K ω ψ Index Sector)
    (indexMap : ∀ Z T, Index Z T → Index Z T)
    (σ W C H Houter β δ δouter : ℝ)
    {Z T : ℝ} (i : Index Z T) (s : Sector) where
  system : PolynomialSystem.{u} K ω ψ σ W
  base_one_le : 1 ≤ F.base i
  core : ClosedParentReduction K system (F.base i) T 0 C H β δ
  parameterSpace : Type u
  parameterMeasurable : MeasurableSpace parameterSpace
  reflection : @OuterReflectionAt K _ _ ω ψ σ W
    (Node.ordinary (F.model Z T (indexMap Z T i) s) (F.parameters (indexMap Z T i)))
    system (F.base i) 0 parameterSpace parameterMeasurable
  floor : ℝ
  padding : ℝ
  boundary : ℝ
  floor_nonneg : 0 ≤ floor
  padding_nonneg : 0 ≤ padding
  boundary_nonneg : 0 ≤ boundary
  terminal_budget : terminalBudget floor padding σ boundary ≤ β
  components : TerminalComponents.{u} reflection.remainder (F.base i) T C Houter
    floor padding σ boundary
  mass : reflection.kernel.real Set.univ ≤ C * (1 + T) ^ Houter * F.base i ^ δouter

/-- The core rank is unchanged and the outer reflection costs exactly
one additional local mass exponent and one additional height degree. -/
theorem ReflectedRootCertificate.energy_bound
    {F : SourceFamily K ω ψ Index Sector}
    {indexMap : ∀ Z T, Index Z T → Index Z T}
    {σ W C H Houter β δ δouter Z T : ℝ} {i : Index Z T} {s : Sector}
    (cert : ReflectedRootCertificate.{u} F indexMap σ W C H Houter β δ δouter i s)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hH : 0 ≤ H) (hδ : 0 ≤ δ) (hδouter : 0 ≤ δouter) :
    pairedEnergy (F.model Z T (indexMap Z T i) s) (F.parameters (indexMap Z T i))
      (F.base i) 0 ≤
      (C * (1 + C * (1 + C) ^ (4 * (widthBand σ W + 1)))) *
        F.base i ^ (F.rowWidth (indexMap Z T i) +
          (β + (4 * (widthBand σ W + 1) : ℕ) * δ + δouter)) *
        (1 + T) ^ (H * ((4 * (widthBand σ W + 1) : ℕ) + 1) + Houter) := by
  letI : MeasurableSpace cert.parameterSpace := cert.parameterMeasurable
  let N : ℕ := 4 * (widthBand σ W + 1)
  have hcore := cert.core.reduction.power_bound C (F.base i) T H β δ
    hC cert.base_one_le hT hH hδ cert.core.terminal cert.core.mass
  have hterminal := cert.components.bound cert.base_one_le cert.floor_nonneg
    cert.padding_nonneg cert.system.sigma_pos.le cert.boundary_nonneg cert.terminal_budget
  have hexponent : β ≤ (β + (N : ℝ) * δ) + δouter := by
    have hNδ : 0 ≤ (N : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
    linarith
  have hnorm := cert.reflection.power_bound T (C * (1 + C) ^ N)
    (H * ((N : ℝ) + 1)) C Houter β (β + (N : ℝ) * δ) δouter
    cert.base_one_le hT (by positivity) (by positivity) hC hexponent
    hcore hterminal cert.mass
  have hwidth :
      (Node.ordinary (F.model Z T (indexMap Z T i) s)
        (F.parameters (indexMap Z T i))).width = F.rowWidth (indexMap Z T i) := by
    simp only [Node.width, Node.ordinary, SourceFamily.parameters, add_zero]
  simp only [Node.normalizedEnergy, Node.ordinary_energy, hwidth] at hnorm
  have hUpos : 0 < F.base i := zero_lt_one.trans_le cert.base_one_le
  have hraw := (div_le_iff₀ (Real.rpow_pos_of_pos hUpos _)).mp hnorm
  apply hraw.trans_eq
  rw [Real.rpow_add hUpos (F.rowWidth (indexMap Z T i))
    (β + (N : ℝ) * δ + δouter)]
  ring

/-- Outer reflection uses the same fixed core mesh and width limit.
Height degrees and the ceiling precede `tau`; the common threshold and
coefficient precede every source index, sector and core node. -/
structure ReflectedRootInput
    (F : SourceFamily K ω ψ Index Sector)
    (indexMap : ∀ Z T, Index Z T → Index Z T)
    (eligible : ∀ Z T, Index Z T → Prop) (σ W : ℝ) where
  sigma_pos : 0 < σ
  heightDegree : ℝ
  outerHeightDegree : ℝ
  terminalLoss : ℝ
  edgeLoss : ℝ
  outerLoss : ℝ
  ceiling : ℝ
  heightDegree_nonneg : 0 ≤ heightDegree
  outerHeightDegree_nonneg : 0 ≤ outerHeightDegree
  edgeLoss_nonneg : 0 ≤ edgeLoss
  outerLoss_nonneg : 0 ≤ outerLoss
  ceiling_pos : 0 < ceiling
  loss_budget : terminalLoss + (4 * (widthBand σ W + 1) : ℕ) * edgeLoss +
    outerLoss ≤ F.loss
  base_at : ∀ Z T (i : Index Z T), F.base (indexMap Z T i) = F.base i
  certificates : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
    ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
        51 / 100 < F.bin Z (Z ^ τ) i → eligible Z (Z ^ τ) i →
          ∀ s : Sector, Nonempty (ReflectedRootCertificate.{u} F indexMap σ W C
            heightDegree outerHeightDegree terminalLoss edgeLoss outerLoss i s)

/-- Consume the core induction and one outer reflection with the exact
source-family row exponent and all original uniform-bound quantifiers. -/
theorem ReflectedRootInput.sectorBound
    {F : SourceFamily K ω ψ Index Sector}
    {indexMap : ∀ Z T, Index Z T → Index Z T}
    {eligible : ∀ Z T, Index Z T → Prop} {σ W : ℝ}
    (input : ReflectedRootInput.{u} F indexMap eligible σ W) :
    F.SectorBound indexMap eligible := by
  let N : ℕ := 4 * (widthBand σ W + 1)
  refine ⟨input.heightDegree * ((N : ℝ) + 1) + input.outerHeightDegree, input.ceiling,
    add_nonneg (mul_nonneg input.heightDegree_nonneg (by positivity))
      input.outerHeightDegree_nonneg, input.ceiling_pos, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hcert⟩ := input.certificates τ hτ hτc
  refine ⟨Z₀, C * (1 + C * (1 + C) ^ N), hZ₀, by positivity, ?_⟩
  intro Z hZ i hbin helig s
  obtain ⟨cert⟩ := hcert Z hZ i hbin helig s
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₀.trans hZ)
  have hT : 0 ≤ Z ^ τ := Real.rpow_nonneg hZn τ
  have hb := cert.energy_bound hC hT input.heightDegree_nonneg
    input.edgeLoss_nonneg input.outerLoss_nonneg
  have hw : F.rowWidth (indexMap Z (Z ^ τ) i) = F.rowWidth i := by
    simp only [SourceFamily.rowWidth, input.base_at Z (Z ^ τ) i]
  rw [hw] at hb
  rw [input.base_at Z (Z ^ τ) i]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le cert.base_one_le
      have hbudget := input.loss_budget
      linarith
    · positivity
  · exact Real.rpow_nonneg (by linarith) _

/-- The unrestricted zero-slot source projection, after an actual outer
reflection into the proved core. No plain-length capacity is assumed. -/
theorem paired_zero_slot_of_reflected_core [Fintype Sector]
    (F : SourceFamily K ω ψ Index Sector) {σ W : ℝ}
    (input : ReflectedRootInput.{u} F F.noSlots (fun _ _ _ => True) σ W) :
    F.ZeroSlotBound :=
  F.zeroSlotBound_of_sectorBound input.sectorBound

end HeckeSkeleton.Moments.EngineInduction
