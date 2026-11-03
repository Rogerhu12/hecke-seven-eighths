import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Ledger
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MomentDataAdapter

/-!
# Comparison margins and capacity derived from the actual length ledger

The capacity defect is a conclusion here.  Its inputs are parent capacity,
the lengths of frozen slots and plain extractions, and explicit clipping
and width errors.  The nominal shift is paid by the main pool enlargement
or one of the three valuations 1, 6, 7.  No moment recurrence is an input.

The actual-energy theorem retains the full finite `MomentData` polynomial
and chooses its removed slots before any row, scale or slot values.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

/-- The reflected zero-slot comparison has the stated uncentered margin. -/
theorem comparison_zero_margin (A M Acomp ξ : ℝ)
    (hA : 5 * M / 6 ≤ A) (hcomp : Acomp ≤ 3 * M / 2 - A + ξ) :
    Acomp ≤ 5 * M / 6 - M / 6 + ξ := by linarith

/-- The same reflected comparison lies inside the uncentered positive-slot region. -/
theorem comparison_uncentered_margin (A M Acomp z ξ : ℝ)
    (hA : 5 * M / 6 ≤ A) (hz : z ≤ M / 20)
    (hcomp : Acomp ≤ 3 * M / 2 - A + 2 * z + ξ) :
    Acomp ≤ 5 * M / 6 - M / 15 + ξ := by linarith

/-- Parent capacity pays for the live slots in the comparison rectangle too. -/
theorem comparison_capacity_margin (A M Acomp z κ ξ : ℝ)
    (hA : 5 * M / 6 ≤ A) (hz : z ≤ M / 20)
    (hparent : A + (6 * κ - 1) * z ≤ M)
    (hcomp : Acomp ≤ 3 * M / 2 - A + 2 * z + ξ) :
    Acomp + (6 * κ - 1) * z ≤ M - M / 15 + ξ := by linarith

/-- The lengths used in the two-transform formulas of §4.8.
`c₂` is the second common-support extraction on the selected child side. -/
structure NominalChildGeometry where
  A : ℝ
  m : ℝ
  q : ℝ
  c : ℝ
  d : ℝ
  R : ℝ
  E : ℝ
  Krow : ℝ
  w : ℝ
  wo : ℝ
  g : ℝ
  g₂ : ℝ
  t₂ : ℝ
  V : ℝ
  c₂ : ℝ

namespace NominalChildGeometry

def parentWidth (s : NominalChildGeometry) : ℝ := s.m + s.q
def firstFrequency (s : NominalChildGeometry) : ℝ :=
  2 * s.A - s.c - s.d + s.R + s.E - s.m
def shiftedCommon (s : NominalChildGeometry) : ℝ := s.d + s.firstFrequency - s.Krow
def enlargementJ (s : NominalChildGeometry) : ℝ :=
  s.shiftedCommon - s.c - 2 * s.w + s.wo
def nominalRow (s : NominalChildGeometry) : ℝ :=
  2 * (s.A - s.c - s.w) - s.Krow - s.g - s.g₂ - s.V
def nominalSupport (s : NominalChildGeometry) : ℝ :=
  s.q + s.R + s.E + s.wo + s.t₂ + s.V
def nominalWidth (s : NominalChildGeometry) : ℝ := s.nominalRow + s.nominalSupport
def rawDegree (s : NominalChildGeometry) : ℝ := s.A - s.c - s.w - s.c₂
def paidShift (s : NominalChildGeometry) : ℝ := s.g + s.w - s.shiftedCommon - s.wo

theorem width_identity (s : NominalChildGeometry) :
    s.nominalWidth = s.parentWidth + s.enlargementJ - s.g - s.g₂ + s.t₂ := by
  dsimp [nominalWidth, nominalRow, nominalSupport, parentWidth, enlargementJ,
    shiftedCommon, firstFrequency]
  ring

theorem degree_shift_identity (s : NominalChildGeometry) :
    s.rawDegree - s.nominalWidth - (s.A - s.parentWidth) =
      s.paidShift + s.g₂ - s.t₂ - s.c₂ := by
  dsimp [rawDegree, nominalWidth, nominalRow, nominalSupport, parentWidth,
    paidShift, shiftedCommon, firstFrequency]
  ring

theorem raw_shift_le (s : NominalChildGeometry) (ell supportError : ℝ)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : s.paidShift ≤ 6 * (s.w + ell) + supportError) :
    s.rawDegree - s.nominalWidth ≤
      s.A - s.parentWidth + 6 * (s.w + ell) + supportError := by
  have := s.degree_shift_identity
  linarith

theorem main_paid_shift (s : NominalChildGeometry) (σ supportError : ℝ)
    (hw : s.w = 0) (hwo : s.wo = 0)
    (hg : s.g = max (s.shiftedCommon - s.c) 0 + 2 * σ)
    (hc : 0 ≤ s.c) (hD : -supportError ≤ s.shiftedCommon)
    (herr : 0 ≤ supportError) :
    s.paidShift ≤ 6 * (s.w + σ / 3) + supportError := by
  have h := main_capacity_shift s.shiftedCommon s.c σ supportError hc hD herr
  simpa only [paidShift, hw, hwo, hg, zero_add, add_zero, sub_zero] using h

theorem error_paid_shift (s : NominalChildGeometry) (e : AmplifierValuation)
    (lp σ supportError : ℝ)
    (hw : s.w = (e.multiplicity : ℝ) * lp)
    (hwo : s.wo = (e.movingMultiplicity : ℝ) * lp)
    (hg : s.g = max (s.shiftedCommon - s.c - 2 * s.w + s.wo) 0 + σ)
    (hc : 0 ≤ s.c) (hlp : 0 ≤ lp) (hpool : σ / 6 ≤ lp)
    (hD : -supportError ≤ s.shiftedCommon) (herr : 0 ≤ supportError) :
    s.paidShift ≤ 6 * (s.w + 0) + supportError := by
  have h := amplifier_error_capacity_shift e s.shiftedCommon s.c lp σ supportError
    hc hlp hpool hD herr
  simpa only [paidShift, hg, hw, hwo, add_zero] using h

theorem main_enlargement (s : NominalChildGeometry) (σ : ℝ) (hσ : 0 ≤ σ)
    (hw : s.w = 0) (hwo : s.wo = 0)
    (hg : s.g = max (s.shiftedCommon - s.c) 0 + 2 * σ) :
    s.enlargementJ + σ ≤ s.g := by
  have hm := le_max_left (s.shiftedCommon - s.c) 0
  dsimp only [enlargementJ]
  rw [hw, hwo, hg]
  linarith

theorem error_enlargement (s : NominalChildGeometry) (σ : ℝ)
    (hg : s.g = max s.enlargementJ 0 + σ) :
    s.enlargementJ + σ ≤ s.g := by
  have hm := le_max_left s.enlargementJ 0
  linarith

end NominalChildGeometry

/-- Derive the positive-part defect after all reductions and boundary errors.
`zBefore` is the slot length before the final divisor allocation; `a.z`
is the actual live length afterwards. -/
theorem child_capacity_from_allocation (s : NominalChildGeometry) (a : RealParameters)
    (zBefore reduction ell supportError clipError widthError : ℝ)
    (hκ : 0 ≤ a.κ) (hlive : a.z ≤ zBefore)
    (hred : zBefore - a.z ≤ reduction)
    (hparent : s.A + (6 * a.κ - 1) * zBefore ≤ s.parentWidth)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : s.paidShift ≤ 6 * (s.w + ell) + supportError)
    (hclip : a.n₁ + a.n₂ + a.z ≤ s.rawDegree - reduction + clipError)
    (hwidth : s.nominalWidth - (a.m + a.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (s.w + ell) + supportError + clipError + widthError) :
    max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤
      6 * (s.w + ell) + supportError + clipError + widthError := by
  have hs := s.raw_shift_le ell supportError hcommon hpaid
  have h := allocated_capacity_defect s.A s.parentWidth s.nominalWidth
    (a.m + a.q + widthError) s.rawDegree
    (a.n₁ + a.n₂ + a.z + widthError) zBefore a.z reduction a.κ
    s.w ell supportError (clipError + widthError) hκ hlive hred hparent hs
    (by linarith) (by linarith) (by linarith)
  have he : a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q) =
      (a.n₁ + a.n₂ + a.z + widthError) - (a.m + a.q + widthError) +
        (6 * a.κ - 1) * a.z := by ring
  rw [he]
  convert h using 1 <;> ring

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Keeping all actual slots preserves the parameters. -/
theorem remainingParameters_univ (d : MomentData K ω ψ) (a : RealParameters)
    (hz : a.z = d.geometry.totalLength) :
    remainingParameters d a Finset.univ = a := by
  have he : (d.geometry.restrictSlots Finset.univ).totalLength = a.z := by
    rw [SlotGeometry.totalLength_restrictSlots]
    exact hz.symm
  unfold remainingParameters
  rw [he]

/-- Reindexing all slots leaves the actual paired energy unchanged. -/
theorem pairedEnergy_restrictSlots_univ (d : MomentData K ω ψ) (a : RealParameters)
    (Z t : ℝ) :
    pairedEnergy (d.restrictSlots Finset.univ) a Z t = pairedEnergy d a Z t := by
  rw [pairedEnergy_restrictSlots]
  rfl

theorem totalLength_eq_zero_of_no_slots (g : SlotGeometry K) (hslots : g.slotCount = 0) :
    g.totalLength = 0 := by
  unfold SlotGeometry.totalLength
  apply Finset.sum_eq_zero
  intro i hi
  have := i.isLt
  exfalso
  omega

/-- One capacity procedure with an unrestricted zero-slot exit.
The nonnegative charge is only an exponent budget, not a capacity condition.
When no slot exists, the proof uses the identity for the original energy;
there is no restriction on either plain length. -/
theorem actual_paired_capacity_step_or_zero (d : MomentData K ω ψ) (a : RealParameters)
    (mesh Δ err : ℝ) (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : d.geometry.fitsMesh mesh) (hz : a.z = d.geometry.totalLength)
    (principal_mem_theta : ∀ u : NonzeroIdeal K,
      d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta)
    (hcharge : 0 ≤ Δ + err / 6 + a.κ * mesh)
    (hstep : d.geometry.slotCount = 0 ∨
      max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤ 6 * Δ + err) :
    ∃ removed : Finset (Fin d.geometry.slotCount),
      let keep := Finset.univ \ removed
      let a' := remainingParameters d a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin d.geometry.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows d a Z, ∀ i,
          ‖primePolynomial d i u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * (d.geometry.slots i).length)) →
        pairedEnergy d a Z t ≤
          (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
            pairedEnergy (d.restrictSlots keep) a' Z t := by
  rcases hstep with hzero | hdefect
  · refine ⟨∅, ?_⟩
    simp only [Finset.sdiff_empty, remainingParameters_univ d a hz]
    constructor
    · left
      exact hz.trans (totalLength_eq_zero_of_no_slots d.geometry hzero)
    · intro Z hZ C hC t hprime
      simp only [Finset.prod_empty, one_mul, pairedEnergy_restrictSlots_univ]
      have hE : 0 ≤ pairedEnergy d a Z t :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hpow : 1 ≤ Z ^ (Δ + err / 6 + a.κ * mesh) :=
        Real.one_le_rpow hZ hcharge
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hE
  · exact actual_paired_capacity_step d a mesh Δ err hκ hmesh hfit hz
      principal_mem_theta hdefect

/-- The actual child-energy step with its capacity defect derived from the
length ledger.  The scalar `hpaid` is supplied by `main_paid_shift` or
`error_paid_shift`, with no analytic recurrence assumption. -/
theorem paired_child_step_of_allocation (dChild : MomentData K ω ψ) (a : RealParameters)
    (s : NominalChildGeometry)
    (zBefore reduction b₂ p₂ B ell σ δ mesh supportError clipError widthError : ℝ)
    (hσ : 0 < σ) (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : dChild.geometry.fitsMesh mesh) (hz : a.z = dChild.geometry.totalLength)
    (hprincipal : ∀ u : NonzeroIdeal K,
      dChild.plainBackground * dChild.rowCharacter u = 1 →
        dChild.rowCharacter u ∈ dChild.theta)
    (henlarge : s.enlargementJ + σ ≤ s.g) (hunit : s.t₂ ≤ s.g₂)
    (hactual : a.m + a.q ≤ s.nominalWidth + δ) (hδ : δ ≤ σ / 2)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B)
    (hlive : a.z ≤ zBefore) (hred : zBefore - a.z ≤ reduction)
    (hparent : dChild.geometry.slotCount = 0 ∨
      s.A + (6 * a.κ - 1) * zBefore ≤ s.parentWidth)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : dChild.geometry.slotCount = 0 ∨
      s.paidShift ≤ 6 * (s.w + ell) + supportError)
    (hclip : a.n₁ + a.n₂ + a.z ≤ s.rawDegree - reduction + clipError)
    (hwidth : s.nominalWidth - (a.m + a.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (s.w + ell) + supportError + clipError + widthError)
    (hcharge : 0 ≤ (b₂ - p₂ + s.w + B + ell) +
      (supportError + clipError + widthError) / 6 + a.κ * mesh) :
    a.m + a.q ≤ s.parentWidth - σ / 2 ∧ a.m + a.q < s.parentWidth ∧
    ∃ removed : Finset (Fin dChild.geometry.slotCount),
      let keep := Finset.univ \ removed
      let a' := remainingParameters dChild a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin dChild.geometry.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows dChild a Z, ∀ i,
          ‖primePolynomial dChild i u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * (dChild.geometry.slots i).length)) →
        pairedEnergy dChild a Z t ≤
          (∏ i ∈ removed, C i) *
            Z ^ ((b₂ - p₂ + s.w + B + ell) +
              (supportError + clipError + widthError) / 6 + a.κ * mesh) *
              pairedEnergy (dChild.restrictSlots keep) a' Z t := by
  have hw := s.width_identity
  have hdrop : a.m + a.q ≤ s.parentWidth - σ / 2 := by linarith
  refine ⟨hdrop, by linarith, ?_⟩
  apply actual_paired_capacity_step_or_zero dChild a mesh (b₂ - p₂ + s.w + B + ell)
    (supportError + clipError + widthError) hκ hmesh hfit hz hprincipal hcharge
  by_cases hzero : dChild.geometry.slotCount = 0
  · exact Or.inl hzero
  · right
    have hparent := hparent.resolve_left hzero
    have hpaid := hpaid.resolve_left hzero
    have hc := child_capacity_from_allocation s a zBefore reduction ell supportError
      clipError widthError hκ.le hlive hred hparent hcommon hpaid hclip hwidth hbudget
    have hallow := child_allowance_lower b₂ p₂ s.w B ell hbp hB
    linarith

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.comparison_capacity_margin
#print axioms HeckeSkeleton.Moments.EngineStep.child_capacity_from_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.actual_paired_capacity_step_or_zero
#print axioms HeckeSkeleton.Moments.EngineStep.paired_child_step_of_allocation
