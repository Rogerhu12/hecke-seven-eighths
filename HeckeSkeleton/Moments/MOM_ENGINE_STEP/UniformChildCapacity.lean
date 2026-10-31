import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DerivedCapacity

/-!
# One geometric capacity choice for the entire Fourier family

The removal is selected from the fixed slot geometry before the Fourier
parameter, scale, polynomial constants, or twist.  Only the actual
profiles and coefficients in `MomentData` may vary with that parameter.
Dependent slot indices are transported along the stated geometry equality;
the child remains the repository's literal `MomentData.restrictSlots`.

The capacity defect is derived from the original parent and nominal-child
ledger.  The geometric greedy step is invoked once, and its universal
product estimate is then applied to every member of the family.  The
zero-slot branch remains unrestricted in the two plain lengths.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- A fixed slot, viewed in the actual data with that same geometry. -/
def geometrySlot (d : MomentData K ω ψ) (g : SlotGeometry K)
    (hgeometry : d.geometry = g) (i : Fin g.slotCount) : Fin d.geometry.slotCount :=
  cast (congrArg (fun g : SlotGeometry K => Fin g.slotCount) hgeometry.symm) i

/-- A single fixed selection transported to the actual slot indices. -/
def geometrySelection (d : MomentData K ω ψ) (g : SlotGeometry K)
    (hgeometry : d.geometry = g) (keep : Finset (Fin g.slotCount)) :
    Finset (Fin d.geometry.slotCount) :=
  cast (congrArg (fun g : SlotGeometry K => Finset (Fin g.slotCount)) hgeometry.symm) keep

/-- These successor parameters depend only on the fixed geometry. -/
def geometryRemainingParameters (g : SlotGeometry K) (a : RealParameters)
    (keep : Finset (Fin g.slotCount)) : RealParameters :=
  { a with z := (g.restrictSlots keep).totalLength }

theorem geometry_remainingParameters_eq (d : MomentData K ω ψ)
    (g : SlotGeometry K) (hgeometry : d.geometry = g) (a : RealParameters)
    (keep : Finset (Fin g.slotCount)) :
    remainingParameters d a (geometrySelection d g hgeometry keep) =
      geometryRemainingParameters g a keep := by
  subst g
  rfl

/-- After the uniform removal the actual children still have one common
geometry, so the same construction can be used at the next step. -/
theorem geometry_restrictSlots_eq (d : MomentData K ω ψ)
    (g : SlotGeometry K) (hgeometry : d.geometry = g)
    (keep : Finset (Fin g.slotCount)) :
    (d.restrictSlots (geometrySelection d g hgeometry keep)).geometry =
      g.restrictSlots keep := by
  subst g
  rfl

/-- Choose the slots once from geometry.  The resulting energy estimate
works for every actual `MomentData` with this geometry, including an
infinite Fourier-indexed family, without a pointwise existential choice. -/
theorem geometry_uniform_capacity_step
    (g : SlotGeometry K) (a : RealParameters) (mesh Δ err : ℝ)
    (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : g.fitsMesh mesh) (hz : a.z = g.totalLength)
    (hdefect : max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤
      6 * Δ + err) :
    ∃ removed : Finset (Fin g.slotCount),
      let keep := Finset.univ \ removed
      let a' := geometryRemainingParameters g a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ (d : MomentData K ω ψ) (hgeometry : d.geometry = g),
        (∀ u : NonzeroIdeal K,
          d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta) →
        ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin g.slotCount → ℝ,
          (∀ i, 0 ≤ C i) → ∀ t : ℝ,
          (∀ u ∈ pairedRows d a Z, ∀ i : Fin g.slotCount,
            ‖primePolynomial d (geometrySlot d g hgeometry i) u Z t‖ ^ 2 ≤
              C i * Z ^ (a.κ * (g.slots i).length)) →
          pairedEnergy d a Z t ≤
            (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
              pairedEnergy (d.restrictSlots (geometrySelection d g hgeometry keep))
                a' Z t := by
  have hdefect' : capacityDefect Finset.univ (fun i => (g.slots i).length)
      a.n₁ a.n₂ (a.m + a.q) a.κ ≤ 6 * Δ + err := by
    simpa only [capacityDefect, hz, SlotGeometry.totalLength] using hdefect
  obtain ⟨removed, hR, hcap, hbound⟩ := capacity_energy_step
    (H := NonzeroIdeal K) Finset.univ (fun i => (g.slots i).length)
    a.n₁ a.n₂ (a.m + a.q) a.κ mesh Δ err hκ hmesh
    (fun i _ => (g.slots i).length_pos.le) (fun i _ => hfit i) hdefect'
  refine ⟨removed, ?_⟩
  dsimp only
  constructor
  · rcases hcap with hall | hcapacity
    · left
      simp only [hall, Finset.sdiff_self, geometryRemainingParameters,
        SlotGeometry.totalLength_restrictSlots, Finset.sum_empty]
    · right
      simpa only [geometryRemainingParameters, SlotGeometry.totalLength_restrictSlots]
        using hcapacity
  · intro d hgeometry hprincipal Z hZ C hC t hprime
    subst g
    dsimp only [geometrySlot, geometrySelection] at hprime ⊢
    let keep := Finset.univ \ removed
    let a' := remainingParameters d a keep
    let f : NonzeroIdeal K → ℝ := fun u =>
      ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
        plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t *
        ∏ i ∈ keep, primePolynomial d i u Z t‖ ^ 2
    have hb := hbound Z hZ C (fun i _ => hC i) (pairedRows d a Z)
      (fun u i => primePolynomial d i u Z t)
      (fun u => plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t)
      (fun u => plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t)
      (fun _ => 1) (fun _ _ => zero_le_one) (fun u hu i _ => hprime u hu i)
    simp only [one_mul] at hb
    have hs : (∑ u ∈ pairedRows d a Z, f u) ≤
        ∑ u ∈ pairedRows (d.restrictSlots keep) a' Z, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (pairedRows_subset_after_removal d a keep hz hprincipal Z)
        (fun _ _ _ => sq_nonneg _)
    have hchild : (∑ u ∈ pairedRows (d.restrictSlots keep) a' Z, f u) =
        pairedEnergy (d.restrictSlots keep) a' Z t := by
      symm
      rw [pairedEnergy_restrictSlots]
      rfl
    rw [hchild] at hs
    have hfactor : 0 ≤ (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) :=
      mul_nonneg (Finset.prod_nonneg (fun i _ => hC i))
        (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    exact hb.trans (mul_le_mul_of_nonneg_left hs hfactor)

/-- The same uniform choice has an unrestricted zero-slot exit. -/
theorem geometry_uniform_capacity_step_or_zero
    (g : SlotGeometry K) (a : RealParameters) (mesh Δ err : ℝ)
    (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : g.fitsMesh mesh) (hz : a.z = g.totalLength)
    (hcharge : 0 ≤ Δ + err / 6 + a.κ * mesh)
    (hstep : g.slotCount = 0 ∨
      max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤ 6 * Δ + err) :
    ∃ removed : Finset (Fin g.slotCount),
      let keep := Finset.univ \ removed
      let a' := geometryRemainingParameters g a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ (d : MomentData K ω ψ) (hgeometry : d.geometry = g),
        (∀ u : NonzeroIdeal K,
          d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta) →
        ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin g.slotCount → ℝ,
          (∀ i, 0 ≤ C i) → ∀ t : ℝ,
          (∀ u ∈ pairedRows d a Z, ∀ i : Fin g.slotCount,
            ‖primePolynomial d (geometrySlot d g hgeometry i) u Z t‖ ^ 2 ≤
              C i * Z ^ (a.κ * (g.slots i).length)) →
          pairedEnergy d a Z t ≤
            (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
              pairedEnergy (d.restrictSlots (geometrySelection d g hgeometry keep))
                a' Z t := by
  rcases hstep with hzero | hdefect
  · refine ⟨∅, ?_⟩
    simp only [Finset.sdiff_empty]
    constructor
    · left
      change (g.restrictSlots Finset.univ).totalLength = 0
      rw [SlotGeometry.totalLength_restrictSlots]
      exact totalLength_eq_zero_of_no_slots g hzero
    · intro d hgeometry hprincipal Z hZ C hC t hprime
      subst g
      have ha : geometryRemainingParameters d.geometry a Finset.univ = a :=
        remainingParameters_univ d a hz
      simp only [geometrySelection, ha, Finset.prod_empty, one_mul,
        pairedEnergy_restrictSlots_univ]
      have hE : 0 ≤ pairedEnergy d a Z t :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hpow : 1 ≤ Z ^ (Δ + err / 6 + a.κ * mesh) :=
        Real.one_le_rpow hZ hcharge
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hE
  · exact geometry_uniform_capacity_step g a mesh Δ err hκ hmesh hfit hz hdefect

/-- Uniform capacity repair for all actual Fourier children, with the
defect derived from the original parent and nominal length ledger.
`removed` and the successor parameters are chosen before `ξ`, `Z`, `C`,
and `t`.  The width falls by at least `σ / 2` for the entire family. -/
theorem uniform_child_capacity_of_allocation {V : Type*}
    (D : V → MomentData K ω ψ) (g : SlotGeometry K)
    (hgeometry : ∀ ξ : V, (D ξ).geometry = g)
    (a : RealParameters) (s : NominalChildGeometry)
    (zBefore reduction b₂ p₂ B ell σ δ mesh supportError clipError widthError : ℝ)
    (hσ : 0 < σ) (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : g.fitsMesh mesh) (hz : a.z = g.totalLength)
    (hprincipal : ∀ ξ : V, ∀ u : NonzeroIdeal K,
      (D ξ).plainBackground * (D ξ).rowCharacter u = 1 →
        (D ξ).rowCharacter u ∈ (D ξ).theta)
    (henlarge : s.enlargementJ + σ ≤ s.g) (hunit : s.t₂ ≤ s.g₂)
    (hactual : a.m + a.q ≤ s.nominalWidth + δ) (hδ : δ ≤ σ / 2)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B)
    (hlive : a.z ≤ zBefore) (hred : zBefore - a.z ≤ reduction)
    (hparent : g.slotCount = 0 ∨
      s.A + (6 * a.κ - 1) * zBefore ≤ s.parentWidth)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : g.slotCount = 0 ∨
      s.paidShift ≤ 6 * (s.w + ell) + supportError)
    (hclip : a.n₁ + a.n₂ + a.z ≤ s.rawDegree - reduction + clipError)
    (hwidth : s.nominalWidth - (a.m + a.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (s.w + ell) + supportError + clipError + widthError)
    (hcharge : 0 ≤ (b₂ - p₂ + s.w + B + ell) +
      (supportError + clipError + widthError) / 6 + a.κ * mesh) :
    a.m + a.q ≤ s.parentWidth - σ / 2 ∧ a.m + a.q < s.parentWidth ∧
    ∃ removed : Finset (Fin g.slotCount),
      let keep := Finset.univ \ removed
      let a' := geometryRemainingParameters g a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ ξ : V, ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin g.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows (D ξ) a Z, ∀ i : Fin g.slotCount,
          ‖primePolynomial (D ξ) (geometrySlot (D ξ) g (hgeometry ξ) i) u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * (g.slots i).length)) →
        pairedEnergy (D ξ) a Z t ≤
          (∏ i ∈ removed, C i) *
            Z ^ ((b₂ - p₂ + s.w + B + ell) +
              (supportError + clipError + widthError) / 6 + a.κ * mesh) *
            pairedEnergy
              ((D ξ).restrictSlots (geometrySelection (D ξ) g (hgeometry ξ) keep))
              a' Z t := by
  have hw := s.width_identity
  have hdrop : a.m + a.q ≤ s.parentWidth - σ / 2 := by linarith
  have hstep : g.slotCount = 0 ∨
      max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤
        6 * (b₂ - p₂ + s.w + B + ell) + (supportError + clipError + widthError) := by
    by_cases hzero : g.slotCount = 0
    · exact Or.inl hzero
    · right
      have hparent' := hparent.resolve_left hzero
      have hpaid' := hpaid.resolve_left hzero
      have hc := child_capacity_from_allocation s a zBefore reduction ell supportError
        clipError widthError hκ.le hlive hred hparent' hcommon hpaid' hclip hwidth hbudget
      have hallow := child_allowance_lower b₂ p₂ s.w B ell hbp hB
      linarith
  obtain ⟨removed, hcap, hbound⟩ := geometry_uniform_capacity_step_or_zero
    (ω := ω) (ψ := ψ) g a mesh (b₂ - p₂ + s.w + B + ell)
    (supportError + clipError + widthError) hκ hmesh hfit hz hcharge hstep
  refine ⟨hdrop, by linarith, removed, hcap, ?_⟩
  intro ξ
  exact hbound (D ξ) (hgeometry ξ) (hprincipal ξ)

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.geometry_uniform_capacity_step
#print axioms HeckeSkeleton.Moments.EngineStep.geometry_uniform_capacity_step_or_zero
#print axioms HeckeSkeleton.Moments.EngineStep.uniform_child_capacity_of_allocation
