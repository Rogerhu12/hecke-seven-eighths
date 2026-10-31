import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DerivedCapacity

/-!
# Uniform capacity removal from slot lengths alone

The fixed data are the number of slots and their real lengths.  A Fourier
parameter may change every prime window profile, its exact support, and
the slot coefficient character.  No equality of `SlotGeometry` is required.

The greedy choice is made once from the lengths, before the actual
`MomentData`, Fourier parameter, scale, constants, and twist.  Every child
is the literal `MomentData.restrictSlots` of that member of the family.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Transport only a slot index; no prime-window data are identified. -/
def lengthSlot (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (i : Fin n) : Fin d.geometry.slotCount :=
  cast (congrArg Fin hcount.symm) i

/-- Transport the one fixed selection using only the slot count. -/
def lengthSelection (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (keep : Finset (Fin n)) :
    Finset (Fin d.geometry.slotCount) :=
  cast (congrArg (fun k : ℕ => Finset (Fin k)) hcount.symm) keep

theorem length_selection_univ (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) :
    lengthSelection d n hcount Finset.univ = Finset.univ := by
  subst n
  rfl

/-- Successor parameters refer only to the fixed length array. -/
def lengthRemainingParameters {n : ℕ} (L : Fin n → ℝ) (a : RealParameters)
    (keep : Finset (Fin n)) : RealParameters :=
  { a with z := ∑ i ∈ keep, L i }

theorem length_totalLength_eq (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (L : Fin n → ℝ)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i) :
    d.geometry.totalLength = ∑ i, L i := by
  subst n
  dsimp only [lengthSlot] at hlength
  unfold SlotGeometry.totalLength
  exact Finset.sum_congr rfl (fun i _ => hlength i)

theorem length_remainingParameters_eq (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (L : Fin n → ℝ)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i)
    (a : RealParameters) (keep : Finset (Fin n)) :
    remainingParameters d a (lengthSelection d n hcount keep) =
      lengthRemainingParameters L a keep := by
  subst n
  change ∀ i, (d.geometry.slots i).length = L i at hlength
  change remainingParameters d a keep = lengthRemainingParameters L a keep
  have hs : (d.geometry.restrictSlots keep).totalLength = ∑ i ∈ keep, L i := by
    rw [SlotGeometry.totalLength_restrictSlots]
    exact Finset.sum_congr rfl (fun i _ => hlength i)
  simp only [remainingParameters, lengthRemainingParameters, hs]

/-- The same fixed lengths after removal describe the actual children;
the prime profiles may still depend on all Fourier parameters. -/
theorem length_restrictSlots_length (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (L : Fin n → ℝ)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i)
    (keep : Finset (Fin n)) :
    ((d.restrictSlots (lengthSelection d n hcount keep)).geometry).totalLength =
      ∑ i ∈ keep, L i := by
  subst n
  change ∀ i, (d.geometry.slots i).length = L i at hlength
  change (d.geometry.restrictSlots keep).totalLength = ∑ i ∈ keep, L i
  rw [SlotGeometry.totalLength_restrictSlots]
  exact Finset.sum_congr rfl (fun i _ => hlength i)

theorem length_restrictSlots_count (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (keep : Finset (Fin n)) :
    (d.restrictSlots (lengthSelection d n hcount keep)).geometry.slotCount = keep.card := by
  subst n
  rfl

/-- The next family has the same retained length array, even when the
prime profiles of its members differ. -/
theorem length_restrictSlots_each (d : MomentData K ω ψ) (n : ℕ)
    (hcount : d.geometry.slotCount = n) (L : Fin n → ℝ)
    (hlength : ∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i)
    (keep : Finset (Fin n)) (j : Fin keep.card) :
    ((d.restrictSlots (lengthSelection d n hcount keep)).geometry.slots
      (lengthSlot (d.restrictSlots (lengthSelection d n hcount keep)) keep.card
        (length_restrictSlots_count d n hcount keep) j)).length =
      L (selectedSlotIndex keep j) := by
  subst n
  dsimp only [lengthSlot, lengthSelection] at hlength ⊢
  exact hlength (selectedSlotIndex keep j)

/-- One removal works for every actual family member having the fixed
slot count and lengths.  The pointwise prime bounds are the only
polynomial-size inputs. -/
theorem length_uniform_capacity_step
    (n : ℕ) (L : Fin n → ℝ) (a : RealParameters) (mesh Δ err : ℝ)
    (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hL : ∀ i, 0 ≤ L i) (hfit : ∀ i, L i ≤ mesh)
    (hz : a.z = ∑ i, L i)
    (hdefect : max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤
      6 * Δ + err) :
    ∃ removed : Finset (Fin n),
      let keep := Finset.univ \ removed
      let a' := lengthRemainingParameters L a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ (d : MomentData K ω ψ) (hcount : d.geometry.slotCount = n),
        (∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i) →
        (∀ u : NonzeroIdeal K,
          d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta) →
        ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin n → ℝ,
          (∀ i, 0 ≤ C i) → ∀ t : ℝ,
          (∀ u ∈ pairedRows d a Z, ∀ i : Fin n,
            ‖primePolynomial d (lengthSlot d n hcount i) u Z t‖ ^ 2 ≤
              C i * Z ^ (a.κ * L i)) →
          pairedEnergy d a Z t ≤
            (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
              pairedEnergy (d.restrictSlots (lengthSelection d n hcount keep))
                a' Z t := by
  have hdefect' : capacityDefect Finset.univ L
      a.n₁ a.n₂ (a.m + a.q) a.κ ≤ 6 * Δ + err := by
    simpa only [capacityDefect, hz] using hdefect
  obtain ⟨removed, hR, hcap, hbound⟩ := capacity_energy_step
    (H := NonzeroIdeal K) Finset.univ L
    a.n₁ a.n₂ (a.m + a.q) a.κ mesh Δ err hκ hmesh
    (fun i _ => hL i) (fun i _ => hfit i) hdefect'
  refine ⟨removed, ?_⟩
  dsimp only
  constructor
  · rcases hcap with hall | hcapacity
    · left
      simp only [hall, Finset.sdiff_self, lengthRemainingParameters, Finset.sum_empty]
    · right
      exact hcapacity
  · intro d hcount hlength hprincipal Z hZ C hC t hprime
    subst n
    dsimp only [lengthSlot, lengthSelection] at hlength hprime ⊢
    have hz' : a.z = d.geometry.totalLength := by
      rw [hz, SlotGeometry.totalLength]
      exact Finset.sum_congr rfl (fun i _ => (hlength i).symm)
    let keep := Finset.univ \ removed
    let a' := lengthRemainingParameters L a keep
    have ha' : remainingParameters d a keep = a' := by
      have hs : (d.geometry.restrictSlots keep).totalLength = ∑ i ∈ keep, L i := by
        rw [SlotGeometry.totalLength_restrictSlots]
        exact Finset.sum_congr rfl (fun i _ => hlength i)
      simp only [remainingParameters, a', lengthRemainingParameters, hs]
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
    have hrows : pairedRows d a Z ⊆ pairedRows (d.restrictSlots keep) a' Z := by
      simpa only [ha'] using
        pairedRows_subset_after_removal d a keep hz' hprincipal Z
    have hs : (∑ u ∈ pairedRows d a Z, f u) ≤
        ∑ u ∈ pairedRows (d.restrictSlots keep) a' Z, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _ => sq_nonneg _)
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

/-- Zero slots retain the unrestricted two-plain-factor exit. -/
theorem length_uniform_capacity_step_or_zero
    (n : ℕ) (L : Fin n → ℝ) (a : RealParameters) (mesh Δ err : ℝ)
    (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hL : ∀ i, 0 ≤ L i) (hfit : ∀ i, L i ≤ mesh)
    (hz : a.z = ∑ i, L i)
    (hcharge : 0 ≤ Δ + err / 6 + a.κ * mesh)
    (hstep : n = 0 ∨
      max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤ 6 * Δ + err) :
    ∃ removed : Finset (Fin n),
      let keep := Finset.univ \ removed
      let a' := lengthRemainingParameters L a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ (d : MomentData K ω ψ) (hcount : d.geometry.slotCount = n),
        (∀ i, (d.geometry.slots (lengthSlot d n hcount i)).length = L i) →
        (∀ u : NonzeroIdeal K,
          d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta) →
        ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin n → ℝ,
          (∀ i, 0 ≤ C i) → ∀ t : ℝ,
          (∀ u ∈ pairedRows d a Z, ∀ i : Fin n,
            ‖primePolynomial d (lengthSlot d n hcount i) u Z t‖ ^ 2 ≤
              C i * Z ^ (a.κ * L i)) →
          pairedEnergy d a Z t ≤
            (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
              pairedEnergy (d.restrictSlots (lengthSelection d n hcount keep))
                a' Z t := by
  rcases hstep with hzero | hdefect
  · refine ⟨∅, ?_⟩
    simp only [Finset.sdiff_empty]
    constructor
    · left
      change (∑ i : Fin n, L i) = 0
      subst n
      exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
    · intro d hcount hlength hprincipal Z hZ C hC t hprime
      have ha : lengthRemainingParameters L a Finset.univ = a := by
        simp only [lengthRemainingParameters, ← hz]
      simp only [length_selection_univ, ha, Finset.prod_empty, one_mul,
        pairedEnergy_restrictSlots_univ]
      have hE : 0 ≤ pairedEnergy d a Z t :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hpow : 1 ≤ Z ^ (Δ + err / 6 + a.κ * mesh) :=
        Real.one_le_rpow hZ hcharge
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hE
  · exact length_uniform_capacity_step n L a mesh Δ err hκ hmesh hL hfit hz hdefect

/-- The original parent and nominal-child ledger give one length-based
capacity choice for the whole Fourier family.  Every profile and support
may vary, while the removed indices and successor parameters are fixed
before the family parameter and before `Z`, `C`, and `t`. -/
theorem uniform_length_child_capacity_of_allocation {V : Type*}
    (D : V → MomentData K ω ψ) (n : ℕ) (L : Fin n → ℝ)
    (hcount : ∀ ξ : V, (D ξ).geometry.slotCount = n)
    (hlength : ∀ ξ : V, ∀ i,
      ((D ξ).geometry.slots (lengthSlot (D ξ) n (hcount ξ) i)).length = L i)
    (a : RealParameters) (s : NominalChildGeometry)
    (zBefore reduction b₂ p₂ B ell σ δ mesh supportError clipError widthError : ℝ)
    (hσ : 0 < σ) (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hL : ∀ i, 0 ≤ L i) (hfit : ∀ i, L i ≤ mesh) (hz : a.z = ∑ i, L i)
    (hprincipal : ∀ ξ : V, ∀ u : NonzeroIdeal K,
      (D ξ).plainBackground * (D ξ).rowCharacter u = 1 →
        (D ξ).rowCharacter u ∈ (D ξ).theta)
    (henlarge : s.enlargementJ + σ ≤ s.g) (hunit : s.t₂ ≤ s.g₂)
    (hactual : a.m + a.q ≤ s.nominalWidth + δ) (hδ : δ ≤ σ / 2)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B)
    (hlive : a.z ≤ zBefore) (hred : zBefore - a.z ≤ reduction)
    (hparent : n = 0 ∨
      s.A + (6 * a.κ - 1) * zBefore ≤ s.parentWidth)
    (hcommon : s.g₂ - s.t₂ ≤ s.c₂)
    (hpaid : n = 0 ∨
      s.paidShift ≤ 6 * (s.w + ell) + supportError)
    (hclip : a.n₁ + a.n₂ + a.z ≤ s.rawDegree - reduction + clipError)
    (hwidth : s.nominalWidth - (a.m + a.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (s.w + ell) + supportError + clipError + widthError)
    (hcharge : 0 ≤ (b₂ - p₂ + s.w + B + ell) +
      (supportError + clipError + widthError) / 6 + a.κ * mesh) :
    a.m + a.q ≤ s.parentWidth - σ / 2 ∧ a.m + a.q < s.parentWidth ∧
    ∃ removed : Finset (Fin n),
      let keep := Finset.univ \ removed
      let a' := lengthRemainingParameters L a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ ξ : V, ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin n → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows (D ξ) a Z, ∀ i : Fin n,
          ‖primePolynomial (D ξ) (lengthSlot (D ξ) n (hcount ξ) i) u Z t‖ ^ 2 ≤
            C i * Z ^ (a.κ * L i)) →
        pairedEnergy (D ξ) a Z t ≤
          (∏ i ∈ removed, C i) *
            Z ^ ((b₂ - p₂ + s.w + B + ell) +
              (supportError + clipError + widthError) / 6 + a.κ * mesh) *
            pairedEnergy
              ((D ξ).restrictSlots (lengthSelection (D ξ) n (hcount ξ) keep))
              a' Z t := by
  have hw := s.width_identity
  have hdrop : a.m + a.q ≤ s.parentWidth - σ / 2 := by linarith
  have hstep : n = 0 ∨
      max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤
        6 * (b₂ - p₂ + s.w + B + ell) + (supportError + clipError + widthError) := by
    by_cases hzero : n = 0
    · exact Or.inl hzero
    · right
      have hparent' := hparent.resolve_left hzero
      have hpaid' := hpaid.resolve_left hzero
      have hc := child_capacity_from_allocation s a zBefore reduction ell supportError
        clipError widthError hκ.le hlive hred hparent' hcommon hpaid' hclip hwidth hbudget
      have hallow := child_allowance_lower b₂ p₂ s.w B ell hbp hB
      linarith
  obtain ⟨removed, hcap, hbound⟩ := length_uniform_capacity_step_or_zero
    (ω := ω) (ψ := ψ) n L a mesh (b₂ - p₂ + s.w + B + ell)
    (supportError + clipError + widthError) hκ hmesh hL hfit hz hcharge hstep
  refine ⟨hdrop, by linarith, removed, hcap, ?_⟩
  intro ξ
  exact hbound (D ξ) (hcount ξ) (hlength ξ) (hprincipal ξ)

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.length_uniform_capacity_step
#print axioms HeckeSkeleton.Moments.EngineStep.length_uniform_capacity_step_or_zero
#print axioms HeckeSkeleton.Moments.EngineStep.uniform_length_child_capacity_of_allocation

