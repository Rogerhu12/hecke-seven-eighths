import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildProvider

/-!
# One actual allocated child family with one fixed capacity choice

The branch is discarded if its actual source energy vanishes everywhere.
Otherwise a true nonzero row gives nonnegative width and the original
annulus gives the clipping cost.  The actual plain profiles are clipped,
then one length-based deletion is selected for the whole Fourier family.
The output is the literal restricted MomentData, with actual slot count,
length sum, kappa, theta membership, and the strict width decrease.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

namespace ActualAllocatedSource

def beforeLength (s : ActualAllocatedSource A V H k) : ℝ := ∑ i, s.length i

def allocatedLength (s : ActualAllocatedSource A V H k) : ℝ :=
  ∑ i ∈ Finset.univ \ s.allocation.keep, s.length i

namespace Calibration

variable {s : ActualAllocatedSource A V H k} (D : s.Calibration (σ := σ) ω ψ)

theorem slot_sum_original : D.parameters.z = ∑ i ∈ s.allocation.keep, s.length i := by
  rw [D.slot_sum]
  exact selectedSlots_sum s.allocation.keep s.length

theorem live_length_le : D.parameters.z ≤ s.beforeLength := by
  rw [D.slot_sum_original]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s.allocation.keep)
    (fun i _ _ => (s.length_pos i).le)

theorem actual_length_reduction : s.beforeLength - D.parameters.z = s.allocatedLength := by
  rw [D.slot_sum_original]
  have hsum := Finset.sum_sdiff (Finset.subset_univ s.allocation.keep) (f := s.length)
  change (∑ i, s.length i) - (∑ i ∈ s.allocation.keep, s.length i) =
    ∑ i ∈ Finset.univ \ s.allocation.keep, s.length i
  linarith

private theorem cast_lengthSlot (d : MomentData F ω ψ) (n : ℕ)
    (hc : d.geometry.slotCount = n) (i : Fin n) :
    Fin.cast hc (lengthSlot d n hc i) = i := by
  subst n
  rfl

theorem clipped_lengths (ξ : V) (i : Fin s.allocation.keep.card) :
    ((D.clippedData ξ).geometry.slots
      (lengthSlot (D.clippedData ξ) s.allocation.keep.card (D.count ξ) i)).length =
        s.childLength i := by
  have hh := D.lengths ξ (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i)
  rw [cast_lengthSlot] at hh
  exact hh

def restrictedClippedData (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    MomentData F ω ψ :=
  (D.clippedData ξ).restrictSlots
    (lengthSelection (D.clippedData ξ) s.allocation.keep.card (D.count ξ) keep)

def restrictedParameters (keep : Finset (Fin s.allocation.keep.card)) : RealParameters :=
  lengthRemainingParameters s.childLength D.clippedParameters keep

theorem restricted_count (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    (D.restrictedClippedData keep ξ).geometry.slotCount = keep.card :=
  length_restrictSlots_count (D.clippedData ξ) _ (D.count ξ) keep

theorem restricted_z (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    (D.restrictedParameters keep).z = (D.restrictedClippedData keep ξ).geometry.totalLength :=
  (length_restrictSlots_length (D.clippedData ξ) _ (D.count ξ) s.childLength
    (D.clipped_lengths ξ) keep).symm

theorem restricted_z_nonneg (keep : Finset (Fin s.allocation.keep.card)) :
    0 ≤ (D.restrictedParameters keep).z := by
  change 0 ≤ ∑ i ∈ keep, s.childLength i
  exact Finset.sum_nonneg fun i _ => (s.length_pos _).le

theorem restricted_z_le (keep : Finset (Fin s.allocation.keep.card)) :
    (D.restrictedParameters keep).z ≤ D.parameters.z := by
  rw [D.slot_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keep)
    (fun i _ _ => (s.length_pos _).le)

theorem restricted_count_le (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    (D.restrictedClippedData keep ξ).geometry.slotCount ≤ k := by
  rw [D.restricted_count]
  have hc : keep.card ≤ s.allocation.keep.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ keep)
  exact hc.trans s.allocation.keep_card_le

theorem restricted_slot_in_theta (keep : Finset (Fin s.allocation.keep.card)) (ξ : V)
    (i : Fin (D.restrictedClippedData keep ξ).geometry.slotCount) :
    (D.restrictedClippedData keep ξ).slotCoefficient i ∈
      (D.restrictedClippedData keep ξ).theta :=
  D.slot_in_theta ξ (selectedSlotIndex
    (lengthSelection (D.clippedData ξ) s.allocation.keep.card (D.count ξ) keep) i)

theorem restricted_mesh (keep : Finset (Fin s.allocation.keep.card)) (ξ : V)
    (mesh : ℝ) (hfit : ∀ i, s.length i ≤ mesh) :
    (D.restrictedClippedData keep ξ).geometry.fitsMesh mesh := by
  apply actual_restriction_mesh
  intro i
  exact (D.lengths ξ i).le.trans (hfit _)

theorem restricted_zero_inherited (keep : Finset (Fin s.allocation.keep.card))
    (hzero : s.beforeLength = 0) :
    (D.restrictedParameters keep).z = 0 ∧
      ∀ ξ, (D.restrictedClippedData keep ξ).geometry.slotCount = 0 := by
  have hnonneg : 0 ≤ D.parameters.z := by
    rw [D.slot_sum]
    exact Finset.sum_nonneg (fun i _ => (s.length_pos _).le)
  have hz : D.parameters.z = 0 := le_antisymm
    (by simpa only [hzero] using D.live_length_le) hnonneg
  have hz' : (D.restrictedParameters keep).z = 0 := le_antisymm
    (by simpa only [hz] using D.restricted_z_le keep) (D.restricted_z_nonneg keep)
  refine ⟨hz', ?_⟩
  intro ξ
  exact actual_slotCount_zero_of_totalLength_zero _ ((D.restricted_z keep ξ).symm.trans hz')

/-- The primitive geometric data are the parent capacity and the actual
nominal-child ledger.  The clipping cost is proved from the source, the
allocated length reduction is computed, and the final energy inequality
is obtained internally from the actual child term dictionaries. -/
theorem zero_or_capacity_provider
    (skeleton : NominalChildGeometry)
    (b₂ p₂ boundary ell gap δ mesh supportError rawClipError widthError : ℝ)
    (leftAnnulus rightAnnulus : ℝ)
    (hleftAnnulus : 1 ≤ leftAnnulus) (hrightAnnulus : 1 ≤ rightAnnulus)
    (hleft : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
      (D.data ξ).plainTest₁.profile u (D.height ξ) x ≠ 0 → x ≤ leftAnnulus)
    (hright : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, ∀ x,
      (D.data ξ).plainTest₂.profile u (D.height ξ) x ≠ 0 → x ≤ rightAnnulus)
    (hgap : 0 < gap) (hκ : 0 < D.parameters.κ) (hmesh : 0 ≤ mesh)
    (hfit : ∀ i, s.length i ≤ mesh)
    (henlarge : skeleton.enlargementJ + gap ≤ skeleton.g)
    (hunit : skeleton.t₂ ≤ skeleton.g₂)
    (hactual : D.parameters.m + D.parameters.q ≤ skeleton.nominalWidth + δ)
    (hδ : δ ≤ gap / 2) (hbp : p₂ ≤ b₂) (hboundary : 0 ≤ boundary)
    (hparent : s.allocation.keep.card = 0 ∨
      skeleton.A + (6 * D.parameters.κ - 1) * s.beforeLength ≤ skeleton.parentWidth)
    (hcommon : skeleton.g₂ - skeleton.t₂ ≤ skeleton.c₂)
    (hpaid : s.allocation.keep.card = 0 ∨
      skeleton.paidShift ≤ 6 * (skeleton.w + ell) + supportError)
    (hraw : D.parameters.n₁ + D.parameters.n₂ + D.parameters.z ≤
      skeleton.rawDegree - s.allocatedLength + rawClipError)
    (hwidth : skeleton.nominalWidth - (D.parameters.m + D.parameters.q) ≤ widthError)
    (hbudget : 0 ≤ 6 * (skeleton.w + ell) + supportError + rawClipError + widthError)
    (hcharge : 0 ≤ (b₂ - p₂ + skeleton.w + boundary + ell) +
      (supportError + rawClipError + widthError) / 6 + D.parameters.κ * mesh)
    (primeBound : V → Fin s.allocation.keep.card → ℝ)
    (hprimeBound : ∀ ξ i, 0 ≤ primeBound ξ i)
    (hprime : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
      ∀ i : Fin s.allocation.keep.card,
      ‖primePolynomial (D.data ξ)
        (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i) u s.base (D.height ξ)‖ ^ 2 ≤
          primeBound ξ i * s.base ^ (D.parameters.κ * s.childLength i)) :
    (∀ ξ, s.energy (σ := σ) ξ = 0) ∨
      (0 ≤ D.parameters.m + D.parameters.q ∧
       D.parameters.m + D.parameters.q ≤ skeleton.parentWidth - gap / 2 ∧
       D.parameters.m + D.parameters.q < skeleton.parentWidth ∧
       ∃ removed : Finset (Fin s.allocation.keep.card),
        let keep := Finset.univ \ removed
        let a' := D.restrictedParameters keep
        0 ≤ a'.n₁ ∧ 0 ≤ a'.n₂ ∧ a'.κ = D.parameters.κ ∧
        a'.m + a'.q = D.parameters.m + D.parameters.q ∧
        0 ≤ a'.z ∧ a'.z ≤ D.parameters.z ∧
        (a'.z = 0 ∨ a'.n₁ + a'.n₂ + 6 * a'.κ * a'.z ≤ a'.m + a'.q) ∧
        (s.beforeLength = 0 → a'.z = 0) ∧
        ∀ ξ, (D.restrictedClippedData keep ξ).geometry.slotCount ≤ k ∧
          a'.z = (D.restrictedClippedData keep ξ).geometry.totalLength ∧
          (D.restrictedClippedData keep ξ).geometry.fitsMesh mesh ∧
          (∀ i, (D.restrictedClippedData keep ξ).slotCoefficient i ∈
            (D.restrictedClippedData keep ξ).theta) ∧
          s.energy (σ := σ) ξ ≤
            D.mass * ((∏ i ∈ removed, primeBound ξ i) *
              s.base ^ ((b₂ - p₂ + skeleton.w + boundary + ell) +
                (supportError + (rawClipError +
                  (Real.log leftAnnulus + Real.log rightAnnulus) / Real.log s.base) +
                    widthError) / 6 + D.parameters.κ * mesh)) *
              pairedEnergy (D.restrictedClippedData keep ξ) a' s.base (D.height ξ)) := by
  by_cases hzero : ∀ ξ, s.energy (σ := σ) ξ = 0
  · exact Or.inl hzero
  right
  obtain ⟨ξ₀, hnonzero⟩ := not_forall.mp hzero
  have hE : pairedEnergy (D.data ξ₀) D.parameters s.base (D.height ξ₀) ≠ 0 := by
    intro he
    have hb := D.energy_le ξ₀
    rw [he, mul_zero] at hb
    exact hnonzero (le_antisymm hb (s.energy_nonneg (σ := σ) ξ₀))
  let clipCost := (Real.log leftAnnulus + Real.log rightAnnulus) / Real.log s.base
  have hclipCost : 0 ≤ clipCost := div_nonneg
    (add_nonneg (Real.log_nonneg hleftAnnulus) (Real.log_nonneg hrightAnnulus))
    (Real.log_pos s.base_gt_one).le
  have hclip := paired_clipping_budget (D.data ξ₀) D.parameters s.base (D.height ξ₀)
    leftAnnulus rightAnnulus s.base_gt_one hleftAnnulus hrightAnnulus
    (hleft ξ₀) (hright ξ₀) hE
  have hclip' : D.clippedParameters.n₁ + D.clippedParameters.n₂ + D.clippedParameters.z ≤
      skeleton.rawDegree - s.allocatedLength + (rawClipError + clipCost) := by
    change (clipPlainParameters D.parameters).n₁ + (clipPlainParameters D.parameters).n₂ +
      D.parameters.z ≤ _
    change (clipPlainParameters D.parameters).n₁ + (clipPlainParameters D.parameters).n₂ -
      (D.parameters.n₁ + D.parameters.n₂) ≤ clipCost at hclip
    linarith
  have hbudget' : 0 ≤ 6 * (skeleton.w + ell) + supportError +
      (rawClipError + clipCost) + widthError := by linarith
  have hcharge' : 0 ≤ (b₂ - p₂ + skeleton.w + boundary + ell) +
      (supportError + (rawClipError + clipCost) + widthError) / 6 + D.clippedParameters.κ * mesh := by
    change 0 ≤ (b₂ - p₂ + skeleton.w + boundary + ell) +
      (supportError + (rawClipError + clipCost) + widthError) / 6 + D.parameters.κ * mesh
    linarith
  obtain ⟨hdrop, hstrict, removed, hcapacity, hbound⟩ :=
    uniform_length_child_capacity_of_allocation D.clippedData s.allocation.keep.card
      s.childLength D.count D.clipped_lengths D.clippedParameters skeleton
      s.beforeLength s.allocatedLength b₂ p₂ boundary ell gap δ mesh
      supportError (rawClipError + clipCost) widthError hgap hκ hmesh
      (fun i => (s.length_pos _).le) (fun i => hfit _) D.slot_sum
      D.principal_in_theta henlarge hunit hactual hδ hbp hboundary
      D.live_length_le D.actual_length_reduction.le hparent hcommon hpaid
      hclip' hwidth hbudget' hcharge'
  refine ⟨D.clipped_width_nonneg_of_source_nonzero ξ₀ hnonzero, hdrop, hstrict,
    removed, ?_⟩
  dsimp only
  let keep : Finset (Fin s.allocation.keep.card) := Finset.univ \ removed
  refine ⟨le_max_right _ _, le_max_right _ _, rfl, rfl,
    D.restricted_z_nonneg keep, D.restricted_z_le keep, hcapacity,
    fun hz => (D.restricted_zero_inherited keep hz).1, ?_⟩
  intro ξ
  refine ⟨D.restricted_count_le keep ξ, D.restricted_z keep ξ,
    D.restricted_mesh keep ξ mesh hfit, D.restricted_slot_in_theta keep ξ, ?_⟩
  have hc := hbound ξ s.base s.base_gt_one.le (primeBound ξ) (hprimeBound ξ) (D.height ξ) (hprime ξ)
  have hmul := mul_le_mul_of_nonneg_left hc D.mass_nonneg
  exact (D.energy_le_clipped ξ).trans (by
    simpa only [mul_assoc, clipCost, restrictedClippedData, restrictedParameters,
      clippedParameters, clipPlainParameters] using hmul)

end Calibration
end ActualAllocatedSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.zero_or_capacity_provider
