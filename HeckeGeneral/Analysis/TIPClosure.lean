import HeckeGeneral.Analysis.TIPAccounting

/-!
# T ∧ I ∧ P ⇒ 7/8 for one fixed infinity type, from the Euler-product bound

The closure of M Sections 4--7 along the direct route.  No separate `11/12`
theorem and no seed input are used: the common boundary of the family is at
most one by the Euler product.  For a common boundary `7/8 < B ≤ 1`, the
closure fixes the moment loss as a fixed fraction of the certificate margin,
takes P's mesh, chooses a fine even slot system, and only then the remaining
losses and each target with its representative.  The accounting of
`TIPAccounting` gives the power-height comparison with the pretarget saving;
the actual principal Mellin closure, whose principal correction is controlled
unconditionally by `PrincipalEulerFactor`, and the family supremum argument
conclude.

The hypotheses can hold only when `μ₁₂ ⊆ K` (see `TIPSources`); a general
field is reached through `K = F(ζ₁₂)` and abelian descent, which is not
constructed here (`HeckeFactorizationDescentData`).
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.TIP

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped BigOperators Topology Classical

variable {K : Type} [Field K] [NumberField K]

/-- The fixed certificate margin is positive. -/
private theorem certificateMargin_pos_closure : (0 : ℝ) < certificateMargin := by
  unfold certificateMargin
  norm_num

/-- The common saving against a boundary `B > 7/8` is positive. -/
private theorem tipFinalSaving_pos_closure (g : PrimeWindowGeometry) {B : ℝ}
    (hB : 7 / 8 < B) : 0 < tipFinalSaving g B := by
  unfold tipFinalSaving tipSaving
  exact lt_min
    (mul_pos (by norm_num) (lt_min certificateMargin_pos_closure (principalSlotSaving_pos g)))
    (by linarith)

/-- The common saving is strictly below half of the gap `B - 7/8`. -/
private theorem tipFinalSaving_lt_half_gap_closure (g : PrimeWindowGeometry) {B : ℝ}
    (hB : 7 / 8 < B) : tipFinalSaving g B < (B - 7 / 8) / 2 := by
  unfold tipFinalSaving
  exact (min_le_right _ _).trans_lt (by linarith)

/-- **T ∧ I ∧ P ⇒ 7/8** for every member of one fixed-type family. -/
theorem heckePacket_sevenEighths_of_TIP (ω : HeckeCharacter K) (hTIP : TIPInput K ω)
    (χ : HeckePacketIndex K ω) :
    MeromorphicZeroFreeOn (heckeContinuation K χ.val) (rightHalfPlane (7 / 8)) := by
  -- The family closure from the Euler-product bound, with representatives.
  refine heckePacket_sevenEighths_of_representativeComparisons ω ?_ χ
  intro B hB hB' hbound
  -- The moment loss, a fixed fraction of the certificate margin.
  have hlamA : (0 : ℝ) < min (1 / 1000) (certificateMargin / 40) :=
    lt_min (by norm_num) (div_pos certificateMargin_pos_closure (by norm_num))
  -- P's mesh.
  obtain ⟨mesh, hmesh, hsrc⟩ :=
    hTIP B hB hB' hbound (min (1 / 1000) (certificateMargin / 40)) hlamA (min_le_left _ _)
  -- A fine even slot system, chosen before the target.
  obtain ⟨g, hg⟩ := exists_primeWindowGeometry_fine (lt_min hmesh hlamA)
  have hfine : (1 / 3 : ℝ) / g.slots < min mesh (min (1 / 1000) (certificateMargin / 40)) := by
    have h : (1 / 3 : ℝ) / g.slots = 2 * (1 / 6 : ℝ) / g.slots := by ring
    rw [h]
    exact hg
  have hround₁ : (1 / 3 : ℝ) / g.slots ≤ mesh := hfine.le.trans (min_le_left _ _)
  have hround₂ : (1 / 3 : ℝ) / g.slots ≤ min (1 / 1000) (certificateMargin / 40) :=
    hfine.le.trans (min_le_right _ _)
  -- The common saving, then the remaining loss, and only then each target.
  have hσ := tipFinalSaving_pos_closure g hB
  refine ⟨tipFinalSaving g B, hσ, tipFinalSaving_lt_half_gap_closure g hB, ?_⟩
  intro ψ
  -- A representative with the same zero real parts, its data and the three sources.
  obtain ⟨ψ', hzeros, D, hT, hI, hP⟩ :=
    hsrc g hround₁ (tipFinalSaving g B / 2) (half_pos hσ) ψ
  -- The primitive principal part of T: the low estimate (6.9) is its last field.
  have hprin := hT.principal
  unfold ProbeMeasures.principalInput at hprin
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlow⟩ := hprin
  refine ⟨ψ', hzeros, D.S, D.probe, D.probeFunction ψ'.val, hlow, ?_⟩
  -- The accounting gives the power-height comparison with the common saving.
  exact powerHeightComparison_of_sources hB hB' hlamA (min_le_right _ _) hround₁ hround₂
    hT hI hP

/-- **T ∧ I ∧ P ⇒ 7/8** over one field, when the inputs hold for every family. -/
theorem heckeSevenEighths_of_TIP (hTIP : ∀ ω : HeckeCharacter K, TIPInput K ω) :
    HeckeSevenEighths K := by
  intro χ
  exact heckePacket_sevenEighths_of_TIP χ (hTIP χ) ⟨χ, base_mem_heckePacket K χ⟩

end HeckeGeneral.ThetaSkeleton.TIP
