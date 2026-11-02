import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.LengthStages

/-!
# The finite proof stage for ordinary nodes outside the padded core

The first two stages retain the actual length split of the core proof.
An ordinary zero-slot node outside the padded core has stage two.  Its
actual ordinary reflection preserves width and enters the padded core,
so this is a genuine same-band decrease.  Strict two-transform children
may land in this third stage; their strict width drop remains earlier.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

namespace Node

/-- The extra stage records a real geometric failure of the padded-core
condition, independently of the Boolean selecting a centered coefficient. -/
def coreStage (n : Node K ω ψ) (padding : ℝ) : Fin 3 :=
  if n.width + padding < n.totalLength then 2 else n.lengthStage

theorem coreStage_of_core (n : Node K ω ψ) (padding : ℝ)
    (hcore : n.totalLength ≤ n.width + padding) :
    n.coreStage padding = n.lengthStage := by
  simp only [coreStage, not_lt.mpr hcore, if_false]

theorem coreStage_of_noncore (n : Node K ω ψ) (padding : ℝ)
    (hnoncore : n.width + padding < n.totalLength) :
    n.coreStage padding = 2 := by
  simp only [coreStage, hnoncore, if_true]

theorem lengthStage_val_le_one (n : Node K ω ψ) :
    n.lengthStage.val ≤ 1 := by
  unfold lengthStage
  split_ifs <;> norm_num

/-- The third stage can only raise the original actual-length stage. -/
theorem lengthStage_le_coreStage (n : Node K ω ψ) (padding : ℝ) :
    n.lengthStage.val ≤ (n.coreStage padding).val := by
  unfold coreStage
  split_ifs
  · change n.lengthStage.val ≤ 2
    have h := n.lengthStage_val_le_one
    omega
  · exact le_rfl

end Node

namespace PolynomialSystem

variable {σ W : ℝ}

/-- Only the proof stage changes; labels and every actual polynomial
remain the original family. -/
def withCoreStages (S : PolynomialSystem.{u} K ω ψ σ W) (padding : ℝ) :
    PolynomialSystem.{u} K ω ψ σ W where
  Label := S.Label
  node := S.node
  proofStage x := (S.node x).coreStage padding
  sigma_pos := S.sigma_pos
  width_nonneg := S.width_nonneg
  width_le := S.width_le

theorem core_schedule_eq_length_schedule
    (S : PolynomialSystem.{u} K ω ψ σ W) (padding : ℝ) (x : S.Label)
    (hcore : (S.node x).totalLength ≤ (S.node x).width + padding) :
    (S.withCoreStages padding).schedule x = S.withLengthStages.schedule x := by
  dsimp only [PolynomialSystem.schedule, PolynomialSystem.withCoreStages,
    PolynomialSystem.withLengthStages]
  rw [(S.node x).coreStage_of_core padding hcore]

/-- Equal actual geometry gives the same full three-stage schedule. -/
theorem same_core_schedule (S : PolynomialSystem.{u} K ω ψ σ W)
    (padding : ℝ) (child parent : S.Label)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (htotal : (S.node child).totalLength = (S.node parent).totalLength) :
    (S.withCoreStages padding).schedule child =
      (S.withCoreStages padding).schedule parent := by
  have hslot :
      (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
        (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1) := by
    rw [hslots]
  have hband :
      boundedBand σ (S.node child).width W S.sigma_pos (S.width_le child) =
        boundedBand σ (S.node parent).width W S.sigma_pos (S.width_le parent) := by
    apply Fin.ext
    change widthBand σ (S.node child).width = widthBand σ (S.node parent).width
    rw [hwidth]
  have hstage : (S.node child).coreStage padding = (S.node parent).coreStage padding := by
    unfold Node.coreStage Node.lengthStage
    rw [htotal, hwidth]
  dsimp only [PolynomialSystem.schedule, PolynomialSystem.withCoreStages]
  rw [hslot, hband, hstage]

/-- A real ordinary reflection from outside the padded core to the
same-width core is an earlier-stage call. -/
theorem core_reflection_earlier (S : PolynomialSystem.{u} K ω ψ σ W)
    (padding : ℝ) (child parent : S.Label)
    (hslots : (S.node child).parameters.z = (S.node parent).parameters.z)
    (hwidth : (S.node child).width = (S.node parent).width)
    (hchildCore : (S.node child).totalLength ≤ (S.node child).width + padding)
    (hparentNoncore : (S.node parent).width + padding < (S.node parent).totalLength) :
    ((S.withCoreStages padding).schedule child).Earlier
      ((S.withCoreStages padding).schedule parent) := by
  dsimp only [PolynomialSystem.schedule, PolynomialSystem.withCoreStages]
  refine Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
  · change (if (S.node child).parameters.z = 0 then (0 : Fin 2) else 1) =
      (if (S.node parent).parameters.z = 0 then (0 : Fin 2) else 1)
    rw [hslots]
  · apply Fin.ext
    change widthBand σ (S.node child).width = widthBand σ (S.node parent).width
    rw [hwidth]
  · change ((S.node child).coreStage padding).val <
      ((S.node parent).coreStage padding).val
    rw [(S.node child).coreStage_of_core padding hchildCore,
      (S.node parent).coreStage_of_noncore padding hparentNoncore]
    change (S.node child).lengthStage.val < 2
    have h := (S.node child).lengthStage_val_le_one
    omega

/-- The added geometric stage preserves every genuine earlier edge of
the two-stage core order.  A same-band earlier core child has length
stage zero and hence is still in the padded core. -/
theorem earlier_core_of_length (S : PolynomialSystem.{u} K ω ψ σ W)
    (padding : ℝ) (hpadding : 0 ≤ padding) (child parent : S.Label)
    (h : (S.withLengthStages.schedule child).Earlier
      (S.withLengthStages.schedule parent)) :
    ((S.withCoreStages padding).schedule child).Earlier
      ((S.withCoreStages padding).schedule parent) := by
  dsimp only [PolynomialSystem.schedule, PolynomialSystem.withCoreStages,
    PolynomialSystem.withLengthStages] at h ⊢
  rcases h with hslot | ⟨hslot, hband | ⟨hband, hstage⟩⟩
  · exact Or.inl hslot
  · exact Or.inr ⟨hslot, Or.inl hband⟩
  · refine Or.inr ⟨hslot, Or.inr ⟨hband, ?_⟩⟩
    change (S.node child).lengthStage.val < (S.node parent).lengthStage.val at hstage
    have hparent := (S.node parent).lengthStage_val_le_one
    have hchildZero : (S.node child).lengthStage.val = 0 := by omega
    have hchildRange : (S.node child).totalLength ≤ 5 * (S.node child).width / 6 := by
      by_contra hnot
      have hone := (S.node child).lengthStage_one (lt_of_not_ge hnot)
      rw [hone] at hchildZero
      norm_num at hchildZero
    have hchildCore : (S.node child).totalLength ≤ (S.node child).width + padding := by
      linarith [S.width_nonneg child]
    change ((S.node child).coreStage padding).val <
      ((S.node parent).coreStage padding).val
    rw [(S.node child).coreStage_of_core padding hchildCore]
    exact hstage.trans_le ((S.node parent).lengthStage_le_coreStage padding)

end PolynomialSystem

end HeckeSkeleton.Moments.EngineInduction
