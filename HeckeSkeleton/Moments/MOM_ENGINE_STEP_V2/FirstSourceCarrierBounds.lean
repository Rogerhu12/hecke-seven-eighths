import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentColumnPhaseBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# A fixed norm box for every original first-source column

Each plain ideal belongs to one of its two literal profile supports.
The two supports may use different rectangles, so both plain scales
are bounded by their common total length. Every prime occurrence and
every zero-coefficient column remains in the original Cartesian carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

section RawCarrier

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}

/-- Membership in the complete union supplies the individual support
windows without any nonvanishing assumption on a whole coefficient. -/
private theorem raw_union_column_norm_le_annulus
    (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)
    (annulus exponent : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ exponent) (hrightPower : Z ^ a.n₂ ≤ Z ^ exponent)
    (hY₁le : Y₁ ≤ Z ^ exponent) (hY₂le : Y₂ ≤ Z ^ exponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (2 * exponent + d.geometry.totalLength) := by
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
  have hp := Finset.mem_product.mp hm.1
  have hleft : idealNorm K v.1.1 ≤ annulus * Z ^ exponent := by
    obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hp.1
    have hbound (scale : ℝ) (hscale : 0 < scale)
        (hI : v.1.1 ∈ d.plainTest₁.support u t scale) :
        idealNorm K v.1.1 ≤ annulus * scale := by
      have hrep : profiles.leftRep u t (idealNorm K v.1.1 / scale) ≠ 0 := by
        simpa only [profiles.left_eq] using (d.plainTest₁.support_spec u t scale v.1.1).mp hI
      exact (div_le_iff₀ hscale).mp
        (hwindow (profiles.left_support u (hrows u hu) t ht hrep))
    rcases Finset.mem_union.mp hI with hI | hI
    · exact (hbound _ (Real.rpow_pos_of_pos hZ _) hI).trans
        (mul_le_mul_of_nonneg_left hleftPower hannulus)
    · exact (hbound _ hY₁ hI).trans (mul_le_mul_of_nonneg_left hY₁le hannulus)
  have hright : idealNorm K v.1.2 ≤ annulus * Z ^ exponent := by
    obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hp.2
    have hbound (scale : ℝ) (hscale : 0 < scale)
        (hI : v.1.2 ∈ d.plainTest₂.support u t scale) :
        idealNorm K v.1.2 ≤ annulus * scale := by
      have hrep : profiles.rightRep u t (idealNorm K v.1.2 / scale) ≠ 0 := by
        simpa only [profiles.right_eq] using (d.plainTest₂.support_spec u t scale v.1.2).mp hI
      exact (div_le_iff₀ hscale).mp
        (hwindow (profiles.right_support u (hrows u hu) t ht hrep))
    rcases Finset.mem_union.mp hI with hI | hI
    · exact (hbound _ (Real.rpow_pos_of_pos hZ _) hI).trans
        (mul_le_mul_of_nonneg_left hrightPower hannulus)
    · exact (hbound _ hY₂ hI).trans (mul_le_mul_of_nonneg_left hY₂le hannulus)
  have hprime (i : Fin d.geometry.slotCount) :
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤
        annulus * Z ^ (d.geometry.slots i).length := by
    have hi := Fintype.mem_piFinset.mp hm.2 i
    have hrep : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using
        ((d.geometry.slots i).support_spec t (Z ^ (d.geometry.slots i).length) (v.2 i)).mp hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
      (hwindow (profiles.prime_support i t ht hrep))
  have hprod : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
    Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hprime i)
  calc
    _ = (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
      rw [raw.columnExterior_val_of_mem v hv]
      simp only [ParentRawAtoms.columnIdeal, idealNorm, map_mul, map_prod,
        Nat.cast_mul, Nat.cast_prod]
    _ ≤ ((annulus * Z ^ exponent) * (annulus * Z ^ exponent)) *
        ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
      mul_le_mul (mul_le_mul hleft hright (idealNorm_pos K _).le
        (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))) hprod
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))
          (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _)))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos hZ]
      rw [show 2 * exponent = exponent + exponent by ring]
      simp only [SlotGeometry.totalLength, Real.rpow_add hZ, pow_add]
      ring

end RawCarrier

variable {c : TargetContext K} {call : Call c}

/-- Each comparison scale is at least one, and their product is the
original product scale. This bounds both branches without reversing
the centered right comparison inequality. -/
private theorem working_comparison_scales_le :
    call.base ^ call.workingComparison₁ ≤
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) ∧
      call.base ^ call.workingComparison₂ ≤
        call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) := by
  constructor
  · simpa only [mul_one, working_comparison_product call] using
      mul_le_mul_of_nonneg_left (working_comparison₂_scale_one_le call)
        (working_comparison₁_scale_nonneg call)
  · simpa only [one_mul, working_comparison_product call] using
      mul_le_mul_of_nonneg_right (working_comparison₁_scale_one_le call)
        (working_comparison₂_scale_nonneg call)

/-- A fixed, deliberately coarse box includes every original exterior
column, even when its complete centered coefficient vanishes. -/
theorem working_column_norm_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (loss : ℝ)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ loss)
    (v : call.workingRaw.Column) (hv : v ∈ call.workingRaw.exteriorColumns) :
    (Arithmetic.data c).exteriorNorm (call.workingRaw.columnExterior v) ≤
      call.base ^ (2 * (2 + recipeInductionSigma c / 16) + loss) := by
  have hleft : call.base ^ call.workingParameters.n₁ ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) :=
    Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      (by
        change call.node.parameters.n₁ ≤ call.node.parameters.n₁ + call.node.parameters.n₂
        linarith [call.domain.plain_right_nonneg])
  have hright : call.base ^ call.workingParameters.n₂ ≤
      call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂) :=
    Real.rpow_le_rpow_of_exponent_le call.domain.scale.le
      (by
        change call.node.parameters.n₂ ≤ call.node.parameters.n₁ + call.node.parameters.n₂
        linarith [call.domain.plain_left_nonneg])
  have hraw := raw_union_column_norm_le_annulus
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    call.workingRaw input.localized (uniformAnnulus c frame)
    (call.workingParameters.n₁ + call.workingParameters.n₂)
    (zero_le_one.trans (uniformAnnulus_one_le c frame)) call.base_pos
    (working_comparison₁_scale_pos call) (working_comparison₂_scale_pos call)
    hleft hright (working_comparison_scales_le (call := call)).1
    (working_comparison_scales_le (call := call)).2
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    (window_subset_uniformAnnulus frame call input hframe) v hv
  have hcap : call.localizedData.geometry.slotCount ≤ c.geometry.slots := call.slots_le
  have hpower : uniformAnnulus c frame ^ (call.localizedData.geometry.slotCount + 2) ≤
      call.base ^ loss :=
    (pow_le_pow_right₀ (uniformAnnulus_one_le c frame)
      (Nat.add_le_add_right hcap 2)).trans hannulusZ
  have hz : 0 ≤ call.workingParameters.z := by
    rw [working_total_length]
    exact HeckeSkeleton.Moments.EngineInduction.slotGeometry_totalLength_nonneg
      call.localizedData.geometry
  have hexponent :
      2 * (call.workingParameters.n₁ + call.workingParameters.n₂) +
        call.localizedData.geometry.totalLength + loss ≤
      2 * (2 + recipeInductionSigma c / 16) + loss := by
    rw [← working_total_length call]
    linarith [working_total_le call]
  calc
    _ ≤ uniformAnnulus c frame ^ (call.localizedData.geometry.slotCount + 2) *
        call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂) +
          call.localizedData.geometry.totalLength) := hraw
    _ ≤ call.base ^ loss *
        call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂) +
          call.localizedData.geometry.totalLength) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg call.base_pos.le _)
    _ = call.base ^ (2 * (call.workingParameters.n₁ + call.workingParameters.n₂) +
        call.localizedData.geometry.totalLength + loss) := by
      rw [← Real.rpow_add call.base_pos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hexponent

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {p : SourceParameters c}

/-- The original source equivalence transports the entire column
carrier, including every coefficient-zero column. -/
theorem first_column_norm_le (frame : SourceFrame) (input : ProfileInput call)
    (hframe : call.frame = frame) (loss : ℝ)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (i : F.source.Column) (hi : i ∈ F.source.columns) :
    (Arithmetic.data c).exteriorNorm (F.source.ideal i) ≤
      call.base ^ (2 * (2 + recipeInductionSigma c / 16) + loss) := by
  rw [hF.ideal i]
  apply working_column_norm_le frame input hframe loss hannulusZ
  rw [← hF.columns]
  exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
