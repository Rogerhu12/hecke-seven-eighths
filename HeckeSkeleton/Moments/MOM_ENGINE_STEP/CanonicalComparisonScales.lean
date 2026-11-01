import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalUnionColumnNorm

/-!
# Choose unused ordinary comparison scales before constructing the source

An ordinary parent does not use its comparison rectangle. Its unused
comparison scales may therefore be chosen equal to the original scales
before forming the complete Cartesian source. Centered parents retain
both given comparison scales. This gives a uniform window on every
original column, including the zero columns retained by the source.

The final transport copies every chosen child, parameter, kernel and
terminal value. Only the identity of the parent energy is used. In
particular, this operation is not a change to an already chosen source
or normalized family.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Keep the centered comparison scale; use the original scale when the
comparison rectangle does not occur in the parent polynomial. -/
def canonicalComparisonScale (centered : Bool) (original comparison : ℝ) : ℝ :=
  match centered with
  | false => original
  | true => comparison

@[simp] theorem canonicalComparisonScale_false (original comparison : ℝ) :
    canonicalComparisonScale false original comparison = original := rfl

@[simp] theorem canonicalComparisonScale_true (original comparison : ℝ) :
    canonicalComparisonScale true original comparison = comparison := rfl

@[simp] theorem pairedStagePolynomial_canonicalComparisonScales
    (centered : Bool) (d : MomentData K ω ψ)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ Z t : ℝ) :
    pairedStagePolynomial centered d u X₁ X₂
      (canonicalComparisonScale centered X₁ Y₁)
      (canonicalComparisonScale centered X₂ Y₂) Z t =
        pairedStagePolynomial centered d u X₁ X₂ Y₁ Y₂ Z t := by
  cases centered
  · simp only [pairedStagePolynomial, Bool.false_eq_true, ite_false]
  · rfl

@[simp] theorem pairedStageEnergy_canonicalComparisonScales
    (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy centered d a Z t
      (canonicalComparisonScale centered (Z ^ a.n₁) Y₁)
      (canonicalComparisonScale centered (Z ^ a.n₂) Y₂) =
        pairedStageEnergy centered d a Z t Y₁ Y₂ := by
  simp only [pairedStageEnergy, pairedStagePolynomial_canonicalComparisonScales]

namespace PairedEngineDomain

variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}

/-- The original domain is unchanged by the choice of its unused
ordinary scales. In particular the full kappa range is retained. -/
def canonicalComparisonScales
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding) :
    PairedEngineDomain centered d a Z
      (canonicalComparisonScale centered (Z ^ a.n₁) Y₁)
      (canonicalComparisonScale centered (Z ^ a.n₂) Y₂) floor padding where
  scale := domain.scale
  width_floor := domain.width_floor
  width_nonneg := domain.width_nonneg
  plain_left_nonneg := domain.plain_left_nonneg
  plain_right_nonneg := domain.plain_right_nonneg
  total_length := domain.total_length
  kappa_lower := domain.kappa_lower
  kappa_upper := domain.kappa_upper
  capacity := domain.capacity
  padded_core := domain.padded_core
  ordinary := domain.ordinary
  centered_left := domain.centered_left
  centered_right := domain.centered_right
  comparison_left hc := by
    simpa only [hc, canonicalComparisonScale_true] using domain.comparison_left hc
  comparison_right hc := by
    simpa only [hc, canonicalComparisonScale_true] using domain.comparison_right hc

end PairedEngineDomain

namespace ParentRawAtoms

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ floor padding : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t
    (canonicalComparisonScale centered (Z ^ a.n₁) Y₁)
    (canonicalComparisonScale centered (Z ^ a.n₂) Y₂))
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Every column of the actual complete Cartesian source has a fixed
power window. This includes zero coefficients and requires no active
carrier or change of the original source after it has been constructed. -/
theorem canonicalComparison_column_norm_le_power
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      Z ^ (2 * (a.n₁ + a.n₂ + a.z) + loss) := by
  have hZ : 0 < Z := zero_lt_one.trans domain.scale
  have hz : 0 ≤ a.z := by
    rw [domain.total_length]
    exact Finset.sum_nonneg (fun i _ => (d.geometry.slots i).length_pos.le)
  cases centered with
  | false =>
    have hraw := raw.original_union_column_norm_le_power profiles
      cap annulus loss a.n₁ a.n₂ hannulus hcap hannulusZ hZ
      (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
      le_rfl le_rfl le_rfl le_rfl hrows ht hwindow v hv
    apply hraw.trans
    apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
    rw [← domain.total_length]
    linarith [domain.plain_left_nonneg, domain.plain_right_nonneg]
  | true =>
    obtain ⟨hY₁, hY₂, hleft, hright, hcomparison⟩ :=
      domain.centered_union_scale_windows rfl
    have hraw := raw.original_union_column_norm_le_power profiles
      cap annulus loss a.n₁ (a.n₁ + a.n₂ - (a.m + a.q) / 4)
      hannulus hcap hannulusZ hZ hY₁ hY₂ le_rfl hright hleft hcomparison
      hrows ht hwindow v hv
    apply hraw.trans
    apply Real.rpow_le_rpow_of_exponent_le domain.scale.le
    rw [← domain.total_length]
    linarith [domain.plain_right_nonneg, domain.width_nonneg]

/-- The complete column bound has its exponent fixed before the moving
data as soon as the original total length lies in the fixed parameter box. -/
theorem canonicalComparison_column_norm_le_fixed_power
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (cap : ℕ) (annulus loss lengthBound : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (hlength : a.n₁ + a.n₂ + a.z ≤ lengthBound)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      Z ^ (2 * lengthBound + loss) :=
  (raw.canonicalComparison_column_norm_le_power profiles domain cap annulus loss
    hannulus hcap hannulusZ hrows ht hwindow v hv).trans
      (Real.rpow_le_rpow_of_exponent_le domain.scale.le (by linarith))

end ParentRawAtoms

namespace PairedEngineConclusion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Restore the user's comparison scales after the canonical source has
proved its conclusion. Every already chosen child and kernel is copied
literally, and the four terminal values are unchanged. -/
def ofCanonicalComparisonScales
    (out : PairedEngineConclusion (Ω := Ω) centered d a Z t
      (canonicalComparisonScale centered (Z ^ a.n₁) Y₁)
      (canonicalComparisonScale centered (Z ^ a.n₂) Y₂)
      σ ε terminalExponent C control admissible) :
    PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible where
  branches := out.branches
  leftData := out.leftData
  rightData := out.rightData
  leftParameters := out.leftParameters
  rightParameters := out.rightParameters
  leftTwist := out.leftTwist
  rightTwist := out.rightTwist
  leftTwist_zero := out.leftTwist_zero
  rightTwist_zero := out.rightTwist_zero
  kernel := out.kernel
  finite_kernel := out.finite_kernel
  left_width := out.left_width
  right_width := out.right_width
  left_width_nonneg := out.left_width_nonneg
  right_width_nonneg := out.right_width_nonneg
  left_plain_left_nonneg := out.left_plain_left_nonneg
  left_plain_right_nonneg := out.left_plain_right_nonneg
  right_plain_left_nonneg := out.right_plain_left_nonneg
  right_plain_right_nonneg := out.right_plain_right_nonneg
  left_length := out.left_length
  right_length := out.right_length
  left_kappa := out.left_kappa
  right_kappa := out.right_kappa
  left_slots := out.left_slots
  right_slots := out.right_slots
  left_theta := out.left_theta
  right_theta := out.right_theta
  left_slot_characters := out.left_slot_characters
  right_slot_characters := out.right_slot_characters
  left_admissible := out.left_admissible
  right_admissible := out.right_admissible
  left_capacity := out.left_capacity
  right_capacity := out.right_capacity
  firstZero := out.firstZero
  secondZero := out.secondZero
  exceptional := out.exceptional
  tail := out.tail
  firstZero_nonneg := out.firstZero_nonneg
  secondZero_nonneg := out.secondZero_nonneg
  exceptional_nonneg := out.exceptional_nonneg
  tail_nonneg := out.tail_nonneg
  terminals := out.terminals
  left_integrable := out.left_integrable
  right_integrable := out.right_integrable
  cauchy_integrable := out.cauchy_integrable
  parent := by simpa only [pairedStageEnergy_canonicalComparisonScales] using out.parent
  mass := out.mass

variable (out : PairedEngineConclusion (Ω := Ω) centered d a Z t
  (canonicalComparisonScale centered (Z ^ a.n₁) Y₁)
  (canonicalComparisonScale centered (Z ^ a.n₂) Y₂)
  σ ε terminalExponent C control admissible)

@[simp] theorem ofCanonicalComparisonScales_leftData :
    out.ofCanonicalComparisonScales.leftData = out.leftData := rfl

@[simp] theorem ofCanonicalComparisonScales_rightData :
    out.ofCanonicalComparisonScales.rightData = out.rightData := rfl

@[simp] theorem ofCanonicalComparisonScales_leftParameters :
    out.ofCanonicalComparisonScales.leftParameters = out.leftParameters := rfl

@[simp] theorem ofCanonicalComparisonScales_rightParameters :
    out.ofCanonicalComparisonScales.rightParameters = out.rightParameters := rfl

@[simp] theorem ofCanonicalComparisonScales_kernel :
    out.ofCanonicalComparisonScales.kernel = out.kernel := rfl

@[simp] theorem ofCanonicalComparisonScales_terminals :
    out.ofCanonicalComparisonScales.firstZero = out.firstZero ∧
      out.ofCanonicalComparisonScales.secondZero = out.secondZero ∧
      out.ofCanonicalComparisonScales.exceptional = out.exceptional ∧
      out.ofCanonicalComparisonScales.tail = out.tail := ⟨rfl, rfl, rfl, rfl⟩

end PairedEngineConclusion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.pairedStageEnergy_canonicalComparisonScales
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.canonicalComparison_column_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.canonicalComparison_column_norm_le_fixed_power
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion.ofCanonicalComparisonScales

