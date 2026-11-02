import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceMassInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCentralCoefficientBound

set_option linter.unusedSectionVars false

/-!
# Sharp original column norms on the actual coefficient support

The original parent carrier is the Cartesian product of the two plain
support unions. A cross combination in this carrier need not have the
sharp original total length. Its full centered coefficient, however,
can be nonzero only if one of the two literal rectangles is nonzero.
Every profile in that rectangle then lies in its own original support
window. The two plain scales of that same rectangle have the prescribed
product, so its whole ideal has the sharp original total length.

All statements below use the unchanged original columns, coefficients,
exterior ideal map and Gram profiles. No carrier is restricted and no
Cartesian atlas or child is replaced. The annulus threshold is the
existing one chosen from the fixed annulus, slot cap and positive loss,
before the moving original profiles or the scale.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

namespace ParentRawAtoms.ConstantValues

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂} (values : raw.ConstantValues)

/-- A nonzero centered coefficient has a nonzero literal rectangle.
The comparison rectangle can occur only in the centered case. -/
theorem coefficient_ne_zero_has_rectangle
    (centered : Bool) (v : raw.Column) (hv : values.coefficient centered v ≠ 0) :
    ∃ comparison : Bool, (comparison = true → centered = true) ∧
      values.rectangle comparison v ≠ 0 := by
  sorry

end ParentRawAtoms.ConstantValues

namespace ParentConstantAtoms

section LiteralRectangle

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

/-- Nonvanishing is extracted from the actual scalar product, with all
prime occurrences retained, including the empty product. -/
theorem rectangle_profiles_ne_zero
    (comparison : Bool) (v : (atoms.raw Y₁ Y₂).Column)
    (hv : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    atoms.leftProfile (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 ∧
    atoms.rightProfile (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 ∧
    ∀ i, (d.geometry.slots i).profile t
      ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
  sorry

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Each norm is paid by the corresponding profile in this single
nonzero rectangle. The equality of the two plain-scale products is used
only after the individual support bounds; no coordinatewise comparison
between a comparison scale and a main scale is required. -/
theorem original_active_rectangle_column_norm_le_annulus
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (comparison : Bool)
    (hleftScale : 0 < (if comparison then Y₁ else Z ^ a.n₁))
    (hrightScale : 0 < (if comparison then Y₂ else Z ^ a.n₂))
    (hscaleProduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns)
    (hrectangle : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  sorry

end LiteralRectangle

section ActualExteriorCarrier

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- The complete original coefficient determines which actual
rectangle supplies the sharp whole-column norm. Empty original row or
column carriers cause no extra existence premise. -/
theorem original_active_column_norm_le_annulus
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  sorry

/-- The previously chosen annulus threshold yields the sharp power
on actual nonzero coefficients, while the full carrier stays unchanged. -/
theorem original_active_column_norm_le_power
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior v).val : ℝ) ≤
      Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength + loss) := by
  sorry

/-- The original pair product has twice the sharp original total
length on the support of its actual two whole coefficients. -/
theorem original_active_pair_norm_le_power
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (i j : (atoms.raw Y₁ Y₂).Column)
    (hi : i ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hj : j ∈ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hci : (atoms.values Y₁ Y₂).coefficient centered i ≠ 0)
    (hcj : (atoms.values Y₁ Y₂).coefficient centered j ≠ 0) :
    (Ideal.absNorm (((atoms.raw Y₁ Y₂).columnExterior i).val *
      ((atoms.raw Y₁ Y₂).columnExterior j).val) : ℝ) ≤
        Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss)) := by
  sorry

/-- This is the original Gram-profile support condition used by the
pure dual-zero count. It follows from the two actual coefficients, so
the zero-profile pairs need no sharp ideal-norm window. -/
theorem original_active_gram_pair_norm_le_power
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (ij : (atoms.raw Y₁ Y₂).Column × (atoms.raw Y₁ Y₂).Column)
    (hij : ij ∈ (atoms.raw Y₁ Y₂).exteriorColumns ×ˢ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hprofile : ((atoms.values Y₁ Y₂).coefficient centered ij.1 *
      star ((atoms.values Y₁ Y₂).coefficient centered ij.2)) • φ ≠ 0) :
    (Ideal.absNorm (((atoms.raw Y₁ Y₂).columnExterior ij.1).val *
      ((atoms.raw Y₁ Y₂).columnExterior ij.2).val) : ℝ) ≤
        Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss)) := by
  sorry

/-- The actual parent domain supplies both comparison-scale facts.
In particular no false upper window on the second comparison scale is
introduced when its exponent exceeds the original second plain length. -/
theorem original_active_gram_pair_norm_of_domain
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus)
    (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    {centered : Bool} {floor padding : ℝ}
    (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (ij : (atoms.raw Y₁ Y₂).Column × (atoms.raw Y₁ Y₂).Column)
    (hij : ij ∈ (atoms.raw Y₁ Y₂).exteriorColumns ×ˢ (atoms.raw Y₁ Y₂).exteriorColumns)
    (hprofile : ((atoms.values Y₁ Y₂).coefficient centered ij.1 *
      star ((atoms.values Y₁ Y₂).coefficient centered ij.2)) • φ ≠ 0) :
    (Ideal.absNorm (((atoms.raw Y₁ Y₂).columnExterior ij.1).val *
      ((atoms.raw Y₁ Y₂).columnExterior ij.2).val) : ℝ) ≤
        Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss)) := by
  sorry

end ActualExteriorCarrier

/-- The sharp active-pair threshold is fixed before the scale, original
profiles, characters, source columns and comparison parameters. It is
the same annulus threshold as for the individual original atoms. -/
theorem original_active_gram_pair_norm_uniform
    {A : SArithmeticData K} {Γ : Subgroup A.U}
    (cap : ℕ) (annulus loss : ℝ) (hannulus : 1 ≤ annulus) (hloss : 0 < loss) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ : ℝ)
      (atoms : ParentConstantAtoms
        (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t)
      (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K))
      (heightDomain window : Set ℝ) (orders : Finset (ℕ × ℕ)) (amplitude : ℝ)
      (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude),
      d.geometry.slotCount ≤ cap →
      (∀ u ∈ pairedRows d a Z, u ∈ rowDomain) →
      t ∈ heightDomain → window ⊆ Set.Iic annulus →
    ∀ centered : Bool, (centered = true → 0 ≤ Y₁) →
      (centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) →
    ∀ (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
      (ij : (atoms.raw Y₁ Y₂).Column × (atoms.raw Y₁ Y₂).Column),
      ij ∈ (atoms.raw Y₁ Y₂).exteriorColumns ×ˢ (atoms.raw Y₁ Y₂).exteriorColumns →
      ((atoms.values Y₁ Y₂).coefficient centered ij.1 *
        star ((atoms.values Y₁ Y₂).coefficient centered ij.2)) • φ ≠ 0 →
      (Ideal.absNorm (((atoms.raw Y₁ Y₂).columnExterior ij.1).val *
        ((atoms.raw Y₁ Y₂).columnExterior ij.2).val) : ℝ) ≤
          Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss)) := by
  sorry

end ParentConstantAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.coefficient_ne_zero_has_rectangle
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.rectangle_profiles_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_of_domain
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_uniform
