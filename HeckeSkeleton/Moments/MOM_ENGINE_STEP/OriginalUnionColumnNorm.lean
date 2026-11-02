import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceMassInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

set_option linter.unusedSectionVars false

/-!
# Complete Cartesian union windows at the two actual comparison scales

The centered comparison increases the second plain scale in general.
The complete Cartesian carrier is therefore bounded with separate
exponent windows for each original scale and its comparison scale. No
ordering between a comparison scale and the same original scale is
assumed. The original source, exterior filter and every repeated prime
occurrence are retained.

These deliberately coarse windows pay the tail and physical-fibre
bounds. The independent zero window uses OriginalActiveColumnNorm and
its literal nonzero-rectangle support. The final domain lemma supplies
the actual centered comparison inequalities with their correct direction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]

namespace ParentRawAtoms

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Both rectangles are bounded on the original union of their plain
supports. There is no assumption about the complete column product. -/
theorem original_union_leftColumns_norm_le (annulus leftExponent : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent) (hY₁le : Y₁ ≤ Z ^ leftExponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ raw.leftColumns) :
    idealNorm K I ≤ annulus * Z ^ leftExponent := by
  sorry

theorem original_union_rightColumns_norm_le (annulus rightExponent : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₂ : 0 < Y₂)
    (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ raw.rightColumns) :
    idealNorm K I ≤ annulus * Z ^ rightExponent := by
  sorry

/-- The literal whole-ideal norm follows from the original individual
profile supports. Every original prime occurrence remains in the product. -/
theorem original_union_column_norm_le_annulus (annulus leftExponent rightExponent : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent) (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (leftExponent + rightExponent + d.geometry.totalLength) := by
  sorry

/-- The fixed annulus threshold and original formal lengths give the
pure power window used by the actual arithmetic and fibre theorems. -/
theorem original_union_column_norm_le_power (cap : ℕ) (annulus loss leftExponent rightExponent : ℝ)
    (hannulus : 1 ≤ annulus) (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hleftPower : Z ^ a.n₁ ≤ Z ^ leftExponent) (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent)
    (hY₁le : Y₁ ≤ Z ^ leftExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      Z ^ (leftExponent + rightExponent + d.geometry.totalLength + loss) := by
  sorry

end ParentRawAtoms

namespace PairedEngineDomain

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)

include domain in
/-- The original centered right scale is at least the original second
scale. The full union must use its larger exponent; the first union
continues to use the original first exponent. -/
theorem centered_union_scale_windows (hc : centered = true) :
    0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ ≤ Z ^ a.n₁ ∧
      Z ^ a.n₂ ≤ Z ^ (a.n₁ + a.n₂ - (a.m + a.q) / 4) ∧
      Y₂ ≤ Z ^ (a.n₁ + a.n₂ - (a.m + a.q) / 4) := by
  sorry

end PairedEngineDomain
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_union_column_norm_le_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_union_column_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.centered_union_scale_windows
