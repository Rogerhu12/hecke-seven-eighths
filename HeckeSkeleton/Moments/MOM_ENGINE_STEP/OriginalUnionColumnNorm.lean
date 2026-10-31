import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceMassInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

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
  obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact (profiles.original_left_norm_le_annulus annulus (Z ^ a.n₁) t
      (Real.rpow_pos_of_pos hZ _) ht hwindow u (hrows u hu) I hI).trans
        (mul_le_mul_of_nonneg_left hleftPower hannulus)
  · exact (profiles.original_left_norm_le_annulus annulus Y₁ t hY₁ ht hwindow
      u (hrows u hu) I hI).trans (mul_le_mul_of_nonneg_left hY₁le hannulus)

theorem original_union_rightColumns_norm_le (annulus rightExponent : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₂ : 0 < Y₂)
    (hrightPower : Z ^ a.n₂ ≤ Z ^ rightExponent) (hY₂le : Y₂ ≤ Z ^ rightExponent)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ raw.rightColumns) :
    idealNorm K I ≤ annulus * Z ^ rightExponent := by
  obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact (profiles.original_right_norm_le_annulus annulus (Z ^ a.n₂) t
      (Real.rpow_pos_of_pos hZ _) ht hwindow u (hrows u hu) I hI).trans
        (mul_le_mul_of_nonneg_left hrightPower hannulus)
  · exact (profiles.original_right_norm_le_annulus annulus Y₂ t hY₂ ht hwindow
      u (hrows u hu) I hI).trans (mul_le_mul_of_nonneg_left hY₂le hannulus)

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
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
  have hp := Finset.mem_product.mp hm.1
  have hleft := raw.original_union_leftColumns_norm_le profiles annulus leftExponent hannulus hZ hY₁ hleftPower hY₁le
    hrows ht hwindow v.1.1 hp.1
  have hright := raw.original_union_rightColumns_norm_le profiles annulus rightExponent hannulus hZ hY₂ hrightPower hY₂le
    hrows ht hwindow v.1.2 hp.2
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
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hprime i)
  calc
    _ = (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
      rw [raw.columnExterior_val_of_mem v hv]
      simp only [columnIdeal, idealNorm, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
    _ ≤ ((annulus * Z ^ leftExponent) * (annulus * Z ^ rightExponent)) *
        ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
      mul_le_mul (mul_le_mul hleft hright (idealNorm_pos K _).le
        (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))) hprod
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))
          (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _)))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos hZ]
      simp only [SlotGeometry.totalLength, Real.rpow_add hZ, pow_add]
      ring

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
  have hraw := raw.original_union_column_norm_le_annulus profiles annulus leftExponent rightExponent
    (zero_le_one.trans hannulus) hZ hY₁ hY₂ hleftPower hrightPower hY₁le hY₂le hrows ht hwindow v hv
  have hpower := (pow_le_pow_right₀ hannulus (Nat.add_le_add_right hcap 2)).trans hannulusZ
  exact (hraw.trans (mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hZ.le _))).trans_eq
    (by rw [Real.rpow_add hZ]; ring)

end ParentRawAtoms

namespace PairedEngineDomain

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)

/-- The original centered right scale is at least the original second
scale. The full union must use its larger exponent; the first union
continues to use the original first exponent. -/
theorem centered_union_scale_windows (hc : centered = true) :
    0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ ≤ Z ^ a.n₁ ∧
      Z ^ a.n₂ ≤ Z ^ (a.n₁ + a.n₂ - (a.m + a.q) / 4) ∧
      Y₂ ≤ Z ^ (a.n₁ + a.n₂ - (a.m + a.q) / 4) := by
  have hz : 0 < Z := zero_lt_one.trans domain.scale
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [domain.comparison_left hc]
    exact Real.rpow_pos_of_pos hz _
  · rw [domain.comparison_right hc]
    exact Real.rpow_pos_of_pos hz _
  · rw [domain.comparison_left hc]
    exact Real.rpow_le_rpow_of_exponent_le domain.scale.le (domain.centered_left hc)
  · exact Real.rpow_le_rpow_of_exponent_le domain.scale.le (by linarith [domain.centered_left hc])
  · exact (domain.comparison_right hc).le

end PairedEngineDomain
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_union_column_norm_le_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_union_column_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.centered_union_scale_windows
