import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroCentral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentTuples

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1/T2: sharp norm windows on the original nonzero coefficient

The actual centered coefficient determines which of the two original
rectangles supplies its support. The Cartesian carrier remains unchanged;
only zero profiles are omitted inside the powerful counting argument.
This retains the negative central exponent from FirstZeroCentral.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

/-- This threshold depends only on the fixed annulus, slot cap and
positive exponent loss. It precedes the actual source. -/
theorem original_annulus_power_threshold (cap : ℕ) (annulus loss : ℝ)
    (hloss : 0 < loss) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → annulus ^ (cap + 2) ≤ Z ^ loss := by
  have hevent := (_root_.tendsto_rpow_atTop hloss).eventually
    (Filter.eventually_ge_atTop (annulus ^ (cap + 2)))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ
  exact hZ₁ Z ((le_max_left _ _).trans hZ)

section ConstantValues

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂} (values : raw.ConstantValues)

/-- A nonzero centered coefficient has a nonzero literal rectangle.
The comparison rectangle can occur only in the centered case. -/
theorem coefficient_ne_zero_has_rectangle
    (centered : Bool) (v : raw.Column) (hv : values.coefficient centered v ≠ 0) :
    ∃ comparison : Bool, (comparison = true → centered = true) ∧
      values.rectangle comparison v ≠ 0 := by
  by_cases hfalse : values.rectangle false v ≠ 0
  · exact ⟨false, by simp, hfalse⟩
  · have hz : values.rectangle false v = 0 := not_not.mp hfalse
    cases centered with
    | false => exact False.elim (hv (by simp [ParentRawAtoms.ConstantValues.coefficient, hz]))
    | true =>
        refine ⟨true, by simp, ?_⟩
        intro htrue
        exact hv (by simp [ParentRawAtoms.ConstantValues.coefficient, hz, htrue])

end ConstantValues

section ConstantAtoms

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
  change atoms.leftValue (if comparison then Y₁ else Z ^ a.n₁) v.1.1 *
    atoms.rightValue (if comparison then Y₂ else Z ^ a.n₂) v.1.2 *
      (∏ i, atoms.primeValue i (v.2 i)) ≠ 0 at hv
  obtain ⟨hplain, hprime⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hplain
  refine ⟨?_, ?_, ?_⟩
  · change (Real.sqrt (if comparison then Y₁ else Z ^ a.n₁) : ℂ)⁻¹ *
      (atoms.leftArithmetic v.1.1 * atoms.leftProfile
        (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁))) ≠ 0 at hleft
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hleft).2).2
  · change (Real.sqrt (if comparison then Y₂ else Z ^ a.n₂) : ℂ)⁻¹ *
      (atoms.rightArithmetic v.1.2 * atoms.rightProfile
        (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂))) ≠ 0 at hright
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hright).2).2
  · intro i
    have hi := Finset.prod_ne_zero_iff.mp hprime i (Finset.mem_univ i)
    change (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
      (atoms.primeArithmetic i (v.2 i) * (d.geometry.slots i).profile t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) ≠ 0 at hi
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).2).2

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
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  have hprofiles := rectangle_profiles_ne_zero atoms comparison v hrectangle
  have hleftRep : profiles.leftRep u t
      (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 := by
    simpa only [← atoms.left_profile u hu, profiles.left_eq] using hprofiles.1
  have hrightRep : profiles.rightRep u t
      (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 := by
    simpa only [← atoms.right_profile u hu, profiles.right_eq] using hprofiles.2.1
  have hleft : idealNorm K v.1.1 ≤ annulus * (if comparison then Y₁ else Z ^ a.n₁) :=
    (div_le_iff₀ hleftScale).mp
      (hwindow (profiles.left_support u (hrows u hu) t ht hleftRep))
  have hright : idealNorm K v.1.2 ≤ annulus * (if comparison then Y₂ else Z ^ a.n₂) :=
    (div_le_iff₀ hrightScale).mp
      (hwindow (profiles.right_support u (hrows u hu) t ht hrightRep))
  have hprime (i : Fin d.geometry.slotCount) :
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤ annulus * Z ^ (d.geometry.slots i).length := by
    have hi : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using hprofiles.2.2 i
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
      (hwindow (profiles.prime_support i t ht hi))
  have hprod : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
    Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hprime i)
  calc
    _ = (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
      simp only [ParentRawAtoms.columnIdeal, idealNorm, map_mul, map_prod,
        Nat.cast_mul, Nat.cast_prod]
    _ ≤ ((annulus * (if comparison then Y₁ else Z ^ a.n₁)) *
          (annulus * (if comparison then Y₂ else Z ^ a.n₂))) *
        ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
      mul_le_mul
        (mul_le_mul hleft hright (idealNorm_pos K _).le
          (mul_nonneg hannulus hleftScale.le)) hprod
        (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hannulus hleftScale.le)
          (mul_nonneg hannulus hrightScale.le))
    _ = annulus ^ (d.geometry.slotCount + 2) *
        (((if comparison then Y₁ else Z ^ a.n₁) *
          (if comparison then Y₂ else Z ^ a.n₂)) *
            Z ^ (∑ i, (d.geometry.slots i).length)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, pow_add, pow_two]
      ring
    _ = _ := by
      rw [hscaleProduct, ← Real.rpow_add hZ]
      rfl

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
  rw [(atoms.raw Y₁ Y₂).columnExterior_val_of_mem v hv]
  obtain ⟨comparison, hallowed, hrectangle⟩ :=
    coefficient_ne_zero_has_rectangle (atoms.values Y₁ Y₂) centered v hcoefficient
  have hmem : v ∈ (atoms.raw Y₁ Y₂).columns := (Finset.mem_filter.mp hv).1
  cases comparison with
  | false =>
      exact original_active_rectangle_column_norm_le_annulus atoms profiles annulus hannulus hZ
        hrows ht hwindow false (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
        (by simpa only [Bool.false_eq_true, if_false] using
          (Real.rpow_add hZ a.n₁ a.n₂).symm) v hmem hrectangle
  | true =>
      have hc : centered = true := hallowed rfl
      have hproduct : 0 < Y₁ * Y₂ := by
        rw [hcomparison hc]
        exact Real.rpow_pos_of_pos hZ _
      have hscales : 0 < Y₁ ∧ 0 < Y₂ := by
        rcases mul_pos_iff.mp hproduct with hpos | hneg
        · exact hpos
        · exact False.elim ((not_lt_of_ge (hY₁ hc)) hneg.1)
      exact original_active_rectangle_column_norm_le_annulus atoms profiles annulus hannulus hZ
        hrows ht hwindow true hscales.1 hscales.2 (hcomparison hc) v hmem hrectangle

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
  have hraw := original_active_column_norm_le_annulus atoms profiles annulus
    (zero_le_one.trans hannulus) hZ hrows ht hwindow centered hY₁ hcomparison v hv hcoefficient
  have hpower :=
    (pow_le_pow_right₀ hannulus (Nat.add_le_add_right hcap 2)).trans hannulusZ
  exact (hraw.trans (mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hZ.le _))).trans_eq
    (by rw [Real.rpow_add hZ]; ring)

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
  have hleft := original_active_column_norm_le_power atoms profiles cap annulus loss hannulus
    hcap hannulusZ hZ hrows ht hwindow centered hY₁ hcomparison i hi hci
  have hright := original_active_column_norm_le_power atoms profiles cap annulus loss hannulus
    hcap hannulusZ hZ hrows ht hwindow centered hY₁ hcomparison j hj hcj
  rw [map_mul, Nat.cast_mul]
  exact (mul_le_mul hleft hright (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)).trans_eq
    (by rw [← Real.rpow_add hZ]; congr 1; ring)

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
  have hleft : (atoms.values Y₁ Y₂).coefficient centered ij.1 ≠ 0 := by
    intro h
    exact hprofile (by rw [h, zero_mul, zero_smul])
  have hright : (atoms.values Y₁ Y₂).coefficient centered ij.2 ≠ 0 := by
    intro h
    exact hprofile (by rw [h, star_zero, mul_zero, zero_smul])
  exact original_active_pair_norm_le_power atoms profiles cap annulus loss hannulus
    hcap hannulusZ hZ hrows ht hwindow centered hY₁ hcomparison ij.1 ij.2
    (Finset.mem_product.mp hij).1 (Finset.mem_product.mp hij).2 hleft hright


end ActualExteriorCarrier
end ConstantAtoms

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
