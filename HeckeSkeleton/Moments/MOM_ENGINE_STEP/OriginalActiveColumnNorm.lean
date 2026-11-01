import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalSourceMassInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCentralCoefficientBound

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
  by_cases hfalse : values.rectangle false v ≠ 0
  · exact ⟨false, by simp, hfalse⟩
  · have hz : values.rectangle false v = 0 := not_not.mp hfalse
    cases centered with
    | false => exact False.elim (hv (by simp [coefficient, hz]))
    | true =>
        refine ⟨true, by simp, ?_⟩
        intro htrue
        exact hv (by simp [coefficient, hz, htrue])

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
  have hprofiles := atoms.rectangle_profiles_ne_zero comparison v hrectangle
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
    (atoms.values Y₁ Y₂).coefficient_ne_zero_has_rectangle centered v hcoefficient
  have hmem : v ∈ (atoms.raw Y₁ Y₂).columns := (Finset.mem_filter.mp hv).1
  cases comparison with
  | false =>
      exact atoms.original_active_rectangle_column_norm_le_annulus profiles annulus hannulus hZ
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
      exact atoms.original_active_rectangle_column_norm_le_annulus profiles annulus hannulus hZ
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
  have hraw := atoms.original_active_column_norm_le_annulus profiles annulus
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
  have hleft := atoms.original_active_column_norm_le_power profiles cap annulus loss hannulus
    hcap hannulusZ hZ hrows ht hwindow centered hY₁ hcomparison i hi hci
  have hright := atoms.original_active_column_norm_le_power profiles cap annulus loss hannulus
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
  exact atoms.original_active_pair_norm_le_power profiles cap annulus loss hannulus
    hcap hannulusZ hZ hrows ht hwindow centered hY₁ hcomparison ij.1 ij.2
    (Finset.mem_product.mp hij).1 (Finset.mem_product.mp hij).2 hleft hright

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
        Z ^ (2 * (a.n₁ + a.n₂ + d.geometry.totalLength + loss)) :=
  atoms.original_active_gram_pair_norm_le_power profiles cap annulus loss hannulus
    hcap hannulusZ (zero_lt_one.trans domain.scale) hrows ht hwindow centered
    domain.comparison_scale_left_nonneg domain.comparison_product_eq_power φ ij hij hprofile

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
  obtain ⟨Z₀, hZ₀, hthreshold⟩ := original_annulus_power_threshold cap annulus loss hloss
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZ ω ψ d a t Y₁ Y₂ atoms rowDomain heightDomain window orders amplitude profiles
    hcap hrows ht hwindow centered hY₁ hcomparison φ ij hij hprofile
  exact atoms.original_active_gram_pair_norm_le_power profiles cap annulus loss hannulus
    hcap (hthreshold Z hZ) ((zero_lt_one.trans hZ₀).trans_le hZ)
    hrows ht hwindow centered hY₁ hcomparison φ ij hij hprofile

end ParentConstantAtoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.coefficient_ne_zero_has_rectangle
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.rectangle_profiles_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_column_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_of_domain
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.original_active_gram_pair_norm_uniform
