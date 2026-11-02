import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Two-sided norm windows on original nonzero coefficients

A nonzero whole coefficient selects one of the original rectangles.
Each factor of that rectangle lies in the same original profile window.
Multiplying the two plain scales preserves their prescribed product;
no coordinatewise bound on the comparison scales is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

theorem coefficient_has_rectangle {raw : ParentRawAtoms Q d a Z t Y₁ Y₂}
    (values : raw.ConstantValues) (centered : Bool) (v : raw.Column)
    (hv : values.coefficient centered v ≠ 0) :
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

theorem rectangle_profiles_nonzero
    (atoms : ParentConstantAtoms Q d a Z t) (comparison : Bool)
    (v : (atoms.raw Y₁ Y₂).Column)
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

variable (atoms : ParentConstantAtoms Q d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}

theorem rectangle_column_norm_bounds
    (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)
    (lower upper : ℝ) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Icc lower upper) (comparison : Bool)
    (hleftScale : 0 < (if comparison then Y₁ else Z ^ a.n₁))
    (hrightScale : 0 < (if comparison then Y₂ else Z ^ a.n₂))
    (hscaleProduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns)
    (hrectangle : (atoms.values Y₁ Y₂).rectangle comparison v ≠ 0) :
    lower ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) ∧
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) ≤
      upper ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  have hp := rectangle_profiles_nonzero (A := A) (Γ := Γ) atoms comparison v hrectangle
  have hleftRep : profiles.leftRep u t
      (idealNorm K v.1.1 / (if comparison then Y₁ else Z ^ a.n₁)) ≠ 0 := by
    simpa only [← atoms.left_profile u hu, profiles.left_eq] using hp.1
  have hrightRep : profiles.rightRep u t
      (idealNorm K v.1.2 / (if comparison then Y₂ else Z ^ a.n₂)) ≠ 0 := by
    simpa only [← atoms.right_profile u hu, profiles.right_eq] using hp.2.1
  have hleftWindow := hwindow (profiles.left_support u (hrows u hu) t ht hleftRep)
  have hrightWindow := hwindow (profiles.right_support u (hrows u hu) t ht hrightRep)
  have hleft : lower * (if comparison then Y₁ else Z ^ a.n₁) ≤ idealNorm K v.1.1 ∧
      idealNorm K v.1.1 ≤ upper * (if comparison then Y₁ else Z ^ a.n₁) :=
    ⟨(le_div_iff₀ hleftScale).mp hleftWindow.1,
      (div_le_iff₀ hleftScale).mp hleftWindow.2⟩
  have hright : lower * (if comparison then Y₂ else Z ^ a.n₂) ≤ idealNorm K v.1.2 ∧
      idealNorm K v.1.2 ≤ upper * (if comparison then Y₂ else Z ^ a.n₂) :=
    ⟨(le_div_iff₀ hrightScale).mp hrightWindow.1,
      (div_le_iff₀ hrightScale).mp hrightWindow.2⟩
  have hprime (i : Fin d.geometry.slotCount) :
      lower * Z ^ (d.geometry.slots i).length ≤ (Ideal.absNorm (v.2 i).asIdeal : ℝ) ∧
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤ upper * Z ^ (d.geometry.slots i).length := by
    have hi : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using hp.2.2 i
    have hw := hwindow (profiles.prime_support i t ht hi)
    exact ⟨(le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp hw.1,
      (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp hw.2⟩
  have hprodLow : (∏ i, lower * Z ^ (d.geometry.slots i).length) ≤
      ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) :=
    Finset.prod_le_prod₀
      (fun _ _ => mul_nonneg hlower (Real.rpow_nonneg hZ.le _)) (fun i _ => (hprime i).1)
  have hprodUp : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      ∏ i, upper * Z ^ (d.geometry.slots i).length :=
    Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => (hprime i).2)
  have hid : (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnIdeal v) : ℝ) =
      (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
    simp only [ParentRawAtoms.columnIdeal, idealNorm, map_mul, map_prod,
      Nat.cast_mul, Nat.cast_prod]
  have hfactor (r : ℝ) :
      ((r * (if comparison then Y₁ else Z ^ a.n₁)) *
        (r * (if comparison then Y₂ else Z ^ a.n₂))) *
        (∏ i, r * Z ^ (d.geometry.slots i).length) =
      r ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Real.rpow_sum_of_pos hZ, pow_add, pow_two]
    rw [Real.rpow_add hZ]
    change _ = r ^ d.geometry.slotCount * (r * r) *
      (Z ^ (a.n₁ + a.n₂) * Z ^ (∑ i, (d.geometry.slots i).length))
    rw [← hscaleProduct]
    ring
  constructor
  · rw [← hfactor lower, hid]
    exact mul_le_mul
      (mul_le_mul hleft.1 hright.1 (mul_nonneg hlower hrightScale.le) (idealNorm_pos K _).le)
      hprodLow
      (Finset.prod_nonneg (fun _ _ => mul_nonneg hlower (Real.rpow_nonneg hZ.le _)))
      (mul_nonneg (idealNorm_pos K _).le (idealNorm_pos K _).le)
  · rw [hid, ← hfactor upper]
    exact mul_le_mul
      (mul_le_mul hleft.2 hright.2 (idealNorm_pos K _).le (mul_nonneg hupper hleftScale.le))
      hprodUp (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg hupper hleftScale.le) (mul_nonneg hupper hrightScale.le))

theorem original_column_norm_bounds
    (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)
    (lower upper : ℝ) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Icc lower upper) (centered : Bool)
    (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column)
    (hv : v ∈ (atoms.raw Y₁ Y₂).exteriorColumns (A := A) (Γ := Γ))
    (hcoefficient : (atoms.values Y₁ Y₂).coefficient centered v ≠ 0) :
    lower ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) ≤
      (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior (A := A) (Γ := Γ) v).val : ℝ) ∧
    (Ideal.absNorm ((atoms.raw Y₁ Y₂).columnExterior (A := A) (Γ := Γ) v).val : ℝ) ≤
      upper ^ (d.geometry.slotCount + 2) * Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  rw [(atoms.raw Y₁ Y₂).columnExterior_val_of_mem (A := A) (Γ := Γ) v hv]
  obtain ⟨comparison, hallowed, hrectangle⟩ :=
    coefficient_has_rectangle (A := A) (Γ := Γ) (atoms.values Y₁ Y₂) centered v hcoefficient
  have hmem : v ∈ (atoms.raw Y₁ Y₂).columns := (Finset.mem_filter.mp hv).1
  cases comparison with
  | false =>
      exact rectangle_column_norm_bounds (A := A) (Γ := Γ)
        atoms profiles lower upper hlower hupper hZ
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
      exact rectangle_column_norm_bounds (A := A) (Γ := Γ)
        atoms profiles lower upper hlower hupper hZ
        hrows ht hwindow true hscales.1 hscales.2 (hcomparison hc) v hmem hrectangle

theorem annulus_power_threshold (cap : ℕ) (annulus loss : ℝ) (hloss : 0 < loss) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → annulus ^ (cap + 2) ≤ Z ^ loss := by
  have hevent := (_root_.tendsto_rpow_atTop hloss).eventually
    (Filter.eventually_ge_atTop (annulus ^ (cap + 2)))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ
  exact hZ₁ Z ((le_max_left _ _).trans hZ)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.original_column_norm_bounds
