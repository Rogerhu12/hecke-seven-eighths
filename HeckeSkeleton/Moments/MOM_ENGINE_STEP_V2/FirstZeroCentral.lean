import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentConstantSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1/T2: the original central coefficient and individual profile bounds

Only the elementary original-atom argument is reused from A-line
OriginalCentralCoefficientBound and CanonicalOriginalFirstWindows.
The two rectangles retain the same original product of scales, and all
prime occurrences remain in the coefficient. No terminal bound, source
replacement, or normalized child construction is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open HeckeSkeleton.Moments.EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

section RawAtoms

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms Q d a Z t Y₁ Y₂}
variable (values : raw.ConstantValues)

/-- Only individual original atoms are bounded. Both comparison
scales and every slot remain in the displayed product. -/
theorem rectangle_norm_le_original_atoms
    (leftBound rightBound : Bool → ℝ) (primeBound : Fin d.geometry.slotCount → ℝ)
    (hleft : ∀ comparison, 0 ≤ leftBound comparison)
    (hright : ∀ comparison, 0 ≤ rightBound comparison)
    (hleftAtom : ∀ comparison I, I ∈ raw.leftColumns →
      ‖values.left comparison I‖ ≤ leftBound comparison)
    (hrightAtom : ∀ comparison I, I ∈ raw.rightColumns →
      ‖values.right comparison I‖ ≤ rightBound comparison)
    (hprimeAtom : ∀ i p, p ∈ raw.slotColumns i → ‖values.prime i p‖ ≤ primeBound i)
    (comparison : Bool) (v : raw.Column) (hv : v ∈ raw.columns) :
    ‖values.rectangle comparison v‖ ≤
      leftBound comparison * rightBound comparison * ∏ i, primeBound i := by
  have hm : (v.1.1 ∈ raw.leftColumns ∧ v.1.2 ∈ raw.rightColumns) ∧
      (∀ i, v.2 i ∈ raw.slotColumns i) := by
    simpa only [ParentRawAtoms.columns, childCartesianColumns,
      Finset.mem_product, Fintype.mem_piFinset] using hv
  rw [ParentRawAtoms.ConstantValues.rectangle, norm_mul, norm_mul, norm_prod]
  exact mul_le_mul
    (mul_le_mul (hleftAtom comparison _ hm.1.1) (hrightAtom comparison _ hm.1.2)
      (norm_nonneg _) (hleft comparison))
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hprimeAtom i _ (hm.2 i)))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (mul_nonneg (hleft comparison) (hright comparison))


end RawAtoms

theorem original_inverse_sqrt_rpow (Z length : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ length))⁻¹ = Z ^ (-length / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le, ← Real.rpow_neg hZ.le]
  congr 1
  ring

private theorem original_normalized_atom_norm_le
    (N B : ℝ) (v : ℂ) (hv : ‖v‖ ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * v‖ ≤ B * (Real.sqrt N)⁻¹ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg N)]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg N))

/-- The original normalization is a single product, including the
empty product when there are no prime slots. -/
theorem original_central_scale_product
    (slots : ℕ) (length : Fin slots → ℝ) (Z B N₁ N₂ plainLength : ℝ)
    (hZ : 0 < Z) (hN₁ : 0 ≤ N₁) (hproduct : N₁ * N₂ = Z ^ plainLength) :
    (B * (Real.sqrt N₁)⁻¹) * (B * (Real.sqrt N₂)⁻¹) *
        (∏ i, B * (Real.sqrt (Z ^ length i))⁻¹) =
      B ^ (slots + 2) * Z ^ (-(plainLength + ∑ i, length i) / 2) := by
  have hplain : (Real.sqrt N₁)⁻¹ * (Real.sqrt N₂)⁻¹ =
      Z ^ (-plainLength / 2) := by
    calc
      _ = (Real.sqrt N₁ * Real.sqrt N₂)⁻¹ := by rw [mul_inv_rev]; ring
      _ = (Real.sqrt (N₁ * N₂))⁻¹ := by rw [Real.sqrt_mul hN₁]
      _ = _ := by rw [hproduct, original_inverse_sqrt_rpow Z plainLength hZ]
  have hslots : (∏ i, (Real.sqrt (Z ^ length i))⁻¹) =
      Z ^ (-(∑ i, length i) / 2) := by
    simp_rw [original_inverse_sqrt_rpow Z _ hZ]
    rw [← Real.rpow_sum_of_pos hZ]
    congr 1
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hslots]
  calc
    _ = B ^ (slots + 2) *
        ((Real.sqrt N₁)⁻¹ * (Real.sqrt N₂)⁻¹ * Z ^ (-(∑ i, length i) / 2)) := by
      rw [pow_add, pow_two]
      ring
    _ = _ := by
      rw [hplain, ← Real.rpow_add hZ]
      congr 1
      congr 1
      ring


section ConstantAtoms

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

/-- A rectangle is bounded on the literal original support. The raw
atom bounds do not contain any central scale or whole-column product. -/
theorem rectangle_norm_le_original_central_scales
    (B : ℝ) (hB : 0 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (comparison : Bool)
    (hN₁ : 0 ≤ (if comparison then Y₁ else Z ^ a.n₁))
    (hproduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).rectangle comparison v‖ ≤
      B ^ (d.geometry.slotCount + 2) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  have h := rectangle_norm_le_original_atoms (atoms.values Y₁ Y₂)
    (fun comparison => B * (Real.sqrt (if comparison then Y₁ else Z ^ a.n₁))⁻¹)
    (fun comparison => B * (Real.sqrt (if comparison then Y₂ else Z ^ a.n₂))⁻¹)
    (fun i => B * (Real.sqrt (Z ^ (d.geometry.slots i).length))⁻¹)
    (fun _ => mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (fun _ => mul_nonneg hB (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (fun comparison I hI => original_normalized_atom_norm_le _ B _ (hleft comparison I hI))
    (fun comparison I hI => original_normalized_atom_norm_le _ B _ (hright comparison I hI))
    (fun i p hp => original_normalized_atom_norm_le _ B _ (hprime i p hp))
    comparison v hv
  apply h.trans_eq
  simpa only [SlotGeometry.totalLength] using
    original_central_scale_product d.geometry.slotCount
      (fun i => (d.geometry.slots i).length) Z B
      (if comparison then Y₁ else Z ^ a.n₁)
      (if comparison then Y₂ else Z ^ a.n₂) (a.n₁ + a.n₂) hZ hN₁ hproduct

/-- The sharp original coefficient exponent is proved before the
common supports are extracted. Both rectangles retain the same scales
and every original slot; the constant uses only the fixed slot cap. -/
theorem coefficient_norm_le_original_central_cap
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (B : ℝ) (hB : 1 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  let bound := B ^ (cap + 2) *
    Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2)
  have hbound : 0 ≤ bound :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hB) _) (Real.rpow_nonneg hZ.le _)
  have hrectangle (comparison : Bool)
      (hN : 0 ≤ (if comparison then Y₁ else Z ^ a.n₁))
      (hprod : (if comparison then Y₁ else Z ^ a.n₁) *
        (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂)) :
      ‖(atoms.values Y₁ Y₂).rectangle comparison v‖ ≤ bound := by
    apply (rectangle_norm_le_original_central_scales atoms B (zero_le_one.trans hB) hZ
      hleft hright hprime comparison hN hprod v hv).trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hB (Nat.add_le_add_right hcap 2)) (Real.rpow_nonneg hZ.le _)
  have hfalse := hrectangle false (Real.rpow_nonneg hZ.le _)
    (by simpa only [Bool.false_eq_true, if_false] using (Real.rpow_add hZ a.n₁ a.n₂).symm)
  have hcoefficient : ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤ 2 * bound := by
    cases centered with
    | false =>
        change ‖(atoms.values Y₁ Y₂).rectangle false v - 0‖ ≤ 2 * bound
        simpa only [sub_zero] using hfalse.trans (by linarith)
    | true =>
        change ‖(atoms.values Y₁ Y₂).rectangle false v -
          (atoms.values Y₁ Y₂).rectangle true v‖ ≤ 2 * bound
        have htrue := hrectangle true (hY₁ rfl) (hcomparison rfl)
        exact (norm_sub_le _ _).trans ((add_le_add hfalse htrue).trans_eq (by ring))
  simpa only [bound, mul_assoc] using hcoefficient

end ConstantAtoms

private theorem original_first_atom_norm_le (c f : ℂ) (B : ℝ)
    (hc : ‖c‖ ≤ 1) (hf : ‖f‖ ≤ B) : ‖c * f‖ ≤ B := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hc hf (norm_nonneg _) zero_le_one

section ProfileBounds

section OriginalProfiles

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window
  (OriginalProfileAtomBounds.profileOrders orders) d B)

include profiles

/-- An actual column contains an original plain-support witness row.
The two row-independent norm profiles therefore inherit their bounds
from the same original single-profile record, even when the original
carrier may be empty. -/
theorem original_profile_bounds_of_column
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    (∀ x, ‖atoms.leftProfile x‖ ≤ B) ∧
      (∀ x, ‖atoms.rightProfile x‖ ≤ B) ∧
      (∀ i x, ‖(d.geometry.slots i).profile t x‖ ≤ B) := by
  have hm := Finset.mem_product.mp hv
  have hplain := Finset.mem_product.mp hm.1
  obtain ⟨u, hu, _⟩ := Finset.mem_biUnion.mp hplain.1
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [← atoms.left_profile u hu, profiles.left_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.leftRep u t) x).trans
      (profiles.left_bound u (hrows u hu) t ht)
  · intro x
    rw [← atoms.right_profile u hu, profiles.right_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.rightRep u t) x).trans
      (profiles.right_bound u (hrows u hu) t ht)
  · intro i x
    rw [profiles.prime_eq]
    exact (OriginalProfileAtomBounds.norm_le_profileOrders orders (profiles.primeRep i t) x).trans
      (profiles.prime_bound i t ht)

/-- The original arithmetic and profile atoms prove the whole
coefficient window. Both rectangles retain their central factors and
the same product of comparison scales. -/
theorem coefficient_norm_le_raw_profile_window
    (hleftArithmetic : ∀ I, ‖atoms.leftArithmetic I‖ ≤ 1)
    (hrightArithmetic : ∀ I, ‖atoms.rightArithmetic I‖ ≤ 1)
    (hprimeArithmetic : ∀ i p, ‖atoms.primeArithmetic i p‖ ≤ 1)
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap) (hB : 1 ≤ B) (hZ : 0 < Z)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) * Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  obtain ⟨hleft, hright, hprime⟩ := original_profile_bounds_of_column atoms profiles hrows ht v hv
  exact coefficient_norm_le_original_central_cap atoms cap hcap B hB hZ
    (fun comparison I _ => original_first_atom_norm_le _ _ B (hleftArithmetic I)
      (hleft (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))))
    (fun comparison I _ => original_first_atom_norm_le _ _ B (hrightArithmetic I)
      (hright (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))))
    (fun i p _ => original_first_atom_norm_le _ _ B (hprimeArithmetic i p)
      (hprime i ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)))
    centered hY₁ hcomparison v hv

end OriginalProfiles
end ProfileBounds


section ArithmeticAtoms

variable {A : SArithmeticData K} {ω ψ : HeckeCharacter K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}

variable (Q : CompleteMovingRowRecipe A P R data)

theorem arithmeticAtoms_left_norm_le_one (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ‖(Q.arithmeticAtoms ξ).leftArithmetic I‖ ≤ 1 := by
  change ‖heckeIdealCoefficient K ((data ξ).plainBackground *
    (Q.correction * Q.moving.character)) I *
      (if IsCoprime I.val Q.arithmeticMask.val then (1 : ℂ) else 0)‖ ≤ 1
  by_cases hI : IsCoprime I.val Q.arithmeticMask.val
  · simpa only [if_pos hI, mul_one] using
      norm_heckeIdealCoefficient_le_one K
        ((data ξ).plainBackground * (Q.correction * Q.moving.character)) I
  · simp only [if_neg hI, mul_zero, norm_zero, zero_le_one]

theorem arithmeticAtoms_right_norm_le_one (ξ : X) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ‖(Q.arithmeticAtoms ξ).rightArithmetic I‖ ≤ 1 :=
  arithmeticAtoms_left_norm_le_one Q ξ I

theorem arithmeticAtoms_prime_norm_le_one (ξ : X)
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    ‖(Q.arithmeticAtoms ξ).primeArithmetic i p‖ ≤ 1 := by
  change ‖primeCoefficient K ((data ξ).slotCoefficient i *
    (Q.correction * Q.moving.character)) p *
      (if IsCoprime p.asIdeal Q.arithmeticMask.val then (1 : ℂ) else 0)‖ ≤ 1
  by_cases hp : IsCoprime p.asIdeal Q.arithmeticMask.val
  · simpa only [if_pos hp, mul_one] using
      norm_primeCoefficient_le_one K
        ((data ξ).slotCoefficient i * (Q.correction * Q.moving.character)) p
  · simp only [if_neg hp, mul_zero, norm_zero, zero_le_one]


end ArithmeticAtoms

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof
