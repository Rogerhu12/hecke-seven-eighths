import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderNodeShort
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderCubePriority
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderBackgrounds
import Mathlib.Algebra.BigOperators.Group.Finset.Preimage

/-!
# The uniform short contribution of the original canonical node

The complete short range is summed with the actual cube divisor mass.
All original row ideals and unit sectors are restored, including their
proved exterior zeros. Finally the original label normalization is
combined with the genuine label divisor mass. Constants and the finite
Schwartz seminorm are chosen before the node, its scale, its marks, or
its profile. The only analytic input is the original reflected-energy
input; no terminal moment estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalShort

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open GeneralReflectedEnergy ProviderNodes TerminalNodes CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

section Completed

variable {K S} {σ : Type*}

def residualData (x : TerminalRows.Data K S σ) (Z : ℝ) (H : Ext) (J : Finset σ) :
    TerminalRows.Data K S σ :=
  { x with
    completionLength := Real.logb Z (exteriorNorm K Sset H)
    slots := x.slots \ J
    primeLists := residualDivisorLists (H.val.val ^ 3) x.primeLists }

theorem residualData_admissible (x : TerminalRows.Data K S σ)
    {slotCap : ℕ} {Z A c z lo hi d : ℝ}
    (hx : x.Admissible slotCap Z A c z lo hi d) (hZ : 1 < Z)
    (H : Ext) (hH : H ∈ shortCubes K Sset (Z ^ d)) (J : Finset σ) :
    (residualData x Z H J).Admissible slotCap Z A c z lo hi d := by
  have hNp : 0 < exteriorNorm K Sset H := idealNorm_pos K H.val
  have hN1 : 1 ≤ exteriorNorm K Sset H := TerminalRows.norm_one_le K S H
  have hsmall : Real.logb Z (exteriorNorm K Sset H) ≤ d := by
    have hb := Real.logb_le_logb_of_le hZ hNp ((mem_shortCubes K Sset (Z ^ d) H).mp hH).le
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hb
  exact
    { column_nonneg := hx.column_nonneg
      label_nonneg := hx.label_nonneg
      row_nonneg := hx.row_nonneg
      puncture_nonneg := hx.puncture_nonneg
      completion_nonneg := Real.logb_nonneg hZ hN1
      completion_le := hsmall
      total_le := hx.total_le
      label_small := hx.label_small
      label_bound := hx.label_bound
      puncture_bound := hx.puncture_bound
      row_bound := hx.row_bound
      marks := (hx.marks.residual_lists (H.val.val ^ 3)).restrict Finset.sdiff_subset
      margins := hx.margins }

theorem residualData_scale (x : TerminalRows.Data K S σ) (Z : ℝ) (hZ : 1 < Z)
    (H : Ext) (J : Finset σ) :
    Z ^ ((residualData x Z H J).columnLength -
        3 * (residualData x Z H J).completionLength) =
      Z ^ x.columnLength / exteriorNorm K Sset H ^ 3 := by
  have hZp := zero_lt_one.trans hZ
  have he : Z ^ Real.logb Z (exteriorNorm K Sset H) = exteriorNorm K Sset H :=
    Real.rpow_logb hZp (ne_of_gt hZ) (exteriorNorm_pos K Sset H)
  change Z ^ (x.columnLength - 3 * Real.logb Z (exteriorNorm K Sset H)) = _
  rw [Real.rpow_sub hZp,
    show 3 * Real.logb Z (exteriorNorm K Sset H) =
      Real.logb Z (exteriorNorm K Sset H) * (3 : ℝ) by ring,
    Real.rpow_mul hZp.le, Real.rpow_ofNat, he]

variable (K S)

/-- Full short-cube energy on an arbitrary original exterior row set.
The fixed saving absorbs the actual cube divisor mass at every
permitted short cutoff. -/
theorem exists_uniform_short_row_energy
    (hD : AllowedGeneratorInput K Sset D)
    (backgrounds : Finset (HeckeCharacter K))
    (R : ReflectionFamily K Sset D backgrounds) (hE : Input K Sset D R.data backgrounds)
    (slotCap : ℕ) (A cstar lo hi : ℝ) (hA : 1 ≤ A) (hcstar : 0 < cstar)
    (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ {σ : Type*} (Z c z d : ℝ) (x : TerminalRows.Data K S σ) (W : SchwartzMap ℝ ℂ),
      Z₀ ≤ Z → cstar ≤ c → 0 ≤ z → z ≤ A → 0 < d → d ≤ cstar / 1000 →
      x.Admissible slotCap Z A c z lo hi d → tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      (∑ k ∈ x.rows, ‖shortCompletedColumn K Sset D θ
        (((Sset).unitEquivUnitsInteger K x.unit).val * D.generator k) x.label x.puncture
        (divisorMark x.slots x.primeLists x.primeWeights) W
        (Z ^ x.columnLength) (Z ^ d)‖ ^ 2) ≤
        C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
          Z ^ (x.totalLength - cstar / 64) := by
  obtain ⟨q, CR, Z₀, hCR, hZ₀, hrows⟩ := TerminalRows.exists_uniform_completed_energy
    K S D hD backgrounds R hE slotCap A cstar lo hi hA hcstar hlo hhi
  obtain ⟨CM, hCM, hmass⟩ := TerminalCubeMass.exists_exterior_cube_mass_bound
    K Sset slotCap 1 (by norm_num)
  let C := ((2 : ℝ) ^ slotCap * CM) ^ 2 * CR
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hCM)) hCR
  refine ⟨q, C, Z₀, hC, hZ₀, ?_⟩
  intro θ hθ σ Z c z d x W hZ hc hz hzA hd hdsmall hx hW
  letI : DecidableEq σ := Classical.decEq _
  have hZ1 : 1 < Z := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hZ₀.trans hZ)
  have hZp := zero_lt_one.trans hZ1
  let B := CR * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
    Z ^ (x.totalLength - cstar / 32)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hmass' : (∑ H ∈ shortCubes K Sset (Z ^ d),
      (((DedekindZetaZeroFree.LargeSieve.idealDivisors (H.val.val ^ 3)).card : ℝ) ^ slotCap) /
        exteriorNorm K Sset H) ≤ CM * Z ^ d := by
    simpa only [Real.rpow_one] using hmass (Z ^ d) (Real.one_le_rpow hZ1.le hd.le)
      (shortCubes K Sset (Z ^ d))
      (fun H hH => ((mem_shortCubes K Sset (Z ^ d) H).mp hH).le)
  have hb := TerminalCubePriority.short_energy K Sset D slotCap θ x.rows
    (fun k => ((Sset).unitEquivUnitsInteger K x.unit).val * D.generator k)
    x.label x.puncture x.slots x.primeLists x.primeWeights hx.marks.card_le
    hx.marks.prime hx.marks.weights_le W (Z ^ x.columnLength) (Z ^ d) B
    (CM * Z ^ d) (Real.rpow_pos_of_pos hZp _)
    (fun t ht => (hW (subset_tsupport W ht)).2) hB hmass' (by
      intro H hH J hJ
      have he := hrows θ hθ Z c z d (residualData x Z H J) W hZ hc hz hzA hd hdsmall
        (residualData_admissible x hx hZ1 H hH J) hW
      unfold TerminalRows.Data.energy TerminalRows.Data.value at he
      rw [residualData_scale x Z hZ1 H J] at he
      simpa only [residualData, TerminalRows.Data.totalLength, B] using he)
  calc
    _ ≤ ((2 : ℝ) ^ slotCap * (CM * Z ^ d)) ^ 2 * B := hb
    _ = C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        Z ^ (x.totalLength - cstar / 32 + 2 * d) := by
      have hp : (Z ^ d) ^ 2 * Z ^ (x.totalLength - cstar / 32) =
          Z ^ (x.totalLength - cstar / 32 + 2 * d) := by
        rw [← Real.rpow_mul_natCast hZp.le, ← Real.rpow_add hZp]
        congr 1
        ring
      dsimp only [B, C]
      calc
        _ = (((2 : ℝ) ^ slotCap * CM) ^ 2 * CR) *
            (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
            ((Z ^ d) ^ 2 * Z ^ (x.totalLength - cstar / 32)) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
      (mul_nonneg (zero_le_one.trans hC) (sq_nonneg _))

end Completed

section Nodes

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K} {σ : Type*}

def exteriorRows (rows : Finset (Ideal (𝓞 K) × Sector)) : Finset Ext :=
  (rows.image Prod.fst).preimage (fun I : Ext => I.val.val) (ideal_injective K Sset).injOn

theorem exteriorRows_bound (rows : Finset (Ideal (𝓞 K) × Sector)) (R : ℝ)
    (hR : ∀ k ∈ rows, (k.1.absNorm : ℝ) ≤ R)
    (I : Ext) (hI : I ∈ exteriorRows K S Γ rows) : exteriorNorm K Sset I ≤ R := by
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (Finset.mem_preimage.mp hI)
  change (I.val.val.absNorm : ℝ) ≤ R
  simpa only [he] using hR k hk

/-- The raw node rows inject into all their ideal-sector pairs. The
preimage identity retains every exterior row, while the original source
proves that the other rows are zero. -/
theorem row_energy_le_sectors [Γ.FiniteIndex] (x : Node K S Γ Θ ψ σ)
    (hbase : 0 < x.family.base) (hpuncture : x.puncture ≠ 0)
    (hW : Function.support x.test ⊆ Set.Iic 2) (T : ℝ) (f : Ext) :
    letI : Fintype Sector := Fintype.ofFinite _
    let r : NonzeroIdeal K := ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
    (∑ k ∈ x.rows, ‖shortValue K S Γ D x T f.val.val k‖ ^ 2) ≤
      ∑ ξ : Sector, ∑ k ∈ exteriorRows K S Γ x.rows,
        ‖shortCompletedColumn K Sset D (period K S Γ x)
          (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val *
            D.generator k) f (exteriorRadicalPuncture K Sset r)
          (mark K S Γ x) x.test (x.family.base ^ x.columnLength) T‖ ^ 2 := by
  letI : Fintype Sector := Fintype.ofFinite _
  dsimp only
  have hs : x.rows ⊆ (x.rows.image Prod.fst) ×ˢ (Finset.univ : Finset Sector) := by
    intro k hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨k, hk, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ k ∈ (x.rows.image Prod.fst) ×ˢ (Finset.univ : Finset Sector),
        ‖shortValue K S Γ D x T f.val.val k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ = ∑ ξ : Sector, ∑ I ∈ x.rows.image Prod.fst,
        ‖shortValue K S Γ D x T f.val.val (I, ξ)‖ ^ 2 := by
      rw [Finset.sum_product, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      have hp := Finset.sum_preimage (fun I : Ext => I.val.val) (x.rows.image Prod.fst)
        (ideal_injective K Sset).injOn
        (fun I => ‖shortValue K S Γ D x T f.val.val (I, ξ)‖ ^ 2) (by
          intro I hI hnot
          have he : ¬IsExterior K Sset I := by
            intro he
            exact hnot ⟨exteriorOf K Sset I he, rfl⟩
          rw [TerminalNodeShort.shortValue_zero_of_nonexterior_row K S Γ D x T f.val.val (I, ξ) he]
          simp)
      rw [← hp]
      apply Finset.sum_congr rfl
      intro k hk
      rw [TerminalNodeShort.shortValue_exterior K S Γ D x hbase hpuncture hW T f k ξ]

def nodeData (Z : ℝ) (x : Node K S Γ Θ ψ σ) (hpuncture : x.puncture ≠ 0)
    (f : Ext) (ξ : Sector) : TerminalRows.Data K S σ where
  label := f
  puncture := exteriorRadicalPuncture K Sset
    ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hpuncture⟩
  puncture_squarefree := exteriorRadicalPuncture_squarefree K Sset _
  unit := CanonicalSectors.sectorUnit K Sset Γ ξ
  rows := exteriorRows K S Γ x.rows
  columnLength := x.columnLength
  labelLength := x.labelLength
  rowLength := x.rowLength
  punctureLength := x.punctureLength Z
  completionLength := 0
  slots := x.family.survivors x.triple
  primeLists := x.family.primeLists
  primeWeights := x.family.primeWeights
  markLengths := x.markLengths

theorem nodeData_admissible {Λ G : HeckeCharacter K} {slotCap : ℕ}
    {Z Fcap A c z lo hi d : ℝ} (x : Node K S Γ Θ ψ σ)
    (hx : x.Admissible D Λ G slotCap Z Fcap c z lo hi) (hZ : 1 < Z)
    (hF : Fcap ≤ A) (hd : 0 ≤ d) (hsmall : x.labelLength ≤ d)
    (f : Ext) (hf : f.val.val ∈ x.labels) (ξ : Sector) :
    (nodeData K S Γ Z x hx.puncture_nonzero f ξ).Admissible slotCap Z A c z lo hi d := by
  refine
    { column_nonneg := hx.column_nonneg
      label_nonneg := hx.label_nonneg
      row_nonneg := hx.row_nonneg
      puncture_nonneg := Node.Admissible.puncture_nonneg x hx hZ
      completion_nonneg := le_rfl
      completion_le := hd
      total_le := hx.total_le.trans hF
      label_small := hsmall
      label_bound := hx.label_bound f.val.val hf
      puncture_bound := ?_
      row_bound := exteriorRows_bound K S Γ x.rows _ hx.row_bound
      marks := hx.marks
      margins := hx.margins }
  exact (exteriorRadicalPuncture_norm_le K Sset
    ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hx.puncture_nonzero⟩).trans_eq
      (Node.Admissible.puncture_norm x hx hZ)

variable (Θ ψ) [Γ.FiniteIndex] [Finite Θ]

/-- The genuine short contribution, uniformly before every original
canonical node. This is the terminal input used by finite backwards
induction, proved solely from the original reflected-energy input. -/
theorem exists_uniform_short_contribution
    (hD : AllowedGeneratorInput K Sset D) (Λ G : HeckeCharacter K)
    (R : ReflectionFamily K Sset D (TerminalBackgrounds.periodInventory K Θ ψ Λ))
    (hE : Input K Sset D R.data (TerminalBackgrounds.periodInventory K Θ ψ Λ))
    (slotCap : ℕ) (A cstar lo hi : ℝ) (hA : 1 ≤ A) (hcstar : 0 < cstar)
    (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (d z : ℝ), 0 < d → d ≤ cstar / 1000 → 0 ≤ z → z ≤ A →
      ∀ {σ : Type*} (Z Fcap c : ℝ) (x : Node K S Γ Θ ψ σ),
      Z₀ ≤ Z → Fcap ≤ A → cstar ≤ c →
      x.Admissible D Λ G slotCap Z Fcap c z lo hi → x.labelLength < d →
      shortEnergy K S Γ D slotCap x (Z ^ d) ≤
        C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 * Z ^ x.totalLength := by
  letI : Fintype Sector := Fintype.ofFinite _
  obtain ⟨q, CR, Z₀, hCR, hZ₀, hrow⟩ := exists_uniform_short_row_energy K S D hD
    (TerminalBackgrounds.periodInventory K Θ ψ Λ) R hE slotCap A cstar lo hi hA hcstar hlo hhi
  obtain ⟨CL, hCL, hlabel⟩ := TerminalNodeShort.exists_label_normalized_bound
    K S Γ D slotCap A (cstar / 64) (zero_le_one.trans hA) (by positivity)
  let CS := (Fintype.card Sector : ℝ) * CR
  let C := max 1 (CL * CS)
  have hCS : 0 ≤ CS := mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hCR)
  refine ⟨q, C, Z₀, le_max_left _ _, hZ₀, ?_⟩
  intro d z hd hdsmall hz hzA σ Z Fcap c x hZ hF hc hx hsmall
  have hZ1 : 1 < Z := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hZ₀.trans hZ)
  have hZp := zero_lt_one.trans hZ1
  have hbase : 0 < x.family.base := hx.base_eq.symm ▸ hZp
  have hW : Function.support x.test ⊆ Set.Iic 2 :=
    fun t ht => (hx.test_support (subset_tsupport x.test ht)).2
  have hθ : period K S Γ x ∈ TerminalBackgrounds.periodInventory K Θ ψ Λ := by
    simpa only [period, hx.lambda_eq] using
      TerminalBackgrounds.period_mem_inventory K Θ ψ Λ (x.family.background x.triple)
        (x.family.background_admissible x.triple)
  let B := CS * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2
  have hB : 0 ≤ B := mul_nonneg hCS (sq_nonneg _)
  have hraw (f : Ideal (𝓞 K)) (hf : f ∈ x.labels) :
      (∑ k ∈ x.rows, ‖shortValue K S Γ D x (Z ^ d) f k‖ ^ 2) ≤
        B * Z ^ (x.totalLength - cstar / 64) := by
    by_cases he : IsExterior K Sset f
    · let f' := exteriorOf K Sset f he
      have hs := row_energy_le_sectors K S D Γ x hbase hx.puncture_nonzero hW (Z ^ d) f'
      have hsector (ξ : Sector) :
          (∑ k ∈ exteriorRows K S Γ x.rows,
            ‖shortCompletedColumn K Sset D (period K S Γ x)
              (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val *
                D.generator k) f'
              (exteriorRadicalPuncture K Sset
                ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hx.puncture_nonzero⟩)
              (mark K S Γ x) x.test (x.family.base ^ x.columnLength) (Z ^ d)‖ ^ 2) ≤
            CR * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
              Z ^ (x.totalLength - cstar / 64) := by
        have hr := hrow (period K S Γ x) hθ Z c z d
          (nodeData K S Γ Z x hx.puncture_nonzero f' ξ) x.test hZ hc hz hzA hd hdsmall
          (nodeData_admissible K S D Γ x hx hZ1 hF hd.le hsmall.le f' hf ξ) hx.test_support
        simpa only [nodeData, TerminalRows.Data.totalLength, Node.totalLength, mark, hx.base_eq] using hr
      calc
        _ ≤ ∑ ξ : Sector, ∑ k ∈ exteriorRows K S Γ x.rows,
            ‖shortCompletedColumn K Sset D (period K S Γ x)
              (((Sset).unitEquivUnitsInteger K (CanonicalSectors.sectorUnit K Sset Γ ξ)).val *
                D.generator k) f'
              (exteriorRadicalPuncture K Sset
                ⟨x.puncture, mem_nonZeroDivisors_of_ne_zero hx.puncture_nonzero⟩)
              (mark K S Γ x) x.test (x.family.base ^ x.columnLength) (Z ^ d)‖ ^ 2 := hs
        _ ≤ ∑ _ξ : Sector, CR * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
            Z ^ (x.totalLength - cstar / 64) := Finset.sum_le_sum (fun ξ _ => hsector ξ)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, B, CS]
          ring
    · have hz' : (∑ k ∈ x.rows, ‖shortValue K S Γ D x (Z ^ d) f k‖ ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [TerminalNodeShort.shortValue_zero_of_nonexterior_label K S Γ D x (Z ^ d) f k he]
        simp
      rw [hz']
      exact mul_nonneg hB (Real.rpow_nonneg hZp.le _)
  have hV : x.labelLength ≤ A := by
    have ht := hx.total_le.trans hF
    change x.columnLength + x.labelLength ≤ A at ht
    linarith [hx.column_nonneg]
  have hl := hlabel Z x.totalLength B (Z ^ d) x hZ1.le hx.base_eq hx.label_nonneg hV
    hx.label_bound hB hraw
  calc
    _ ≤ CL * B * Z ^ (x.totalLength - (cstar / 64) / 2) := hl
    _ ≤ CL * B * Z ^ x.totalLength :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
        (mul_nonneg (zero_le_one.trans hCL) hB)
    _ = (CL * CS) * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
        Z ^ x.totalLength := by dsimp only [B]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end Nodes
end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalShort

end
