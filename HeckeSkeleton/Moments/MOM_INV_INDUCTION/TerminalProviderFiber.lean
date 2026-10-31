import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderMarkEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderStateProfile
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

/-!
# The actual marked source in a frozen row fiber

The data below consist only of original ideals, norm windows, original
prime lists and their individual coefficients. The source is defined by
the literal completed theta sum. No energy estimate or reconstruction
identity is stored in the data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalFiber

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open GeneralReflectedEnergy ProviderTerminalConductor TerminalMarks TerminalAggregation
open TerminalMarkFamily TerminalMarkEnergy
open HeckeSkeleton.Moments.MOM_BASE
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

structure Data (σ : Type*) where
  powerful : Ext
  supported : Ext
  label : Ext
  puncture : Ext
  puncture_squarefree : Squarefree puncture.val.val
  unit : Sset.unit K
  rows : Finset Ext
  columnLength : ℝ
  labelLength : ℝ
  rowLength : ℝ
  punctureLength : ℝ
  powerfulLength : ℝ
  residualLength : ℝ
  completionLength : ℝ
  slots : Finset σ
  primeLists : σ → Finset (Ideal (𝓞 K))
  primeWeights : σ → Ideal (𝓞 K) → ℂ
  markLengths : σ → ℝ

variable {K S} {σ : Type*}

namespace Data

def frozen (x : Data K S σ) : Ext := frozenIdeal K Sset x.powerful x.supported x.label
def totalLength (x : Data K S σ) : ℝ := x.columnLength + x.labelLength

structure Admissible (slotCap : ℕ) (Z A c z lo hi d : ℝ) (x : Data K S σ) : Prop where
  powerful : Powerful x.powerful.val
  column_nonneg : 0 ≤ x.columnLength
  label_nonneg : 0 ≤ x.labelLength
  row_nonneg : 0 ≤ x.rowLength
  puncture_nonneg : 0 ≤ x.punctureLength
  powerful_nonneg : 0 ≤ x.powerfulLength
  residual_nonneg : 0 ≤ x.residualLength
  completion_nonneg : 0 ≤ x.completionLength
  completion_le : x.completionLength ≤ d
  total_le : x.totalLength ≤ A
  label_small : x.labelLength ≤ d
  label_bound : exteriorNorm K Sset x.label ≤ Z ^ x.labelLength
  puncture_bound : exteriorNorm K Sset x.puncture ≤ Z ^ x.punctureLength
  powerful_bound : Z ^ x.powerfulLength ≤ exteriorNorm K Sset x.powerful
  row_bound : ∀ k ∈ x.rows,
    exteriorNorm K Sset (exteriorMul K Sset (exteriorMul K Sset x.powerful x.supported) k) ≤
      Z ^ x.rowLength
  residual_window : ∀ k ∈ x.rows, InAnnulus K Sset Z x.residualLength k
  residual_squarefree : ∀ k ∈ x.rows, Squarefree k.val.val
  residual_coprime_frozen : ∀ k ∈ x.rows, IsCoprime k.val.val x.frozen.val.val
  residual_coprime_puncture : ∀ k ∈ x.rows, IsCoprime k.val.val x.puncture.val.val
  marks : ProviderNodes.MarkConditions K S slotCap Z z lo hi x.slots
    x.primeLists x.primeWeights x.markLengths
  margins : HeckePort.Moments.CanonicalMargins x.totalLength x.rowLength x.punctureLength z c

def value (D : ThetaArithmeticData K Sset) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ) (k : Ext) : ℂ :=
  canonicalCompletedSum (exteriorGamma K Sset D)
    (canonicalTau K Sset D θ
      ((Sset.unitEquivUnitsInteger K x.unit).val * D.generator (exteriorMul K Sset k x.frozen))
      x.puncture.val.val)
    (HeckeSkeleton.Moments.MOMInvStep.divisorMark x.slots x.primeLists x.primeWeights)
    (canonicalVstar W) (Z ^ (x.columnLength - 3 * x.completionLength))

def energy (D : ThetaArithmeticData K Sset) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ) : ℝ :=
  ∑ k ∈ x.rows, ‖x.value D θ W Z k‖ ^ 2

end Data

variable (K S)
variable (D : ThetaArithmeticData K Sset)

private theorem fullSource_active_energy
    (f : FixedData K Sset) (s : FrozenState K Sset f.frozen f.puncture)
    (F : FiniteMellinData K Sset) (θ : HeckeCharacter K) (a : Ext → ℂ)
    (W : ℝ → ℂ) (X cap : ℝ) (rows ps : Finset Ext)
    (hcap : ∀ p ∈ ps, exteriorNorm K Sset p ≤ cap) (B : ℝ) (hB : 0 ≤ B)
    (hblocks : ∀ j ∈ Finset.range (CubeCompletionBlocks.count cap),
      (∑ k ∈ rows, ‖TerminalFrozenBlock.fullSource K Sset D f s F θ a W X
        (CubeCompletionBlocks.block ps (exteriorNorm K Sset) j) k‖ ^ 2) ≤ B) :
    (∑ k ∈ rows, ‖TerminalFrozenBlock.fullSource K Sset D f s F θ a W X ps k‖ ^ 2) ≤
      (CubeCompletionBlocks.count cap : ℝ) ^ 2 * B := by
  have h := finite_reconstruction_energy (Finset.range (CubeCompletionBlocks.count cap)) rows
    (fun _ => (1 : ℂ))
    (fun j k => TerminalFrozenBlock.fullSource K Sset D f s F θ a W X
      (CubeCompletionBlocks.block ps (exteriorNorm K Sset) j) k)
    (fun k => TerminalFrozenBlock.fullSource K Sset D f s F θ a W X ps k)
    hB (Nat.cast_nonneg (CubeCompletionBlocks.count cap))
    (by
      intro k hk
      simp only [one_mul, TerminalFrozenBlock.fullSource]
      exact CubeCompletionBlocks.sum_eq_blocks ps (exteriorNorm K Sset) cap
        (fun p _ => TerminalRectangles.norm_one_le K Sset p) hcap _)
    (by simp) hblocks
  exact h

/-- Uniform energy of the literal original marked source in one actual
powerful/supported row fiber. Only original arithmetic data enter the
class, and every finite coefficient is reconstructed before estimation. -/
theorem exists_uniform_energy
    (backgrounds : Finset (HeckeCharacter K))
    (R : ReflectionFamily K Sset D backgrounds) (hE : Input K Sset D R.data backgrounds)
    (slotCap : ℕ) (A cstar lo hi : ℝ) (hA : 1 ≤ A) (hcstar : 0 < cstar)
    (_hlo : 0 < lo) (_hhi : lo ≤ hi) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ {σ : Type*} (Z c z d : ℝ) (x : Data K S σ) (W : SchwartzMap ℝ ℂ),
      Z₀ ≤ Z → cstar ≤ c → 0 ≤ z → z ≤ A → 0 < d → d ≤ cstar / 1000 →
      x.Admissible slotCap Z A c z lo hi d → tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      x.energy D θ W Z ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        Z ^ (x.totalLength - cstar / 16 - x.powerfulLength / 2) := by
  classical
  let eta := cstar / 1024
  let L₀ := 8 * (A + cstar + 1)
  have heta : 0 < eta := div_pos hcstar (by norm_num)
  have hL₀ : 1 ≤ L₀ := by dsimp only [L₀]; linarith
  have hL₀p : 0 < L₀ := zero_lt_one.trans_le hL₀
  let delta := eta / L₀
  have hdelta : 0 < delta := div_pos heta hL₀p
  obtain ⟨q, C₀, Z₁, hC₀, hZ₁, hstate⟩ := TerminalStateProfile.exists_uniform_state_energy
    K Sset D backgrounds R hE L₀ cstar hL₀ hcstar
  obtain ⟨CD, hCD, hcount⟩ := CubeCompletionBlocks.exists_count_small_power delta hdelta
  obtain ⟨CS, hCS, hstates⟩ := TerminalStates.exists_state_mass_bound K Sset
    (eta / (2 * L₀)) (by positivity)
  obtain ⟨CM, hCM, hmass⟩ := TerminalAggregation.exists_inactive_mass_bound K Sset slotCap delta hdelta
  let supportConstant := (max 1 hi) ^ (slotCap + 1)
  have hSupport : 1 ≤ supportConstant := one_le_pow₀ (le_max_left 1 hi)
  obtain ⟨Z₂, hZ₂, hsupport⟩ := exists_uniform_power_threshold eta supportConstant heta hSupport
  let C := CS ^ 2 * (2 : ℝ) ^ (2 * slotCap) * CM ^ 2 * CD ^ 2 * C₀
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCS) (one_le_pow₀ (by norm_num)))
          (one_le_pow₀ hCM)) (one_le_pow₀ hCD)) hC₀
  refine ⟨q, C, max Z₁ Z₂, hC, hZ₁.trans (le_max_left _ _), ?_⟩
  intro θ hθ σ Z c z d x W hZ hc hz hzA hd hdsmall hx hW
  have hZ₁' : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ₂' : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZ2 : 2 ≤ Z := hZ₁.trans hZ₁'
  have hZ' : 1 < Z := lt_of_lt_of_le (by norm_num) hZ2
  have hz0 := zero_lt_one.trans hZ'
  have hq : 0 ≤ q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by positivity
  by_cases hne : x.rows.Nonempty
  swap
  · rw [Data.energy, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    positivity
  obtain ⟨k₀, hk₀⟩ := hne
  have hN := hx.column_nonneg
  have hV := hx.label_nonneg
  have hM := hx.row_nonneg
  have hQ := hx.puncture_nonneg
  have hF := hx.total_le
  have hmarg := hx.margins.1
  change c ≤ x.columnLength + x.labelLength - x.rowLength - x.punctureLength - z at hmarg
  change x.columnLength + x.labelLength ≤ A at hF
  have hcA : cstar ≤ A := by linarith
  have hNA : x.columnLength ≤ A := by linarith
  have hVA : x.labelLength ≤ A := by linarith
  have hMA : x.rowLength ≤ A := by linarith
  have hQA : x.punctureLength ≤ A := by linarith
  have hdA : d ≤ A := by linarith
  have hcompA : x.completionLength ≤ A := hx.completion_le.trans hdA
  have hPJ : exteriorNorm K Sset (exteriorMul K Sset x.powerful x.supported) ≤ Z ^ x.rowLength := by
    have hb := hx.row_bound k₀ hk₀
    rw [HeckeSkeleton.LowEnergy.ActualFrozenCube.exteriorNorm_mul] at hb
    exact (le_mul_of_one_le_right (exteriorNorm_pos K Sset _).le
      (TerminalRectangles.norm_one_le K Sset k₀)).trans hb
  have hPN : exteriorNorm K Sset x.powerful ≤ Z ^ x.rowLength := by
    have hn : exteriorNorm K Sset x.powerful ≤
        exteriorNorm K Sset (exteriorMul K Sset x.powerful x.supported) := by
      rw [HeckeSkeleton.LowEnergy.ActualFrozenCube.exteriorNorm_mul]
      exact le_mul_of_one_le_right (exteriorNorm_pos K Sset _).le
        (TerminalRectangles.norm_one_le K Sset _)
    exact hn.trans hPJ
  have hOA : x.powerfulLength ≤ A := by
    have hh := (Real.rpow_le_rpow_left_iff hZ').mp (hx.powerful_bound.trans hPN)
    exact hh.trans hMA
  have hHA : x.residualLength ≤ A := by
    have hh := TerminalGeometry.row_conductor K Sset hZ' x.powerful x.supported k₀
      (hx.row_bound k₀ hk₀) hx.powerful_bound (hx.residual_window k₀ hk₀).1
    linarith [hx.powerful_nonneg]
  have hfrozen : exteriorNorm K Sset x.frozen ≤ Z ^ L₀ := by
    have hn : exteriorNorm K Sset x.frozen =
        exteriorNorm K Sset (exteriorMul K Sset x.powerful x.supported) *
          exteriorNorm K Sset x.label ^ 4 := by
      simp only [Data.frozen, frozenIdeal, HeckeSkeleton.LowEnergy.ActualFrozenCube.exteriorNorm_mul]
      congr 1
      simp only [exteriorNorm, exteriorPower, SubmonoidClass.coe_pow, map_pow, Nat.cast_pow]
    rw [hn]
    have hh := mul_le_mul hPJ
      (pow_le_pow_left₀ (exteriorNorm_pos K Sset x.label).le hx.label_bound 4)
      (pow_nonneg (exteriorNorm_pos K Sset x.label).le 4) (Real.rpow_nonneg hz0.le _)
    apply hh.trans
    rw [← Real.rpow_mul_natCast hz0.le, ← Real.rpow_add hz0]
    apply Real.rpow_le_rpow_of_exponent_le hZ'.le
    dsimp only [L₀]
    linarith
  have hpuncture : exteriorNorm K Sset x.puncture ≤ Z ^ L₀ :=
    hx.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le hZ'.le (by dsimp only [L₀]; linarith))
  have hNstar : |x.columnLength - 3 * x.completionLength| ≤ L₀ := by
    apply abs_le.mpr
    dsimp only [L₀]
    constructor <;> linarith [hx.completion_nonneg]
  have hAL : A ≤ L₀ := by dsimp only [L₀]; linarith
  have hzaL : z + eta ≤ L₀ := by dsimp only [L₀, eta]; linarith
  have hmarks := hx.marks
  have hsupportZ := hsupport Z hZ₂'
  have hmax : max 1 hi ≤ supportConstant := by
    have hh := pow_le_pow_right₀ (le_max_left 1 hi) (Nat.succ_le_succ (Nat.zero_le slotCap))
    simpa only [pow_one] using hh
  have hprimeNorm (i : σ) (hiI : i ∈ x.slots) (p : Ideal (𝓞 K)) (hp : p ∈ x.primeLists i) :
      (p.absNorm : ℝ) ≤ Z ^ L₀ := by
    have hli : x.markLengths i ≤ z :=
      (Finset.single_le_sum (fun j hj => hmarks.length_nonneg j hj) hiI).trans hmarks.total_length
    have hhi : hi ≤ Z ^ eta := (le_max_right 1 hi).trans (hmax.trans hsupportZ)
    calc
      _ ≤ hi * Z ^ x.markLengths i := (hmarks.norm_window i hiI p hp).2
      _ ≤ Z ^ eta * Z ^ z := mul_le_mul hhi
        (Real.rpow_le_rpow_of_exponent_le hZ'.le hli) (Real.rpow_nonneg hz0.le _)
        (Real.rpow_nonneg hz0.le _)
      _ = Z ^ (z + eta) := by rw [← Real.rpow_add hz0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ'.le hzaL
  have hsubsetNorm (J : Finset σ) (hJ : J ⊆ x.slots)
      (P : Ext) (hP : P ∈ idealPool K Sset J x.primeLists
        (fun i hi => hmarks.prime i (hJ hi)) (fun i hi => hmarks.exterior i (hJ hi))) :
      exteriorNorm K Sset P ≤ Z ^ (z + eta) := by
    have hb := TerminalMarkEnergy.idealPool_norm_le K Sset J x.primeLists
      (fun i hi => hmarks.prime i (hJ hi)) (fun i hi => hmarks.exterior i (hJ hi))
      (fun i hi j hj hij => hmarks.disjoint i (hJ hi) j (hJ hj) hij)
      slotCap Z z hi hZ'.le x.markLengths
      ((Finset.card_le_card hJ).trans hmarks.card_le)
      ((Finset.sum_le_sum_of_subset_of_nonneg hJ
        (fun i hi _ => hmarks.length_nonneg i hi)).trans hmarks.total_length)
      (fun i hi p hp => (hmarks.norm_window i (hJ hi) p hp).2) P hP
    have hbase : (max 1 hi) ^ slotCap ≤ Z ^ eta :=
      (pow_le_pow_right₀ (le_max_left 1 hi) (Nat.le_succ slotCap)).trans hsupportZ
    exact hb.trans ((mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hz0.le _)).trans_eq (by
      rw [← Real.rpow_add hz0]
      congr 1
      ring))
  have hdeltaEq : L₀ * delta = eta := by
    dsimp only [delta]
    field_simp [hL₀p.ne']
  have hcapCount : (CubeCompletionBlocks.count (Z ^ (z + eta)) : ℝ) ≤ CD * Z ^ eta := by
    have hb := hcount (Z ^ (z + eta)) (Real.one_le_rpow hZ'.le (by linarith))
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hCD)
    calc
      _ ≤ (Z ^ L₀) ^ delta := Real.rpow_le_rpow (Real.rpow_nonneg hz0.le _)
        (Real.rpow_le_rpow_of_exponent_le hZ'.le hzaL) hdelta.le
      _ = _ := by rw [← Real.rpow_mul hz0.le, hdeltaEq]
  have hstateCard : (Nat.card (FrozenState K Sset x.frozen x.puncture) : ℝ) ≤ CS * Z ^ eta := by
    apply (hstates x.frozen x.puncture).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hCS)
    calc
      _ ≤ ((Z ^ L₀) * (Z ^ L₀)) ^ (eta / (2 * L₀)) := by gcongr
      _ = Z ^ eta := by
        rw [← Real.rpow_add hz0, ← Real.rpow_mul hz0.le]
        congr 1
        field_simp [hL₀p.ne']
        <;> ring
  let mass := CM * Z ^ eta
  have hmass' (J : {J : Finset σ // J ⊆ x.slots}) :
      (∑ qi : tuplePool K (x.slots \ J.val) x.primeLists,
        ‖tupleWeight K (x.slots \ J.val) x.primeWeights qi.val‖ *
        reciprocalWeight K Sset (x.slots \ J.val) x.primeLists
          (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) qi) ≤ mass := by
    have hb := hmass (x.slots \ J.val) x.primeLists
      (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1)
      (fun i hi j hj hij => hmarks.disjoint i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hij)
      ((Finset.card_le_card Finset.sdiff_subset).trans hmarks.card_le)
      x.primeWeights (fun i hi => hmarks.weights_le i (Finset.mem_sdiff.mp hi).1)
      (Z ^ L₀) (Real.one_le_rpow hZ'.le hL₀p.le)
      (fun i hi => hprimeNorm i (Finset.mem_sdiff.mp hi).1)
    simpa only [← Real.rpow_mul hz0.le, hdeltaEq, mass] using hb
  let B := CD ^ 2 * C₀ * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
    Z ^ (x.totalLength - cstar / 8 - x.powerfulLength / 2 + 2 * eta)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpiece (s : FrozenState K Sset x.frozen x.puncture)
      (J : {J : Finset σ // J ⊆ x.slots})
      (qi : tuplePool K (x.slots \ J.val) x.primeLists) :
      (∑ k ∈ x.rows, ‖inactiveBlock K Sset D x.slots x.primeLists x.primeWeights
        hmarks.prime hmarks.exterior (R.data θ) θ x.frozen x.puncture x.puncture_squarefree
        x.unit s J qi (canonicalVstar W) (Z ^ (x.columnLength - 3 * x.completionLength)) k‖ ^ 2) ≤
      (reciprocalWeight K Sset (x.slots \ J.val) x.primeLists
        (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
        (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) qi) ^ 2 * B := by
    let inactive := tuplePrimes K Sset (x.slots \ J.val) x.primeLists
      (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
      (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) qi
    by_cases haway : InactiveAway K Sset x.frozen x.puncture inactive
    swap
    · simp only [inactiveBlock, choiceValue, dif_neg haway, mul_zero,
        Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
    let fdata := fixedMarkData K Sset x.frozen x.puncture x.puncture_squarefree x.unit inactive haway
    let ps := idealPool K Sset J.val x.primeLists
      (fun i hi => hmarks.prime i (J.property hi)) (fun i hi => hmarks.exterior i (J.property hi))
    let coeff := coefficient K Sset J.val x.primeLists
      (fun i hi => hmarks.prime i (J.property hi)) (fun i hi => hmarks.exterior i (J.property hi)) x.primeWeights
    let w := ‖inactiveWeight K Sset fdata‖
    have hps : ∀ p ∈ ps, exteriorNorm K Sset p ≤ Z ^ (z + eta) := hsubsetNorm J.val J.property
    have hw : w = reciprocalWeight K Sset (x.slots \ J.val) x.primeLists
        (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
        (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) qi :=
      TerminalMarkEnergy.inactiveWeight_norm K Sset _ _ _ _ x.frozen x.puncture x.puncture_squarefree x.unit qi haway
    have hinactive : exteriorNorm K Sset (primeSetIdeal K Sset inactive) ≤ Z ^ L₀ := by
      have hiP : tupleIdeal K Sset (x.slots \ J.val) x.primeLists
          (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) qi ∈
        idealPool K Sset (x.slots \ J.val) x.primeLists
          (fun i hi => hmarks.prime i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hmarks.exterior i (Finset.mem_sdiff.mp hi).1) :=
        Finset.mem_image.mpr ⟨qi, Finset.mem_univ _, rfl⟩
      exact (hsubsetNorm (x.slots \ J.val) Finset.sdiff_subset _ hiP).trans
        (Real.rpow_le_rpow_of_exponent_le hZ'.le hzaL)
    have hblock (j : ℕ) (hj : j ∈ Finset.range (CubeCompletionBlocks.count (Z ^ (z + eta)))) :
        (∑ k ∈ x.rows, ‖TerminalFrozenBlock.fullSource K Sset D fdata s (R.data θ) θ coeff
          (canonicalVstar W) (Z ^ (x.columnLength - 3 * x.completionLength))
          (CubeCompletionBlocks.block ps (exteriorNorm K Sset) j) k‖ ^ 2) ≤
        C₀ * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * w ^ 2 *
          Z ^ (x.totalLength - cstar / 8 - x.powerfulLength / 2) := by
      let block := CubeCompletionBlocks.block ps (exteriorNorm K Sset) j
      by_cases hbne : block.Nonempty
      swap
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hbne,
          TerminalFrozenBlock.fullSource, Finset.sum_empty, norm_zero,
          zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
        positivity
      obtain ⟨p₀, hp₀⟩ := hbne
      let za := Real.logb Z (CubeCompletionBlocks.scale j)
      have hza : 0 ≤ za := Real.logb_nonneg hZ' (CubeCompletionBlocks.scale_one_le _)
      have hwindows (p : Ext) (hp : p ∈ block) : InAnnulus K Sset Z za p := by
        have hh := CubeCompletionBlocks.block_window ps (exteriorNorm K Sset) j
          (fun p _ => TerminalRectangles.norm_one_le K Sset p) p hp
        simpa only [za, InAnnulus, Real.rpow_logb hz0 (ne_of_gt hZ')
          (CubeCompletionBlocks.scale_pos j)] using hh
      have hzaUpper : za ≤ z + eta :=
        (Real.rpow_le_rpow_left_iff hZ').mp
          ((hwindows p₀ hp₀).1.trans (hps p₀ (Finset.mem_filter.mp hp₀).1))
      have hs : BoundedSource K Sset fdata Z L₀
          (x.columnLength - 3 * x.completionLength) x.residualLength za :=
        ⟨hNstar, hx.residual_nonneg, hHA.trans hAL, hza, hzaUpper.trans hzaL,
          hfrozen, hpuncture, hinactive⟩
      have hmarg' : HeckePort.Moments.CanonicalMargins x.totalLength x.rowLength
          x.punctureLength (z + eta) (c - 6 * eta) := by
        obtain ⟨hm, hn⟩ := hx.margins
        constructor <;> linarith
      have hh := hstate θ hθ x.powerful x.supported x.label x.puncture
        x.puncture_squarefree x.unit inactive haway s W hW
        Z x.columnLength x.labelLength x.rowLength x.punctureLength (z + eta) d (c - 6 * eta)
        x.powerfulLength x.residualLength za x.completionLength 1 hZ₁' hx.powerful hs
        hx.powerful_nonneg (hOA.trans hAL) hza hzaUpper hx.completion_nonneg hx.completion_le
        (by norm_num) hx.label_bound hx.puncture_bound hx.row_nonneg hx.puncture_nonneg
        (by change 0 ≤ x.columnLength + x.labelLength; positivity) hx.label_small hmarg'
        (by dsimp only [eta]; linarith) hdsmall x.rows block coeff hx.row_bound hx.powerful_bound
        hx.residual_window hwindows (fun p hp => coefficient_norm_le_one K Sset J.val x.primeLists
          (fun i hi => hmarks.prime i (J.property hi)) (fun i hi => hmarks.exterior i (J.property hi))
          (fun i hi j hj hij => hmarks.disjoint i (J.property hi) j (J.property hj) hij)
          x.primeWeights (fun i hi => hmarks.weights_le i (J.property hi)) p)
      simpa only [one_pow, mul_one] using hh
    have hh := fullSource_active_energy K S D fdata s (R.data θ) θ coeff (canonicalVstar W)
      (Z ^ (x.columnLength - 3 * x.completionLength)) (Z ^ (z + eta)) x.rows ps hps
      (C₀ * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * w ^ 2 *
        Z ^ (x.totalLength - cstar / 8 - x.powerfulLength / 2)) (by positivity) hblock
    simp_rw [inactiveBlock_eq_fullSource K Sset D x.slots x.primeLists x.primeWeights
      hmarks.prime hmarks.exterior (R.data θ) θ x.frozen x.puncture x.puncture_squarefree
      x.unit s J qi (canonicalVstar W) (Z ^ (x.columnLength - 3 * x.completionLength)) _ haway]
    apply hh.trans
    rw [← hw]
    calc
      _ ≤ (CD * Z ^ eta) ^ 2 * (C₀ * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 * w ^ 2 *
          Z ^ (x.totalLength - cstar / 8 - x.powerfulLength / 2)) := by gcongr
      _ = w ^ 2 * B := by
        dsimp only [B]
        rw [mul_pow, ← Real.rpow_mul_natCast hz0.le, Real.rpow_add hz0]
        ring
  have hprofile : (TerminalProfile.completedTest W hW).toFun = canonicalVstar W :=
    TerminalProfile.completionCLM_eq_vstar W hW
  have hsources := TerminalMarkEnergy.marked_source_energy K Sset x.slots x.primeLists x.primeWeights
    hmarks.prime hmarks.exterior hmarks.disjoint D (R.data θ) θ (R.reflection θ hθ)
    x.frozen x.puncture x.puncture_squarefree x.unit x.rows
    (fun k hk => ⟨hx.residual_squarefree k hk, hx.residual_coprime_frozen k hk,
      hx.residual_coprime_puncture k hk⟩)
    (TerminalProfile.completedTest W hW) (Z ^ (x.columnLength - 3 * x.completionLength)) B mass
    (Real.rpow_pos_of_pos hz0 _) hB (by dsimp only [mass]; positivity) hmass'
    (by simpa only [hprofile] using hpiece)
  rw [hprofile] at hsources
  change x.energy D θ W Z ≤ _ at hsources
  apply hsources.trans
  have hslots : (2 : ℝ) ^ (2 * x.slots.card) ≤ (2 : ℝ) ^ (2 * slotCap) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hmarks.card_le)
  calc
    _ ≤ (CS * Z ^ eta) ^ 2 * (2 : ℝ) ^ (2 * slotCap) * mass ^ 2 * B := by gcongr
    _ = C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        Z ^ (x.totalLength - cstar / 8 - x.powerfulLength / 2 + 6 * eta) := by
      dsimp only [mass, B, C]
      simp only [mul_pow, ← Real.rpow_mul_natCast hz0.le]
      rw [show x.totalLength - cstar / 8 - x.powerfulLength / 2 + 6 * eta =
        eta * 2 + eta * 2 + (x.totalLength - cstar / 8 - x.powerfulLength / 2 + 2 * eta) by ring,
        Real.rpow_add hz0, Real.rpow_add hz0]
      ring
    _ ≤ _ := by
      gcongr
      dsimp only [eta]
      linarith

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalFiber

end
