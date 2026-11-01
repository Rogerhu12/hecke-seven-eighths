import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderFiber
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderCounts
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderReflection
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CubeCompletionBlocks

/-!
# All original rows in the completed marked source

The original rows are partitioned by the dyadic norm of their actual
powerful part, then by their actual powerful and supported pair, and
finally by the norm of their residual ideal. These are disjoint finite
partitions. The residual coordinate is injective in each fixed pair, so
there is no additional Cauchy factor in the row sum.

The literal whole-index divisor mark and original unit are retained.
The allowed generator section is compared only through its exact ideal
symbols. The square-root count of powerful ideals is cancelled by the
proved one-half powerful saving in each reflected fiber.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.Moments.MOM_BASE
open ProviderTerminalConductor TerminalCounts GeneralReflectedEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

/-- Original arithmetic data only. The energy is defined below by the
actual completed canonical source. -/
structure Data (σ : Type*) where
  label : Ext
  puncture : Ext
  puncture_squarefree : Squarefree puncture.val.val
  unit : (Sset).unit K
  rows : Finset Ext
  columnLength : ℝ
  labelLength : ℝ
  rowLength : ℝ
  punctureLength : ℝ
  completionLength : ℝ
  slots : Finset σ
  primeLists : σ → Finset (Ideal (𝓞 K))
  primeWeights : σ → Ideal (𝓞 K) → ℂ
  markLengths : σ → ℝ

variable {K S} {σ : Type*}

namespace Data

def totalLength (x : Data K S σ) : ℝ := x.columnLength + x.labelLength

structure Admissible (slotCap : ℕ) (Z A c z lo hi d : ℝ) (x : Data K S σ) : Prop where
  column_nonneg : 0 ≤ x.columnLength
  label_nonneg : 0 ≤ x.labelLength
  row_nonneg : 0 ≤ x.rowLength
  puncture_nonneg : 0 ≤ x.punctureLength
  completion_nonneg : 0 ≤ x.completionLength
  completion_le : x.completionLength ≤ d
  total_le : x.totalLength ≤ A
  label_small : x.labelLength ≤ d
  label_bound : exteriorNorm K Sset x.label ≤ Z ^ x.labelLength
  puncture_bound : exteriorNorm K Sset x.puncture ≤ Z ^ x.punctureLength
  row_bound : ∀ k ∈ x.rows, exteriorNorm K Sset k ≤ Z ^ x.rowLength
  marks : ProviderNodes.MarkConditions K S slotCap Z z lo hi x.slots
    x.primeLists x.primeWeights x.markLengths
  margins : HeckePort.Moments.CanonicalMargins x.totalLength x.rowLength x.punctureLength z c

def value (D : ThetaArithmeticData K Sset) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ) (k : Ext) : ℂ :=
  canonicalCompletedSum (exteriorGamma K Sset D)
    (canonicalTau K Sset D θ
      ((((Sset).unitEquivUnitsInteger K x.unit).val * D.generator k) * D.generator x.label ^ 4)
      x.puncture.val.val)
    (HeckeSkeleton.Moments.MOMInvStep.divisorMark x.slots x.primeLists x.primeWeights)
    (canonicalVstar W) (Z ^ (x.columnLength - 3 * x.completionLength))

def energy (D : ThetaArithmeticData K Sset) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ) : ℝ :=
  ∑ k ∈ x.rows, ‖x.value D θ W Z k‖ ^ 2

def powerfulRows (x : Data K S σ) (j : ℕ) : Finset Ext :=
  CubeCompletionBlocks.block x.rows
    (fun k => exteriorNorm K Sset (exteriorPowerfulPart K Sset k)) j

def pairs (x : Data K S σ) (j : ℕ) : Finset (Ext × Ext) :=
  frozenPairs K Sset x.label x.puncture (x.powerfulRows j)

def movingRows (x : Data K S σ) (j : ℕ) (p : Ext × Ext) : Finset Ext :=
  residualRows K Sset x.label x.puncture (x.powerfulRows j) p

def fiberData (x : Data K S σ) (Z : ℝ) (j : ℕ) (p : Ext × Ext) (l : ℕ) :
    TerminalFiber.Data K S σ where
  powerful := p.1
  supported := p.2
  label := x.label
  puncture := x.puncture
  puncture_squarefree := x.puncture_squarefree
  unit := x.unit
  rows := CubeCompletionBlocks.block (x.movingRows j p) (exteriorNorm K Sset) l
  columnLength := x.columnLength
  labelLength := x.labelLength
  rowLength := x.rowLength
  punctureLength := x.punctureLength
  powerfulLength := Real.logb Z (CubeCompletionBlocks.scale j)
  residualLength := Real.logb Z (CubeCompletionBlocks.scale l)
  completionLength := x.completionLength
  slots := x.slots
  primeLists := x.primeLists
  primeWeights := x.primeWeights
  markLengths := x.markLengths

end Data

variable (K S)

theorem norm_one_le (I : Ext) : 1 ≤ exteriorNorm K Sset I := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem powerful_norm_le (I : Ext) :
    exteriorNorm K Sset (exteriorPowerfulPart K Sset I) ≤ exteriorNorm K Sset I := by
  exact_mod_cast Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I.val)
    (map_dvd Ideal.absNorm (powerfulPart_dvd I.val))

variable {K S}

theorem Data.powerfulRows_subset (x : Data K S σ) (j : ℕ) :
    x.powerfulRows j ⊆ x.rows := Finset.filter_subset _ _

theorem Data.powerfulRows_window (x : Data K S σ) (j : ℕ) (k : Ext)
    (hk : k ∈ x.powerfulRows j) :
    CubeCompletionBlocks.scale j ≤ exteriorNorm K Sset (exteriorPowerfulPart K Sset k) ∧
      exteriorNorm K Sset (exteriorPowerfulPart K Sset k) ≤ 2 * CubeCompletionBlocks.scale j :=
  CubeCompletionBlocks.block_window x.rows _ j
    (fun I hI => norm_one_le K S (exteriorPowerfulPart K Sset I)) k hk

theorem Data.pair_powerful_window (x : Data K S σ) (j : ℕ) (p : Ext × Ext)
    (hp : p ∈ x.pairs j) :
    CubeCompletionBlocks.scale j ≤ exteriorNorm K Sset p.1 ∧
      exteriorNorm K Sset p.1 ≤ 2 * CubeCompletionBlocks.scale j := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
  exact x.powerfulRows_window j k hk

theorem Data.movingRows_bound (x : Data K S σ) (j : ℕ) (p : Ext × Ext)
    (R : ℝ) (hrows : ∀ k ∈ x.rows, exteriorNorm K Sset k ≤ R)
    (a : Ext) (ha : a ∈ x.movingRows j p) : exteriorNorm K Sset a ≤ R := by
  have hm := (Finset.mem_filter.mp
    (reconstruct_mem K Sset x.label x.puncture (x.powerfulRows j) p a ha)).1
  have hn := hrows (reconstruct K Sset p a) (x.powerfulRows_subset j hm)
  rw [reconstruct_norm] at hn
  have hprod : 1 ≤ exteriorNorm K Sset p.1 * exteriorNorm K Sset p.2 :=
    one_le_mul_of_one_le_of_one_le (norm_one_le K S p.1) (norm_one_le K S p.2)
  calc
    exteriorNorm K Sset a = 1 * exteriorNorm K Sset a := (one_mul _).symm
    _ ≤ exteriorNorm K Sset p.1 * exteriorNorm K Sset p.2 * exteriorNorm K Sset a :=
      mul_le_mul_of_nonneg_right hprod (exteriorNorm_pos K Sset a).le
    _ ≤ R := hn

/-- Equality of the full canonical coefficient homomorphisms follows
from symbol equality on exterior ideals and their actual exterior zeros. -/
theorem canonicalTau_symbol_congr (D : ThetaArithmeticData K Sset)
    (θ : HeckeCharacter K) (m m' : (Sset).integer K) (r : Ideal (𝓞 K))
    (he : ∀ A : Ext, idealSymbol K Sset D A m = idealSymbol K Sset D A m') :
    canonicalTau K Sset D θ m r = canonicalTau K Sset D θ m' r := by
  ext I
  by_cases hI : HeckePort.CenteredMomentGenerator.IsExterior K Sset I
  · let A := HeckePort.CenteredMomentGenerator.toExterior K Sset I hI
    change canonicalTau K Sset D θ m r A.val.val = canonicalTau K Sset D θ m' r A.val.val
    rw [canonicalTau_apply, canonicalTau_apply, he]
  · rw [canonicalTau_eq_zero_of_not_exterior K Sset D θ m r I hI,
      canonicalTau_eq_zero_of_not_exterior K Sset D θ m' r I hI]

theorem totalRow_reconstruct (p : Ext × Ext) (a f : Ext) :
    TerminalReflection.totalRow K Sset (reconstruct K Sset p a) f =
      exteriorMul K Sset a (frozenIdeal K Sset p.1 p.2 f) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((p.1.val.val * p.2.val.val) * a.val.val) * f.val.val ^ 4 =
    a.val.val * ((p.1.val.val * p.2.val.val) * f.val.val ^ 4)
  ring

theorem Data.value_reconstruct (D : ThetaArithmeticData K Sset)
    (hD : AllowedGeneratorInput K Sset D) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ)
    (j : ℕ) (p : Ext × Ext) (l : ℕ) (a : Ext) :
    x.value D θ W Z (reconstruct K Sset p a) =
      (x.fiberData Z j p l).value D θ W Z a := by
  have he := canonicalTau_symbol_congr D θ
    ((((Sset).unitEquivUnitsInteger K x.unit).val * D.generator (reconstruct K Sset p a)) *
      D.generator x.label ^ 4)
    (((Sset).unitEquivUnitsInteger K x.unit).val *
      D.generator (exteriorMul K Sset a (frozenIdeal K Sset p.1 p.2 x.label)))
    x.puncture.val.val (fun A => by
      rw [TerminalReflection.canonical_row_symbol K Sset D hD, totalRow_reconstruct])
  simpa only [Data.value, Data.fiberData, TerminalFiber.Data.value,
    TerminalFiber.Data.frozen, he]

/-- Every generated fiber satisfies the genuine reflected-source
conditions. All arithmetic facts come from the actual decomposition. -/
theorem Data.fiberData_admissible (x : Data K S σ)
    {slotCap : ℕ} {Z A c z lo hi d : ℝ}
    (hx : x.Admissible slotCap Z A c z lo hi d) (hZ : 1 < Z)
    (j : ℕ) (p : Ext × Ext) (hp : p ∈ x.pairs j) (l : ℕ) :
    (x.fiberData Z j p l).Admissible slotCap Z A c z lo hi d := by
  have hj : Z ^ Real.logb Z (CubeCompletionBlocks.scale j) = CubeCompletionBlocks.scale j :=
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (CubeCompletionBlocks.scale_pos j)
  have hl : Z ^ Real.logb Z (CubeCompletionBlocks.scale l) = CubeCompletionBlocks.scale l :=
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (CubeCompletionBlocks.scale_pos l)
  refine
    { powerful := (frozenPairs_spec K Sset x.label x.puncture (x.powerfulRows j) p hp).1
      column_nonneg := hx.column_nonneg
      label_nonneg := hx.label_nonneg
      row_nonneg := hx.row_nonneg
      puncture_nonneg := hx.puncture_nonneg
      powerful_nonneg := Real.logb_nonneg hZ (CubeCompletionBlocks.scale_one_le j)
      residual_nonneg := Real.logb_nonneg hZ (CubeCompletionBlocks.scale_one_le l)
      completion_nonneg := hx.completion_nonneg
      completion_le := hx.completion_le
      total_le := hx.total_le
      label_small := hx.label_small
      label_bound := hx.label_bound
      puncture_bound := hx.puncture_bound
      powerful_bound := by simpa only [Data.fiberData, hj] using (x.pair_powerful_window j p hp).1
      row_bound := ?_
      residual_window := ?_
      residual_squarefree := ?_
      residual_coprime_frozen := ?_
      residual_coprime_puncture := ?_
      marks := hx.marks
      margins := hx.margins }
  · intro a ha
    have ham := (Finset.mem_filter.mp ha).1
    exact hx.row_bound (reconstruct K Sset p a) (x.powerfulRows_subset j
      (Finset.mem_filter.mp
        (reconstruct_mem K Sset x.label x.puncture (x.powerfulRows j) p a ham)).1)
  · intro a ha
    have hw := CubeCompletionBlocks.block_window (x.movingRows j p)
      (exteriorNorm K Sset) l (fun a ha => norm_one_le K S a) a ha
    simpa only [Data.fiberData, InAnnulus, hl] using hw
  · intro a ha
    exact residualRows_squarefree K Sset x.label x.puncture (x.powerfulRows j) p a
      (Finset.mem_filter.mp ha).1
  · intro a ha
    exact residualRows_coprime_frozen K Sset x.label x.puncture (x.powerfulRows j) p a
      (Finset.mem_filter.mp ha).1
  · intro a ha
    exact residualRows_coprime_puncture K Sset x.label x.puncture (x.powerfulRows j) p a
      (Finset.mem_filter.mp ha).1

/-- Exact disjoint decomposition of the original positive row energy.
There is no norm or absolute-value estimate in this identity. -/
theorem Data.energy_eq_fibers (D : ThetaArithmeticData K Sset)
    (hD : AllowedGeneratorInput K Sset D) (θ : HeckeCharacter K)
    (x : Data K S σ) (W : SchwartzMap ℝ ℂ) (Z : ℝ)
    (hrows : ∀ k ∈ x.rows, exteriorNorm K Sset k ≤ Z ^ x.rowLength) :
    x.energy D θ W Z =
      ∑ j ∈ Finset.range (CubeCompletionBlocks.count (Z ^ x.rowLength)),
        ∑ p ∈ x.pairs j,
          ∑ l ∈ Finset.range (CubeCompletionBlocks.count (Z ^ x.rowLength)),
            (x.fiberData Z j p l).energy D θ W Z := by
  unfold Data.energy
  rw [CubeCompletionBlocks.sum_eq_blocks x.rows
    (fun k => exteriorNorm K Sset (exteriorPowerfulPart K Sset k)) (Z ^ x.rowLength)
    (fun k hk => norm_one_le K S _) (fun k hk => (powerful_norm_le K S k).trans (hrows k hk))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sum_rows_eq_pairs_residualRows K Sset x.label x.puncture (x.powerfulRows j)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [CubeCompletionBlocks.sum_eq_blocks (x.movingRows j p) (exteriorNorm K Sset)
    (Z ^ x.rowLength) (fun a ha => norm_one_le K S a)
    (x.movingRows_bound j p _ hrows)]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro a ha
  rw [x.value_reconstruct D hD θ W Z j p l a]

theorem scale_le_of_lt_count (R : ℝ) (hR : 1 ≤ R) (j : ℕ)
    (hj : j < CubeCompletionBlocks.count R) : CubeCompletionBlocks.scale j ≤ R := by
  have hjn : j ≤ CubeCompletionBlocks.index R := Nat.lt_succ_iff.mp hj
  have hjr : (j : ℝ) ≤ (CubeCompletionBlocks.index R : ℝ) := by exact_mod_cast hjn
  calc
    CubeCompletionBlocks.scale j = (2 : ℝ) ^ (j : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (CubeCompletionBlocks.index R : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hjr
    _ = CubeCompletionBlocks.scale (CubeCompletionBlocks.index R) := Real.rpow_natCast _ _
    _ ≤ R := (CubeCompletionBlocks.norm_window R hR).1

theorem sqrt_scale_eq (Z : ℝ) (hZ : 1 < Z) (j : ℕ) :
    Real.sqrt (2 * CubeCompletionBlocks.scale j) =
      Real.sqrt 2 * Z ^ (Real.logb Z (CubeCompletionBlocks.scale j) / 2) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  calc
    Real.sqrt (CubeCompletionBlocks.scale j) =
        Real.sqrt (Z ^ Real.logb Z (CubeCompletionBlocks.scale j)) := by
      rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
        (CubeCompletionBlocks.scale_pos j)]
    _ = Z ^ (Real.logb Z (CubeCompletionBlocks.scale j) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (zero_lt_one.trans hZ).le]
      congr 1
      ring

/-- The finite frozen-pair count at its actual powerful dyad. The
displayed square-root exponent will cancel the reflected fiber saving. -/
theorem Data.pair_count_bound (x : Data K S σ)
    {slotCap : ℕ} {Z A c z lo hi d delta C : ℝ}
    (hx : x.Admissible slotCap Z A c z lo hi d) (hZ : 1 < Z)
    (hdelta : 0 ≤ delta) (hC : 0 ≤ C)
    (hcount : ∀ (f r : Ext) (U : ℝ), 1 ≤ U → ∀ rows : Finset Ext,
      (∀ k ∈ rows, exteriorNorm K Sset (exteriorPowerfulPart K Sset k) ≤ U) →
      ((frozenPairs K Sset f r rows).card : ℝ) ≤ C * Real.sqrt U *
        (U * exteriorNorm K Sset f * exteriorNorm K Sset r) ^ delta)
    (j : ℕ) (hj : j < CubeCompletionBlocks.count (Z ^ x.rowLength)) :
    ((x.pairs j).card : ℝ) ≤ (C * Real.sqrt 2 * (2 : ℝ) ^ delta) *
      Z ^ (Real.logb Z (CubeCompletionBlocks.scale j) / 2 +
        (x.rowLength + x.labelLength + x.punctureLength) * delta) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hR : 1 ≤ Z ^ x.rowLength := Real.one_le_rpow hZ.le hx.row_nonneg
  have hs := scale_le_of_lt_count (Z ^ x.rowLength) hR j hj
  have hU : 1 ≤ 2 * CubeCompletionBlocks.scale j := by
    linarith [CubeCompletionBlocks.scale_one_le j]
  have hp := hcount x.label x.puncture (2 * CubeCompletionBlocks.scale j) hU
    (x.powerfulRows j) (fun k hk => (x.powerfulRows_window j k hk).2)
  have hi : 2 * CubeCompletionBlocks.scale j * exteriorNorm K Sset x.label *
        exteriorNorm K Sset x.puncture ≤
      2 * Z ^ (x.rowLength + x.labelLength + x.punctureLength) := by
    calc
      _ ≤ (2 * Z ^ x.rowLength) * Z ^ x.labelLength * Z ^ x.punctureLength := by
        apply mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hx.label_bound
            (exteriorNorm_pos K Sset x.label).le (by positivity)) hx.puncture_bound
          (exteriorNorm_pos K Sset x.puncture).le (by positivity)
      _ = _ := by rw [Real.rpow_add hZp, Real.rpow_add hZp]; ring
  have hipow := Real.rpow_le_rpow (by positivity) hi hdelta
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (Real.rpow_nonneg hZp.le _), ← Real.rpow_mul hZp.le] at hipow
  calc
    _ ≤ C * Real.sqrt (2 * CubeCompletionBlocks.scale j) *
        (2 * CubeCompletionBlocks.scale j * exteriorNorm K Sset x.label *
          exteriorNorm K Sset x.puncture) ^ delta := hp
    _ ≤ C * Real.sqrt (2 * CubeCompletionBlocks.scale j) *
        ((2 : ℝ) ^ delta *
          Z ^ ((x.rowLength + x.labelLength + x.punctureLength) * delta)) :=
      mul_le_mul_of_nonneg_left hipow (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = _ := by rw [sqrt_scale_eq Z hZ j, Real.rpow_add hZp]; ring

variable (K S) (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- A uniform estimate for the literal completed marked source over
all original exterior rows. The constants and finite Schwartz family
precede every original row, label, mark coefficient and profile.

The only analytic input is the proved reflected-energy input used to
construct `TerminalFiber.exists_uniform_energy`; no canonical moment
bound or fiber estimate is assumed here. -/
theorem exists_uniform_completed_energy
    (hD : AllowedGeneratorInput K Sset D)
    (backgrounds : Finset (HeckeCharacter K))
    (R : ReflectionFamily K Sset D backgrounds) (hE : Input K Sset D R.data backgrounds)
    (slotCap : ℕ) (A cstar lo hi : ℝ) (hA : 1 ≤ A) (hcstar : 0 < cstar)
    (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ q : Finset (ℕ × ℕ), ∃ C Z₀ : ℝ, 1 ≤ C ∧ 2 ≤ Z₀ ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      ∀ {σ : Type*} (Z c z d : ℝ) (x : Data K S σ) (W : SchwartzMap ℝ ℂ),
      Z₀ ≤ Z → cstar ≤ c → 0 ≤ z → z ≤ A → 0 < d → d ≤ cstar / 1000 →
      x.Admissible slotCap Z A c z lo hi d → tsupport W ⊆ Set.Icc (1 : ℝ) 2 →
      x.energy D θ W Z ≤ C * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) ^ 2 *
        Z ^ (x.totalLength - cstar / 32) := by
  obtain ⟨q, CF, Z₀, hCF, hZ₀, hfiber⟩ := TerminalFiber.exists_uniform_energy
    K S D backgrounds R hE slotCap A cstar lo hi hA hcstar hlo hhi
  let delta := cstar / (128 * (A + 1))
  have hdelta : 0 < delta := div_pos hcstar (by positivity)
  obtain ⟨CP, hCP, hpairs⟩ := exists_frozen_pair_count K Sset delta hdelta
  obtain ⟨CD, hCD, hdyads⟩ := CubeCompletionBlocks.exists_count_small_power delta hdelta
  let Cbase := CF * CP * Real.sqrt 2 * (2 : ℝ) ^ delta
  let C := CD ^ 2 * Cbase
  have hCbase : 0 ≤ Cbase := by dsimp only [Cbase]; positivity
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hCbase
  refine ⟨q, max 1 C, Z₀, le_max_left _ _, hZ₀, ?_⟩
  intro θ hθ σ Z c z d x W hZ hc hz hzA hd hdsmall hx hW
  have hZ1 : 1 < Z := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hZ₀.trans hZ)
  have hZp : 0 < Z := zero_lt_one.trans hZ1
  have hrow1 : 1 ≤ Z ^ x.rowLength := Real.one_le_rpow hZ1.le hx.row_nonneg
  have hM : x.rowLength ≤ A := by
    have hm := hx.margins.1
    have ht := hx.total_le
    linarith [hx.puncture_nonneg]
  have hV : x.labelLength ≤ A := by
    have ht := hx.total_le
    change x.columnLength + x.labelLength ≤ A at ht
    linarith [hx.column_nonneg]
  have hMQ : x.rowLength + x.punctureLength ≤ A := by
    have hm := hx.margins.1
    linarith [hx.total_le]
  have hcost : (x.rowLength + x.labelLength + x.punctureLength + 2 * x.rowLength) * delta ≤
      cstar / 32 := by
    have hlen : x.rowLength + x.labelLength + x.punctureLength + 2 * x.rowLength ≤
        4 * (A + 1) := by linarith
    have hm := mul_le_mul_of_nonneg_right hlen hdelta.le
    have he : 4 * (A + 1) * delta = cstar / 32 := by
      dsimp only [delta]
      field_simp [show A + 1 ≠ 0 by linarith]
      <;> ring
    exact hm.trans_eq he
  let n := CubeCompletionBlocks.count (Z ^ x.rowLength)
  let qW := q.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hqW : 0 ≤ qW := apply_nonneg _ _
  have hcount : (n : ℝ) ^ 2 ≤ CD ^ 2 * Z ^ (2 * x.rowLength * delta) := by
    have hb := pow_le_pow_left₀ (Nat.cast_nonneg _)
      (hdyads (Z ^ x.rowLength) hrow1) 2
    rw [mul_pow, ← Real.rpow_mul_natCast (Real.rpow_nonneg hZp.le _),
      ← Real.rpow_mul hZp.le] at hb
    simpa only [n, mul_assoc, mul_left_comm, mul_comm] using hb
  have hblock (j : ℕ) (hj : j ∈ Finset.range n) :
      (∑ p ∈ x.pairs j, ∑ l ∈ Finset.range n,
        (x.fiberData Z j p l).energy D θ W Z) ≤
      (n : ℝ) * Cbase * qW ^ 2 *
        Z ^ (x.totalLength - cstar / 16 +
          (x.rowLength + x.labelLength + x.punctureLength) * delta) := by
    let O := Real.logb Z (CubeCompletionBlocks.scale j)
    let B := CF * qW ^ 2 * Z ^ (x.totalLength - cstar / 16 - O / 2)
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    have hp := x.pair_count_bound hx hZ1 hdelta.le (zero_le_one.trans hCP) hpairs j
      (Finset.mem_range.mp hj)
    have hf (p : Ext × Ext) (hp : p ∈ x.pairs j) (l : ℕ) :
        (x.fiberData Z j p l).energy D θ W Z ≤ B := by
      exact hfiber θ hθ Z c z d (x.fiberData Z j p l) W hZ hc hz hzA hd hdsmall
        (x.fiberData_admissible hx hZ1 j p hp l) hW
    calc
      _ ≤ ∑ p ∈ x.pairs j, ∑ l ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun l hl => hf p hp l))
      _ = ((x.pairs j).card : ℝ) * (n : ℝ) * B := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      _ ≤ ((CP * Real.sqrt 2 * (2 : ℝ) ^ delta) *
          Z ^ (O / 2 + (x.rowLength + x.labelLength + x.punctureLength) * delta)) *
          (n : ℝ) * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) hB
      _ = _ := by
        dsimp only [B, Cbase]
        calc
          _ = (n : ℝ) * (CF * CP * Real.sqrt 2 * (2 : ℝ) ^ delta) * qW ^ 2 *
              (Z ^ (O / 2 + (x.rowLength + x.labelLength + x.punctureLength) * delta) *
                Z ^ (x.totalLength - cstar / 16 - O / 2)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hZp]
            congr 2
            ring
  calc
    x.energy D θ W Z = ∑ j ∈ Finset.range n, ∑ p ∈ x.pairs j,
        ∑ l ∈ Finset.range n, (x.fiberData Z j p l).energy D θ W Z :=
      x.energy_eq_fibers D hD θ W Z hx.row_bound
    _ ≤ ∑ j ∈ Finset.range n, (n : ℝ) * Cbase * qW ^ 2 *
        Z ^ (x.totalLength - cstar / 16 +
          (x.rowLength + x.labelLength + x.punctureLength) * delta) :=
      Finset.sum_le_sum hblock
    _ = (n : ℝ) ^ 2 * Cbase * qW ^ 2 *
        Z ^ (x.totalLength - cstar / 16 +
          (x.rowLength + x.labelLength + x.punctureLength) * delta) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ (CD ^ 2 * Z ^ (2 * x.rowLength * delta)) * Cbase * qW ^ 2 *
        Z ^ (x.totalLength - cstar / 16 +
          (x.rowLength + x.labelLength + x.punctureLength) * delta) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcount hCbase) (sq_nonneg _))
        (Real.rpow_nonneg hZp.le _)
    _ = C * qW ^ 2 * Z ^ (x.totalLength - cstar / 16 +
        (x.rowLength + x.labelLength + x.punctureLength + 2 * x.rowLength) * delta) := by
      dsimp only [C]
      calc
        _ = (CD ^ 2 * Cbase) * qW ^ 2 * (Z ^ (2 * x.rowLength * delta) *
            Z ^ (x.totalLength - cstar / 16 +
              (x.rowLength + x.labelLength + x.punctureLength) * delta)) := by ring
        _ = _ := by rw [← Real.rpow_add hZp]; congr 2; ring
    _ ≤ C * qW ^ 2 * Z ^ (x.totalLength - cstar / 32) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
        (mul_nonneg hC (sq_nonneg _))
    _ ≤ max 1 C * qW ^ 2 * Z ^ (x.totalLength - cstar / 32) := by
      gcongr
      exact le_max_right (1 : ℝ) C

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalRows

end
