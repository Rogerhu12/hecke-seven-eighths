import HeckeSkeleton.LowEnergy.GeneralKernelTail
import HeckeSkeleton.LowEnergy.GeneralReconstruction
import HeckeSkeleton.LowEnergy.ActualDyadicReflection
import HeckeSkeleton.LowEnergy.DyadicTail

/-!
# Exact finite dual-annulus projection and the actual discarded tail

The full squarefree/full-cube series is absolutely summable by the
proved kernel majorant.  A finite set of complete ratio-two rectangles
is retained before taking any norm.  The complement is a literal zero
extension of the same summands, and is bounded by the actual kernel tail.
The retained rectangles are selected from their real norm endpoints;
no reconstruction or convergence estimate is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralColumnCutoff

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.ActualDyadicReflection
open HeckeSkeleton.LowEnergy.GeneralReflectedBlock
open HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
open HeckeSkeleton.LowEnergy.GeneralKernelTail
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open HeckeSkeleton.LowEnergy.LogGeometry
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

private theorem baseScale_pos (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) {X : ℝ} (hX : 0 < X) :
    0 < baseScale K S f s X :=
  div_pos (mul_pos hX (exteriorNorm_pos K S s.minimum))
    (sq_pos_of_pos (exteriorNorm_pos K S (primeSetIdeal K S s.active)))

theorem argument_minimum (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture) {X : ℝ} (hX : 0 < X)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    baseScale K S f s X / (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2) ≤
      CommonMellin.argument (baseScale K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S cb.1) (exteriorNorm K S cb.2) := by
  have hbase := baseScale_pos K S f s hX
  have hc := exteriorNorm_one_le K S cb.1
  have hb := one_le_pow₀ (exteriorNorm_one_le K S cb.2) (n := 3)
  have hn : baseScale K S f s X ≤ baseScale K S f s X *
      exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3 := by
    calc
      _ ≤ baseScale K S f s X * exteriorNorm K S cb.1 :=
        le_mul_of_one_le_right hbase.le hc
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb
  exact div_le_div_of_nonneg_right hn (by positivity)

/-- The complete actual column series, without a separately supplied
summability hypothesis. -/
theorem column_norm_summable (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
    (X : ℝ) (hX : 0 < X) (k P : ExteriorIdeal K S) :
    Summable (fun cb => ‖columnAtom K S D f s F θ q V.toFun X k P cb‖) := by
  obtain ⟨J, C, hC, hb⟩ := actual_column_tail K S D F θ hKernel hθ hD 1 le_rfl
  let T := baseScale K S f s X / (exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2)
  have hT : 0 < T := by
    dsimp [T]
    exact div_pos (baseScale_pos K S f s hX)
      (mul_pos (sq_pos_of_pos (exteriorNorm_pos K S k))
        (sq_pos_of_pos (exteriorNorm_pos K S P)))
  have h := (hb V q f s X T k P hX hT).1
  have he (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      tailColumnAtom K S D f s F θ q V.toFun X T k P cb =
        columnAtom K S D f s F θ q V.toFun X k P cb :=
    if_pos (argument_minimum K S f s hX k P cb)
  simpa only [he] using h

def columnIndex (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℕ × ℕ :=
  (DyadicReindex.index (idealNatNorm K S) cb.1,
    DyadicReindex.index (idealNatNorm K S) cb.2)

def columnShell (p : ℕ × ℕ) : Finset (ExteriorIdeal K S × ExteriorIdeal K S) :=
  idealShell K S p.1 ×ˢ idealShell K S p.2

@[simp] theorem mem_columnShell (p : ℕ × ℕ)
    (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    cb ∈ columnShell K S p ↔ columnIndex K S cb = p := by
  rcases p with ⟨j, l⟩
  simp only [columnShell, Finset.mem_product, idealShell, DyadicReindex.mem_shell,
    columnIndex, Prod.mk.injEq]

def selectedColumns (annuli : Finset (ℕ × ℕ)) :
    Finset (ExteriorIdeal K S × ExteriorIdeal K S) :=
  annuli.biUnion (columnShell K S)

@[simp] theorem mem_selectedColumns (annuli : Finset (ℕ × ℕ))
    (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    cb ∈ selectedColumns K S annuli ↔ columnIndex K S cb ∈ annuli := by
  simp only [selectedColumns, Finset.mem_biUnion, mem_columnShell]
  constructor
  · rintro ⟨p, hp, he⟩
    exact he.symm ▸ hp
  · intro h
    exact ⟨_, h, rfl⟩

theorem sum_selectedColumns (annuli : Finset (ℕ × ℕ))
    (a : ExteriorIdeal K S × ExteriorIdeal K S → ℂ) :
    (∑ cb ∈ selectedColumns K S annuli, a cb) =
      ∑ p ∈ annuli, ∑ c ∈ idealShell K S p.1, ∑ b ∈ idealShell K S p.2, a (c, b) := by
  have hdis : Set.PairwiseDisjoint (↑annuli) (columnShell K S) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro cb hcp hcq
    exact hpq (((mem_columnShell K S p cb).mp hcp).symm.trans
      ((mem_columnShell K S q cb).mp hcq))
  rw [selectedColumns, Finset.sum_biUnion hdis]
  simp only [columnShell, Finset.sum_product]

/-- Endpoint product of the two complete column annuli. -/
def dyadProduct (p : ℕ × ℕ) : ℝ := (2 : ℝ) ^ p.1 * ((2 : ℝ) ^ p.2) ^ 3

def annuliBelow (R : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.range (DyadicReindex.shellCount (max 1 R))) ×ˢ
    Finset.range (DyadicReindex.shellCount (max 1 R))).filter (fun p => dyadProduct p < R)

private theorem pow_lt_radius_index {R : ℝ} {j : ℕ} (hj : (2 : ℝ) ^ j < R) :
    j < DyadicReindex.shellCount (max 1 R) := by
  have hpow : (2 : ℕ) ^ j ≤ ⌊max 1 R⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast (hj.le.trans (le_max_right 1 R))
  exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide) hpow)

@[simp] theorem mem_annuliBelow (R : ℝ) (p : ℕ × ℕ) :
    p ∈ annuliBelow R ↔ dyadProduct p < R := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have ha : (1 : ℝ) ≤ 2 ^ p.1 := one_le_pow₀ (by norm_num)
    have hb : (1 : ℝ) ≤ 2 ^ p.2 := one_le_pow₀ (by norm_num)
    have hb3 : (2 : ℝ) ^ p.2 ≤ ((2 : ℝ) ^ p.2) ^ 3 := by
      calc
        _ ≤ (2 : ℝ) ^ p.2 * ((2 : ℝ) ^ p.2) ^ 2 :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ hb)
        _ = _ := by ring
    have hleft : (2 : ℝ) ^ p.1 ≤ dyadProduct p :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hb)
    have hright : (2 : ℝ) ^ p.2 ≤ dyadProduct p := hb3.trans
      (le_mul_of_one_le_left (by positivity) ha)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (pow_lt_radius_index (hleft.trans_lt h)),
        Finset.mem_range.mpr (pow_lt_radius_index (hright.trans_lt h))⟩, h⟩

theorem annuliBelow_card_le (R : ℝ) :
    ((annuliBelow R).card : ℝ) ≤ (Real.log (max 1 R) / Real.log 2 + 1) ^ 2 := by
  have hc : (annuliBelow R).card ≤ DyadicReindex.shellCount (max 1 R) ^ 2 := by
    have h := Finset.card_filter_le
      (s := Finset.range (DyadicReindex.shellCount (max 1 R)) ×ˢ
        Finset.range (DyadicReindex.shellCount (max 1 R))) (p := fun p => dyadProduct p < R)
    simpa only [annuliBelow, Finset.card_product, Finset.card_range, pow_two] using h
  have hreal : ((annuliBelow R).card : ℝ) ≤ (DyadicReindex.shellCount (max 1 R) : ℝ) ^ 2 := by
    exact_mod_cast hc
  exact hreal.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (DyadicReindex.shellCount_le_log (le_max_left 1 R)) 2)

/-- The squared number of retained dual blocks is a small power, with
the constant selected before the scale and the actual cutoff radius. -/
theorem annuliBelow_count_small_power (B eps : ℝ) (hB : 0 ≤ B) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z R : ℝ, 1 ≤ Z → R ≤ Z ^ B →
      ((annuliBelow R).card : ℝ) ^ 2 ≤ C * Z ^ eps := by
  let a := B / Real.log 2 + 1
  let c := a ^ 2 * (1 + 2 / (eps / 2)) ^ 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have ha : 0 < a := by
    dsimp [a]
    linarith [div_nonneg hB hlog2.le]
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c ^ 2, sq_pos_of_pos hc, ?_⟩
  intro Z R hZ hR
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hmax : max 1 R ≤ Z ^ B := max_le (Real.one_le_rpow hZ hB) hR
  have hlog : Real.log (max 1 R) ≤ B * Real.log Z := by
    have h := Real.log_le_log (zero_lt_one.trans_le (le_max_left 1 R)) hmax
    simpa only [Real.log_rpow hZp] using h
  have hendpoint : Real.log (max 1 R) / Real.log 2 + 1 ≤ a * (1 + Real.log Z) := by
    have hh : Real.log (max 1 R) / Real.log 2 ≤ B / Real.log 2 * Real.log Z := by
      calc
        _ ≤ (B * Real.log Z) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog hlog2.le
        _ = _ := by ring
    calc
      _ ≤ B / Real.log 2 * Real.log Z + 1 := add_le_add hh (le_refl 1)
      _ ≤ B / Real.log 2 * Real.log Z + 1 + (B / Real.log 2 + Real.log Z) :=
        le_add_of_nonneg_right (add_nonneg (div_nonneg hB hlog2.le) hlogZ)
      _ = _ := by dsimp [a]; ring
  have hendpoint0 : 0 ≤ Real.log (max 1 R) / Real.log 2 + 1 := by
    have hh := Real.log_nonneg (le_max_left 1 R)
    positivity
  have hcount : ((annuliBelow R).card : ℝ) ≤ c * Z ^ (eps / 2) := by
    calc
      _ ≤ (Real.log (max 1 R) / Real.log 2 + 1) ^ 2 := annuliBelow_card_le R
      _ ≤ (a * (1 + Real.log Z)) ^ 2 := pow_le_pow_left₀ hendpoint0 hendpoint 2
      _ = a ^ 2 * (1 + Real.log Z) ^ 2 := mul_pow _ _ _
      _ ≤ a ^ 2 * ((1 + 2 / (eps / 2)) ^ 2 * Z ^ (eps / 2)) :=
        mul_le_mul_of_nonneg_left (DyadicTail.log_square_small_power hZ (by linarith))
          (sq_nonneg _)
      _ = c * Z ^ (eps / 2) := by dsimp [c]; ring
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  apply hsq.trans_eq
  rw [mul_pow, ← Real.rpow_mul_natCast hZp.le]
  congr 1
  congr 1
  ring

/-- The dyadic cutoff is chosen from common row/mark endpoints, hence is
independent of the actual row and mark inside the ratio-two box. -/
def cutoffRadius (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo T : ℝ) : ℝ :=
  16 * T * (Klo ^ 2 * Plo ^ 2) / baseScale K S f s X

def retainedAnnuli (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo T : ℝ) : Finset (ℕ × ℕ) :=
  annuliBelow (cutoffRadius K S f s X Klo Plo T)

/-- The cutoff radius has a fixed polynomial budget obtained directly
from the actual lengths.  No bound on a reflected series enters it. -/
theorem cutoffRadius_le_from_lengths (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    {Z X Klo Plo Hmax Pmax Amax Nmax tau : ℝ}
    (hZ : 1 < Z) (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo)
    (hlarge : 16 ≤ Z ^ (tau / 2))
    (hk : Klo ≤ Z ^ Hmax) (hp : Plo ≤ Z ^ Pmax)
    (ha : exteriorNorm K S (primeSetIdeal K S s.active) ≤ Z ^ Amax)
    (hx : Z ^ (-Nmax) ≤ X) :
    cutoffRadius K S f s X Klo Plo (Z ^ (tau / 2)) ≤
      Z ^ (tau + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hm := exteriorNorm_pos K S s.minimum
  have hm1 := exteriorNorm_one_le K S s.minimum
  have ha0 := exteriorNorm_pos K S (primeSetIdeal K S s.active)
  have hnum : Klo ^ 2 * Plo ^ 2 * exteriorNorm K S (primeSetIdeal K S s.active) ^ 2 ≤
      (Z ^ Hmax) ^ 2 * (Z ^ Pmax) ^ 2 * (Z ^ Amax) ^ 2 := by
    exact mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ hK.le hk 2) (pow_le_pow_left₀ hP.le hp 2)
        (sq_nonneg _) (by positivity))
      (pow_le_pow_left₀ ha0.le ha 2) (sq_nonneg _) (by positivity)
  have hratio : (Klo ^ 2 * Plo ^ 2) / baseScale K S f s X ≤
      Z ^ (2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) := by
    calc
      _ = (Klo ^ 2 * Plo ^ 2 * exteriorNorm K S (primeSetIdeal K S s.active) ^ 2) /
          (X * exteriorNorm K S s.minimum) := by
        unfold baseScale
        field_simp [hX.ne', hm.ne', ha0.ne']
        <;> ring
      _ ≤ (Klo ^ 2 * Plo ^ 2 * exteriorNorm K S (primeSetIdeal K S s.active) ^ 2) / X :=
        div_le_div_of_nonneg_left (by positivity) hX (le_mul_of_one_le_right hX.le hm1)
      _ ≤ ((Z ^ Hmax) ^ 2 * (Z ^ Pmax) ^ 2 * (Z ^ Amax) ^ 2) / Z ^ (-Nmax) :=
        div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hZp _) hx
      _ = _ := by
        rw [← Real.rpow_mul_natCast hZp.le, ← Real.rpow_mul_natCast hZp.le,
          ← Real.rpow_mul_natCast hZp.le, ← Real.rpow_add hZp,
          ← Real.rpow_add hZp, ← Real.rpow_sub hZp]
        congr 1
        ring
  have hthreshold : 16 * Z ^ (tau / 2) ≤ Z ^ tau := by
    calc
      _ ≤ Z ^ (tau / 2) * Z ^ (tau / 2) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add hZp]; congr 1 <;> ring
  have hbase := baseScale_pos K S f s hX
  calc
    _ = (16 * Z ^ (tau / 2)) * ((Klo ^ 2 * Plo ^ 2) / baseScale K S f s X) := by
      unfold cutoffRadius
      ring
    _ ≤ Z ^ tau * Z ^ (2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) :=
      mul_le_mul hthreshold hratio (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZp]; congr 1 <;> ring

theorem retainedAnnuli_count_small_power
    (Hmax Pmax Amax Nmax tau eps : ℝ)
    (hH : 0 ≤ Hmax) (hPmax : 0 ≤ Pmax) (hA : 0 ≤ Amax) (hN : 0 ≤ Nmax)
    (htau : 0 ≤ tau) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z X Klo Plo : ℝ)
      (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture),
      1 < Z → 0 < X → 0 < Klo → 0 < Plo → 16 ≤ Z ^ (tau / 2) →
      Klo ≤ Z ^ Hmax → Plo ≤ Z ^ Pmax →
      exteriorNorm K S (primeSetIdeal K S s.active) ≤ Z ^ Amax →
      Z ^ (-Nmax) ≤ X →
      ((retainedAnnuli K S f s X Klo Plo (Z ^ (tau / 2))).card : ℝ) ^ 2 ≤ C * Z ^ eps := by
  obtain ⟨C, hC, hb⟩ := annuliBelow_count_small_power
    (tau + 2 * Hmax + 2 * Pmax + 2 * Amax + Nmax) eps (by positivity) heps
  refine ⟨C, hC, ?_⟩
  intro Z X Klo Plo f s hZ hX hK hP hlarge hk hp ha hx
  exact hb Z _ hZ.le
    (cutoffRadius_le_from_lengths K S f s hZ hX hK hP hlarge hk hp ha hx)

theorem outside_retained_argument (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (X Klo Plo T : ℝ) (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo)
    (k P : ExteriorIdeal K S)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2)
    (cb : ExteriorIdeal K S × ExteriorIdeal K S)
    (hout : columnIndex K S cb ∉ retainedAnnuli K S f s X Klo Plo T) :
    T ≤ CommonMellin.argument (baseScale K S f s X)
      (exteriorNorm K S k) (exteriorNorm K S P)
      (exteriorNorm K S cb.1) (exteriorNorm K S cb.2) := by
  let p := columnIndex K S cb
  have hbelow : cutoffRadius K S f s X Klo Plo T ≤ dyadProduct p :=
    le_of_not_gt (fun h => hout ((mem_annuliBelow _ _).mpr h))
  have hc := DyadicReindex.index_bounds_real (idealNatNorm K S) (idealNatNorm_pos K S cb.1)
  have hb := DyadicReindex.index_bounds_real (idealNatNorm K S) (idealNatNorm_pos K S cb.2)
  have hc0 : (2 : ℝ) ^ p.1 ≤ exteriorNorm K S cb.1 := hc.1
  have hb0 : (2 : ℝ) ^ p.2 ≤ exteriorNorm K S cb.2 := hb.1
  have hbase := baseScale_pos K S f s hX
  have hn : baseScale K S f s X * dyadProduct p ≤
      baseScale K S f s X * exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3 := by
    have h := mul_le_mul hc0 (pow_le_pow_left₀ (by positivity) hb0 3)
      (by positivity) (exteriorNorm_pos K S cb.1).le
    exact (mul_le_mul_of_nonneg_left h hbase.le).trans_eq (by ring)
  have hden : exteriorNorm K S k ^ 2 * exteriorNorm K S P ^ 2 ≤
      16 * (Klo ^ 2 * Plo ^ 2) := by
    have hk : exteriorNorm K S k ≤ 2 * Klo := (div_le_iff₀ hK).mp hk1
    have hp : exteriorNorm K S P ≤ 2 * Plo := (div_le_iff₀ hP).mp hp1
    have h := mul_le_mul
      (pow_le_pow_left₀ (exteriorNorm_pos K S k).le hk 2)
      (pow_le_pow_left₀ (exteriorNorm_pos K S P).le hp 2)
      (sq_nonneg _) (by positivity)
    convert h using 1 <;> ring
  have htarget : 16 * T * (Klo ^ 2 * Plo ^ 2) ≤
      baseScale K S f s X * dyadProduct p := by
    change 16 * T * (Klo ^ 2 * Plo ^ 2) / baseScale K S f s X ≤
      dyadProduct p at hbelow
    have h := (div_le_iff₀ hbase).mp hbelow
    simpa only [mul_comm (dyadProduct p)] using h
  by_cases hT : 0 ≤ T
  · apply (le_div_iff₀
      (mul_pos (sq_pos_of_pos (exteriorNorm_pos K S k))
        (sq_pos_of_pos (exteriorNorm_pos K S P)))).mpr
    have ht : T * (16 * (Klo ^ 2 * Plo ^ 2)) ≤
        baseScale K S f s X * dyadProduct p := by
      convert htarget using 1 <;> ring
    exact (mul_le_mul_of_nonneg_left hden hT).trans (ht.trans hn)
  · exact (lt_of_not_ge hT).le.trans (CommonMellin.argument_pos hbase
      (exteriorNorm_pos K S k) (exteriorNorm_pos K S P)
      (exteriorNorm_pos K S cb.1) (exteriorNorm_pos K S cb.2)).le

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

def discardedColumn (annuli : Finset (ℕ × ℕ))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  if columnIndex K S cb ∈ annuli then 0 else columnAtom K S D f s F θ q V X k P cb

theorem discarded_norm_le (annuli : Finset (ℕ × ℕ))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    ‖discardedColumn K S D f s annuli F θ q V X k P cb‖ ≤
      ‖columnAtom K S D f s F θ q V X k P cb‖ := by
  unfold discardedColumn
  split_ifs <;> simp

/-- Exact finite-annulus projection of the complete actual column series. -/
theorem column_series_decomposition
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
    (X : ℝ) (hX : 0 < X) (k P : ExteriorIdeal K S) (annuli : Finset (ℕ × ℕ)) :
    Summable (fun cb => ‖discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖) ∧
      (∑' cb, columnAtom K S D f s F θ q V.toFun X k P cb) =
        (∑ p ∈ annuli, ∑ c ∈ idealShell K S p.1, ∑ b ∈ idealShell K S p.2,
          columnAtom K S D f s F θ q V.toFun X k P (c, b)) +
        ∑' cb, discardedColumn K S D f s annuli F θ q V.toFun X k P cb := by
  have hn := column_norm_summable K S D F θ hKernel hθ hD f s q V X hX k P
  have hd := hn.of_nonneg_of_le (fun cb => norm_nonneg _)
    (discarded_norm_le K S D f s annuli F θ q V.toFun X k P)
  refine ⟨hd, ?_⟩
  let a := fun cb => if columnIndex K S cb ∈ annuli
    then columnAtom K S D f s F θ q V.toFun X k P cb else 0
  have ha : Summable a := hn.of_norm_bounded (fun cb => by
    dsimp [a]
    split_ifs <;> simp)
  have he (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      columnAtom K S D f s F θ q V.toFun X k P cb =
        a cb + discardedColumn K S D f s annuli F θ q V.toFun X k P cb := by
    dsimp [a, discardedColumn]
    split_ifs <;> simp
  have hfinite : (∑' cb, a cb) = ∑ cb ∈ selectedColumns K S annuli,
      columnAtom K S D f s F θ q V.toFun X k P cb := by
    rw [tsum_eq_sum (s := selectedColumns K S annuli)
      (fun cb hcb => by dsimp [a]; rw [if_neg (by simpa only [mem_selectedColumns] using hcb)])]
    apply Finset.sum_congr rfl
    intro cb hcb
    exact if_pos ((mem_selectedColumns K S annuli cb).mp hcb)
  calc
    _ = ∑' cb, (a cb + discardedColumn K S D f s annuli F θ q V.toFun X k P cb) :=
      tsum_congr he
    _ = (∑' cb, a cb) + ∑' cb, discardedColumn K S D f s annuli F θ q V.toFun X k P cb :=
      ha.tsum_add hd.of_norm
    _ = _ := by rw [hfinite, sum_selectedColumns]

/-- The omitted complete annuli lie in the literal kernel tail. -/
theorem discarded_norm_le_tail
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ)
    (X Klo Plo T : ℝ) (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo)
    (k P : ExteriorIdeal K S)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2)
    (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    ‖discardedColumn K S D f s (retainedAnnuli K S f s X Klo Plo T) F θ q V X k P cb‖ ≤
      ‖tailColumnAtom K S D f s F θ q V X T k P cb‖ := by
  unfold discardedColumn
  split_ifs with h
  · simpa only [norm_zero] using norm_nonneg
      (tailColumnAtom K S D f s F θ q V X T k P cb)
  · rw [tailColumnAtom, if_pos (outside_retained_argument K S f s X Klo Plo T
      hX hK hP k P hk0 hk1 hp0 hp1 cb h)]

theorem columnAtom_zero_of_not_squarefree
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) (hc : ¬ Squarefree c.val.val) :
    columnAtom K S D f s F θ q V X k P (c, b) = 0 := by
  have hcol : ¬ ColumnCondition K S s c b := fun h => hc h.1
  rw [columnAtom, ordinaryColumn_exterior K S D f s]
  simp [slicedColumn, columnCoefficient, extendColumn, hcol]

theorem column_shell_filter_squarefree
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (j l : ℕ) :
    (∑ c ∈ idealShell K S j, ∑ b ∈ idealShell K S l,
      columnAtom K S D f s F θ q V X k P (c, b)) =
    ∑ c ∈ squarefreeShell K S j, ∑ b ∈ idealShell K S l,
      columnAtom K S D f s F θ q V X k P (c, b) := by
  rw [squarefreeShell, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Squarefree c.val.val
  · simp only [if_pos hc]
  · simp [hc, columnAtom_zero_of_not_squarefree K S D f s F θ q V X k P c _ hc]

/-- The retained finite series uses exactly the squarefree column and
the unrestricted cube column required by the two exterior sieves. -/
theorem column_series_squarefree_decomposition
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
    (X : ℝ) (hX : 0 < X) (k P : ExteriorIdeal K S) (annuli : Finset (ℕ × ℕ)) :
    Summable (fun cb => ‖discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖) ∧
      (∑' cb, columnAtom K S D f s F θ q V.toFun X k P cb) =
        (∑ p ∈ annuli, ∑ c ∈ squarefreeShell K S p.1, ∑ b ∈ idealShell K S p.2,
          columnAtom K S D f s F θ q V.toFun X k P (c, b)) +
        ∑' cb, discardedColumn K S D f s annuli F θ q V.toFun X k P cb := by
  have h := column_series_decomposition K S D f s F θ hKernel hθ hD q V X hX k P annuli
  refine ⟨h.1, ?_⟩
  simpa only [column_shell_filter_squarefree K S D f s F θ q V.toFun X k P] using h.2

/-- Each retained complete annulus satisfies the paper's dual threshold.
The threshold for discarding is the actual kernel argument Z^(tau/2). -/
theorem retainedAnnuli_threshold
    (Z X Klo Plo tau : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hK : 0 < Klo) (hP : 0 < Plo) (hlarge : 16 ≤ Z ^ (tau / 2))
    (p : ℕ × ℕ)
    (hp : p ∈ retainedAnnuli K S f s X Klo Plo (Z ^ (tau / 2))) :
    scale Z ((2 : ℝ) ^ p.1) + 3 * scale Z ((2 : ℝ) ^ p.2) <
      dualThreshold K S f s Z X Klo Plo + tau := by
  have hbase := baseScale_pos K S f s hX
  have hden : 0 < Klo ^ 2 * Plo ^ 2 :=
    mul_pos (sq_pos_of_pos hK) (sq_pos_of_pos hP)
  have hp' : dyadProduct p <
      16 * Z ^ (tau / 2) * (Klo ^ 2 * Plo ^ 2) / baseScale K S f s X :=
    (mem_annuliBelow _ _).mp hp
  have hY : GeneralReflectedBlock.normalizedScale K S f s X Klo Plo
      ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) <
      16 * Z ^ (tau / 2) := by
    apply (div_lt_iff₀ hden).mpr
    have h := (lt_div_iff₀ hbase).mp hp'
    dsimp [dyadProduct] at h
    nlinarith only [h]
  have ht : 16 * Z ^ (tau / 2) ≤ Z ^ tau := by
    calc
      _ ≤ Z ^ (tau / 2) * Z ^ (tau / 2) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hZ)]; congr 1 <;> ring
  have he : GeneralReflectedBlock.normalizedScale K S f s X Klo Plo
      ((2 : ℝ) ^ p.1) ((2 : ℝ) ^ p.2) =
      Z ^ (scale Z ((2 : ℝ) ^ p.1) + 3 * scale Z ((2 : ℝ) ^ p.2) -
        dualThreshold K S f s Z X Klo Plo) := by
    rw [normalizedScale_eq_kernelScale K S f s]
    exact GeneralBlockPolynomial.kernelScale_eq_rpow hZ hX
      (exteriorNorm_pos K S (primeSetIdeal K S s.active))
      (exteriorNorm_pos K S (minimumLinearIdeal K S s))
      (exteriorNorm_pos K S (minimumCubeIdeal K S s)) hK hP (by positivity) (by positivity)
  have hh := hY.trans_le ht
  rw [he] at hh
  have hlt := (Real.rpow_lt_rpow_left_iff hZ).mp hh
  linarith

/-- Multiplication by the genuine static row/mark coefficient preserves
the pointwise comparison with the already proved kernel tail. -/
theorem weighted_discarded_mass_le
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (q : ClassSlices.FourClasses (SixthLocalClasses K S)) (V : SmoothAnnularTest)
    (X Klo Plo T : ℝ) (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo) (hT : 0 < T)
    (k P : ExteriorIdeal K S) (w : ℂ)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2) :
    Summable (fun cb => ‖w * discardedColumn K S D f s
      (retainedAnnuli K S f s X Klo Plo T) F θ q V.toFun X k P cb‖) ∧
      (∑' cb, ‖w * discardedColumn K S D f s
        (retainedAnnuli K S f s X Klo Plo T) F θ q V.toFun X k P cb‖) ≤
      ∑' cb, ‖w * tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖ := by
  obtain ⟨J, C, hC, hb⟩ := actual_column_tail K S D F θ hKernel hθ hD 1 le_rfl
  have hs : Summable (fun cb => ‖w * tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖) := by
    simpa only [norm_mul] using (hb V q f s X T k P hX hT).1.mul_left ‖w‖
  have hp (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      ‖w * discardedColumn K S D f s (retainedAnnuli K S f s X Klo Plo T)
        F θ q V.toFun X k P cb‖ ≤
      ‖w * tailColumnAtom K S D f s F θ q V.toFun X T k P cb‖ := by
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (discarded_norm_le_tail K S D f s F θ q V.toFun
      X Klo Plo T hX hK hP k P hk0 hk1 hp0 hp1 cb) (norm_nonneg w)
  have hd := hs.of_nonneg_of_le (fun cb => norm_nonneg _) hp
  exact ⟨hd, hd.tsum_le_tsum hp hs⟩

/-- Arbitrary power saving for the actual complement of the retained
complete dual annuli.  The constant and seminorm order precede every
finite-order child, norm twist and finite family of source pieces. -/
theorem actual_total_discarded_power_tail_height [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K) (hD : AllowedGeneratorInput K S D)
    (B tau L : ℝ) (hB : 0 ≤ B) (htau : 0 < tau) (hL : 0 < L) :
    ∃ (J : ℕ) (C Z0 : ℝ), 0 ≤ C ∧ 1 < Z0 ∧
      ∀ (ν : HeckeCharacter K), FiniteOrder ν → ∀ (t : ℝ),
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) →
      ∀ Z : ℝ, Z0 ≤ Z → 16 ≤ Z ^ (tau / 2) ∧
      ∀ (V : SmoothAnnularTest) {ι : Type*} (I : Finset ι)
        (p : ι → TailPiece K S) (Klo Plo : ι → ℝ),
      (∀ i ∈ I, 0 < (p i).X) → (∑ i ∈ I, (p i).prefactor) ≤ Z ^ B →
      (∀ i ∈ I, 0 < Klo i ∧ 0 < Plo i ∧
        1 ≤ exteriorNorm K S (p i).row / Klo i ∧
        exteriorNorm K S (p i).row / Klo i ≤ 2 ∧
        1 ≤ exteriorNorm K S (p i).mark / Plo i ∧
        exteriorNorm K S (p i).mark / Plo i ≤ 2) →
      (∀ i ∈ I, Summable (fun cb => ‖(p i).weight *
        discardedColumn K S D (p i).fixed (p i).state
          (retainedAnnuli K S (p i).fixed (p i).state (p i).X (Klo i) (Plo i) (Z ^ (tau / 2)))
          F (ν * θ₀ * heckeNormTwist K t) (p i).classes V.toFun (p i).X
          (p i).row (p i).mark cb‖)) ∧
      (∑ i ∈ I, ∑' cb, ‖(p i).weight *
        discardedColumn K S D (p i).fixed (p i).state
          (retainedAnnuli K S (p i).fixed (p i).state (p i).X (Klo i) (Plo i) (Z ^ (tau / 2)))
          F (ν * θ₀ * heckeNormTwist K t) (p i).classes V.toFun (p i).X
          (p i).row (p i).mark cb‖) ≤
        C * (1 + |t|) ^ (8 * HeckeSkeleton.ThetaKernel.ncx K * GeneralTailNumerics.tailOrder B tau L) *
          testSeminorm V.toFun J (GeneralTailNumerics.tailOrder B tau L) * Z ^ (-L) := by
  obtain ⟨J, C, Z0, hC, hZ0, hb⟩ :=
    actual_total_power_tail_height K S D F hF θ₀ hD B tau L hB htau hL
  refine ⟨J, C, Z0, hC, hZ0, ?_⟩
  intro ν hν t hθ Z hZ
  obtain ⟨hlarge, hbZ⟩ := hb ν hν t hθ Z hZ
  refine ⟨hlarge, ?_⟩
  intro V ι I p Klo Plo hX hpref hbox
  obtain ⟨hs, hsum⟩ := hbZ V I p hX hpref
  have hpoint (i : ι) (hi : i ∈ I) (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      ‖(p i).weight * discardedColumn K S D (p i).fixed (p i).state
        (retainedAnnuli K S (p i).fixed (p i).state (p i).X (Klo i) (Plo i) (Z ^ (tau / 2)))
        F (ν * θ₀ * heckeNormTwist K t) (p i).classes V.toFun (p i).X
        (p i).row (p i).mark cb‖ ≤
      ‖(p i).weight * tailColumnAtom K S D (p i).fixed (p i).state
        F (ν * θ₀ * heckeNormTwist K t) (p i).classes V.toFun (p i).X
        (Z ^ (tau / 2)) (p i).row (p i).mark cb‖ := by
    obtain ⟨hK, hP, hk0, hk1, hp0, hp1⟩ := hbox i hi
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (discarded_norm_le_tail K S D (p i).fixed (p i).state F
        (ν * θ₀ * heckeNormTwist K t) (p i).classes V.toFun (p i).X
        (Klo i) (Plo i) (Z ^ (tau / 2)) (hX i hi) hK hP
        (p i).row (p i).mark hk0 hk1 hp0 hp1 cb) (norm_nonneg _)
  have hd (i : ι) (hi : i ∈ I) :=
    (hs i hi).of_nonneg_of_le (fun cb => norm_nonneg _) (hpoint i hi)
  refine ⟨hd, ?_⟩
  apply le_trans _ hsum
  exact Finset.sum_le_sum (fun i hi =>
    (hd i hi).tsum_le_tsum (hpoint i hi) (hs i hi))

#print axioms column_norm_summable
#print axioms column_series_decomposition
#print axioms outside_retained_argument
#print axioms discarded_norm_le_tail
#print axioms column_series_squarefree_decomposition
#print axioms retainedAnnuli_threshold
#print axioms weighted_discarded_mass_le
#print axioms annuliBelow_count_small_power
#print axioms cutoffRadius_le_from_lengths
#print axioms retainedAnnuli_count_small_power
#print axioms actual_total_discarded_power_tail_height

end HeckeSkeleton.LowEnergy.GeneralColumnCutoff
