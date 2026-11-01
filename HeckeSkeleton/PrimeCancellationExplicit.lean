import HeckeSkeleton.PrimeCancellationHecke
import HeckeSkeleton.PrimeCancellationPolynomials
import HeckeSkeleton.PrimeCancellationMoment
import HeckeSkeleton.PrimeCancellationBounds
import HeckeSkeleton.PrimeCancellationWindows

/-!
# Prime cancellation for an explicit family of actual moment data

The index family is an independent parameter. Its data are the original
`MomentData`, its finite ideal rows, the complete original common mask, and
the original prime polynomials. The contract records structural identities,
Schwartz-window control and arithmetic conductor control. No prime-sum or
moment estimate is a field. Linear row counting is proved from the actual
number-field ideal-counting theorem.

The constants are uniform in independent external scale and height. The
final theorem then specializes the height while preserving the original
order of the exponent, height ceiling, threshold and scalar constants.
-/

set_option autoImplicit false
noncomputable section

universe u

namespace HeckeSkeleton.PrimeCancellationExplicit

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open HeckeSkeleton.PrimeCancellationBounds HeckeSkeleton.ExplicitHeckeFunctionalEquation
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles PrimeCancellation.PairedProfiles
open scoped Classical BigOperators SchwartzMap

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}

local instance sectorFintype : Fintype (SixthUnitClasses K (places K c)) :=
  Fintype.ofFinite _

/-- An explicit family of the actual ideal/Hecke polynomial data. The
normalization of the row exponent and the two length identities are purely
structural. In particular the row norm bound follows from `rows_spec`.
-/
structure ExplicitModelFamily (c : TargetContext K) (ι : ℝ → ℝ → Type u) where
  model : ∀ Z T, ι Z T → SixthUnitClasses K (places K c) →
    MomentData K c.family.omega (targetCharacter K c)
  base : ∀ Z T, ι Z T → ℝ
  parameters : ∀ Z T, ι Z T → RealParameters
  length : ∀ Z T, ι Z T → ℝ
  base_pos : ∀ Z T i, 1 ≤ Z → 1 ≤ T → 0 < base Z T i
  row_exponent : ∀ Z T i, 1 ≤ (parameters Z T i).m + (parameters Z T i).q ∧
    base Z T i ^ ((parameters Z T i).m + (parameters Z T i).q) ≤ 2 * base Z T i
  parameter_length : ∀ Z T i, (parameters Z T i).z = length Z T i
  geometry_length : ∀ Z T i s, (model Z T i s).geometry.totalLength = length Z T i
  mask : ∀ Z T i s u I,
    (model Z T i s).commonMask u I = originalMomentMask (c := c) u I
  finite_slots : ∀ Z T i s j, FiniteOrder ((model Z T i s).slotCoefficient j)

variable {ι : ℝ → ℝ → Type u}

/-- The only capacity consequence needed for this estimate. It bounds the
total selected length by the fixed slot ceiling times the fixed mesh.
-/
def ExplicitPairedCapacity (F : ExplicitModelFamily c ι) {Z T : ℝ} (i : ι Z T) : Prop :=
  F.length Z T i ≤ (c.geometry.slots : ℝ) * (momentMesh K c.family).val

/-- Window, finite exceptional-character and conductor requirements for
the entire explicit family. All conductor bounds cover every summed row.
-/
structure ExplicitModelControl (F : ExplicitModelFamily c ι) where
  slot_count : ∀ Z T (i : ι Z T) s,
    (F.model Z T i s).geometry.slotCount ≤ c.geometry.slots
  inverse_mem : ∀ Z T (i : ι Z T) s j,
    ((F.model Z T i s).slotCoefficient j)⁻¹ ∈ (F.model Z T i s).theta
  window : ∀ Z T (i : ι Z T) s,
    Fin (F.model Z T i s).geometry.slotCount → SchwartzMap ℝ ℂ
  window_eq : ∀ Z T (i : ι Z T) s j,
    (window Z T i s j : ℝ → ℂ) = ((F.model Z T i s).geometry.slots j).profile 0
  window_support : ∀ Z T (i : ι Z T) s j,
    Function.support (window Z T i s j : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2
  window_control : ∀ seminorms : Finset (ℕ × ℕ),
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ Z T (i : ι Z T) s j, 1 ≤ Z → 1 ≤ T →
        sourceSeminorm seminorms (window Z T i s j) ≤ C * (1 + T) ^ A
  conductor_control : ∃ D q : ℝ, 1 ≤ D ∧ 0 ≤ q ∧
    ∀ Z T (i : ι Z T) s u,
      1 ≤ Z → 1 ≤ T → 1 ≤ F.base Z T i →
      u ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i) →
      ∀ j, Real.log (heckeConductorScale K
        ((F.model Z T i s).rowCharacter u * (F.model Z T i s).slotCoefficient j)) ≤
          D * (1 + Real.log (F.base Z T i)) * (1 + T) ^ q

variable {Z T : ℝ}

/-- Every row in the full model sum has norm at most twice the model base
(the actual dyadic row window `U < N(u) ≤ 2U`). -/
theorem row_norm_le (F : ExplicitModelFamily c ι) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)) :
    idealNorm K u ≤ 2 * F.base Z T i :=
  (norm_le_of_mem_pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i) u hu).trans
    (F.row_exponent Z T i).2

theorem rows_eq_empty_of_base_lt_one (F : ExplicitModelFamily c ι) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (hpos : 0 < F.base Z T i)
    (hbase : F.base Z T i < 1) :
    pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hn := norm_le_of_mem_pairedRows (F.model Z T i s) (F.parameters Z T i)
    (F.base Z T i) u hu
  have hle : F.base Z T i ^ ((F.parameters Z T i).m + (F.parameters Z T i).q) ≤
      F.base Z T i ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hpos hbase.le (F.row_exponent Z T i).1
  rw [Real.rpow_one] at hle
  exact (not_le_of_gt hbase) ((one_le_idealNorm K u).trans (hn.trans hle))

/-- The logarithmic deletion budget at the doubled row scale. -/
private theorem two_base_mask_budget (B₀ X T q : ℝ) (hB₀ : 0 ≤ B₀) (hX : 1 ≤ X)
    (hT : 1 ≤ T) (hq : 0 ≤ q) :
    B₀ * (1 + Real.log (2 * X)) ≤ (2 * B₀) * ((1 + Real.log X) * (1 + T) ^ q) := by
  have hl2 : Real.log (2 * X) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpow : 1 ≤ (1 + T) ^ q := Real.one_le_rpow (by linarith) hq
  have h1 : 1 + Real.log (2 * X) ≤ 2 * (1 + Real.log X) := by
    rw [hl2]
    linarith
  calc
    B₀ * (1 + Real.log (2 * X)) ≤ B₀ * (2 * (1 + Real.log X)) :=
      mul_le_mul_of_nonneg_left h1 hB₀
    _ = (2 * B₀) * ((1 + Real.log X) * 1) := by ring
    _ ≤ (2 * B₀) * ((1 + Real.log X) * (1 + T) ^ q) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hpow (by linarith)

/-- Zero selected length has no slots; no nonprincipal premise is needed. -/
theorem zero_slot_product (F : ExplicitModelFamily c ι) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (hz : F.length Z T i = 0)
    (v : NonzeroIdeal K) (t : ℝ) :
    slotProduct (F.model Z T i s) v (F.base Z T i) t = 1 := by
  exact slotProduct_eq_one_of_totalLength_zero (F.model Z T i s)
    ((F.geometry_length Z T i s).trans hz) v (F.base Z T i) t

theorem slot_character_finite (F : ExplicitModelFamily c ι) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (v : NonzeroIdeal K)
    (j : Fin (F.model Z T i s).geometry.slotCount) :
    FiniteOrder ((F.model Z T i s).rowCharacter v * (F.model Z T i s).slotCoefficient j) :=
  ((F.model Z T i s).rowCharacter_finite v).mul (F.finite_slots Z T i s j)

theorem slot_character_ne_one (F : ExplicitModelFamily c ι)
    (control : ExplicitModelControl F) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (v : NonzeroIdeal K)
    (hv : v ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i))
    (j : Fin (F.model Z T i s).geometry.slotCount) :
    (F.model Z T i s).rowCharacter v * (F.model Z T i s).slotCoefficient j ≠ 1 := by
  exact paired_slot_character_ne_one (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)
    ((F.geometry_length Z T i s).trans (F.parameter_length Z T i).symm)
    (control.inverse_mem Z T i s) v hv j

/-- The field-only ideal-counting theorem applies by injecting all actual
filtered rows into the finite set of ideals with bounded absolute norm.
-/
theorem exists_paired_linear_count (F : ExplicitModelFamily c ι) :
    ∃ Crows : ℝ, 0 < Crows ∧ ∀ Z T (i : ι Z T)
      (s : SixthUnitClasses K (places K c)), 1 ≤ F.base Z T i →
      ((pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)).card : ℝ)
        ≤ Crows * F.base Z T i := by
  obtain ⟨Crows, hCrows, hcount⟩ := exists_ideal_count_bound K
  refine ⟨2 * Crows, by linarith, ?_⟩
  intro Z T i s hbase
  have hbase2 : 1 ≤ 2 * F.base Z T i := by linarith
  let X := 2 * F.base Z T i
  let rows := pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)
  have hfinite : {I : Ideal (𝓞 K) | (I.absNorm : ℝ) ≤ X}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset
      (fun I hI => (Nat.le_floor_iff (zero_le_one.trans hbase2)).mpr hI)
  letI : Finite {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ X} := hfinite.to_subtype
  let f : rows → {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ X} := fun v =>
    ⟨v.val.val, row_norm_le F i s v.val v.property⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun I : {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ X} => I.val) h
  have hc := Nat.card_le_card_of_injective f hf
  have hc' : rows.card ≤ Nat.card {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ X} := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  have hXc : Crows * X = 2 * Crows * F.base Z T i := by
    dsimp only [X]
    ring
  exact (Nat.cast_le.mpr hc').trans ((hcount X hbase2).trans_eq hXc)

theorem deleted_prime_dvd (F : ExplicitModelFamily c ι) (D : FixedBadPrimeSupport c)
    (i : ι Z T) (s : SixthUnitClasses K (places K c)) (v : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K))
    (hdeleted : (F.model Z T i s).commonMask v p.asIdeal = false) :
    p.asIdeal ∣ D.ideal.val * v.val := by
  apply deleted_prime_dvd_fixed_mul_row D v p
  rw [← F.mask Z T i s v p.asIdeal]
  exact hdeleted

theorem deleted_count (F : ExplicitModelFamily c ι) (D : FixedBadPrimeSupport c)
    (i : ι Z T) (s : SixthUnitClasses K (places K c)) (v : NonzeroIdeal K)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) (hB : 1 < B)
    (hlower : ∀ p ∈ pool, B ≤ (Ideal.absNorm p.asIdeal : ℝ)) :
    ((pool.filter (fun p => (F.model Z T i s).commonMask v p.asIdeal = false)).card : ℝ)
      ≤ Real.log (idealNorm K (D.ideal * v)) / Real.log B := by
  apply PrimeCancellation.MaskCount.card_prime_divisors_le_log
    Ideal.absNorm _ (D.ideal.val * v.val) B
    (Ideal.absNorm_pos_of_nonZeroDivisors (D.ideal * v)) hB
  · intro p hp
    exact hlower p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact deleted_prime_dvd F D i s v p (Finset.mem_filter.mp hp).2

theorem deleted_count_le_base (F : ExplicitModelFamily c ι) (D : FixedBadPrimeSupport c)
    (i : ι Z T) (s : SixthUnitClasses K (places K c)) (v : NonzeroIdeal K)
    (hv : v ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i))
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ((pool.filter (fun p => (F.model Z T i s).commonMask v p.asIdeal = false)).card : ℝ)
      ≤ (Real.log (idealNorm K D.ideal) + Real.log (2 * F.base Z T i)) / Real.log 2 := by
  have hdel := deleted_count F D i s v pool 2 (by norm_num)
    (fun p _ => by exact_mod_cast (Nat.succ_le_iff.mpr
      (NumberField.HeightOneSpectrum.one_lt_absNorm p)))
  have hprod : idealNorm K (D.ideal * v) = idealNorm K D.ideal * idealNorm K v := by
    simp only [idealNorm, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  have hlog := Real.log_le_log (idealNorm_pos K v) (row_norm_le F i s v hv)
  rw [hprod, Real.log_mul (idealNorm_pos K D.ideal).ne' (idealNorm_pos K v).ne'] at hdel
  exact hdel.trans ((div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (add_le_add (le_refl (Real.log (idealNorm K D.ideal))) hlog))

/-- Numerical transfer from separately proved individual slot estimates. -/
theorem energy_le_of_slot_bounds (F : ExplicitModelFamily c ι) (i : ι Z T)
    (s : SixthUnitClasses K (places K c)) (κ eps Crows : ℝ)
    (hbase : 1 ≤ F.base Z T i)
    (C loss : Fin (F.model Z T i s).geometry.slotCount → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hloss : (∑ j, loss j) ≤ eps)
    (hcard : ((pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)).card : ℝ)
      ≤ Crows * F.base Z T i)
    (hslot : ∀ v ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i),
      ∀ j, ‖primePolynomial (F.model Z T i s) j v (F.base Z T i) 0‖ ^ 2 ≤
        C j * (F.base Z T i) ^ (κ * ((F.model Z T i s).geometry.slots j).length + loss j)) :
    (∑ v ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i),
      ‖slotProduct (F.model Z T i s) v (F.base Z T i) 0‖ ^ 2) ≤
      (Crows * ∏ j, C j) * (F.base Z T i) ^ (1 + (κ * F.length Z T i + eps)) := by
  have hcard' :
      ((pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)).card : ℝ)
        ≤ Crows * (F.base Z T i) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hcard
  have htransfer := PrimeCancellationAux.paired_sum_le_of_slot_bounds
    (pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i)) Finset.univ
    (fun v j => primePolynomial (F.model Z T i s) j v (F.base Z T i) 0)
    C (fun j => ((F.model Z T i s).geometry.slots j).length) loss
    (F.base Z T i) κ eps Crows 1 hbase (fun j _ => hC j) hcard' hloss
    (fun v hv j _ => hslot v hv j)
  change
    (∑ v ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i),
      ‖slotProduct (F.model Z T i s) v (F.base Z T i) 0‖ ^ 2) ≤
      (Crows * ∏ j, C j) * (F.base Z T i) ^
        (1 + (κ * (F.model Z T i s).geometry.totalLength + eps)) at htransfer
  rw [F.geometry_length Z T i s] at htransfer
  exact htransfer

/-- A uniform bound with independent external scale and height. All
constants precede both variables, every model index and every ideal row.
-/
theorem exists_uniform_paired_prime_bound
    (F : ExplicitModelFamily c ι) (hB : c.family.B < 1)
    (control : ExplicitModelControl F) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ Z T (i : ι Z T), 1 ≤ Z → 1 ≤ T → ExplicitPairedCapacity F i →
        (∑ s : SixthUnitClasses K (places K c),
          ∑ u ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i),
            ‖slotProduct (F.model Z T i s) u (F.base Z T i) 0‖ ^ 2) ≤
          C * (F.base Z T i) ^
            (1 + (2 * c.family.B - 1) * F.length Z T i + c.family.lamA) * (1 + T) ^ A := by
  obtain ⟨seminorms, Cstar, hCstar, _, hprime⟩ :=
    exists_uniform_masked_prime_seminorm_bound
  obtain ⟨Wc, a, hWc, ha, hwindow⟩ := control.window_control seminorms
  obtain ⟨D, q, hD, hq, hconductor⟩ := control.conductor_control
  obtain ⟨Cg, hCg, hgrowth⟩ :=
    exists_uniform_finiteOrder_polynomial K (isComplex_of_family K c)
  obtain ⟨Crows, hCrows, hcount⟩ := exists_paired_linear_count F
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  let H : ℝ := 1 + Real.log Cg + (5 / 8 : ℝ) * D + eulerLogSize K + 3 * (k : ℝ)
  have hEuler : 0 ≤ eulerLogSize K := (norm_nonneg _).trans
    (deleted_centerLog_bound K 1 ∅ 0)
  have hH : 0 ≤ H := by
    have hc := Real.log_nonneg hCg
    dsimp only [H]
    positivity
  let bad := canonicalFixedBadPrimeSupport c
  let Bmask : ℝ := 2 * ((Real.log (idealNorm K bad.ideal) + 1) / Real.log 2)
  have hbadLog : 0 ≤ Real.log (idealNorm K bad.ideal) :=
    Real.log_nonneg (one_le_idealNorm K bad.ideal)
  have hBmask : 0 ≤ Bmask := by
    dsimp only [Bmask]
    exact mul_nonneg (by norm_num)
      (div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  let L : ℝ := (c.geometry.slots : ℝ) * (momentMesh K c.family).val
  let δ := PrimeCancellationUniformity.contourBuffer (c.family.lamA / 2) L
  have hδ : 0 < δ := PrimeCancellationUniformity.contourBuffer_pos
    (by linarith [c.family.lamA_pos])
  have hδ' : δ ≤ (1 : ℝ) / 4 := PrimeCancellationUniformity.contourBuffer_le_quarter _ _
  let Kslot : ℝ := max 1 ((uniformConstant δ Cstar (primeCountConstant K) H + Bmask) * Wc)
  have hKslot : 1 ≤ Kslot := le_max_left _ _
  let A : ℝ := (q + a) * (2 * c.geometry.slots : ℕ)
  let Csector : ℝ := Crows * Kslot ^ (2 * c.geometry.slots) *
    PrimeCancellationUniformity.logAbsorptionConstant (2 * c.geometry.slots) (c.family.lamA / 2)
  have hCsector : 0 ≤ Csector := mul_nonneg
    (mul_nonneg hCrows.le (pow_nonneg (zero_le_one.trans hKslot) _))
    (PrimeCancellationUniformity.logAbsorptionConstant_pos _
      (show 0 < c.family.lamA / 2 by linarith [c.family.lamA_pos])).le
  refine ⟨A, (Fintype.card (SixthUnitClasses K (places K c)) : ℝ) * Csector,
    mul_nonneg (add_nonneg hq ha) (Nat.cast_nonneg _),
    mul_nonneg (Nat.cast_nonneg _) hCsector, ?_⟩
  intro Z T i hZ hT hcap
  have hXpos : 0 < F.base Z T i := F.base_pos Z T i hZ hT
  have hsector (s : SixthUnitClasses K (places K c)) :
      (∑ u ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i),
        ‖slotProduct (F.model Z T i s) u (F.base Z T i) 0‖ ^ 2) ≤
        Csector * (F.base Z T i) ^
          (1 + (2 * c.family.B - 1) * F.length Z T i + c.family.lamA) * (1 + T) ^ A := by
    by_cases hX : 1 ≤ F.base Z T i
    · let f : ℝ := (1 + Real.log (F.base Z T i)) * (1 + T) ^ q
      let amplitude : ℝ := Kslot * (1 + Real.log (F.base Z T i)) * (1 + T) ^ (q + a)
      have hf : 1 ≤ f := one_le_mul_of_one_le_of_one_le (by linarith [Real.log_nonneg hX])
        (Real.one_le_rpow (by linarith) hq)
      have hamp : 0 ≤ amplitude := mul_nonneg
        (mul_nonneg (zero_le_one.trans hKslot) (by linarith [Real.log_nonneg hX]))
        (Real.rpow_nonneg (by linarith) _)
      have hslot (u : NonzeroIdeal K)
          (hu : u ∈ pairedRows (F.model Z T i s) (F.parameters Z T i) (F.base Z T i))
          (j : Fin (F.model Z T i s).geometry.slotCount) :
          ‖primePolynomial (F.model Z T i s) j u (F.base Z T i) 0‖ ^ 2 ≤
            amplitude ^ 2 * (F.base Z T i) ^
              ((2 * c.family.B - 1) * ((F.model Z T i s).geometry.slots j).length +
                (2 * δ) * ((F.model Z T i s).geometry.slots j).length) := by
        let χ := (F.model Z T i s).rowCharacter u * (F.model Z T i s).slotCoefficient j
        have hfinite : FiniteOrder χ := slot_character_finite F i s u j
        have hne : χ ≠ 1 := slot_character_ne_one F control i s u hu j
        have hnon := nonNorm_of_finiteOrder_ne_one K χ hfinite hne
        have hpacket := finiteOrder_mem_heckePacket K c.family.omega χ hfinite
        have hβ : 1 / 2 ≤ c.family.B := by linarith [c.family.B_lower]
        have hQ := one_le_actualConductorScale K χ hnon
        let data := emptySlotData K c.family.omega χ hpacket hnon c.family.B hβ
          c.family.boundary Cg (heckeConductorScale K χ) (5 / 8) k hCg hQ
          (by norm_num) (hgrowth χ hfinite hne)
        let W := control.window Z T i s j
        have hheight : heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H * f := by
          change 1 + Real.log Cg + (5 / 8 : ℝ) * Real.log (heckeConductorScale K χ) +
            eulerLogSize K + 3 * (k : ℝ) ≤ H * f
          exact conductor_height_budget Cg D (eulerLogSize K) (heckeConductorScale K χ)
            (F.base Z T i) T q k hCg hEuler hX hT hq (hconductor Z T i s u hZ hT hX hu j)
        have hdelete : (((((F.model Z T i s).geometry.slots j).support 0
            ((F.base Z T i) ^ ((F.model Z T i s).geometry.slots j).length)).filter
              (fun p => (F.model Z T i s).commonMask u p.asIdeal = false)).card : ℝ) ≤
                Bmask * f := by
          have hb := deleted_count_le_base F bad i s u hu (((F.model Z T i s).geometry.slots j).support 0
              ((F.base Z T i) ^ ((F.model Z T i s).geometry.slots j).length))
          have hX2 : 1 ≤ 2 * F.base Z T i := by linarith
          refine hb.trans ((logarithmic_mask_budget (Real.log (idealNorm K bad.ideal))
            (2 * F.base Z T i) hbadLog hX2).trans ?_)
          exact two_base_mask_budget ((Real.log (idealNorm K bad.ideal) + 1) / Real.log 2)
            (F.base Z T i) T q (div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) hX hT hq
        have hbudget : (uniformConstant δ Cstar (primeCountConstant K) (H * f) + Bmask * f) *
            sourceSeminorm seminorms W ≤ amplitude := by
          exact profile_budget δ Cstar (primeCountConstant K) H Bmask Wc
            (F.base Z T i) T q a (sourceSeminorm seminorms W) hCstar.le
            (primeCountConstant_pos K).le hH hBmask (zero_le_one.trans hWc) hX hT hq
            (sourceSeminorm_nonneg _ _) (hwindow Z T i s j hZ hT)
        exact HeckeSkeleton.PrimeCancellationWiring.primePolynomial_bound_of_analytic_data (F.model Z T i s) u j (F.base Z T i)
          W (control.window_eq Z T i s j) c.family.B (primeCountConstant K) data rfl
          (emptySlotData_coefficient K c.family.omega χ hpacket hnon c.family.B hβ
            c.family.boundary Cg (heckeConductorScale K χ) (5 / 8) k hCg hQ
            (by norm_num) (hgrowth χ hfinite hne)) seminorms Cstar δ (H * f) (Bmask * f)
          hprime (control.window_support Z T i s j) hheight hβ hB.le hδ hδ' hX hdelete
          amplitude hamp hbudget
      have hloss : (∑ j : Fin (F.model Z T i s).geometry.slotCount,
          (2 * δ) * ((F.model Z T i s).geometry.slots j).length) ≤ c.family.lamA / 2 := by
        rw [← Finset.mul_sum]
        change 2 * δ * (F.model Z T i s).geometry.totalLength ≤ c.family.lamA / 2
        rw [F.geometry_length Z T i s]
        exact PrimeCancellationUniformity.contourBuffer_total_loss
          (show 0 < c.family.lamA / 2 by linarith [c.family.lamA_pos])
          hcap
      have henergy := energy_le_of_slot_bounds F i s
        (2 * c.family.B - 1) (c.family.lamA / 2) Crows hX
        (fun _ => amplitude ^ 2)
        (fun j => (2 * δ) * ((F.model Z T i s).geometry.slots j).length)
        (fun _ => sq_nonneg _) hloss (hcount Z T i s hX) hslot
      have hprod : (∏ _j : Fin (F.model Z T i s).geometry.slotCount, amplitude ^ 2) ≤
          Kslot ^ (2 * c.geometry.slots) * (1 + Real.log (F.base Z T i)) ^ (2 * c.geometry.slots) *
            (1 + T) ^ ((q + a) * (2 * c.geometry.slots : ℕ)) := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          finite_slot_budget (F.model Z T i s).geometry.slotCount c.geometry.slots
            Kslot (F.base Z T i) T (q + a) (control.slot_count Z T i s) hKslot hX hT
            (add_nonneg hq ha)
      refine henergy.trans (le_trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCrows.le)
          (Real.rpow_nonneg hXpos.le _)) ?_)
      exact absorb_slot_logarithms c.geometry.slots Crows Kslot (F.base Z T i) T (q + a)
        (2 * c.family.B - 1) (F.length Z T i) c.family.lamA hCrows.le
        (zero_le_one.trans hKslot) hX hT c.family.lamA_pos
    · rw [rows_eq_empty_of_base_lt_one F i s hXpos (lt_of_not_ge hX), Finset.sum_empty]
      exact mul_nonneg (mul_nonneg hCsector (Real.rpow_nonneg hXpos.le _))
        (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ ∑ _s : SixthUnitClasses K (places K c), Csector * (F.base Z T i) ^
        (1 + (2 * c.family.B - 1) * F.length Z T i + c.family.lamA) * (1 + T) ^ A :=
      Finset.sum_le_sum (fun s _ => hsector s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The original height-parameter quantifier order on the independent
index family. The conclusion holds without an additional bin restriction.
-/
def ExplicitPairedPrimeProductBound (F : ExplicitModelFamily c ι) (κ : ℝ) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : ι Z (Z ^ τ), ExplicitPairedCapacity F i →
        (∑ s : SixthUnitClasses K (places K c),
          ∑ v ∈ pairedRows (F.model Z (Z ^ τ) i s)
              (F.parameters Z (Z ^ τ) i) (F.base Z (Z ^ τ) i),
            ‖slotProduct (F.model Z (Z ^ τ) i s) v (F.base Z (Z ^ τ) i) 0‖ ^ 2) ≤
          C * (F.base Z (Z ^ τ) i) ^
            (1 + κ * F.length Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A

/-- The independent actual-model prime-cancellation theorem. Its exponent,
complete row mask and height quantifier order are the original ones.
The index family and all actual model data are explicit parameters.
-/
theorem paired_primes_below_one_of_explicit_models
    (F : ExplicitModelFamily c ι) (hB : c.family.B < 1)
    (control : ExplicitModelControl F) :
    ExplicitPairedPrimeProductBound F (2 * c.family.B - 1) := by
  obtain ⟨A, C, hA, hC, hbound⟩ := exists_uniform_paired_prime_bound F hB control
  refine ⟨A, 1, hA, zero_lt_one, ?_⟩
  intro τ hτ _hτupper
  refine ⟨1, C, le_rfl, hC, ?_⟩
  intro Z hZ i hcap
  exact hbound Z (Z ^ τ) i hZ (Real.one_le_rpow hZ hτ.le) hcap

#print axioms exists_paired_linear_count
#print axioms exists_uniform_paired_prime_bound
#print axioms paired_primes_below_one_of_explicit_models

end HeckeSkeleton.PrimeCancellationExplicit
