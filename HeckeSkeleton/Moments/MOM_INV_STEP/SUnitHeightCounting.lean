import HeckeSkeleton.Moments.MOM_INV_STEP.SUnitLogCounting
import HeckeGeneral.Analysis.SUnitFiniteSupportDenominators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual local height bounds give logarithmic S-unit boxes

Both archimedean and finite coordinates below are the actual embeddings.
The missing lower bounds follow from the proved S-unit product formula.
In particular, compact additive finite-place support is allowed to contain
zero. It supplies upper bounds; no lower bound on that support is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SUnitHeightCounting

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open SUnitLogCounting
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def finiteNorm (u : S.unit K) (v : S) : ℝ :=
  ‖FinitePlace.embedding v.val ((u : Kˣ) : K)‖

theorem finiteNorm_pos (u : S.unit K) (v : S) : 0 < finiteNorm K S u v :=
  norm_pos_iff.mpr ((map_ne_zero _).mpr (u : Kˣ).ne_zero)

theorem finiteNorm_eq_zpow (u : S.unit K) (v : S) :
    finiteNorm K S u v = (v.val.asIdeal.absNorm : ℝ) ^ valuationVector K S u v := by
  rw [finiteNorm, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ ((map_ne_zero _).mpr (u : Kˣ).ne_zero),
    NNReal.coe_zpow, NNReal.coe_natCast, ← HeightOneSpectrum.valuationOfNeZero_eq]
  rfl

theorem finiteLog_eq (u : S.unit K) (v : S) :
    Real.log (finiteNorm K S u v) =
      (valuationVector K S u v : ℝ) * Real.log (v.val.asIdeal.absNorm : ℝ) := by
  rw [finiteNorm_eq_zpow, Real.log_zpow]

theorem primeLog_pos (v : S) : 0 < Real.log (v.val.asIdeal.absNorm : ℝ) := by
  apply Real.log_pos
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val

/-- The true global product formula, expressed in logarithmic coordinates. -/
theorem sum_archLog_add_finiteLog (u : S.unit K) :
    (∑ w : InfinitePlace K, archLog K S u w) +
      (∑ v : S, Real.log (finiteNorm K S u v)) = 0 := by
  have hp := sLocalProductNorm_diagonal K S u
  change mixedEmbedding.norm (mixedEmbedding K ((u : Kˣ) : K)) *
    (∏ v : S, finiteNorm K S u v) = 1 at hp
  simp only [mixedEmbedding.norm_apply, mixedEmbedding.normAtPlace_apply] at hp
  have ha (w : InfinitePlace K) : w ((u : Kˣ) : K) ≠ 0 :=
    (InfinitePlace.pos_iff.mpr (u : Kˣ).ne_zero).ne'
  have hf (v : S) : finiteNorm K S u v ≠ 0 := (finiteNorm_pos K S u v).ne'
  have hlog := congrArg Real.log hp
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun w _ => pow_ne_zero _ (ha w)))
    (Finset.prod_ne_zero_iff.mpr (fun v _ => hf v)),
    Real.log_prod (fun w _ => pow_ne_zero _ (ha w)),
    Real.log_prod (fun v _ => hf v), Real.log_one] at hlog
  simpa only [archLog, Real.log_pow] using hlog

/-- A finite list of bounded-above real numbers with zero sum is bounded
below as well. This is the elementary product-formula estimate. -/
theorem abs_le_card_mul_of_sum_zero {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hsum : ∑ i, f i = 0) (hupper : ∀ i, f i ≤ A) (i : ι) :
    |f i| ≤ (Fintype.card ι : ℝ) * A := by
  have hsum' : ∑ j, (A - f j) = (Fintype.card ι : ℝ) * A := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hsum, sub_zero]
  have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j => A - f j)
    (fun j _ => sub_nonneg.mpr (hupper j)) (Finset.mem_univ i)
  rw [hsum'] at hi
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  apply abs_le.mpr
  constructor
  · linarith
  · exact (hupper i).trans (by nlinarith)

def logCoordinate (u : S.unit K) : InfinitePlace K ⊕ S → ℝ :=
  Sum.elim (archLog K S u) (fun v => Real.log (finiteNorm K S u v))

theorem logCoordinate_sum (u : S.unit K) : ∑ i, logCoordinate K S u i = 0 := by
  simpa only [Fintype.sum_sum_type, logCoordinate, Sum.elim_inl, Sum.elim_inr] using
    sum_archLog_add_finiteLog K S u

def logDimension : ℕ := Fintype.card (InfinitePlace K ⊕ S)

def logBoxRadius (F H : ℝ) : ℝ :=
  (logDimension K S : ℝ) * (2 * Real.log H + Real.log F)

theorem logBoxRadius_nonneg (F H : ℝ) (hF : 1 ≤ F) (hH : 1 ≤ H) :
    0 ≤ logBoxRadius K S F H := by
  unfold logBoxRadius
  exact mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hH)) (Real.log_nonneg hF))

theorem logCoordinate_le (u : S.unit K) (F H : ℝ) (hF : 1 ≤ F) (hH : 1 ≤ H)
    (harch : ∀ w : InfinitePlace K, w ((u : Kˣ) : K) ≤ H)
    (hfin : ∀ v : S, finiteNorm K S u v ≤ F) (i : InfinitePlace K ⊕ S) :
    logCoordinate K S u i ≤ 2 * Real.log H + Real.log F := by
  have hlogH := Real.log_nonneg hH
  have hlogF := Real.log_nonneg hF
  cases i with
  | inl w =>
    have hm : (InfinitePlace.mult w : ℝ) ≤ 2 := by
      unfold InfinitePlace.mult
      split_ifs <;> norm_num
    have hl := Real.log_le_log (InfinitePlace.pos_iff.mpr (u : Kˣ).ne_zero) (harch w)
    change (InfinitePlace.mult w : ℝ) * Real.log (w ((u : Kˣ) : K)) ≤ _
    calc
      _ ≤ (InfinitePlace.mult w : ℝ) * Real.log H :=
        mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
      _ ≤ 2 * Real.log H := mul_le_mul_of_nonneg_right hm hlogH
      _ ≤ _ := le_add_of_nonneg_right hlogF
  | inr v =>
    exact (Real.log_le_log (finiteNorm_pos K S u v) (hfin v)).trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num) hlogH))

theorem logCoordinate_abs_le (u : S.unit K) (F H : ℝ) (hF : 1 ≤ F) (hH : 1 ≤ H)
    (harch : ∀ w : InfinitePlace K, w ((u : Kˣ) : K) ≤ H)
    (hfin : ∀ v : S, finiteNorm K S u v ≤ F) (i : InfinitePlace K ⊕ S) :
    |logCoordinate K S u i| ≤ logBoxRadius K S F H :=
  abs_le_card_mul_of_sum_zero (logCoordinate K S u) _
    (add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hH)) (Real.log_nonneg hF))
    (logCoordinate_sum K S u) (logCoordinate_le K S u F H hF hH harch hfin) i

/-- A fixed field-and-S constant converts weighted finite logarithms to
integer valuation coordinates. The empty finite set is harmless. -/
def finiteLogScale : ℝ := 1 + ∑ v : S, (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹

theorem finiteLogScale_pos : 0 < finiteLogScale K S := by
  unfold finiteLogScale
  have h : 0 ≤ ∑ v : S, (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹ :=
    Finset.sum_nonneg (fun v _ => (inv_pos.mpr (primeLog_pos K S v)).le)
  linarith

theorem inv_primeLog_le (v : S) :
    (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹ ≤ finiteLogScale K S := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun v : S => (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹)
    (fun v _ => (inv_pos.mpr (primeLog_pos K S v)).le) (Finset.mem_univ v)
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem valuation_abs_le (u : S.unit K) (F H : ℝ) (hF : 1 ≤ F) (hH : 1 ≤ H)
    (harch : ∀ w : InfinitePlace K, w ((u : Kˣ) : K) ≤ H)
    (hfin : ∀ v : S, finiteNorm K S u v ≤ F) (v : S) :
    |(valuationVector K S u v : ℝ)| ≤ finiteLogScale K S * logBoxRadius K S F H := by
  have hb := logCoordinate_abs_le K S u F H hF hH harch hfin (Sum.inr v)
  change |Real.log (finiteNorm K S u v)| ≤ _ at hb
  rw [finiteLog_eq, abs_mul, abs_of_pos (primeLog_pos K S v)] at hb
  calc
    _ = (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹ *
        (|(valuationVector K S u v : ℝ)| * Real.log (v.val.asIdeal.absNorm : ℝ)) := by
      field_simp
    _ ≤ (Real.log (v.val.asIdeal.absNorm : ℝ))⁻¹ * logBoxRadius K S F H :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (primeLog_pos K S v).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right (inv_primeLog_le K S v)
      (logBoxRadius_nonneg K S F H hF hH)

/-- The number of actual S-units with bounded local coordinates is
controlled by a logarithmic box, with no assumed counting hypothesis. -/
theorem local_height_count (M : ℕ) (hM : NumberField.Units.rank K < M)
    (F H : ℝ) (hF : 1 ≤ F) (hH : 1 ≤ H) (s : Finset (S.unit K))
    (harch : ∀ u ∈ s, ∀ w : InfinitePlace K, w ((u : Kˣ) : K) ≤ H)
    (hfin : ∀ u ∈ s, ∀ v : S, finiteNorm K S u v ≤ F) :
    (s.card : ℝ) ≤
      ((2 * ⌈finiteLogScale K S * logBoxRadius K S F H⌉₊ + 1 : ℕ) : ℝ) ^ Fintype.card S *
      ((Nat.card (NumberField.Units.torsion K) : ℝ) *
        (1 + (2 * logBoxRadius K S F H) ^ M *
          latticeInversePowerMass (NumberField.Units.unitLattice K) M)) := by
  apply sunit_log_box_count K S M hM _ _ (logBoxRadius_nonneg K S F H hF hH) s
  · intro u hu w
    exact logCoordinate_abs_le K S u F H hF hH (harch u hu) (hfin u hu) (Sum.inl w)
  · intro u hu v
    have hv := (valuation_abs_le K S u F H hF hH (harch u hu) (hfin u hu) v).trans
      (Nat.le_ceil (finiteLogScale K S * logBoxRadius K S F H))
    exact_mod_cast hv

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- Compact additive finite-place support gives one upper bound for every
S-unit detected anywhere on the actual compact domain and at every radius. -/
theorem exists_finiteNorm_bound_on_radial_domain
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (hψ : HasCompactSupport ψ) :
    ∃ F : ℝ, 1 ≤ F ∧ ∀ r : {r : ℝ // 0 < r},
      ∀ x ∈ closure (sUnitFundamentalDomain K S Γ), ∀ u : S.unit K,
        ψ (fun v : S => ((sLocalNormSection K S r *
          (x : sLocalMultiplicativeGroup K S) * sLocalDiagonal K S u).2 v).val) ≠ 0 →
        ∀ v : S, finiteNorm K S u v ≤ F := by
  let B := (fun x : sLocalNormOneGroup K S => (x : sLocalMultiplicativeGroup K S).2) ''
    closure (sUnitFundamentalDomain K S Γ)
  let q : (((v : S) → v.val.adicCompletion K) × SFiniteLocalGroup K S) →
      ((v : S) → v.val.adicCompletion K) := fun p v => p.1 v * ((p.2 v)⁻¹).val
  have hq : Continuous q := by
    apply continuous_pi
    intro v
    exact ((continuous_apply v).comp continuous_fst).mul
      (Units.continuous_val.comp (((continuous_apply v).comp continuous_snd).inv))
  have hcompact : IsCompact (q '' (tsupport ψ ×ˢ B)) :=
    (hψ.isCompact.prod (isCompact_finiteProjection_sUnitFundamentalDomain_closure K S Γ)).image hq
  obtain ⟨C, hC, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨max 1 C, le_max_left _ _, fun r x hx u hu v => ?_⟩
  let z : (v : S) → v.val.adicCompletion K := fun v =>
    ((sLocalNormSection K S r * (x : sLocalMultiplicativeGroup K S) *
      sLocalDiagonal K S u).2 v).val
  have hz : z ∈ tsupport ψ := subset_closure hu
  have hqz : q (z, (x : sLocalMultiplicativeGroup K S).2) =
      fun v : S => FinitePlace.embedding v.val ((u : Kˣ) : K) := by
    funext v
    change (1 * ((x : sLocalMultiplicativeGroup K S).2 v).val *
      (FinitePlace.embedding v.val ((u : Kˣ) : K))) *
        (((x : sLocalMultiplicativeGroup K S).2 v)⁻¹).val = _
    rw [one_mul]
    calc
      _ = FinitePlace.embedding v.val ((u : Kˣ) : K) *
          (((x : sLocalMultiplicativeGroup K S).2 v).val *
            (((x : sLocalMultiplicativeGroup K S).2 v)⁻¹).val) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, mul_one]
  have hm : (fun v : S => FinitePlace.embedding v.val ((u : Kˣ) : K)) ∈
      q '' (tsupport ψ ×ˢ B) :=
    ⟨(z, (x : sLocalMultiplicativeGroup K S).2),
      ⟨hz, Set.mem_image_of_mem _ hx⟩, hqz⟩
  exact (norm_le_pi_norm (fun v : S => FinitePlace.embedding v.val ((u : Kˣ) : K)) v).trans
    ((hbound _ hm).trans (le_max_right _ _))

end HeckeSkeleton.Moments.MOM_INV_STEP.SUnitHeightCounting

end
