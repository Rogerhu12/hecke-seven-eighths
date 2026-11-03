import HeckeGeneral.Analysis.SUnitPartitionFiniteFibres
import HeckeGeneral.Arithmetic.SIntegerCompactDenominators
import HeckeGeneral.Characters.SIntegerSexticSymbol

/-!
The symbol import is the actual two-argument symbol,
not an arbitrary periodic coefficient. No reciprocity claim is made.
Finite cosets below cover the actual finite-place-active nonzero elements,
before any archimedean truncation. Neither unit associates nor torsion are
discarded. The origin is a separate additive-lattice term.

The auxiliary nonzero ordinary ideal M permits a later proved fixed-ray
conductor. Multiplying the period by M does not itself prove invariance
of deeper ray factors. In the actual correlation chi_(dm)(k), m is the
denominator: reciprocity with its bad-place correction must first turn
this into fixed-denominator numerator factors (Q:7102-7113,8406-8438).
-/

noncomputable section
namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Z" => SFiniteLocalGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- An ordinary ideal preserving exterior residues and active finite-place
valuations, refined by an arbitrary auxiliary ordinary ideal. -/
def sIntegerAnnularSexticPeriod (M : Ideal (𝓞 K)) (c : N) : Ideal (𝓞 K) :=
  (sIntegerModulusContraction K S c.val * ∏ v : S, v.val.asIdeal) * M

theorem sIntegerAnnularSexticPeriod_ne_bot (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c : N) :
    sIntegerAnnularSexticPeriod K S M c ≠ ⊥ := by
  exact mul_ne_zero
    (mul_ne_zero (sIntegerModulusContraction_ne_bot K S c.val c.property)
      (Finset.prod_ne_zero_iff.mpr (fun v _ => v.val.ne_bot))) hM

theorem sIntegerAnnularSexticPeriod_le_prime (M : Ideal (𝓞 K)) (c : N) (v : S) :
    sIntegerAnnularSexticPeriod K S M c ≤ v.val.asIdeal := by
  exact Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ v))))

@[simp] theorem sIntegerAnnularSexticPeriod_top (c : N) :
    sIntegerAnnularSexticPeriod K S ⊤ c =
      sIntegerModulusContraction K S c.val * ∏ v : S, v.val.asIdeal := by
  simp only [sIntegerAnnularSexticPeriod, Ideal.mul_top]

/-- A strict integral increment preserves all orders in an active fibre.
This is proved from the valuation, not assumed as a covariance field. -/
theorem sIntegerAnnular_active_orders_eq
    (m n : N) (t : 𝓞 K)
    (hdiff : m.val - n.val = algebraMap (𝓞 K) (S.integer K) t)
    (ht : ∀ v : S, t ∈ v.val.asIdeal)
    (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    ∀ v : S, localOrderHom K v.val ((sLocalNonzeroIntegerDiagonal K S m).2 v) =
      localOrderHom K v.val ((sLocalNonzeroIntegerDiagonal K S n).2 v) := by
  intro v
  let M := ((sLocalNonzeroIntegerDiagonal K S m).2 v).val
  let Q := ((sLocalNonzeroIntegerDiagonal K S n).2 v).val
  have hfield : (m.val : K) - (n.val : K) = algebraMap (𝓞 K) K t :=
    congrArg (fun z : S.integer K => (z : K)) hdiff
  have hdiffval : (Valued.v (M - Q) : WithZero (Multiplicative ℤ)) < 1 := by
    change Valued.v (algebraMap K (v.val.adicCompletion K) (m.val : K) -
      algebraMap K (v.val.adicCompletion K) (n.val : K)) < 1
    rw [← map_sub, hfield]
    change Valued.v ((algebraMap (𝓞 K) K t : K) : v.val.adicCompletion K) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.val.valuation_lt_one_iff_mem t).mpr (ht v)
  have hlo := ((mem_localValuationBox_iff_order_bounds K v.val
    (finiteIndexSUnitBoxWidth K S Γ) _).mp (hm v)).1
  have hlarge : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v M := by
    rw [show M = ((sLocalNonzeroIntegerDiagonal K S m).2 v).val from rfl,
      localOrder_valuation]
    exact WithZero.one_le_exp_iff.mpr hlo
  have hv : (Valued.v Q : WithZero (Multiplicative ℤ)) = Valued.v M := by
    have h := (Valued.v : Valuation (v.val.adicCompletion K) (WithZero (Multiplicative ℤ))).map_sub_eq_of_lt_left
      (hdiffval.trans_le hlarge)
    simpa only [sub_sub_cancel] using h
  change Multiplicative.ofAdd (-WithZero.log (Valued.v M)) =
    Multiplicative.ofAdd (-WithZero.log (Valued.v Q))
  rw [hv]

theorem sIntegerAnnular_active_mem_iff_of_period
    (M : Ideal (𝓞 K)) (c m n : N) (t : 𝓞 K)
    (ht : t ∈ sIntegerAnnularSexticPeriod K S M c)
    (hdiff : m.val - n.val = algebraMap (𝓞 K) (S.integer K) t) :
    (sLocalNonzeroIntegerDiagonal K S m).2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ↔
      (sLocalNonzeroIntegerDiagonal K S n).2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) := by
  have forward (m n : N) (t : 𝓞 K)
      (ht : t ∈ sIntegerAnnularSexticPeriod K S M c)
      (hdiff : m.val - n.val = algebraMap (𝓞 K) (S.integer K) t)
      (hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
      (sLocalNonzeroIntegerDiagonal K S n).2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) := by
    have ho := sIntegerAnnular_active_orders_eq K S Γ m n t hdiff
      (fun v => sIntegerAnnularSexticPeriod_le_prime K S M c v ht) hm
    intro v
    rw [mem_localValuationBox_iff_order_bounds, ← ho v,
      ← mem_localValuationBox_iff_order_bounds]
    exact hm v
  refine ⟨forward m n t ht hdiff, ?_⟩
  apply forward n m (-t) ((sIntegerAnnularSexticPeriod K S M c).neg_mem ht)
  rw [map_neg, ← hdiff, neg_sub]

/-- Full equality on nonzero original and translated elements, including
inactive fibres. The reverse implication uses the increment -t. -/
theorem sIntegerAnnular_fibre_eq_of_period
    (a : ℝ → ℝ) (M : Ideal (𝓞 K)) (c m n : N) (t : 𝓞 K)
    (ht : t ∈ sIntegerAnnularSexticPeriod K S M c)
    (hdiff : m.val - n.val = algebraMap (𝓞 K) (S.integer K) t) :
    sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S m).2 =
      sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S n).2 := by
  let B := finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  have htS : ∀ v : S, t ∈ v.val.asIdeal :=
    fun v => sIntegerAnnularSexticPeriod_le_prime K S M c v ht
  by_cases hm : (sLocalNonzeroIntegerDiagonal K S m).2 ∈ B
  · exact sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a _ _
      (sIntegerAnnular_active_orders_eq K S Γ m n t hdiff htS hm)
  · by_cases hn : (sLocalNonzeroIntegerDiagonal K S n).2 ∈ B
    · have hreverse : n.val - m.val = algebraMap (𝓞 K) (S.integer K) (-t) := by
        rw [map_neg, ← hdiff, neg_sub]
      exact (sUnitAnnularPartitionCutoff_eq_of_orders_eq K S Γ a _ _
        (sIntegerAnnular_active_orders_eq K S Γ n m (-t) hreverse
          (fun v => (v.val.asIdeal).neg_mem (htS v)) hn)).symm
    · rw [sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a _ hm,
        sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a _ hn]

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- The actual sextic numerator and the entire finite-fibre cutoff have
one common ordinary ideal period. No independent Gamma invariance or
reciprocity is inferred from this additive statement. -/
theorem sIntegerAnnularSextic_eq_of_period
    (a : ℝ → ℝ) (M : Ideal (𝓞 K)) (c m n : N) (t : 𝓞 K)
    (ht : t ∈ sIntegerAnnularSexticPeriod K S M c)
    (hdiff : m.val - n.val = algebraMap (𝓞 K) (S.integer K) t) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 m.val c =
      sIntegerSexticSymbol K S ζ hζ σ hS6 n.val c ∧
    sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S m).2 =
      sUnitAnnularPartitionCutoff K S Γ a (sLocalNonzeroIntegerDiagonal K S n).2 := by
  refine ⟨?_, sIntegerAnnular_fibre_eq_of_period K S Γ a M c m n t ht hdiff⟩
  apply sIntegerSexticSymbol_periodic K S ζ hζ σ hS6
  rw [hdiff]
  exact (Ideal.mul_le_left (Ideal.mul_le_left ht) :
    t ∈ sIntegerModulusContraction K S c.val)

/-- The actual archimedean annular factor kills the additive origin,
including when S is empty. This is not finite-place nonvanishing. -/
theorem sUnitAnnularPartitionCutoff_origin (a : ℝ → ℝ) (ξ : Z) :
    sUnitAnnularPartitionCutoff K S Γ a ξ (0 : V) = 0 := by
  have hz : (0 : V) ∉ traceArchRegular K := by
    simp only [traceArchRegular_iff_isUnit, map_zero, isUnit_zero_iff]
    exact zero_ne_one
  simp only [sUnitAnnularPartitionCutoff, sUnitNormalizedPartitionArchPullback,
    dif_neg hz, mul_zero]

/-- Finitely many actual element representatives cover all finite-place
active elements modulo the explicit ordinary ideal, before the moving
archimedean scale is chosen. This is not a quotient by unit associates. -/
theorem exists_finite_sIntegerAnnular_period_representatives (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (c : N) :
    ∃ T : Finset N,
      (∀ m ∈ T, ∀ n ∈ T, m ≠ n →
        ¬ ∃ t ∈ sIntegerAnnularSexticPeriod K S M c,
          m.val - n.val = algebraMap (𝓞 K) (S.integer K) t) ∧
      ∀ m : N,
      (sLocalNonzeroIntegerDiagonal K S m).2 ∈
        finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ↔
      ∃ n ∈ T, ∃ t ∈ sIntegerAnnularSexticPeriod K S M c,
        m.val - n.val = algebraMap (𝓞 K) (S.integer K) t := by
  let B : Set Z := finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  let Cf := (fun ξ : Z => fun v : S => (ξ v).val) '' B
  have hCf : IsCompact Cf := (isCompact_finiteLocalValuationBox K S _).image
    (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v))
  obtain ⟨den, hden, hclear⟩ := exists_nonzero_integer_mul_sIntegers_mem_range_of_compact
    K S (Set.toFinite S) Cf hCf
  let Active := {m : N // (sLocalNonzeroIntegerDiagonal K S m).2 ∈ B}
  have hcleared (m : Active) : ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K den * (m.val.val : K) :=
    hclear m.val.val ⟨(sLocalNonzeroIntegerDiagonal K S m.val).2, m.property, rfl⟩
  choose y hy using hcleared
  let P : Ideal (𝓞 K) := Ideal.span ({den} : Set (𝓞 K)) * sIntegerAnnularSexticPeriod K S M c
  have hP : P ≠ ⊥ := mul_ne_zero (fun h => hden (Ideal.span_singleton_eq_bot.mp h))
    (sIntegerAnnularSexticPeriod_ne_bot K S M hM c)
  letI : Finite (𝓞 K ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  let q : Active → (𝓞 K ⧸ P) := fun m => Ideal.Quotient.mk P (y m)
  let rep : Set.range q → Active := fun z => Classical.choose z.property
  have hrep (z : Set.range q) : q (rep z) = z.val := Classical.choose_spec z.property
  letI : Fintype (Set.range q) := Fintype.ofFinite _
  let T : Finset N := Finset.univ.image (fun z : Set.range q => (rep z).val)
  have hdisjoint : ∀ m ∈ T, ∀ n ∈ T, m ≠ n →
      ¬ ∃ t ∈ sIntegerAnnularSexticPeriod K S M c,
        m.val - n.val = algebraMap (𝓞 K) (S.integer K) t := by
    intro m hm n hn hmn
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hn
    rintro ⟨t, ht, hdiff⟩
    have hfield : ((rep z).val.val : K) - ((rep w).val.val : K) =
        algebraMap (𝓞 K) K t := congrArg (fun u : S.integer K => (u : K)) hdiff
    have he : den * t = y (rep z) - y (rep w) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_sub, hy, hy]
      rw [← hfield]
      ring
    have hq : q (rep z) = q (rep w) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_mul.mpr ⟨t, ht, he⟩)
    have hz : z = w := Subtype.ext ((hrep z).symm.trans (hq.trans (hrep w)))
    exact hmn (congrArg (fun u : Set.range q => (rep u).val) hz)
  refine ⟨T, hdisjoint, fun m => ⟨fun hm => ?_, ?_⟩⟩
  swap
  · rintro ⟨n, hn, t, ht, hdiff⟩
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hn
    exact (sIntegerAnnular_active_mem_iff_of_period K S Γ M c m (rep z).val
      t ht hdiff).mpr (rep z).property
  let mA : Active := ⟨m, hm⟩
  let z : Set.range q := ⟨q mA, ⟨mA, rfl⟩⟩
  let nA := rep z
  have hn : nA.val ∈ T := Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
  have hq : q mA = q nA := (hrep z).symm
  have hsub : y mA - y nA ∈ P := Ideal.Quotient.eq.mp hq
  obtain ⟨t, ht, he⟩ := Ideal.mem_span_singleton_mul.mp hsub
  refine ⟨nA.val, hn, t, ht, ?_⟩
  apply Subtype.ext
  have hmul : algebraMap (𝓞 K) K den * ((m.val : K) - (nA.val.val : K)) =
      algebraMap (𝓞 K) K den * algebraMap (𝓞 K) K t := by
    calc
      _ = algebraMap (𝓞 K) K (y mA - y nA) := by rw [map_sub, hy, hy]; ring
      _ = _ := by rw [← he, map_mul]
  exact mul_left_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hden) hmul

end HeckeGeneral.Analysis
