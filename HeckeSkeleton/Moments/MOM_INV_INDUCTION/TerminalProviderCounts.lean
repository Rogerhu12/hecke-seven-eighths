import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderTerminalConductor
import HeckeSkeleton.LowFrozenCube.FrozenCounts
import HeckeSkeleton.LowHybrid.ExteriorArithmetic

/-!
# Actual frozen-row pairs and their residual fibers

The powerful part and the supported valuation-one part are constructed
from each original exterior row. Their finite image has the proved
square-root powerful count and only a small-power support cost. The
support radical divides the original label times the puncture.

Within a fixed pair the residual row determines the original row
injectively. All finite row sums therefore reindex exactly, without a
fiber multiplicity or an extra Cauchy factor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalCounts

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualFrozenCube
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowHybrid HeckeSkeleton.LowFrozenCube
open ProviderTerminalConductor
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

/-- The abstract coordinate radical is the actual exterior prime-set
ideal, with every prime exponent identified. -/
theorem fromSupport_eq_primeSetIdeal (T : Finset (ExteriorPrime K S)) :
    PrimeArithmetic.fromSupport (ExteriorArithmetic.coords K S) T = primeSetIdeal K S T := by
  apply PrimeCoordinates.valuation_injective (ExteriorArithmetic.coords K S)
  ext p
  rw [PrimeArithmetic.valuation_fromSupport, ExteriorArithmetic.valuation_coords,
    exponent_primeSetIdeal]

theorem supported_coords_iff (T : Finset (ExteriorPrime K S)) (I : Ext) :
    PrimeCoordinates.Supported (ExteriorArithmetic.coords K S) T I ↔
      exteriorSupport K S I ⊆ T := by
  constructor
  · intro h p hp
    by_contra hnot
    have hz : primeExponents I.val p.val = 0 := h p hnot
    exact ((exponent_ne_zero_iff_dvd I.val p.val).mpr
      ((mem_exteriorSupport_iff K S I p).mp hp)) hz
  · intro h p hp
    change primeExponents I.val p.val = 0
    by_contra hn
    exact hp (h ((mem_exteriorSupport_iff K S I p).mpr
      ((exponent_ne_zero_iff_dvd I.val p.val).mp hn)))

theorem rowSupported_squarefree (k f r : Ext) :
    Squarefree (rowSupported K S k f r).val.val :=
  (residualPart_squarefree k.val).squarefree_of_dvd
    (supportedIdeal_dvd ((rowSupport K S f r).image Subtype.val) (residualPart k.val))

theorem rowSupported_coords_squarefree (k f r : Ext) :
    PrimeArithmetic.Squarefree (ExteriorArithmetic.coords K S) (rowSupported K S k f r) :=
  (ExteriorArithmetic.coords_squarefree_iff K S _).mpr (rowSupported_squarefree K S k f r)

theorem rowSupported_coords_supported (k f r : Ext) :
    PrimeCoordinates.Supported (ExteriorArithmetic.coords K S) (rowSupport K S f r)
      (rowSupported K S k f r) :=
  (supported_coords_iff K S _ _).mpr
    (supportedExterior_support K S (rowSupport K S f r) (exteriorResidualPart K S k))

theorem powerful_coords (k : Ext) (p : ExteriorPrime K S) :
    PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) (exteriorPowerfulPart K S k) p = 0 ∨
      2 ≤ PrimeCoordinates.valuation (ExteriorArithmetic.coords K S) (exteriorPowerfulPart K S k) p :=
  powerfulPart_powerful k.val p.val

theorem primeSetIdeal_dvd_of_primes (T : Finset (ExteriorPrime K S)) (I : Ext)
    (hI : ∀ p ∈ T, p.val.asIdeal ∣ I.val.val) :
    (primeSetIdeal K S T).val.val ∣ I.val.val := by
  have hd : PrimeArithmetic.fromSupport (ExteriorArithmetic.coords K S) T ∣ I := by
    apply (PrimeArithmetic.fromSupport_dvd_iff (ExteriorArithmetic.coords K S) T I).mpr
    intro p hp
    apply Finsupp.mem_support_iff.mpr
    change primeExponents I.val p.val ≠ 0
    exact (exponent_ne_zero_iff_dvd I.val p.val).mpr (hI p hp)
  rw [fromSupport_eq_primeSetIdeal K S] at hd
  exact (ExteriorArithmetic.dvd_iff K S _ _).mp hd

theorem rowSupport_primeSetIdeal_dvd (f r : Ext) :
    (primeSetIdeal K S (rowSupport K S f r)).val.val ∣ f.val.val * r.val.val := by
  apply primeSetIdeal_dvd_of_primes K S _ (exteriorMul K S f r)
  intro p hp
  rcases Finset.mem_union.mp hp with hf | hr
  · exact dvd_mul_of_dvd_left ((mem_exteriorSupport_iff K S f p).mp hf) _
  · exact dvd_mul_of_dvd_right ((mem_exteriorSupport_iff K S r p).mp hr) _

/-- The fixed support cost uses the original label and puncture once,
including their possible common prime factors. -/
theorem rowSupport_norm_le (f r : Ext) :
    exteriorNorm K S (primeSetIdeal K S (rowSupport K S f r)) ≤
      exteriorNorm K S f * exteriorNorm K S r := by
  have hn := Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors (f.val * r.val))
    (map_dvd Ideal.absNorm (rowSupport_primeSetIdeal_dvd K S f r))
  simpa only [exteriorNorm, Submonoid.coe_mul, map_mul, Nat.cast_mul] using
    (Nat.cast_le.mpr hn :
      ((primeSetIdeal K S (rowSupport K S f r)).val.val.absNorm : ℝ) ≤
        ((f.val.val * r.val.val).absNorm : ℝ))

def frozenPair (f r k : Ext) : Ext × Ext :=
  (exteriorPowerfulPart K S k, rowSupported K S k f r)

def frozenPairs (f r : Ext) (rows : Finset Ext) : Finset (Ext × Ext) :=
  rows.image (frozenPair K S f r)

theorem frozenPairs_spec (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (hp : p ∈ frozenPairs K S f r rows) :
    Powerful p.1.val ∧ Squarefree p.2.val.val ∧ exteriorSupport K S p.2 ⊆ rowSupport K S f r := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨powerfulPart_powerful k.val, rowSupported_squarefree K S k f r,
    supportedExterior_support K S (rowSupport K S f r) (exteriorResidualPart K S k)⟩

/-- One constant precedes the label, puncture, powerful-part ceiling
and original finite row set. The one-half exponent is paid exactly once. -/
theorem exists_frozen_pair_count (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f r : Ext) (U : ℝ), 1 ≤ U → ∀ rows : Finset Ext,
      (∀ k ∈ rows, exteriorNorm K S (exteriorPowerfulPart K S k) ≤ U) →
      ((frozenPairs K S f r rows).card : ℝ) ≤ C * Real.sqrt U *
        (U * exteriorNorm K S f * exteriorNorm K S r) ^ eps := by
  obtain ⟨C, hC, hb⟩ := HeckeSkeleton.LowFrozenCube.frozen_pair_count_small_power
    (ExteriorArithmetic.coords K S) (ExteriorArithmetic.normHom K S)
    (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
    (ExteriorArithmetic.countConstant K) (ExteriorArithmetic.countConstant_pos K)
    (ExteriorArithmetic.one_le_natNorm K S) (ExteriorArithmetic.linearNormCounting K S)
    eps heps
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro f r U hU rows hrows
  have hpairs := hb U hU (rowSupport K S f r) (frozenPairs K S f r rows) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨powerful_coords K S k, hrows k hk,
      rowSupported_coords_squarefree K S k f r, rowSupported_coords_supported K S k f r⟩)
  simp only [fromSupport_eq_primeSetIdeal, ExteriorArithmetic.normHom_apply] at hpairs
  have hU0 := zero_le_one.trans hU
  have hpower := Real.rpow_le_rpow
    (mul_nonneg hU0 (exteriorNorm_pos K S _).le)
    (mul_le_mul_of_nonneg_left (rowSupport_norm_le K S f r) hU0) heps.le
  calc
    _ ≤ C * Real.sqrt U *
        (U * exteriorNorm K S (primeSetIdeal K S (rowSupport K S f r))) ^ eps := hpairs
    _ ≤ C * Real.sqrt U * (U * (exteriorNorm K S f * exteriorNorm K S r)) ^ eps :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg hC.le (Real.sqrt_nonneg _))
    _ = C * Real.sqrt U * (U * exteriorNorm K S f * exteriorNorm K S r) ^ eps := by
      rw [mul_assoc U]
    _ ≤ _ := by
      gcongr
      exact le_max_right (1 : ℝ) C

def fiber (f r : Ext) (rows : Finset Ext) (p : Ext × Ext) : Finset Ext :=
  rows.filter (fun k => frozenPair K S f r k = p)

def residualRows (f r : Ext) (rows : Finset Ext) (p : Ext × Ext) : Finset Ext :=
  (fiber K S f r rows p).image (fun k => rowResidual K S k f r)

def reconstruct (p : Ext × Ext) (a : Ext) : Ext :=
  exteriorMul K S (exteriorMul K S p.1 p.2) a

theorem reconstruct_residual (f r k : Ext) (p : Ext × Ext)
    (hp : frozenPair K S f r k = p) :
    reconstruct K S p (rowResidual K S k f r) = k := by
  rw [← hp]
  exact ProviderTerminalConductor.row_decomposition K S k f r

/-- Fixing the actual powerful and supported pair leaves an injective
residual coordinate. No norm argument or energy premise is needed. -/
theorem rowResidual_injective_on_pair (f r : Ext) (p : Ext × Ext) :
    Set.InjOn (fun k => rowResidual K S k f r) {k | frozenPair K S f r k = p} := by
  intro k hk l hl he
  calc
    k = reconstruct K S p (rowResidual K S k f r) := (reconstruct_residual K S f r k p hk).symm
    _ = reconstruct K S p (rowResidual K S l f r) := congrArg (reconstruct K S p) he
    _ = l := reconstruct_residual K S f r l p hl

theorem rowResidual_injective_on_fiber (f r : Ext) (rows : Finset Ext) (p : Ext × Ext) :
    Set.InjOn (fun k => rowResidual K S k f r) (fiber K S f r rows p) := by
  intro k hk l hl he
  exact rowResidual_injective_on_pair K S f r p
    (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2 he

theorem reconstruct_mem (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) :
    reconstruct K S p a ∈ fiber K S f r rows p := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  rw [reconstruct_residual K S f r k p (Finset.mem_filter.mp hk).2]
  exact hk

theorem residualRows_squarefree (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) : Squarefree a.val.val := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  exact rowResidual_squarefree K S k f r

theorem residualRows_coprime_label (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) : IsCoprime a.val.val f.val.val := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  exact rowResidual_coprime_label K S k f r

theorem residualRows_coprime_puncture (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) : IsCoprime a.val.val r.val.val := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  exact rowResidual_coprime_puncture K S k f r

theorem residualRows_coprime_frozen (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) :
    IsCoprime a.val.val (frozenIdeal K S p.1 p.2 f).val.val := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  have hp := (Finset.mem_filter.mp hk).2
  have hP : exteriorPowerfulPart K S k = p.1 := congrArg Prod.fst hp
  have hJ : rowSupported K S k f r = p.2 := congrArg Prod.snd hp
  simpa only [hP, hJ] using rowResidual_coprime_frozen K S k f r

theorem reconstruct_norm (p : Ext × Ext) (a : Ext) :
    exteriorNorm K S (reconstruct K S p a) =
      exteriorNorm K S p.1 * exteriorNorm K S p.2 * exteriorNorm K S a := by
  simp only [reconstruct, exteriorNorm_mul]

theorem residualRows_norm_le (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (R : ℝ) (hrows : ∀ k ∈ rows, exteriorNorm K S k ≤ R)
    (a : Ext) (ha : a ∈ residualRows K S f r rows p) :
    exteriorNorm K S a ≤ R / (exteriorNorm K S p.1 * exteriorNorm K S p.2) := by
  have hm := (Finset.mem_filter.mp (reconstruct_mem K S f r rows p a ha)).1
  have hn := hrows (reconstruct K S p a) hm
  rw [reconstruct_norm] at hn
  apply (le_div_iff₀ (mul_pos (exteriorNorm_pos K S p.1) (exteriorNorm_pos K S p.2))).mpr
  simpa only [mul_comm (exteriorNorm K S a)] using hn

variable {A : Type*} [AddCommMonoid A]

/-- The equality applies in particular to the positive squared norm
of the literal reflected row. -/
theorem sum_fiber_eq_residualRows (f r : Ext) (rows : Finset Ext) (p : Ext × Ext)
    (a : Ext → A) :
    (∑ k ∈ fiber K S f r rows p, a k) =
      ∑ k₁ ∈ residualRows K S f r rows p, a (reconstruct K S p k₁) := by
  symm
  rw [residualRows, Finset.sum_image (fun k hk l hl he =>
    rowResidual_injective_on_fiber K S f r rows p hk hl he)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [reconstruct_residual K S f r k p (Finset.mem_filter.mp hk).2]

/-- The full finite row sum first partitions by its genuine frozen
pair and then reindexes each fiber by the actual residual ideal. -/
theorem sum_rows_eq_pairs_residualRows (f r : Ext) (rows : Finset Ext) (a : Ext → A) :
    (∑ k ∈ rows, a k) =
      ∑ p ∈ frozenPairs K S f r rows,
        ∑ k₁ ∈ residualRows K S f r rows p, a (reconstruct K S p k₁) := by
  calc
    _ = ∑ p ∈ frozenPairs K S f r rows, ∑ k ∈ fiber K S f r rows p, a k := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun k hk => Finset.mem_image_of_mem (frozenPair K S f r) hk) a
    _ = _ := Finset.sum_congr rfl (fun p hp => sum_fiber_eq_residualRows K S f r rows p a)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalCounts
