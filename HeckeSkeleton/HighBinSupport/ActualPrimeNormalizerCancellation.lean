import HeckeSkeleton.HighBinSupport.PositiveNormalizer
import HeckeGeneral.Analysis.PhysicalProbeContours
/-!
The literal prime normalizer cancels the mass of the same positive windows.
This boundary estimate does not use a prime-density theorem, a nonzero
window assertion, or a small-power inverse-normalizer input. The zero-mass
case follows the original totalized division and is covered explicitly.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinBoundary.ActualPrimeNormalizer

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def slotMassWeight (g : PrimeWindowGeometry) (Z : ℝ) (i : Fin g.slots)
    (p : ExteriorPrime K S) : ℝ :=
  (windowWeight K S g Z i p).re * (p.val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ))

def tupleMassWeight (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) : ℝ :=
  ∏ i, slotMassWeight K S g Z i (p i)

theorem windowWeight_eq_real (g : PrimeWindowGeometry) (Z : ℝ)
    (i : Fin g.slots) (p : ExteriorPrime K S) :
    windowWeight K S g Z i p = ((windowWeight K S g Z i p).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [windowWeight, g.real_valued]

theorem norm_windowWeight (g : PrimeWindowGeometry) (Z : ℝ)
    (i : Fin g.slots) (p : ExteriorPrime K S) :
    ‖windowWeight K S g Z i p‖ = (windowWeight K S g Z i p).re := by
  rw [windowWeight_eq_real K S g Z i p, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (g.nonnegative i _)]

theorem slotMassWeight_nonneg (g : PrimeWindowGeometry) (Z : ℝ)
    (i : Fin g.slots) (p : ExteriorPrime K S) :
    0 ≤ slotMassWeight K S g Z i p :=
  mul_nonneg (g.nonnegative i _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem tupleMassWeight_nonneg (g : PrimeWindowGeometry) (Z : ℝ)
    (p : Fin g.slots → ExteriorPrime K S) :
    0 ≤ tupleMassWeight K S g Z p :=
  Finset.prod_nonneg (fun i _ => slotMassWeight_nonneg K S g Z i (p i))

/-- The same identity-ray filter occurs on both sides. -/
theorem normalizerSlot_eq_real_mass (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots) :
    normalizerSlot K S g T Z i =
      ((∑ p ∈ primeWindow K S g T Z i, slotMassWeight K S g Z i p : ℝ) : ℂ) := by
  unfold normalizerSlot
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hpow : (p.val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) =
      (((p.val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
    simp
  rw [hpow, windowWeight_eq_real K S g Z i p]
  exact (Complex.ofReal_mul _ _).symm

/-- Exact product-of-slot-sums expansion of the actual normalizer. -/
theorem primeNormalizer_eq_tuple_mass (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) :
    primeNormalizer K S g T Z =
      ((-1 : ℂ) ^ g.slots * (Z : ℂ) ^ (-(1 / 36 : ℂ))) *
        ((∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          tupleMassWeight K S g Z p : ℝ) : ℂ) := by
  unfold primeNormalizer
  simp_rw [normalizerSlot_eq_real_mass]
  rw [← Complex.ofReal_prod, Finset.prod_univ_sum]
  rfl

/-- The literal window cutoff supplies the only norm envelope needed here. -/
theorem primeWindow_norm_upper (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (hZ : 0 < Z)
    (i : Fin g.slots) (p : ExteriorPrime K S) (hp : p ∈ primeWindow K S g T Z i) :
    (p.val.asIdeal.absNorm : ℝ) ≤ 2 * primeScale g Z := by
  obtain ⟨q, _hq, heq⟩ := Finset.mem_image.mp hp
  have hq := Finset.mem_filter.mp q.property
  have hv : q.val = p.val := congrArg Subtype.val heq
  rw [hv] at hq
  have htest := g.support_annular i hq.2.2.2
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hZ _)).mp htest.2).le

/-- A literal per-tuple bound with q^(-5/6) normalized weights gives a
whole finite-sum bound without any prime-normalizer lower estimate. -/
theorem normalized_tuple_sum_bound (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (hZ : 0 < Z)
    (F : (Fin g.slots → ExteriorPrime K S) → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      ‖F p‖ ≤ M * ∏ i : Fin g.slots,
        ((p i).val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ))) :
    ‖(∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) * F p) /
      primeNormalizer K S g T Z‖ ≤ Z ^ (1 / 36 : ℝ) * M := by
  let A := Fintype.piFinset (fun i => primeWindow K S g T Z i)
  have hterm (p : Fin g.slots → ExteriorPrime K S) (hp : p ∈ A) :
      ‖(∏ i : Fin g.slots, windowWeight K S g Z i (p i)) * F p‖ ≤
        M * tupleMassWeight K S g Z p := by
    rw [norm_mul, norm_prod]
    simp_rw [norm_windowWeight]
    calc
      _ ≤ (∏ i : Fin g.slots, (windowWeight K S g Z i (p i)).re) *
          (M * ∏ i : Fin g.slots, ((p i).val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hF p hp)
          (Finset.prod_nonneg (fun i _ => g.nonnegative i _))
      _ = M * tupleMassWeight K S g Z p := by
        unfold tupleMassWeight slotMassWeight
        rw [Finset.prod_mul_distrib]
        ring
  have h := PositiveNormalizer.norm_sum_div_scaled_nonneg_sum_le A
    (tupleMassWeight K S g Z)
    (fun p => (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) * F p)
    ((-1 : ℂ) ^ g.slots * (Z : ℂ) ^ (-(1 / 36 : ℂ))) M hM
    (fun p _ => tupleMassWeight_nonneg K S g Z p) hterm
  have hc : ‖(-1 : ℂ) ^ g.slots * (Z : ℂ) ^ (-(1 / 36 : ℂ))‖ =
      Z ^ (-(1 / 36 : ℝ)) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    norm_num
  rw [norm_inv, hc, Real.rpow_neg hZ.le, inv_inv] at h
  simpa only [A, primeNormalizer_eq_tuple_mass] using h

/-- A coarse supremum bound only costs the fixed power Z^(1/6).
The norm envelope is derived from the actual window and support in (1,2). -/
theorem normalized_tuple_sum_coarse_bound (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (hZ : 0 < Z)
    (F : (Fin g.slots → ExteriorPrime K S) → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i), ‖F p‖ ≤ M) :
    ‖(∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) * F p) /
      primeNormalizer K S g T Z‖ ≤
        (2 ^ ((5 / 6 : ℝ) * (g.slots : ℝ)) * Z ^ (1 / 6 : ℝ)) * M := by
  let Q : ℝ := 2 * primeScale g Z
  let J : ℝ := (5 / 6 : ℝ) * (g.slots : ℝ)
  have hQ : 0 < Q := mul_pos (by norm_num) (Real.rpow_pos_of_pos hZ _)
  have hdamp (p : Fin g.slots → ExteriorPrime K S)
      (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) :
      1 ≤ Q ^ J * ∏ i : Fin g.slots,
        ((p i).val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) := by
    have hprod : (Q ^ (-(5 / 6 : ℝ))) ^ g.slots ≤
        ∏ i : Fin g.slots, ((p i).val.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (Finset.prod_le_prod₀
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin g.slots))) =>
            Real.rpow_nonneg hQ.le (-(5 / 6 : ℝ)))
          (fun i _ => Real.rpow_le_rpow_of_nonpos
            (show 0 < ((p i).val.asIdeal.absNorm : ℝ) from idealNorm_pos K
              ⟨(p i).val.asIdeal, mem_nonZeroDivisors_of_ne_zero (p i).val.ne_bot⟩)
            (primeWindow_norm_upper K S g T Z hZ i (p i)
              ((Fintype.mem_piFinset.mp hp) i)) (by norm_num)))
    have he : Q ^ J * (Q ^ (-(5 / 6 : ℝ))) ^ g.slots = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
      have hz : J + -(5 / 6 : ℝ) * (g.slots : ℝ) = 0 := by dsimp [J]; ring
      rw [hz, Real.rpow_zero]
    rw [← he]
    exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hQ.le _)
  have h := normalized_tuple_sum_bound K S g T Z hZ F (M * Q ^ J)
    (mul_nonneg hM (Real.rpow_nonneg hQ.le _)) (fun p hp => (hF p hp).trans (by
      have hm := mul_le_mul_of_nonneg_left (hdamp p hp) hM
      simpa only [mul_one, mul_assoc] using hm))
  have hcost : Z ^ (1 / 36 : ℝ) * Q ^ J =
      2 ^ ((5 / 6 : ℝ) * (g.slots : ℝ)) * Z ^ (1 / 6 : ℝ) :=
    PositiveNormalizer.prime_normalizer_coarse_cost g.slots g.slots_pos Z hZ
  apply h.trans_eq
  calc
    _ = (Z ^ (1 / 36 : ℝ) * Q ^ J) * M := by ring
    _ = _ := by rw [hcost]

#print axioms primeNormalizer_eq_tuple_mass
#print axioms normalized_tuple_sum_bound
#print axioms normalized_tuple_sum_coarse_bound

/-- The literal subset amplitude from the original compensated kernel.
No Euler factor is cancelled or replaced by a ratio in this definition. -/
def tupleMellinAmplitude
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ)
    (p : Fin g.slots → ExteriorPrime K S) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
    let selected := subsetPrimeIdeal K S p J
    let marked := subsetPrimeIdeal K S p (Finset.univ \ J)
    (-1 : ℂ) ^ J.card * (exteriorNorm K S selected : ℂ) ^ (-(3 / 2 : ℂ)) *
      conj (heckeIdealCoefficient K ψ marked.val) *
      ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (1 / 2 - z) *
      ((Z * exteriorNorm K S marked : ℝ) : ℂ) ^ (s + z - 1) *
      ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S selected : ℝ) : ℂ) ^ (w - 1) *
      rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]
  [∀ p : S, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S) → Measure (p.val.adicCompletion K))
variable [∀ p : S, (μ p).IsAddHaarMeasure]

/-- Exact isolation of the positive prime-window normalization. This
identity remains valid when either normalizer is zero. -/
theorem compensatedRowMellinKernel_eq_normalized_tuple_sum
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (s w z : ℂ) :
    compensatedRowMellinKernel K S μ P ψ E g T u Z s w z =
      (Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S μ P.additive z *
        mellin P.denominator.toFun w * (frequencyRowNorm K S u : ℂ) ^ (-z) /
          physicalResidueNormalizer K S μ P) *
      ((∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
          tupleMellinAmplitude K S P ψ E g u Z s w z p) /
        primeNormalizer K S g T Z) := by
  simp only [compensatedRowMellinKernel, tupleMellinAmplitude, div_eq_mul_inv, mul_inv]
  ring

/-- Actual kernel normalization consumes only a per-tuple pointwise bound.
All profiles and every marked subset remain the literal original terms. -/
theorem compensatedRowMellinKernel_bound_of_tuple_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (hZ : 0 < Z) (s w z : ℂ)
    (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      ‖tupleMellinAmplitude K S P ψ E g u Z s w z p‖ ≤ M) :
    ‖compensatedRowMellinKernel K S μ P ψ E g T u Z s w z‖ ≤
      ‖Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S μ P.additive z *
        mellin P.denominator.toFun w * (frequencyRowNorm K S u : ℂ) ^ (-z) /
          physicalResidueNormalizer K S μ P‖ *
      ((2 ^ ((5 / 6 : ℝ) * (g.slots : ℝ)) * Z ^ (1 / 6 : ℝ)) * M) := by
  rw [compensatedRowMellinKernel_eq_normalized_tuple_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (normalized_tuple_sum_coarse_bound K S g T Z hZ
      (tupleMellinAmplitude K S P ψ E g u Z s w z) M hM hF) (norm_nonneg _)

#print axioms compensatedRowMellinKernel_eq_normalized_tuple_sum
#print axioms compensatedRowMellinKernel_bound_of_tuple_bound

end HighBinBoundary.ActualPrimeNormalizer
