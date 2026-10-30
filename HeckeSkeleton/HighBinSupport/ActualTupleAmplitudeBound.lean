import HeckeSkeleton.HighBinSupport.ActualPrimeNormalizerCancellation
import HeckeSkeleton.HighBinSupport.BoundaryTupleScalar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-!
The original subset amplitude has a fixed coarse polynomial bound once
the literal row Euler continuations have a common pointwise bound.
All subset ideals, repeated-prime images, window weights and coefficients
are the original objects. No estimate for a contour or a high-bin sum is
assumed. The prime-window norm envelope is derived from its support.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinBoundary.ActualTuple

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Taking an image of selected slots can only remove repeated positive
norm factors. Thus even this coarse bound does not need tuple injectivity. -/
theorem subsetPrimeIdeal_norm_le_tuple_product (g : PrimeWindowGeometry)
    (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) :
    exteriorNorm K S (subsetPrimeIdeal K S p J) ≤
      ∏ i : Fin g.slots, ((p i).val.asIdeal.absNorm : ℝ) := by
  have he : (subsetPrimeIdeal K S p J).val.val.absNorm =
      ∏ q ∈ J.image p, q.val.asIdeal.absNorm := by
    change (∏ q ∈ (J.image p).image Subtype.val, q.asIdeal).absNorm = _
    rw [map_prod, Finset.prod_image (by
      intro a _ b _ h
      exact Subtype.ext h)]
  have hnorm (q : ExteriorPrime K S) : 1 ≤ q.val.asIdeal.absNorm :=
    (one_lt_primeIdeal_absNorm K q.val).le
  have himage : (∏ q ∈ J.image p, q.val.asIdeal.absNorm) ≤
      ∏ i ∈ J, (p i).val.asIdeal.absNorm :=
    Finset.prod_image_le_of_one_le (fun q _ => hnorm q)
  have hsubset : (∏ i ∈ J, (p i).val.asIdeal.absNorm) ≤
      ∏ i : Fin g.slots, (p i).val.asIdeal.absNorm :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ J)
      (fun i _ _ => hnorm (p i))
  have h := he.trans_le (himage.trans hsubset)
  change ((subsetPrimeIdeal K S p J).val.val.absNorm : ℝ) ≤ _
  exact_mod_cast h

theorem primeScale_power_slots (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) :
    (primeScale g Z) ^ g.slots = Z ^ (1 / 6 : ℝ) := by
  have hJ : (g.slots : ℝ) ≠ 0 := by exact_mod_cast g.slots_pos.ne'
  unfold primeScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
  congr 1
  field_simp [hJ]

/-- Both selected and marked ideal norms lie in this explicit interval. -/
theorem subsetPrimeIdeal_norm_range (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (hZ : 0 < Z)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) :
    1 ≤ exteriorNorm K S (subsetPrimeIdeal K S p J) ∧
      exteriorNorm K S (subsetPrimeIdeal K S p J) ≤
        (2 : ℝ) ^ g.slots * Z ^ (1 / 6 : ℝ) := by
  refine ⟨one_le_idealNorm K _, ?_⟩
  apply (subsetPrimeIdeal_norm_le_tuple_product K S g p J).trans
  calc
    _ ≤ ∏ i : Fin g.slots, (2 * primeScale g Z) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
        (fun i _ => ActualPrimeNormalizer.primeWindow_norm_upper K S g T Z hZ i (p i)
          ((Fintype.mem_piFinset.mp hp) i))
    _ = (2 : ℝ) ^ g.slots * Z ^ (1 / 6 : ℝ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow,
        primeScale_power_slots g Z hZ]

/-- Every subset uses the actual whole-index-marked row continuation.
Only their lower-level pointwise bound is assumed, and their finite sum
costs 32^J Z^4, independent of every external tail derivative order. -/
theorem tupleMellinAmplitude_bound_of_rowEuler_bound
    (P : ProbeData K S) (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S) (Z : ℝ) (hZ : 1 ≤ Z) (s w z : ℂ)
    (hs : s.re ≤ 2) (hw0 : -1 ≤ w.re) (hw1 : w.re ≤ 1) (hz : z.re = 17 / 50)
    (M : ℝ) (hM : 0 ≤ M)
    (p : Fin g.slots → ExteriorPrime K S)
    (hp : p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (hrow : ∀ Q : Finset (ExteriorPrime K S), Q ⊆ Finset.univ.image p →
      ‖rowEulerContinuation K S P ψ E Q u s w z‖ ≤ M) :
    ‖ActualPrimeNormalizer.tupleMellinAmplitude K S P ψ E g u Z s w z p‖ ≤
      (32 : ℝ) ^ g.slots * Z ^ 4 * M := by
  have hZ0 : 0 < Z := by linarith
  let R : ℝ := (2 : ℝ) ^ g.slots * Z ^ (1 / 6 : ℝ)
  have hterm (J : Finset (Fin g.slots)) :
      ‖(-1 : ℂ) ^ J.card *
        (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (-(3 / 2 : ℂ)) *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
        ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S p J) : ℝ) : ℂ) ^ (1 / 2 - z) *
        ((Z * exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℝ) : ℂ) ^ (s + z - 1) *
        ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S p J) : ℝ) : ℂ) ^ (w - 1) *
        rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z‖ ≤
          Z ^ 3 * R ^ 4 * M := by
    have hA := subsetPrimeIdeal_norm_range K S g T Z hZ0 p hp J
    have hB := subsetPrimeIdeal_norm_range K S g T Z hZ0 p hp (Finset.univ \ J)
    have hc : ‖(-1 : ℂ) ^ J.card *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val)‖ ≤ 1 := by
      simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_conj] using
        norm_heckeIdealCoefficient_le_one K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val
    have hL := hrow ((Finset.univ \ J).image p)
      (Finset.image_subset_image (Finset.sdiff_subset))
    have h := TupleScalar.compensatedTerm_norm_bound Z
      (exteriorNorm K S (subsetPrimeIdeal K S p J))
      (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J))) R M s w z
      ((-1 : ℂ) ^ J.card *
        conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val))
      (rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z)
      hZ hA.1 hB.1 hA.2 hB.2 hs hw0 hw1 hz hc hL
    simpa only [TupleScalar.compensationScalar, mul_assoc, mul_left_comm, mul_comm] using h
  have hsum : ‖ActualPrimeNormalizer.tupleMellinAmplitude K S P ψ E g u Z s w z p‖ ≤
      (2 : ℝ) ^ g.slots * (Z ^ 3 * R ^ 4 * M) := by
    unfold ActualPrimeNormalizer.tupleMellinAmplitude
    calc
      _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          ‖(-1 : ℂ) ^ J.card *
            (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (-(3 / 2 : ℂ)) *
            conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
            ((Z ^ (17 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S p J) : ℝ) : ℂ) ^ (1 / 2 - z) *
            ((Z * exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℝ) : ℂ) ^ (s + z - 1) *
            ((Z ^ (23 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S p J) : ℝ) : ℂ) ^ (w - 1) *
            rowEulerContinuation K S P ψ E ((Finset.univ \ J).image p) u s w z‖ := norm_sum_le _ _
      _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          Z ^ 3 * R ^ 4 * M := Finset.sum_le_sum (fun J _ => hterm J)
      _ = _ := by simp [nsmul_eq_mul]
  have hsmall : (Z ^ (1 / 6 : ℝ)) ^ 4 ≤ Z := by
    calc
      _ = Z ^ ((1 / 6 : ℝ) * 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
        norm_num
      _ ≤ Z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
      _ = Z := Real.rpow_one _
  have hR4 : R ^ 4 ≤ ((2 : ℝ) ^ g.slots) ^ 4 * Z := by
    dsimp only [R]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  have hcoef : (2 : ℝ) ^ g.slots * ((2 : ℝ) ^ g.slots) ^ 4 = (32 : ℝ) ^ g.slots := by
    calc
      _ = ((2 : ℝ) ^ g.slots) ^ 5 := by ring
      _ = ((2 : ℝ) ^ 5) ^ g.slots := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by norm_num
  apply hsum.trans
  calc
    _ ≤ (2 : ℝ) ^ g.slots * (Z ^ 3 * (((2 : ℝ) ^ g.slots) ^ 4 * Z) * M) := by gcongr
    _ = ((2 : ℝ) ^ g.slots * ((2 : ℝ) ^ g.slots) ^ 4) * Z ^ 4 * M := by ring
    _ = _ := by rw [hcoef]

#print axioms subsetPrimeIdeal_norm_le_tuple_product
#print axioms tupleMellinAmplitude_bound_of_rowEuler_bound

end HighBinBoundary.ActualTuple
