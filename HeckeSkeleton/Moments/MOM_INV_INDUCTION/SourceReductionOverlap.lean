import HeckeGeneral.Analysis.MomentInputs
import HeckePort.Moments.Descent.IdealMasks
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The initial overlap decomposition of the literal inverse polynomial

This file starts from `MomentData.inversePolynomial` and `slotProduct`.
It expands the actual prime windows, removes only columns whose ideal
Moebius coefficient vanishes, and groups the original summands by their
actual gcd with the selected prime product. No energy identity or moment
bound is an input.

The squarefree-overlap constructor proves the coefficient identities in
the proof of Theorem 4.1. The original zero-extended Hecke values and the
common puncture are retained, including on ramified ideals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-- The actual gcd extraction in the initial inverse moment. -/
structure SourceSquarefreeOverlap (n P : Ideal (𝓞 K)) where
  common : Ideal (𝓞 K)
  inverseResidual : Ideal (𝓞 K)
  slotResidual : Ideal (𝓞 K)
  common_eq_gcd : common = gcd n P
  inverse_eq : n = common * inverseResidual
  slots_eq : P = common * slotResidual
  common_squarefree : Squarefree common
  inverse_squarefree : Squarefree inverseResidual
  slots_squarefree : Squarefree slotResidual
  common_inverse_coprime : IsRelPrime common inverseResidual
  common_slots_coprime : IsRelPrime common slotResidual
  residual_coprime : IsCoprime inverseResidual slotResidual

/-- The common ideal and both quotients are constructed from the
original ideals. Their squarefreeness and coprimality are proved. -/
def sourceSquarefreeOverlap (n P : Ideal (𝓞 K))
    (hn : Squarefree n) (hP : Squarefree P) : SourceSquarefreeOverlap n P := by
  let j := gcd n P
  let n₀ := idealQuotient j n
  let P₀ := idealQuotient j P
  have hjn : j ∣ n := gcd_dvd_left n P
  have hjP : j ∣ P := gcd_dvd_right n P
  have hj : Squarefree j := hn.of_dvd hjn
  have hn' : n = j * n₀ := (idealQuotient_mul hjn).symm
  have hP' : P = j * P₀ := (idealQuotient_mul hjP).symm
  obtain ⟨hjn₀, _, hn₀⟩ := squarefree_mul_iff.mp (hn' ▸ hn)
  obtain ⟨hjP₀, _, hP₀⟩ := squarefree_mul_iff.mp (hP' ▸ hP)
  have hcop : IsCoprime n₀ P₀ :=
    (gcd_eq_iff_quotient_coprime j n P hj.ne_zero hjn hjP).mp rfl
  exact ⟨j, n₀, P₀, rfl, hn', hP', hj, hn₀, hP₀, hjn₀, hjP₀, hcop⟩

namespace SourceSquarefreeOverlap

variable {n P : Ideal (𝓞 K)}

/-- The residual column is squarefree even when the original column
and prime product share primes. -/
theorem column_squarefree (o : SourceSquarefreeOverlap n P) :
    Squarefree (o.inverseResidual * o.slotResidual) :=
  squarefree_mul_iff.mpr
    ⟨o.residual_coprime.isRelPrime, o.inverse_squarefree, o.slots_squarefree⟩

/-- The full original ideal product has exactly the extracted square
and the new squarefree column. -/
theorem product_identity (o : SourceSquarefreeOverlap n P) :
    n * P = o.common ^ 2 * (o.inverseResidual * o.slotResidual) := by
  rw [o.inverse_eq, o.slots_eq]
  ring

/-- This identity applies to the zero-extended ideal character. It
therefore preserves the row-character zeros before any norm bound. -/
theorem coefficient_identity (o : SourceSquarefreeOverlap n P)
    (χ : HeckeCharacter K) :
    (moebius n : ℂ) * idealCoefficient (primeCoefficient K χ) n *
        idealCoefficient (primeCoefficient K χ) P =
      (moebius o.common : ℂ) * (moebius o.slotResidual : ℂ) *
        (moebius (o.inverseResidual * o.slotResidual) : ℂ) *
        idealCoefficient (primeCoefficient K χ) o.common ^ 2 *
        idealCoefficient (primeCoefficient K χ) (o.inverseResidual * o.slotResidual) := by
  rw [o.inverse_eq, o.slots_eq]
  exact moebius_character_overlap
    (idealCoefficientHom (primeCoefficient K χ)).toMonoidHom
    o.common_inverse_coprime o.residual_coprime.isRelPrime o.slots_squarefree

/-- The extracted character square is a contraction, with no
unramifiedness assumption or removal of a displayed zero. -/
theorem scalar_norm_le (o : SourceSquarefreeOverlap n P) (χ : HeckeCharacter K) :
    ‖idealCoefficient (primeCoefficient K χ) o.common ^ 2‖ ≤ 1 :=
  overlap_scalar_norm_le
    (norm_idealCoefficient_le_one _ (norm_primeCoefficient_le_one K χ) _)

/-- The common puncture remains a mask on the extracted ideal and
on the residual column. The repeated occurrence on the overlap is
idempotent; it is never replaced by a principal character value. -/
theorem puncture_identity (o : SourceSquarefreeOverlap n P) (R : Ideal (𝓞 K)) :
    (if IsCoprime n R then (1 : ℂ) else 0) *
        (if IsCoprime P R then 1 else 0) =
      (if IsCoprime o.common R then 1 else 0) *
        (if IsCoprime (o.inverseResidual * o.slotResidual) R then 1 else 0) := by
  rw [o.inverse_eq, o.slots_eq]
  simp only [IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

/-- The norm identity used for the separated initial profile has
exactly the square of the overlap norm. -/
theorem norm_identity (o : SourceSquarefreeOverlap n P) :
    (n.absNorm : ℝ) * (P.absNorm : ℝ) =
      (o.common.absNorm : ℝ) ^ 2 *
        ((o.inverseResidual * o.slotResidual).absNorm : ℝ) := by
  have h := congrArg (fun I : Ideal (𝓞 K) => (I.absNorm : ℝ)) o.product_identity
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h

end SourceSquarefreeOverlap

variable {ω ψ : HeckeCharacter K}

/-- All tuples in the literal original prime windows, before masks. -/
def sourceSlotTuples (d : MomentData K ω ψ) (Z t : ℝ) :
    Finset (Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K)) :=
  Fintype.piFinset (fun i =>
    (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))

/-- Disjoint original slot windows make every selected tuple injective,
before any row-dependent mask is applied. -/
theorem sourceSlotTuples_injective (d : MomentData K ω ψ) (Z t : ℝ)
    (hdisjoint : ∀ i j : Fin d.geometry.slotCount, i ≠ j →
      Disjoint ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
        ((d.geometry.slots j).support t (Z ^ (d.geometry.slots j).length)))
    (p : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K))
    (hp : p ∈ sourceSlotTuples d Z t) : Function.Injective p := by
  have hmem := Fintype.mem_piFinset.mp hp
  intro i j heq
  by_contra hij
  exact Finset.disjoint_left.mp (hdisjoint i j hij) (hmem i)
    (by simpa only [heq] using hmem j)

/-- The prime product used by the gcd is genuinely squarefree. -/
theorem sourceSlotTuples_product_squarefree (d : MomentData K ω ψ) (Z t : ℝ)
    (hdisjoint : ∀ i j : Fin d.geometry.slotCount, i ≠ j →
      Disjoint ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
        ((d.geometry.slots j).support t (Z ^ (d.geometry.slots j).length)))
    (p : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K))
    (hp : p ∈ sourceSlotTuples d Z t) : Squarefree (∏ i, (p i).asIdeal) := by
  have hinj := sourceSlotTuples_injective d Z t hdisjoint p hp
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact ((p i).isCoprime_of_ne (p j) (fun h => hij (hinj h))).isRelPrime
  · intro i hi
    exact (p i).prime.squarefree

def sourceSlotTerm (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (Z t : ℝ) (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
    (primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t
        ((p.asIdeal.absNorm : ℝ) / Z ^ (d.geometry.slots i).length) *
      maskValue d u p.asIdeal)

def sourceInverseTerm (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (D t : ℝ) (n : NonzeroIdeal K) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ *
    ((moebius n.val : ℂ) * heckeIdealCoefficient K d.inverseBackground n *
      heckeIdealCoefficient K (d.rowCharacter u) n ^ d.direction *
      d.inverseTest.profile u t (idealNorm K n / D) * maskValue d u n.val)

/-- The literal product of prime windows is its finite tuple sum,
including every original profile, coefficient, and row mask. -/
theorem slotProduct_eq_sourceSlotTuples (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct d u Z t = ∑ p ∈ sourceSlotTuples d Z t,
      ∏ i, sourceSlotTerm d u Z t i (p i) := by
  unfold slotProduct primePolynomial sourceSlotTuples sourceSlotTerm
  simp only [Finset.mul_sum]
  exact Finset.prod_univ_sum _ _

theorem sourceInverseTerm_eq_zero_of_not_squarefree
    (d : MomentData K ω ψ) (u n : NonzeroIdeal K) (D t : ℝ)
    (hn : ¬ Squarefree n.val) : sourceInverseTerm d u D t n = 0 := by
  simp only [sourceInverseTerm, moebius_of_not_squarefree hn,
    Int.cast_zero, zero_mul, mul_zero]

/-- Restrict only the inverse column to its actual squarefree support. -/
theorem inversePolynomial_eq_squarefree_sum (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial d u D t =
      ∑ n ∈ (d.inverseTest.support u t D).filter (fun n => Squarefree n.val),
        sourceInverseTerm d u D t n := by
  unfold inversePolynomial
  rw [Finset.mul_sum]
  change (∑ n ∈ d.inverseTest.support u t D, sourceInverseTerm d u D t n) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hbad
  have hnsf : ¬ Squarefree n.val := by
    intro hsf
    exact hbad (Finset.mem_filter.mpr ⟨hn, hsf⟩)
  exact sourceInverseTerm_eq_zero_of_not_squarefree d u n D t hnsf

/-- The original marked polynomial is expanded before overlap
extraction; both sums remain on their exact finite source sets. -/
theorem inverse_marked_polynomial_eq_source_sum (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D Z t : ℝ) :
    inversePolynomial d u D t * slotProduct d u Z t =
      ∑ n ∈ (d.inverseTest.support u t D).filter (fun n => Squarefree n.val),
        ∑ p ∈ sourceSlotTuples d Z t,
          sourceInverseTerm d u D t n *
            ∏ i, sourceSlotTerm d u Z t i (p i) := by
  rw [inversePolynomial_eq_squarefree_sum, slotProduct_eq_sourceSlotTuples,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]

/-- The actual overlap ideal attached to an original source pair. -/
def sourceOverlapKey (d : MomentData K ω ψ)
    (x : NonzeroIdeal K × (Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K))) :
    Ideal (𝓞 K) := gcd x.1.val (∏ i, (x.2 i).asIdeal)

/-- Exact finite regrouping by the original gcd. No choice of a
post-estimate label family or source support enters this identity. -/
theorem inverse_marked_polynomial_eq_overlap_sum (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (D Z t : ℝ) :
    let pairs := ((d.inverseTest.support u t D).filter (fun n => Squarefree n.val)) ×ˢ
      sourceSlotTuples d Z t
    inversePolynomial d u D t * slotProduct d u Z t =
      ∑ j ∈ pairs.image (sourceOverlapKey d),
        ∑ x ∈ pairs.filter (fun x => sourceOverlapKey d x = j),
          sourceInverseTerm d u D t x.1 *
            ∏ i, sourceSlotTerm d u Z t i (x.2 i) := by
  dsimp only
  rw [inverse_marked_polynomial_eq_source_sum, ← Finset.sum_product]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem (sourceOverlapKey d) hx) _).symm

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
