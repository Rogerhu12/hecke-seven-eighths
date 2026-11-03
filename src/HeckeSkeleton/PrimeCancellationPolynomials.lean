import HeckeGeneral.Analysis.MomentInputs
import PrimeCancellationAux
import PrimeCancellationPairedProfiles

/-!
# The actual moment polynomial interface for prime cancellation

This module imports the existing `MomentInputs` definitions and proves the
literal normalization and single-slot analytic transfer for `MomentData`.
It does not import the unfinished source-model or target-context pipeline.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationMoment

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-! ## Row membership, length, and nonprincipality -/

theorem mem_rows_of_mem_pairedRows (d : MomentData K ω ψ)
    (a : RealParameters) (V : ℝ) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows d a V) :
    u ∈ d.rows (V ^ (a.m + a.q)) :=
  (Finset.mem_filter.mp hu).1

theorem norm_le_of_mem_pairedRows (d : MomentData K ω ψ)
    (a : RealParameters) (V : ℝ) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows d a V) :
    idealNorm K u ≤ V ^ (a.m + a.q) :=
  ((d.rows_spec (V ^ (a.m + a.q)) u).mp
    (mem_rows_of_mem_pairedRows d a V u hu)).2

theorem not_mem_theta_of_mem_pairedRows (d : MomentData K ω ψ)
    (a : RealParameters) (V : ℝ) (u : NonzeroIdeal K)
    (hz : a.z ≠ 0) (hu : u ∈ pairedRows d a V) :
    d.rowCharacter u ∉ d.theta := by
  have hexclusion := (Finset.mem_filter.mp hu).2
  simpa only [if_neg hz] using hexclusion

theorem totalLength_nonneg (g : SlotGeometry K) : 0 ≤ g.totalLength := by
  unfold SlotGeometry.totalLength
  exact Finset.sum_nonneg (fun j _ => (g.slots j).length_pos.le)

theorem totalLength_pos_of_slot (g : SlotGeometry K) (j : Fin g.slotCount) :
    0 < g.totalLength := by
  unfold SlotGeometry.totalLength
  exact (g.slots j).length_pos.trans_le
    (Finset.single_le_sum (fun k _ => (g.slots k).length_pos.le) (Finset.mem_univ j))

theorem slotProduct_eq_one_of_totalLength_zero (d : MomentData K ω ψ)
    (hlen : d.geometry.totalLength = 0) (u : NonzeroIdeal K) (V t : ℝ) :
    slotProduct d u V t = 1 := by
  unfold slotProduct
  apply Finset.prod_eq_one
  intro j _
  exfalso
  have hpos := totalLength_pos_of_slot d.geometry j
  rw [hlen] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- Membership of the inverse slot coefficient in theta is the exact finite
exceptional-set fact needed for the nonprincipal conclusion. -/
theorem slot_character_ne_one_of_exclusion (d : MomentData K ω ψ)
    (j : Fin d.geometry.slotCount) (u : NonzeroIdeal K)
    (hrow : d.rowCharacter u ∉ d.theta)
    (hinverse : (d.slotCoefficient j)⁻¹ ∈ d.theta) :
    d.rowCharacter u * d.slotCoefficient j ≠ 1 := by
  intro heq
  have hchar := congrArg (fun χ : HeckeCharacter K => χ * (d.slotCoefficient j)⁻¹) heq
  simp only [mul_assoc, mul_inv_cancel, mul_one, one_mul] at hchar
  apply hrow
  simpa only [hchar] using hinverse

theorem paired_slot_character_ne_one (d : MomentData K ω ψ)
    (a : RealParameters) (V : ℝ)
    (hlen : d.geometry.totalLength = a.z)
    (hinverse : ∀ j, (d.slotCoefficient j)⁻¹ ∈ d.theta)
    (u : NonzeroIdeal K) (hu : u ∈ pairedRows d a V)
    (j : Fin d.geometry.slotCount) :
    d.rowCharacter u * d.slotCoefficient j ≠ 1 := by
  have hzpos : 0 < a.z := by
    rw [← hlen]
    exact totalLength_pos_of_slot d.geometry j
  exact slot_character_ne_one_of_exclusion d j u
    (not_mem_theta_of_mem_pairedRows d a V u hzpos.ne' hu) (hinverse j)

/-- A model slot-index embedding supplies the missing uniform cardinality
bound.  Total length alone does not imply this bound. -/
theorem slotCount_le_of_embedding (g : SlotGeometry K) (N : ℕ)
    (e : Fin g.slotCount ↪ Fin N) : g.slotCount ≤ N := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective

/-- Literal equality between the project's normalized finite prime
polynomial and the analytic core's finite masked sum. -/
theorem primePolynomial_eq_normalizedMaskedPrimeSum
    (d : MomentData K ω ψ) (j : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (X β degreeBound : ℝ)
    (data : PrimeCancellation.Paired.SlotData (HeightOneSpectrum (𝓞 K)) β degreeBound)
    (hnorm : data.norm = fun p => (Ideal.absNorm p.asIdeal : ℝ))
    (hcoeff : data.coefficient = primeCoefficient K (d.rowCharacter u * d.slotCoefficient j))
    (W : ℝ → ℂ) (hW : W = (d.geometry.slots j).profile 0) :
    primePolynomial d j u X 0 =
      PrimeCancellation.Paired.normalizedMaskedPrimeSum data W
        (X ^ (d.geometry.slots j).length)
        ((d.geometry.slots j).support 0 (X ^ (d.geometry.slots j).length))
        (fun p => d.commonMask u p.asIdeal) := by
  simp only [primePolynomial, PrimeCancellation.Paired.normalizedMaskedPrimeSum,
    PrimeCancellation.Paired.maskedPrimeSum, PrimeCancellationAux.maskedSum,
    maskValue, hnorm, hcoeff, hW]

theorem slotProduct_norm_sq_le_of_slot_bounds (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (V t κ eps : ℝ) (hV : 1 ≤ V)
    (C loss : Fin d.geometry.slotCount → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hloss : (∑ j, loss j) ≤ eps)
    (hslot : ∀ j, ‖primePolynomial d j u V t‖ ^ 2 ≤
      C j * V ^ (κ * (d.geometry.slots j).length + loss j)) :
    ‖slotProduct d u V t‖ ^ 2 ≤
      (∏ j, C j) * V ^ (κ * d.geometry.totalLength + eps) := by
  simpa only [slotProduct, SlotGeometry.totalLength] using
    PrimeCancellationAux.norm_product_sq_le_rpow_of_total_loss Finset.univ
      (fun j => primePolynomial d j u V t) C
      (fun j => (d.geometry.slots j).length) loss V κ eps hV
      (fun j _ => hC j) (fun j _ => hslot j) hloss

/-- A polynomial arithmetic conductor estimate gives the logarithmic
budget consumed by prime cancellation. All constants precede the row norm. -/
theorem logQ_le_of_norm_polynomial (Q C₀ N X r : ℝ)
    (hQ : 0 < Q) (hC₀ : 1 ≤ C₀) (hN : 0 < N) (hNX : N ≤ X)
    (hX : 1 ≤ X) (hr : 0 ≤ r) (hpoly : Q ≤ C₀ * N ^ r) :
    Real.log Q ≤ (1 + Real.log C₀ + r) * (1 + Real.log X) := by
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  have hlogC : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlogN : Real.log N ≤ Real.log X := Real.log_le_log hN hNX
  have hb := Real.log_le_log hQ hpoly
  rw [Real.log_mul hC₀pos.ne' (Real.rpow_pos_of_pos hN r).ne', Real.log_rpow hN] at hb
  calc
    Real.log Q ≤ Real.log C₀ + r * Real.log N := hb
    _ ≤ Real.log C₀ + r * Real.log X :=
      add_le_add (le_refl (Real.log C₀)) (mul_le_mul_of_nonneg_left hlogN hr)
    _ ≤ (1 + Real.log C₀ + r) * (1 + Real.log X) := by
      nlinarith [mul_nonneg hlogC hlogX]

#print axioms logQ_le_of_norm_polynomial

end HeckeSkeleton.PrimeCancellationMoment

namespace HeckeSkeleton.PrimeCancellationWiring

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.PrimeCancellationMoment
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles PrimeCancellation.PairedProfiles
open scoped Classical BigOperators SchwartzMap

variable {K : Type} [Field K] [NumberField K]

/-- The coefficient and normalization in the abstract theorem are literally
those of `primePolynomial`; no polynomial calibration is assumed here. -/
theorem primePolynomial_bound_of_analytic_data
    {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (j : Fin d.geometry.slotCount) (X : ℝ)
    (W : SchwartzMap ℝ ℂ) (hW : (W : ℝ → ℂ) = (d.geometry.slots j).profile 0)
    (β degreeBound : ℝ) (data : SlotData (HeightOneSpectrum (𝓞 K)) β degreeBound)
    (hnorm : data.norm = fun p => (Ideal.absNorm p.asIdeal : ℝ))
    (hcoeff : data.coefficient = primeCoefficient K (d.rowCharacter u * d.slotCoefficient j))
    (seminorms : Finset (ℕ × ℕ)) (Cstar δ H B : ℝ)
    (hbound : ∀ (W : SchwartzMap ℝ ℂ),
      Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2 →
      ∀ (β δ degreeBound H B : ℝ) (data : SlotData (HeightOneSpectrum (𝓞 K)) β degreeBound),
      heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H →
      ∀ (P : ℝ) (pool : Finset (HeightOneSpectrum (𝓞 K)))
        (keep : HeightOneSpectrum (𝓞 K) → Bool),
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 → 1 ≤ P →
      (∀ p, W (data.norm p / P) ≠ 0 → p ∈ pool) →
      ((pool.filter (fun p => keep p = false)).card : ℝ) ≤ B →
      ‖maskedPrimeSum data W P pool keep‖ ≤
        (uniformConstant δ Cstar degreeBound H + B) * sourceSeminorm seminorms W *
          P ^ (β + δ))
    (hsupport : Function.support (W : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2)
    (hH : heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H)
    (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 1) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hX : 1 ≤ X)
    (hdeleted : ((((d.geometry.slots j).support 0 (X ^ (d.geometry.slots j).length)).filter
      (fun p => d.commonMask u p.asIdeal = false)).card : ℝ) ≤ B)
    (A : ℝ) (hA : 0 ≤ A)
    (hbudget : (uniformConstant δ Cstar degreeBound H + B) *
      sourceSeminorm seminorms W ≤ A) :
    ‖primePolynomial d j u X 0‖ ^ 2 ≤
      A ^ 2 * X ^ ((2 * β - 1) * (d.geometry.slots j).length +
        (2 * δ) * (d.geometry.slots j).length) := by
  let P := X ^ (d.geometry.slots j).length
  let pool := (d.geometry.slots j).support 0 P
  have hP : 1 ≤ P := Real.one_le_rpow hX (d.geometry.slots j).length_pos.le
  have hcover : ∀ p, W (data.norm p / P) ≠ 0 → p ∈ pool := by
    intro p hp
    apply ((d.geometry.slots j).support_spec 0 P p).mpr
    simpa only [hnorm, hW] using hp
  have hb := hbound W hsupport β δ degreeBound H B data hH P pool
    (fun p => d.commonMask u p.asIdeal) hβ hβ' hδ hδ' hP hcover hdeleted
  have hb' : ‖maskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)‖ ≤
      A * P ^ (β + δ) := hb.trans (mul_le_mul_of_nonneg_right hbudget
        (Real.rpow_nonneg (zero_le_one.trans hP) _))
  have hn := PrimeCancellationAux.norm_normalized_sq_le_rpow P (β + δ) A
    (zero_lt_one.trans_le hP) hA
    (maskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)) hb'
  rw [primePolynomial_eq_normalizedMaskedPrimeSum d j u X β degreeBound data
    hnorm hcoeff W hW]
  change ‖normalizedMaskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)‖ ^ 2 ≤ _
  change ‖normalizedMaskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)‖ ^ 2 ≤
    A ^ 2 * P ^ (2 * (β + δ) - 1) at hn
  dsimp only [P] at hn
  rw [← Real.rpow_mul (zero_le_one.trans hX)] at hn
  have hexp : (d.geometry.slots j).length * (2 * (β + δ) - 1) =
      (2 * β - 1) * (d.geometry.slots j).length +
        (2 * δ) * (d.geometry.slots j).length := by ring
  rw [hexp] at hn
  exact hn

#print axioms primePolynomial_bound_of_analytic_data

end HeckeSkeleton.PrimeCancellationWiring
