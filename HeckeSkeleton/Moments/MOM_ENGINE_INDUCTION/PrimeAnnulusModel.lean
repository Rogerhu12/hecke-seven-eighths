import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularSchwartzControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceProfileAnnulus
import HeckeSkeleton.PrimeCancellationPolynomials

/-!
# Actual prime polynomials from their original annular profile control

The finite Schwartz seminorms required by the genuine prime theorem are
controlled by one preselected Euler-integral order on the same fixed
positive annulus.  The original `ModelProfileControl` supplies every
actual prime profile, with no separate Schwartz representative or prime
bound hypothesis.  The common mask and the normalization X^length are
unchanged.

The resulting coefficient is uniform in the model, row, slot, scale and
height.  Its square has height degree twice the original profile degree.
An actual ranked family may use its preselected maximal annulus and put
this finite order into the ground order; support weakening and order
weakening then give the same estimate at every rank.  This does not assume
that a canonical child retained support in the smaller interval [1,2].
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles
open scoped Classical BigOperators SchwartzMap

private theorem sourceSeminorm_le_complex_sup (s : Finset (ℕ × ℕ))
    (W : SchwartzMap ℝ ℂ) :
    sourceSeminorm s W ≤ s.sup (schwartzSeminormFamily ℂ ℝ ℂ) W := by
  unfold sourceSeminorm
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro q hq
  have h := Seminorm.le_def.mp
    (Finset.le_sup (f := schwartzSeminormFamily ℂ ℝ ℂ) hq) W
  simpa only [schwartzSeminormFamily, SchwartzMap.seminorm_apply] using h

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The Euler order and both fixed constants precede every moving
quantity. `SlotData` contains only zero-free analytic data, the exact
Euler series and elementary counting; cancellation is proved internally.
The actual Boolean mask is charged by its literal deleted-term count. -/
theorem exists_primePolynomial_annulus_bound (lower upper : ℝ)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ J : ℕ, ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (d : MomentData K omegaCharacter psiCharacter)
        (u : NonzeroIdeal K) (j : Fin d.geometry.slotCount)
        (X weight Cp Hp T β δ degreeBound H B : ℝ),
      1 ≤ X → 0 ≤ weight → 0 ≤ Cp → 0 ≤ T →
      ModelProfileControl d J weight Cp Hp lower upper T →
      ∀ data : SlotData (HeightOneSpectrum (𝓞 K)) β degreeBound,
      data.norm = (fun p => (Ideal.absNorm p.asIdeal : ℝ)) →
      data.coefficient = primeCoefficient K (d.rowCharacter u * d.slotCoefficient j) →
      heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H →
      1 / 2 ≤ β → β ≤ 1 → 0 < δ → δ ≤ 1 / 4 →
      (((((d.geometry.slots j).support 0 (X ^ (d.geometry.slots j).length)).filter
        (fun p => d.commonMask u p.asIdeal = false)).card : ℝ) ≤ B) →
      ‖primePolynomial d j u X 0‖ ^ 2 ≤
        ((PrimeAnnulus.primeConstant lower upper δ C degreeBound H + B) *
          D * Cp * (1 + T) ^ Hp) ^ 2 *
            X ^ ((2 * β - 1) * (d.geometry.slots j).length +
              (2 * δ) * (d.geometry.slots j).length) := by
  obtain ⟨s, C, hC, _hs, hprime⟩ :=
    PrimeAnnulus.exists_uniform_annulus_masked_prime_bound lower upper hlower hinterval
  obtain ⟨J, D₀, hD₀, hschwartz⟩ :=
    exists_sliceControl_schwartz_bound lower upper hlower hinterval s
  let D := 2 * D₀
  have hD : 0 < D := mul_pos (by norm_num) hD₀
  refine ⟨J, C, D, hC, hD, ?_⟩
  intro d u j X weight Cp Hp T β δ degreeBound H B hX hweight hCp hT hprofiles
    data hnorm hcoeff hH hβ hβ' hδ hδ' hdeleted
  have hprofile := modelProfileControl_prime
    (modelProfileControl_weight_zero hprofiles hweight hlower hinterval) j
  obtain ⟨W, hW, hWS⟩ := hschwartz _ (2 * Cp) Hp T hprofile
  have hWfun : (W : ℝ → ℂ) = (d.geometry.slots j).profile 0 := funext hW
  have hsupport : Function.support (W : ℝ → ℂ) ⊆ Icc lower upper := by
    intro y hy
    apply hprofile.2.1 y
    simpa only [hW y] using hy
  have hS : sourceSeminorm s W ≤ D * Cp * (1 + T) ^ Hp := by
    apply (sourceSeminorm_le_complex_sup s W).trans
    simpa only [D, mul_assoc, mul_left_comm, mul_comm] using hWS
  let P := X ^ (d.geometry.slots j).length
  let pool := (d.geometry.slots j).support 0 P
  let A := (PrimeAnnulus.primeConstant lower upper δ C degreeBound H + B) *
    D * Cp * (1 + T) ^ Hp
  have hP : 1 ≤ P := Real.one_le_rpow hX (d.geometry.slots j).length_pos.le
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hHnon : 0 ≤ H :=
    (add_nonneg (heightConstant_nonneg data.analytic) (by positivity)).trans hH
  have hBnon : 0 ≤ B := (Nat.cast_nonneg _).trans hdeleted
  have hcost : 0 ≤ PrimeAnnulus.primeConstant lower upper δ C degreeBound H + B :=
    add_nonneg (PrimeAnnulus.primeConstant_nonneg lower upper δ C degreeBound H
      (hlower.trans_le hinterval).le hC.le data.arithmetic.d_nonneg hHnon) hBnon
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg (mul_nonneg hcost hD.le) hCp)
      (Real.rpow_nonneg (by linarith) _)
  have hcover : ∀ p, W (data.norm p / P) ≠ 0 → p ∈ pool := by
    intro p hp
    apply ((d.geometry.slots j).support_spec 0 P p).mpr
    simpa only [hnorm, hWfun] using hp
  have hraw := hprime W hsupport β δ degreeBound H B data hH P pool
    (fun p => d.commonMask u p.asIdeal) hβ hβ' hδ hδ' hP hcover hdeleted
  have hb : ‖maskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)‖ ≤
      A * P ^ (β + δ) := by
    calc
      _ ≤ (PrimeAnnulus.primeConstant lower upper δ C degreeBound H + B) *
          sourceSeminorm s W * P ^ (β + δ) := hraw
      _ ≤ (PrimeAnnulus.primeConstant lower upper δ C degreeBound H + B) *
          (D * Cp * (1 + T) ^ Hp) * P ^ (β + δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hcost)
          (Real.rpow_nonneg hPpos.le _)
      _ = A * P ^ (β + δ) := by dsimp only [A]; ring
  have hn := PrimeCancellationAux.norm_normalized_sq_le_rpow P (β + δ) A hPpos hA
    (maskedPrimeSum data W P pool (fun p => d.commonMask u p.asIdeal)) hb
  rw [HeckeSkeleton.PrimeCancellationMoment.primePolynomial_eq_normalizedMaskedPrimeSum
    d j u X β degreeBound data hnorm hcoeff W hWfun]
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

end HeckeSkeleton.Moments.EngineInduction
