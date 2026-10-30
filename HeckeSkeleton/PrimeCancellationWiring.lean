import HeckeSkeleton.PrimeCancellationHecke
import HeckeSkeleton.PrimeCancellationMoment
import HeckeSkeleton.PrimeCancellationBounds
import HeckeSkeleton.PrimeCancellationWindows

/-!
# Prime cancellation for the actual paired moment models

`PrimeSlotModelControl` repairs the original model interface.  It controls
the actual prime windows and the conductors of every summed row, bounds the
number of slots, and records the finite exceptional characters needed to
exclude the principal prime character.  It contains no prime-sum, moment,
Euler-series, nonvanishing, or growth estimate.

The analytic data use the actual Hecke continuation (equivalently the
deleted continuation with empty deletion).  The packet boundary is taken
from `c.family.boundary`; finite-order polynomial growth is proved by the
Hecke adapter.  The complete original mask is retained.  Both the contour
loss and the logarithmic mask/conductor losses fit the original `lamA`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationWiring

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

/-- Additional, purely structural and profile/conductor requirements on
the entire family of actual paired models.  The existing calibration and
eligibility records are retained as separate premises.

The all-row conductor bound is deliberate: physical-row calibration alone
does not cover the sum in `PairedPrimeProductBound`.  The window bound is on
the actual chosen height parameters, so no unproved height-range condition
is imported from `WholeMomentProfileControl`.
-/
structure PrimeSlotModelControl (M : SourceMomentModels K c) where
  slot_count : ∀ Z T (i : SourceMomentIndex K c Z T) s,
    (pairedModel M i s).geometry.slotCount ≤ c.geometry.slots
  inverse_mem : ∀ Z T (i : SourceMomentIndex K c Z T) s j,
    ((pairedModel M i s).slotCoefficient j)⁻¹ ∈ (pairedModel M i s).theta
  window : ∀ Z T (i : SourceMomentIndex K c Z T) s,
    Fin (pairedModel M i s).geometry.slotCount → SchwartzMap ℝ ℂ
  window_eq : ∀ Z T (i : SourceMomentIndex K c Z T) s j,
    (window Z T i s j : ℝ → ℂ) = ((pairedModel M i s).geometry.slots j).profile 0
  window_support : ∀ Z T (i : SourceMomentIndex K c Z T) s j,
    Function.support (window Z T i s j : ℝ → ℂ) ⊆ Set.Icc (1 : ℝ) 2
  window_control : ∀ seminorms : Finset (ℕ × ℕ),
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ Z T (i : SourceMomentIndex K c Z T) s j, 1 ≤ Z → 1 ≤ T →
        sourceSeminorm seminorms (window Z T i s j) ≤ C * (1 + T) ^ A
  conductor_control : ∃ D q : ℝ, 1 ≤ D ∧ 0 ≤ q ∧
    ∀ Z T (i : SourceMomentIndex K c Z T) s u,
      1 ≤ Z → 1 ≤ T → 1 ≤ momentBase i →
      u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i) →
      ∀ j, Real.log (heckeConductorScale K
        ((pairedModel M i s).rowCharacter u * (pairedModel M i s).slotCoefficient j)) ≤
          D * (1 + Real.log (momentBase i)) * (1 + T) ^ q

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
  convert hn using 1 <;> congr 1 <;> ring

/-- A uniform bound at independent external scale and height.  The constants
are chosen before both; the later `UniformMomentBound` quantifiers are weaker.
-/
theorem exists_uniform_paired_prime_bound
    (M : SourceMomentModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) M)
    (hrows : SourceRowEligibility M) (control : PrimeSlotModelControl M) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
      ∀ Z T (i : SourceMomentIndex K c Z T), 1 ≤ Z → 1 ≤ T → pairedCapacity i →
        (∑ s : SixthUnitClasses K (places K c),
          ∑ u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i),
            ‖slotProduct (pairedModel M i s) u (momentBase i) 0‖ ^ 2) ≤
          C * (momentBase i) ^
            (1 + (2 * c.family.B - 1) * selectedLength i + c.family.lamA) * (1 + T) ^ A := by
  obtain ⟨seminorms, Cstar, hCstar, _, hprime⟩ :=
    exists_uniform_masked_prime_seminorm_bound
  obtain ⟨Wc, a, hWc, ha, hwindow⟩ := control.window_control seminorms
  obtain ⟨D, q, hD, hq, hconductor⟩ := control.conductor_control
  obtain ⟨Cg, hCg, hgrowth⟩ :=
    exists_uniform_finiteOrder_polynomial K (isComplex_of_family K c)
  obtain ⟨Crows, hCrows, hcount⟩ := exists_source_paired_linear_count (K := K) (c := c)
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  let H : ℝ := 1 + Real.log Cg + (5 / 8 : ℝ) * D + eulerLogSize K + 3 * (k : ℝ)
  have hEuler : 0 ≤ eulerLogSize K := (norm_nonneg _).trans
    (deleted_centerLog_bound K 1 ∅ 0)
  have hH : 0 ≤ H := by
    have hc := Real.log_nonneg hCg
    dsimp only [H]
    positivity
  let bad := canonicalFixedBadPrimeSupport c
  let Bmask : ℝ := (Real.log (idealNorm K bad.ideal) + 1) / Real.log 2
  have hbadLog : 0 ≤ Real.log (idealNorm K bad.ideal) :=
    Real.log_nonneg (one_le_idealNorm K bad.ideal)
  have hBmask : 0 ≤ Bmask := by
    dsimp only [Bmask]
    exact div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
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
  have hXpos : 0 < momentBase i := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have hsector (s : SixthUnitClasses K (places K c)) :
      (∑ u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i),
        ‖slotProduct (pairedModel M i s) u (momentBase i) 0‖ ^ 2) ≤
        Csector * (momentBase i) ^
          (1 + (2 * c.family.B - 1) * selectedLength i + c.family.lamA) * (1 + T) ^ A := by
    by_cases hX : 1 ≤ momentBase i
    · let f : ℝ := (1 + Real.log (momentBase i)) * (1 + T) ^ q
      let amplitude : ℝ := Kslot * (1 + Real.log (momentBase i)) * (1 + T) ^ (q + a)
      have hf : 1 ≤ f := one_le_mul_of_one_le_of_one_le (by linarith [Real.log_nonneg hX])
        (Real.one_le_rpow (by linarith) hq)
      have hamp : 0 ≤ amplitude := mul_nonneg
        (mul_nonneg (zero_le_one.trans hKslot) (by linarith [Real.log_nonneg hX]))
        (Real.rpow_nonneg (by linarith) _)
      have hslot (u : NonzeroIdeal K)
          (hu : u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i))
          (j : Fin (pairedModel M i s).geometry.slotCount) :
          ‖primePolynomial (pairedModel M i s) j u (momentBase i) 0‖ ^ 2 ≤
            amplitude ^ 2 * (momentBase i) ^
              ((2 * c.family.B - 1) * ((pairedModel M i s).geometry.slots j).length +
                (2 * δ) * ((pairedModel M i s).geometry.slots j).length) := by
        let χ := (pairedModel M i s).rowCharacter u * (pairedModel M i s).slotCoefficient j
        have hfinite : FiniteOrder χ := source_paired_slot_finite M hrows i s u j
        have hne : χ ≠ 1 := source_paired_slot_character_ne_one M hrows i s
          (control.inverse_mem Z T i s) u hu j
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
            (momentBase i) T q k hCg hEuler hX hT hq (hconductor Z T i s u hZ hT hX hu j)
        have hdelete : (((((pairedModel M i s).geometry.slots j).support 0
            ((momentBase i) ^ ((pairedModel M i s).geometry.slots j).length)).filter
              (fun p => (pairedModel M i s).commonMask u p.asIdeal = false)).card : ℝ) ≤
                Bmask * f := by
          have hb := source_paired_deleted_count_le_base (momentRowCharacters K c) M hcal
            bad i s u hu (((pairedModel M i s).geometry.slots j).support 0
              ((momentBase i) ^ ((pairedModel M i s).geometry.slots j).length))
          refine hb.trans ((logarithmic_mask_budget (Real.log (idealNorm K bad.ideal))
            (momentBase i) hbadLog hX).trans ?_)
          change Bmask * (1 + Real.log (momentBase i)) ≤
            Bmask * ((1 + Real.log (momentBase i)) * (1 + T) ^ q)
          have hpow := Real.one_le_rpow (show 1 ≤ 1 + T by linarith) hq
          simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hBmask (show 0 ≤ 1 + Real.log (momentBase i) by
              linarith [Real.log_nonneg hX]))
        have hbudget : (uniformConstant δ Cstar (primeCountConstant K) (H * f) + Bmask * f) *
            sourceSeminorm seminorms W ≤ amplitude := by
          exact profile_budget δ Cstar (primeCountConstant K) H Bmask Wc
            (momentBase i) T q a (sourceSeminorm seminorms W) hCstar.le
            (primeCountConstant_pos K).le hH hBmask (zero_le_one.trans hWc) hX hT hq
            (sourceSeminorm_nonneg _ _) (hwindow Z T i s j hZ hT)
        exact primePolynomial_bound_of_analytic_data (pairedModel M i s) u j (momentBase i)
          W (control.window_eq Z T i s j) c.family.B (primeCountConstant K) data rfl
          (emptySlotData_coefficient K c.family.omega χ hpacket hnon c.family.B hβ
            c.family.boundary Cg (heckeConductorScale K χ) (5 / 8) k hCg hQ
            (by norm_num) (hgrowth χ hfinite hne)) seminorms Cstar δ (H * f) (Bmask * f)
          hprime (control.window_support Z T i s j) hheight hβ hB.le hδ hδ' hX hdelete
          amplitude hamp hbudget
      have hloss : (∑ j : Fin (pairedModel M i s).geometry.slotCount,
          (2 * δ) * ((pairedModel M i s).geometry.slots j).length) ≤ c.family.lamA / 2 := by
        rw [← Finset.mul_sum]
        change 2 * δ * (pairedModel M i s).geometry.totalLength ≤ c.family.lamA / 2
        rw [(hrows.geometry Z T i s).2]
        exact PrimeCancellationUniformity.contourBuffer_total_loss
          (show 0 < c.family.lamA / 2 by linarith [c.family.lamA_pos])
          (selectedLength_le_slots_mul_mesh_of_pairedCapacity i hcap)
      have henergy := source_paired_energy_le_of_slot_bounds M hrows i s
        (2 * c.family.B - 1) (c.family.lamA / 2) Crows hX
        (fun _ => amplitude ^ 2)
        (fun j => (2 * δ) * ((pairedModel M i s).geometry.slots j).length)
        (fun _ => sq_nonneg _) hloss (hcount M Z T i s hX) hslot
      have hprod : (∏ _j : Fin (pairedModel M i s).geometry.slotCount, amplitude ^ 2) ≤
          Kslot ^ (2 * c.geometry.slots) * (1 + Real.log (momentBase i)) ^ (2 * c.geometry.slots) *
            (1 + T) ^ ((q + a) * (2 * c.geometry.slots : ℕ)) := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          finite_slot_budget (pairedModel M i s).geometry.slotCount c.geometry.slots
            Kslot (momentBase i) T (q + a) (control.slot_count Z T i s) hKslot hX hT
            (add_nonneg hq ha)
      refine henergy.trans (le_trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCrows.le)
          (Real.rpow_nonneg hXpos.le _)) ?_)
      exact absorb_slot_logarithms c.geometry.slots Crows Kslot (momentBase i) T (q + a)
        (2 * c.family.B - 1) (selectedLength i) c.family.lamA hCrows.le
        (zero_le_one.trans hKslot) hX hT c.family.lamA_pos
    · rw [pairedRows_eq_empty_of_base_lt_one M i s (lt_of_not_ge hX), Finset.sum_empty]
      exact mul_nonneg (mul_nonneg hCsector (Real.rpow_nonneg hXpos.le _))
        (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ ∑ _s : SixthUnitClasses K (places K c), Csector * (momentBase i) ^
        (1 + (2 * c.family.B - 1) * selectedLength i + c.family.lamA) * (1 + T) ^ A :=
      Finset.sum_le_sum (fun s _ => hsector s)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The corrected MI-P-PRIME-CANCELLATION-BELOW-ONE theorem.  It has the exact
original `PairedPrimeProductBound` conclusion for any model satisfying the
explicit corrected structural contract.  `momentModels` is never invoked.
-/
theorem paired_primes_below_one_of_models
    (M : SourceMomentModels K c) (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) M)
    (hrows : SourceRowEligibility M) (control : PrimeSlotModelControl M) :
    PairedPrimeProductBound K c M (2 * c.family.B - 1) := by
  obtain ⟨A, C, hA, hC, hbound⟩ := exists_uniform_paired_prime_bound M hB hcal hrows control
  refine ⟨A, 1, hA, zero_lt_one, ?_⟩
  intro τ hτ _hτupper
  refine ⟨1, C, le_rfl, hC, ?_⟩
  intro Z hZ i _hbin hcap
  exact hbound Z (Z ^ τ) i hZ (Real.one_le_rpow hZ hτ.le) hcap

#print axioms primePolynomial_bound_of_analytic_data
#print axioms exists_uniform_paired_prime_bound
#print axioms paired_primes_below_one_of_models

end HeckeSkeleton.PrimeCancellationWiring
