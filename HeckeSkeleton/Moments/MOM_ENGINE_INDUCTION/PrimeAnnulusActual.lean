import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeAnnulusArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeAnnulusModel
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependent
import HeckeSkeleton.PrimeCancellationBounds

/-!
# Actual uniform prime-slot cancellation for the recursive family

The analytic `SlotData` is constructed here from the real Hecke
continuation, its Euler coefficients, the original packet zero boundary,
and the proved common finite-order growth estimate.  Its conductor and
the original deletion mask are bounded by the complete-row arithmetic
calibration, including the entire remaining ideal.

One finite Euler order is selected on a fixed positive annulus before
the model, row, slot, base, profile budget or height.  The logarithmic
cost is then absorbed in an arbitrarily small fixed base exponent.  No
prime-polynomial estimate, recursive moment bound or final parent bound
is a hypothesis.  The proof also allows the endpoint B = 1.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationBounds
open HeckeSkeleton.Moments.UniformAmplify
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellationPrimePowers
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

private theorem primeConstant_mul_height_le (a b delta C degreeBound H f : ℝ)
    (hb : 0 ≤ b) (hdegree : 0 ≤ degreeBound) (hf : 1 ≤ f) :
    PrimeAnnulus.primeConstant a b delta C degreeBound (H * f) ≤
      PrimeAnnulus.primeConstant a b delta C degreeBound H * f := by
  have htail : 0 ≤ degreeBound * (1 + ratio) * Real.sqrt b +
      b * degreeBound * PrimeAnnulus.threshold a b := by
    have hr := ratio_pos.le
    have ht := (PrimeAnnulus.threshold_pos a b).le
    positivity
  have hm := le_mul_of_one_le_right htail hf
  calc
    _ = (24 * C * H / delta ^ 2) * f +
        (degreeBound * (1 + ratio) * Real.sqrt b +
          b * degreeBound * PrimeAnnulus.threshold a b) := by
      unfold PrimeAnnulus.primeConstant
      ring
    _ ≤ (24 * C * H / delta ^ 2) * f +
        (degreeBound * (1 + ratio) * Real.sqrt b +
          b * degreeBound * PrimeAnnulus.threshold a b) * f :=
      add_le_add le_rfl hm
    _ = _ := by unfold PrimeAnnulus.primeConstant; ring

/-- A genuine pointwise estimate with the two remaining logarithmic
powers exposed.  The contour buffer and constant may vary after the
single common Euler order has been selected. -/
theorem exists_actual_prime_slot_annulus_log_bound
    (c : TargetContext K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (theta : Finset (HeckeCharacter K))
    (hinverse : ∀ chi ∈ theta, chi⁻¹ ∈ theta)
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ J : ℕ, ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 4 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (node : Node K omegaCharacter psiCharacter)
        (extra : NonzeroIdeal K → NonzeroIdeal K) (U weight Cp Hp T : ℝ),
      1 ≤ U → 0 ≤ weight → 0 ≤ Cp → 0 ≤ T →
      node.width ≤ 2 → node.parameters.z = node.data.geometry.totalLength →
      node.data.theta = theta → (∀ j, node.data.slotCoefficient j ∈ theta) →
      ReflectionRowCalibration S probe rows node extra U →
      (∀ u I, node.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      ModelProfileControl node.data J weight Cp Hp lower upper T →
      ∀ u ∈ pairedRows node.data node.parameters U, ∀ j : Fin node.data.geometry.slotCount,
      ‖primePolynomial node.data j u U 0‖ ^ 2 ≤
        C * (Cp * (1 + T) ^ Hp) ^ 2 * (1 + Real.log U) ^ 2 *
          U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length +
            (2 * delta) * (node.data.geometry.slots j).length) := by
  obtain ⟨J, Cstar, Dprofile, hCstar, hDprofile, hprime⟩ :=
    exists_primePolynomial_annulus_bound (K := K)
      (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
      lower upper hlower hinterval
  obtain ⟨Cg, hCg, hgrowth⟩ :=
    exists_uniform_finiteOrder_polynomial K (isComplex_of_family K c)
  let degree : ℕ := 2 * Fintype.card (InfinitePlace K)
  let Dconductor : ℝ := 3 + Real.log (primeThetaConductorConstant S theta)
  have hDconductor : 0 ≤ Dconductor := by
    have hlog := Real.log_nonneg (primeThetaConductorConstant_one_le S theta)
    dsimp only [Dconductor]
    linarith
  let H : ℝ := 1 + Real.log Cg + (5 / 8 : ℝ) * Dconductor +
    eulerLogSize K + 3 * (degree : ℝ)
  have hH : 0 ≤ H := by
    have hlog := Real.log_nonneg hCg
    have heuler := eulerLogSize_nonneg K
    dsimp only [H]
    positivity
  have hfixed : 1 ≤ (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot S (Ideal.absNorm_eq_zero_iff.mp hz)))
  let Bmask : ℝ :=
    (3 + Real.log (Ideal.absNorm (fixedRowDeletionIdeal S) : ℝ)) / Real.log 2
  have hBmask : 0 ≤ Bmask := by
    have hlog := Real.log_nonneg hfixed
    dsimp only [Bmask]
    exact div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  refine ⟨J, ?_⟩
  intro delta hdelta hdeltaUpper
  let Kslot : ℝ := max 1
    ((PrimeAnnulus.primeConstant lower upper delta Cstar (primeCountConstant K) H + Bmask) *
      Dprofile)
  have hKslot : 1 ≤ Kslot := le_max_left _ _
  refine ⟨Kslot ^ 2, pow_pos (zero_lt_one.trans_le hKslot) _, ?_⟩
  intro node extra U weight Cp Hp T hU hweight hCp hT hwidth hlength htheta hslots
    cal hmask hprofiles u hu j
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hheightFactor : 0 ≤ (1 + T) ^ Hp := Real.rpow_nonneg (by linarith) _
  let f : ℝ := 1 + Real.log U
  have hf : 1 ≤ f := by dsimp only [f]; linarith [Real.log_nonneg hU]
  have hfnon : 0 ≤ f := zero_le_one.trans hf
  let chi := node.data.rowCharacter u * node.data.slotCoefficient j
  obtain ⟨hfinite, hne, hnon⟩ := paired_slot_finite_nonNorm_of_theta
    node.data node.parameters U theta htheta hinverse hslots hlength u hu j
  have hpacket := finiteOrder_mem_heckePacket K c.family.omega chi hfinite
  have hbeta : 1 / 2 ≤ c.family.B := by linarith [c.family.B_lower]
  have hQ := one_le_actualConductorScale K chi hnon
  let data := emptySlotData K c.family.omega chi hpacket hnon c.family.B hbeta
    c.family.boundary Cg (heckeConductorScale K chi) (5 / 8) degree hCg hQ
    (by norm_num) (hgrowth chi hfinite hne)
  have hQlog : Real.log (heckeConductorScale K chi) ≤ Dconductor * f :=
    cal.slot_log_conductor_le theta hslots hU hwidth u hu j
  have hheight : heightConstant data.analytic + 3 * (data.analytic.k : ℝ) ≤ H * f := by
    change 1 + Real.log Cg + (5 / 8 : ℝ) * Real.log (heckeConductorScale K chi) +
      eulerLogSize K + 3 * (degree : ℝ) ≤ H * f
    have h := conductor_height_budget Cg Dconductor (eulerLogSize K)
      (heckeConductorScale K chi) U 1 0 degree hCg (eulerLogSize_nonneg K)
      hU (by norm_num) (by norm_num)
      (by simpa only [Real.rpow_zero, mul_one] using hQlog)
    simpa only [Real.rpow_zero, mul_one, H, f] using h
  have hdeleted : (((((node.data.geometry.slots j).support 0
      (U ^ (node.data.geometry.slots j).length)).filter
        (fun p => node.data.commonMask u p.asIdeal = false)).card : ℝ)) ≤ Bmask * f :=
    cal.deleted_prime_count hmask hU hwidth u hu _
  have hraw := hprime node.data u j U weight Cp Hp T c.family.B delta
    (primeCountConstant K) (H * f) (Bmask * f)
    hU hweight hCp hT hprofiles data rfl
    (emptySlotData_coefficient K c.family.omega chi hpacket hnon c.family.B hbeta
      c.family.boundary Cg (heckeConductorScale K chi) (5 / 8) degree hCg hQ
      (by norm_num) (hgrowth chi hfinite hne))
    hheight hbeta c.family.B_upper hdelta hdeltaUpper hdeleted
  have hcost : PrimeAnnulus.primeConstant lower upper delta Cstar
        (primeCountConstant K) (H * f) + Bmask * f ≤
      (PrimeAnnulus.primeConstant lower upper delta Cstar
        (primeCountConstant K) H + Bmask) * f := by
    calc
      _ ≤ PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) H * f + Bmask * f :=
        add_le_add (primeConstant_mul_height_le lower upper delta Cstar
          (primeCountConstant K) H f (hlower.trans_le hinterval).le
          (primeCountConstant_pos K).le hf) le_rfl
      _ = _ := by ring
  have hcoefficient : (PrimeAnnulus.primeConstant lower upper delta Cstar
        (primeCountConstant K) (H * f) + Bmask * f) * Dprofile ≤ Kslot * f := by
    calc
      _ ≤ ((PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) H + Bmask) * f) * Dprofile :=
        mul_le_mul_of_nonneg_right hcost hDprofile.le
      _ = ((PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) H + Bmask) * Dprofile) * f := by ring
      _ ≤ Kslot * f := mul_le_mul_of_nonneg_right (le_max_right _ _) hfnon
  have hamplitude := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoefficient hCp) hheightFactor
  have hamplitudeNonneg : 0 ≤
      (PrimeAnnulus.primeConstant lower upper delta Cstar (primeCountConstant K) (H * f) +
        Bmask * f) * Dprofile * Cp * (1 + T) ^ Hp := by
    have hpc := PrimeAnnulus.primeConstant_nonneg lower upper delta Cstar
      (primeCountConstant K) (H * f) (hlower.trans_le hinterval).le hCstar.le
      (primeCountConstant_pos K).le (mul_nonneg hH hfnon)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (add_nonneg hpc (mul_nonneg hBmask hfnon))
        hDprofile.le) hCp) hheightFactor
  refine hraw.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hamplitudeNonneg hamplitude 2)
      (Real.rpow_nonneg hUp.le _)).trans_eq ?_)
  dsimp only [f]
  ring

/-- Every actual retained slot satisfies the required small-loss bound.
Only upper bounds for the row width and total slot length are used; an
individual slot may have arbitrarily small positive length. -/
theorem exists_actual_prime_slot_annulus_bound
    (c : TargetContext K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (theta : Finset (HeckeCharacter K))
    (hinverse : ∀ chi ∈ theta, chi⁻¹ ∈ theta)
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ J : ℕ, ∀ loss : ℝ, 0 < loss → ∃ C : ℝ, 0 < C ∧
      ∀ (node : Node K omegaCharacter psiCharacter)
        (extra : NonzeroIdeal K → NonzeroIdeal K) (U weight Cp Hp T : ℝ),
      1 ≤ U → 0 ≤ weight → 0 ≤ Cp → 0 ≤ T →
      node.width ≤ 2 → node.parameters.z = node.data.geometry.totalLength →
      node.data.geometry.totalLength ≤ 2 →
      node.data.theta = theta → (∀ j, node.data.slotCoefficient j ∈ theta) →
      ReflectionRowCalibration S probe rows node extra U →
      (∀ u I, node.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      ModelProfileControl node.data J weight Cp Hp lower upper T →
      ∀ u ∈ pairedRows node.data node.parameters U, ∀ j : Fin node.data.geometry.slotCount,
      ‖primePolynomial node.data j u U 0‖ ^ 2 ≤
        C * (Cp * (1 + T) ^ Hp) ^ 2 *
          U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss) := by
  obtain ⟨J, hlogBound⟩ := exists_actual_prime_slot_annulus_log_bound
    (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
    c S probe rows theta hinverse lower upper hlower hinterval
  refine ⟨J, ?_⟩
  intro loss hloss
  let delta := PrimeCancellationUniformity.contourBuffer (loss / 2) 2
  have hhalf : 0 < loss / 2 := by linarith
  have hdelta : 0 < delta := PrimeCancellationUniformity.contourBuffer_pos hhalf
  have hdeltaUpper : delta ≤ 1 / 4 :=
    PrimeCancellationUniformity.contourBuffer_le_quarter _ _
  obtain ⟨C, hC, hbound⟩ := hlogBound delta hdelta hdeltaUpper
  let Cl := PrimeCancellationUniformity.logAbsorptionConstant 2 (loss / 2)
  have hCl : 0 < Cl := PrimeCancellationUniformity.logAbsorptionConstant_pos 2 hhalf
  refine ⟨C * Cl, mul_pos hC hCl, ?_⟩
  intro node extra U weight Cp Hp T hU hweight hCp hT hwidth hlength htotal
    htheta hslots cal hmask hprofiles u hu j
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hraw := hbound node extra U weight Cp Hp T hU hweight hCp hT
    hwidth hlength htheta hslots cal hmask hprofiles u hu j
  have hlengthSlot : (node.data.geometry.slots j).length ≤ 2 :=
    (Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin node.data.geometry.slotCount))) =>
        (node.data.geometry.slots k).length_pos.le) (Finset.mem_univ j)).trans htotal
  have hdeltaLoss : (2 * delta) * (node.data.geometry.slots j).length ≤ loss / 2 :=
    PrimeCancellationUniformity.contourBuffer_total_loss hhalf hlengthSlot
  have hlog : (1 + Real.log U) ^ 2 ≤ Cl * U ^ (loss / 2) :=
    PrimeCancellationUniformity.one_add_log_pow_le_rpow 2 hhalf hU
  calc
    _ ≤ C * (Cp * (1 + T) ^ Hp) ^ 2 * (1 + Real.log U) ^ 2 *
        U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length +
          (2 * delta) * (node.data.geometry.slots j).length) := hraw
    _ ≤ C * (Cp * (1 + T) ^ Hp) ^ 2 * (1 + Real.log U) ^ 2 *
        U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (add_le_add le_rfl hdeltaLoss))
        (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (sq_nonneg _))
    _ ≤ C * (Cp * (1 + T) ^ Hp) ^ 2 * (Cl * U ^ (loss / 2)) *
        U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss / 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hC.le (sq_nonneg _)))
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by
      rw [show (2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss =
        loss / 2 + ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss / 2)
        by ring, Real.rpow_add hUp (loss / 2)
          ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss / 2)]
      ring

/-- The exact shape consumed by `ActualCapacityProduction` at its real
evaluation height.  All profiles are evaluated at that height before
the same proved estimate is applied.  On the actual time-independent
family, `ProfileTimeIndependent.freeze_modelProfileControl_iff` derives
this frozen profile premise from the original order-zero-time control.
No uniform-in-time bound for arbitrary, unfrozen profiles is asserted. -/
theorem exists_actual_prime_slot_capacity_bound
    (c : TargetContext K)
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (probe : ProbeData K S) (rows : RowCharacterInput K S probe)
    (theta : Finset (HeckeCharacter K))
    (hinverse : ∀ chi ∈ theta, chi⁻¹ ∈ theta)
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ J : ℕ, ∀ loss : ℝ, 0 < loss → ∃ C : ℝ, 0 < C ∧
      ∀ (node : Node K omegaCharacter psiCharacter)
        (extra : NonzeroIdeal K → NonzeroIdeal K) (U time weight Cp Hp T : ℝ),
      1 ≤ U → 0 ≤ weight → 0 ≤ Cp → 0 ≤ T →
      node.width ≤ 2 → node.parameters.z = node.data.geometry.totalLength →
      node.data.geometry.totalLength ≤ 2 → node.parameters.κ = 2 * c.family.B - 1 →
      node.data.theta = theta → (∀ j, node.data.slotCoefficient j ∈ theta) →
      ReflectionRowCalibration S probe rows node extra U →
      (∀ u I, node.data.commonMask u I =
        (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) →
      ModelProfileControl (freezeMomentTime node.data time) J weight Cp Hp lower upper T →
      ∀ u ∈ pairedRows node.data node.parameters U, ∀ j : Fin node.data.geometry.slotCount,
      ‖primePolynomial node.data j u U time‖ ^ 2 ≤
        (C * (Cp * (1 + T) ^ Hp) ^ 2 * U ^ loss) *
          U ^ (node.parameters.κ * (node.data.geometry.slots j).length) := by
  obtain ⟨J, hprime⟩ := exists_actual_prime_slot_annulus_bound
    (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
    c S probe rows theta hinverse lower upper hlower hinterval
  refine ⟨J, ?_⟩
  intro loss hloss
  obtain ⟨C, hC, hbound⟩ := hprime loss hloss
  refine ⟨C, hC, ?_⟩
  intro node extra U time weight Cp Hp T hU hweight hCp hT hwidth hlength htotal
    hkappa htheta hslots cal hmask hprofiles u hu j
  have frozenCal : ReflectionRowCalibration S probe rows (node.freezeTime time) extra U :=
    ⟨cal.identify, cal.product_budget⟩
  have hraw := hbound (node.freezeTime time) extra U weight Cp Hp T
    hU hweight hCp hT hwidth hlength htotal htheta hslots frozenCal hmask hprofiles u hu j
  change ‖primePolynomial (freezeMomentTime node.data time) j u U 0‖ ^ 2 ≤
    C * (Cp * (1 + T) ^ Hp) ^ 2 *
      U ^ ((2 * c.family.B - 1) * (node.data.geometry.slots j).length + loss) at hraw
  rw [freezeMomentTime_primePolynomial] at hraw
  refine hraw.trans_eq ?_
  rw [hkappa, Real.rpow_add (zero_lt_one.trans_le hU)
    ((2 * c.family.B - 1) * (node.data.geometry.slots j).length) loss]
  ring

end HeckeSkeleton.Moments.EngineInduction
