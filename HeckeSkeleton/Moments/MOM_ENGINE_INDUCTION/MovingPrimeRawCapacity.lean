import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeAnnulusSlice
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingPrimeArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SchwartzEulerControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ProfileNormalizationInput
import HeckeSkeleton.PrimeCancellationBounds

/-!
# The canonical raw prime windows supply actual capacity estimates

Only the authoritative raw window's prime representative, support and
finite Schwartz seminorm bound are used. The row domain may be
arbitrary: no ordinary or inverse profile control outside that domain
is inferred. The evaluation time is the original calibration's time.

The finite seminorm set is selected before the loss, and the numerical
constant precedes every index type, moving recipe, raw radius, Fourier
parameter and scale. The output prime cost is C times the square of the
actual raw radius times the allotted small power of the common base.
It can therefore be inserted directly in CapacityInput.primeBound.
The original raw radius remains a cost in the later kernel integration;
it is never silently replaced by one before normalization.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationBounds
open HeckeSkeleton.PrimeCancellationMoment
open HeckeSkeleton.Moments.UniformAmplify
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellationPrimePowers
open scoped Classical BigOperators SchwartzMap

universe u

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The prime part of the actual raw window gives precisely one
literal slice. Neither the row domain nor any plain profile is used. -/
theorem exists_rawProfileWindow_prime_sliceControl
    (lower upper : ℝ) (hlower : 0 < lower) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ D : ℝ, 0 < D ∧
      ∀ (d : MomentData K omegaCharacter psiCharacter) (radius : ℝ)
        (rowDomain : Set (NonzeroIdeal K)) (heightDomain : Set ℝ)
        (window : EngineStep.RawProfileWindow rowDomain heightDomain
          (Icc lower upper) s d radius),
      ∀ time ∈ heightDomain, ∀ j : Fin d.geometry.slotCount,
      SliceControl J 0 (D * radius) 0 lower upper 0 ((d.geometry.slots j).profile time) := by
  obtain ⟨s, D, hD, hslice⟩ :=
    exists_schwartz_sliceControl_bound lower upper hlower J 0
  refine ⟨s, D, hD, ?_⟩
  intro d radius rowDomain heightDomain window time htime j
  have heq : (d.geometry.slots j).profile time =
      (window.primeRep j time : ℝ → ℂ) := funext (window.prime_eq j time)
  rw [heq]
  exact hslice (window.primeRep j time) radius
    (window.prime_support j time htime) (window.prime_bound j time htime)

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

/-- This conclusion has the actual CapacityInput.prime_bound shape.
The recipe and raw window are original arithmetic and profile data;
there is no prime-polynomial or completed capacity estimate among the
premises. The one coefficient is uniform even in the Fourier space. -/
theorem exists_moving_raw_prime_capacity_bound
    (c : TargetContext K) (A : DedekindZetaZeroFree.SArithmeticData K)
    (probe : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (rows : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) probe)
    (theta : Finset (HeckeCharacter K))
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper) :
    ∃ s : Finset (ℕ × ℕ), ∀ loss : ℝ, 0 < loss →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) (data : X → MomentData K omegaCharacter psiCharacter)
        (Q : EngineStep.CompleteMovingRowRecipe A probe rows data)
        (xi : X) (a : RealParameters) (U width time radius : ℝ)
        (rowDomain : Set (NonzeroIdeal K)) (heightDomain : Set ℝ)
        (window : EngineStep.RawProfileWindow rowDomain heightDomain
          (Icc lower upper) s (data xi) radius),
      time ∈ heightDomain → 1 ≤ U → width ≤ 2 →
      a.z = (data xi).geometry.totalLength → (data xi).geometry.totalLength ≤ 2 →
      a.κ = 2 * c.family.B - 1 → (data xi).theta ⊆ theta →
      (∀ j, (data xi).slotCoefficient j ∈ (data xi).theta) →
      (∀ j, ((data xi).slotCoefficient j)⁻¹ ∈ (data xi).theta) →
      Q.FullJointBudget U width →
      ∀ v ∈ pairedRows (data xi) a U, ∀ j : Fin (data xi).geometry.slotCount,
      ‖primePolynomial (data xi) j v U time‖ ^ 2 ≤
        (C * radius ^ 2 * U ^ loss) * U ^ (a.κ * ((data xi).geometry.slots j).length) := by
  obtain ⟨J, Cstar, Dprofile, hCstar, hDprofile, hprime⟩ :=
    exists_primePolynomial_annulus_slice_bound (K := K)
      (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
      lower upper hlower hinterval
  obtain ⟨s, Dslice, hDslice, hrawSlice⟩ :=
    exists_rawProfileWindow_prime_sliceControl (K := K)
      (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter)
      lower upper hlower J
  obtain ⟨Cg, hCg, hgrowth⟩ :=
    exists_uniform_finiteOrder_polynomial K (isComplex_of_family K c)
  let degree : ℕ := 2 * Fintype.card (InfinitePlace K)
  let Dconductor : ℝ := 3 + Real.log (primeThetaConductorConstant
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (MovingRecipe.primeBackgrounds theta))
  have hDconductor : 0 ≤ Dconductor := by
    have hlog := Real.log_nonneg (primeThetaConductorConstant_one_le
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (MovingRecipe.primeBackgrounds theta))
    dsimp only [Dconductor]
    linarith
  let H : ℝ := 1 + Real.log Cg + (5 / 8 : ℝ) * Dconductor +
    eulerLogSize K + 3 * (degree : ℝ)
  have hH : 0 ≤ H := by
    have hlog := Real.log_nonneg hCg
    have heuler := eulerLogSize_nonneg K
    dsimp only [H]
    positivity
  have hfixed : 1 ≤ (Ideal.absNorm
      (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Ideal.absNorm_eq_zero_iff.mp hz)))
  let Bmask : ℝ :=
    (3 + Real.log (Ideal.absNorm (fixedRowDeletionIdeal
      (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ)) / Real.log 2
  have hBmask : 0 ≤ Bmask := by
    have hlog := Real.log_nonneg hfixed
    dsimp only [Bmask]
    exact div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  refine ⟨s, ?_⟩
  intro loss hloss
  let delta := PrimeCancellationUniformity.contourBuffer (loss / 2) 2
  have hhalf : 0 < loss / 2 := by linarith
  have hdelta : 0 < delta := PrimeCancellationUniformity.contourBuffer_pos hhalf
  have hdeltaUpper : delta ≤ 1 / 4 :=
    PrimeCancellationUniformity.contourBuffer_le_quarter _ _
  let Kslot : ℝ := max 1
    ((PrimeAnnulus.primeConstant lower upper delta Cstar (primeCountConstant K) H + Bmask) *
      Dprofile * Dslice)
  have hKslot : 1 ≤ Kslot := le_max_left _ _
  let Cl := PrimeCancellationUniformity.logAbsorptionConstant 2 (loss / 2)
  have hCl : 0 < Cl := PrimeCancellationUniformity.logAbsorptionConstant_pos 2 hhalf
  refine ⟨Kslot ^ 2 * Cl, mul_pos (pow_pos (zero_lt_one.trans_le hKslot) _) hCl, ?_⟩
  intro X data Q xi a U width time radius rowDomain heightDomain window htime
    hU hwidth hlength htotal hkappa htheta hslots hinverse hbudget v hv j
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hradius : 0 ≤ radius :=
    (apply_nonneg _ (window.primeRep j time)).trans (window.prime_bound j time htime)
  let d := freezeMomentTime (data xi) time
  have hprofileEq : (d.geometry.slots j).profile 0 =
      ((data xi).geometry.slots j).profile time := by
    funext y
    change ((data xi).geometry.slots j).profile time y * profilePower 0 y = _
    rw [profilePower_zero, mul_one]
  have hprofile : SliceControl J 0 (Dslice * radius) 0 lower upper 0
      ((d.geometry.slots j).profile 0) := by
    rw [hprofileEq]
    exact hrawSlice (data xi) radius rowDomain heightDomain window time htime j
  let f : ℝ := 1 + Real.log U
  have hf : 1 ≤ f := by dsimp only [f]; linarith [Real.log_nonneg hU]
  have hfnon : 0 ≤ f := zero_le_one.trans hf
  let chi := (data xi).rowCharacter v * (data xi).slotCoefficient j
  have hfinite : FiniteOrder chi :=
    ((data xi).rowCharacter_finite v).mul ((data xi).theta_finite _ (hslots j))
  have hne : chi ≠ 1 := paired_slot_character_ne_one
    (data xi) a U hlength.symm hinverse v hv j
  have hnon : ∀ t : ℝ, chi ≠ heckeNormTwist K t :=
    nonNorm_of_finiteOrder_ne_one K chi hfinite hne
  have hpacket := finiteOrder_mem_heckePacket K c.family.omega chi hfinite
  have hbeta : 1 / 2 ≤ c.family.B := by linarith [c.family.B_lower]
  have hQ := one_le_actualConductorScale K chi hnon
  let slotData := emptySlotData K c.family.omega chi hpacket hnon c.family.B hbeta
    c.family.boundary Cg (heckeConductorScale K chi) (5 / 8) degree hCg hQ
    (by norm_num) (hgrowth chi hfinite hne)
  have hc : Q.correction ∈ insert 1 theta := by
    rcases Q.correction_mem xi with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (htheta h))
  have hfixedCharacter : (data xi).slotCoefficient j * Q.correction ∈
      MovingRecipe.primeBackgrounds theta :=
    Finset.mem_image.mpr ⟨(Q.correction, (data xi).slotCoefficient j),
      Finset.mem_product.mpr ⟨hc, htheta (hslots j)⟩, rfl⟩
  have hallowed : (data xi).allowedRow v :=
    (((data xi).rows_spec _ v).mp (Finset.mem_filter.mp hv).1).1
  have hscale := MovingRecipe.row_scale_le_fullJointBudget Q U width hbudget xi
    ((data xi).slotCoefficient j) v hallowed
  have hslotScale : heckeConductorScale K chi ≤
      primeThetaConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (MovingRecipe.primeBackgrounds theta) * U ^ (2 : ℝ) := by
    calc
      _ = heckeConductorScale K ((data xi).slotCoefficient j * (data xi).rowCharacter v) :=
        congrArg (heckeConductorScale K) (mul_comm _ _)
      _ ≤ reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          ((data xi).slotCoefficient j * Q.correction) * U ^ width := hscale
      _ ≤ _ := mul_le_mul
        (reflectionConductorConstant_le_primeTheta
          (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (MovingRecipe.primeBackgrounds theta)
          _ hfixedCharacter)
        (Real.rpow_le_rpow_of_exponent_le hU hwidth)
        (Real.rpow_nonneg hUp.le _)
        (zero_le_one.trans (primeThetaConductorConstant_one_le
          (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (MovingRecipe.primeBackgrounds theta)))
  have hQlog : Real.log (heckeConductorScale K chi) ≤ Dconductor * f := by
    have h := logQ_le_of_norm_polynomial _
      (primeThetaConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (MovingRecipe.primeBackgrounds theta)) U U 2 (zero_lt_one.trans_le hQ)
      (primeThetaConductorConstant_one_le (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (MovingRecipe.primeBackgrounds theta))
      hUp (le_refl U) hU (by norm_num) hslotScale
    dsimp only [Dconductor, f]
    convert h using 1 <;> ring
  have hheight : heightConstant slotData.analytic + 3 * (slotData.analytic.k : ℝ) ≤ H * f := by
    change 1 + Real.log Cg + (5 / 8 : ℝ) * Real.log (heckeConductorScale K chi) +
      eulerLogSize K + 3 * (degree : ℝ) ≤ H * f
    have h := conductor_height_budget Cg Dconductor (eulerLogSize K)
      (heckeConductorScale K chi) U 1 0 degree hCg (eulerLogSize_nonneg K)
      hU (by norm_num) (by norm_num)
      (by simpa only [Real.rpow_zero, mul_one] using hQlog)
    simpa only [Real.rpow_zero, mul_one, H, f] using h
  have hdeleted : (((((d.geometry.slots j).support 0
      (U ^ (d.geometry.slots j).length)).filter
        (fun p => d.commonMask v p.asIdeal = false)).card : ℝ)) ≤ Bmask * f :=
    MovingRecipe.deleted_prime_count Q xi a U width hbudget hU hwidth v hv _
  have hraw := hprime d v j U (Dslice * radius) 0 0 c.family.B delta
    (primeCountConstant K) (H * f) (Bmask * f) hU (mul_nonneg hDslice.le hradius)
    (le_refl (0 : ℝ)) hprofile slotData rfl
    (emptySlotData_coefficient K c.family.omega chi hpacket hnon c.family.B hbeta
      c.family.boundary Cg (heckeConductorScale K chi) (5 / 8) degree hCg hQ
      (by norm_num) (hgrowth chi hfinite hne))
    hheight hbeta c.family.B_upper hdelta hdeltaUpper hdeleted
  change ‖primePolynomial (freezeMomentTime (data xi) time) j v U 0‖ ^ 2 ≤ _ at hraw
  rw [freezeMomentTime_primePolynomial] at hraw
  simp only [Real.rpow_zero, mul_one] at hraw
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
        (primeCountConstant K) (H * f) + Bmask * f) * Dprofile * Dslice ≤ Kslot * f := by
    calc
      _ ≤ ((PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) H + Bmask) * f) * Dprofile * Dslice :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcost hDprofile.le) hDslice.le
      _ = ((PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) H + Bmask) * Dprofile * Dslice) * f := by ring
      _ ≤ Kslot * f := mul_le_mul_of_nonneg_right (le_max_right _ _) hfnon
  have hamplitude := mul_le_mul_of_nonneg_right hcoefficient hradius
  have hamplitudeNonneg : 0 ≤
      (PrimeAnnulus.primeConstant lower upper delta Cstar (primeCountConstant K) (H * f) +
        Bmask * f) * Dprofile * Dslice * radius := by
    have hpc := PrimeAnnulus.primeConstant_nonneg lower upper delta Cstar
      (primeCountConstant K) (H * f) (hlower.trans_le hinterval).le hCstar.le
      (primeCountConstant_pos K).le (mul_nonneg hH hfnon)
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (add_nonneg hpc (mul_nonneg hBmask hfnon)) hDprofile.le) hDslice.le) hradius
  have hlogBound : ‖primePolynomial (data xi) j v U time‖ ^ 2 ≤
      Kslot ^ 2 * radius ^ 2 * f ^ 2 *
        U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length +
          (2 * delta) * ((data xi).geometry.slots j).length) := by
    have hraw' : ‖primePolynomial (data xi) j v U time‖ ^ 2 ≤
        ((PrimeAnnulus.primeConstant lower upper delta Cstar
          (primeCountConstant K) (H * f) + Bmask * f) * Dprofile * Dslice * radius) ^ 2 *
          U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length +
            (2 * delta) * ((data xi).geometry.slots j).length) := by
      have hslotLength : (d.geometry.slots j).length =
          ((data xi).geometry.slots j).length := rfl
      simpa only [hslotLength, mul_assoc] using hraw
    refine hraw'.trans ((mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hamplitudeNonneg hamplitude 2)
        (Real.rpow_nonneg hUp.le _)).trans_eq ?_)
    ring
  have hlengthSlot : ((data xi).geometry.slots j).length ≤ 2 :=
    (Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin (data xi).geometry.slotCount))) =>
        ((data xi).geometry.slots k).length_pos.le) (Finset.mem_univ j)).trans htotal
  have hdeltaLoss : (2 * delta) * ((data xi).geometry.slots j).length ≤ loss / 2 :=
    PrimeCancellationUniformity.contourBuffer_total_loss hhalf hlengthSlot
  have hlog : f ^ 2 ≤ Cl * U ^ (loss / 2) :=
    PrimeCancellationUniformity.one_add_log_pow_le_rpow 2 hhalf hU
  have hpowers : U ^ (loss / 2) *
      U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length + loss / 2) =
        U ^ loss * U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length) := by
    rw [← Real.rpow_add hUp (loss / 2)
      ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length + loss / 2),
      ← Real.rpow_add hUp loss ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length)]
    congr 1
    ring
  calc
    _ ≤ Kslot ^ 2 * radius ^ 2 * f ^ 2 *
        U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length +
          (2 * delta) * ((data xi).geometry.slots j).length) := hlogBound
    _ ≤ Kslot ^ 2 * radius ^ 2 * f ^ 2 *
        U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length + loss / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU (add_le_add le_rfl hdeltaLoss))
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    _ ≤ Kslot ^ 2 * radius ^ 2 * (Cl * U ^ (loss / 2)) *
        U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length + loss / 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (Real.rpow_nonneg hUp.le _)
    _ = (Kslot ^ 2 * Cl * radius ^ 2) *
        (U ^ (loss / 2) *
          U ^ ((2 * c.family.B - 1) * ((data xi).geometry.slots j).length + loss / 2)) := by ring
    _ = _ := by rw [hpowers, hkappa]; ring

end HeckeSkeleton.Moments.EngineInduction
