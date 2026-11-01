import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingPrimeArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeAnalyticProvider
import HeckeSkeleton.PrimeCancellationBounds

/-!
# The original moving-character analytic provider

The uniform strip theorem, the actual Euler logarithm, and the original
finite-order zero boundary construct the single-step owner's analytic
provider.  No prime sum, descendant, or moment bound is an input.

The fixed constant is selected before the scale, kappa, moving elements,
integer powers, residual ideal, sector, correction and slot.  The actual
complete support, including the unchanged remaining mask, is charged
once.  Neither the integer exponents nor the number of moving factors
enlarge the norm-box exponent.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.ActualEulerLogarithm
open HeckeSkeleton.PrimeCancellationHecke HeckeSkeleton.PrimeCancellationMoment
open HeckeSkeleton.PrimeCancellationBounds
open EngineStep PrimeCancellation.Analytic
open scoped Classical BigOperators Topology nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {A : DedekindZetaZeroFree.SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}

/-- The actual boundary rules out zeros of a nonprincipal finite-order
continuation.  This statement does not assume a packet estimate. -/
theorem finiteOrderBoundary_continuation_ne_zero
    (chi : HeckeCharacter K) (hfinite : FiniteOrder chi) (hne : chi ≠ 1)
    (B : ℝ) (boundary : FiniteOrderBoundary (K := K) B)
    (s : ℂ) (hs : B < s.re) : heckeContinuation K chi s ≠ 0 := by
  intro hzero
  have hd := differentiable_heckeContinuation_of_nonNorm K chi
    (nonNorm_of_finiteOrder_ne_one K chi hfinite hne)
  have hlim : Tendsto (heckeContinuation K chi) (𝓝[≠] s) (𝓝 0) := by
    simpa only [hzero] using
      ((hd.continuous.continuousAt : ContinuousAt (heckeContinuation K chi) s).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hpositive : 0 < meromorphicOrderAt (heckeContinuation K chi) s :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ((hd.analyticAt s).meromorphicAt)).mp hlim
  exact (not_lt_of_ge (boundary chi hfinite s hs)) hpositive

/-- Every field is supplied by the same genuine Hecke continuation. -/
def finiteOrderBoundaryZeroFreeData
    (chi : HeckeCharacter K) (hfinite : FiniteOrder chi) (hne : chi ≠ 1)
    (B : ℝ) (boundary : FiniteOrderBoundary (K := K) B)
    (C : ℝ) (degree : ℕ) (hC : 1 ≤ C)
    (growth : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeContinuation K chi s‖ ≤ C * heckeConductorScale K chi ^ (5 / 8 : ℝ) *
        (2 + |s.im|) ^ degree) :
    ZeroFreeData (heckeContinuation K chi) B where
  C := C
  Q := heckeConductorScale K chi
  p := 5 / 8
  k := degree
  A := eulerLogSize K
  C_one := hC
  Q_one := one_le_actualConductorScale K chi
    (nonNorm_of_finiteOrder_ne_one K chi hfinite hne)
  p_nonneg := by norm_num
  entire := differentiable_heckeContinuation_of_nonNorm K chi
    (nonNorm_of_finiteOrder_ne_one K chi hfinite hne)
  zeroFree := finiteOrderBoundary_continuation_ne_zero chi hfinite hne B boundary
  centerLog := fun t => idealEulerLog K (deletedCoefficient K chi ∅)
    ((2 : ℂ) + t * Complex.I)
  centerLog_exp := by
    intro t
    simpa only [deletedContinuation_empty] using deleted_centerLog_exp K chi ∅ t
  centerLog_bound := deleted_centerLog_bound K chi ∅
  polynomial := growth

namespace MovingRecipe

/-- The raw character has the same linear support bound before any
MomentData, Fourier index or source has been selected. -/
theorem original_character_scale_le
    (moving : OriginalMovingFactors A P R) (correction slot : HeckeCharacter K)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining u : NonzeroIdeal K)
    (hu : completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u) :
    heckeConductorScale K
      (CanonicalNormalizedPrimeAtoms.originalCharacter moving correction slot sector u) ≤
      reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (slot * correction) * idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) := by
  let v : ExteriorIdeal K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := ⟨u, hu⟩
  have hscale := completeMovingRowCharacter_scale_le
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P R (slot * correction)
    Finset.univ (fun i => (moving.decomposition i).1)
    (fun i => (moving.decomposition i).2) moving.power
    (moving.fullMaskSupport remaining)
    (fun i _ => factor_radical_dvd_fullMaskSupport moving remaining i) sector v
  rw [← character_eq_complete_product moving] at hscale
  have hfixed : 1 ≤ (Ideal.absNorm
      (fixedRowDeletionIdeal (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero
      (fun hz => fixedRowDeletionIdeal_ne_bot (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hmass : 0 ≤ ((NumberField.discr K).natAbs : ℝ) *
      (Ideal.absNorm (finiteConductor K (slot * correction)).val : ℝ) *
        (Ideal.absNorm (sexticSConductorBudgetIdeal K
          (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
            idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) := by
    have huN := (idealNorm_pos K u).le
    have hDN := (idealNorm_pos K (moving.fullMaskSupport remaining)).le
    positivity
  calc
    _ ≤ ((NumberField.discr K).natAbs : ℝ) *
        (Ideal.absNorm (finiteConductor K (slot * correction)).val : ℝ) *
          (Ideal.absNorm (sexticSConductorBudgetIdeal K
            (A.Sf : Set (HeightOneSpectrum (𝓞 K)))).val : ℝ) *
              idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) := by
      simpa only [CanonicalNormalizedPrimeAtoms.originalCharacter, v,
        mul_assoc, mul_left_comm, mul_comm] using hscale
    _ ≤ _ := by
      have h := le_mul_of_one_le_right hmass hfixed
      simpa only [reflectionConductorConstant, reflectionConductorBudget,
        map_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem original_character_scale_le_normBox
    (theta : Finset (HeckeCharacter K))
    (moving : OriginalMovingFactors A P R) (correction slot : HeckeCharacter K)
    (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
    (remaining u : NonzeroIdeal K) (Z normBox : ℝ)
    (hcorrection : correction = 1 ∨ correction ∈ theta) (hslot : slot ∈ theta)
    (hu : completeIdealIsExterior K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u)
    (hZ : 0 ≤ Z)
    (hbudget : idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) ≤ Z ^ normBox) :
    heckeConductorScale K
      (CanonicalNormalizedPrimeAtoms.originalCharacter moving correction slot sector u) ≤
      primeThetaConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (primeBackgrounds theta) * Z ^ normBox := by
  have hc : correction ∈ insert 1 theta := Finset.mem_insert.mpr hcorrection
  have hbackground : slot * correction ∈ primeBackgrounds theta :=
    Finset.mem_image.mpr
      ⟨(correction, slot), Finset.mem_product.mpr ⟨hc, hslot⟩, rfl⟩
  have hconstant := reflectionConductorConstant_le_primeTheta
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (primeBackgrounds theta)
    (slot * correction) hbackground
  calc
    _ ≤ reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (slot * correction) * idealNorm K u * idealNorm K (moving.fullMaskSupport remaining) :=
      original_character_scale_le moving correction slot sector remaining u hu
    _ = reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (slot * correction) *
          (idealNorm K u * idealNorm K (moving.fullMaskSupport remaining)) := by ring
    _ ≤ reflectionConductorConstant (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (slot * correction) * Z ^ normBox :=
      mul_le_mul_of_nonneg_left hbudget
        (reflectionConductorConstant_pos (A.Sf : Set (HeightOneSpectrum (𝓞 K))) _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hZ _)

end MovingRecipe

/-- This discharges the owner's raw analytic Provider from original
arithmetic and the existing uniform strip growth theorem. -/
theorem originalPrimeAnalyticProvider
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (theta : Finset (HeckeCharacter K))
    (htheta : ∀ chi ∈ theta, FiniteOrder chi) :
    CanonicalOriginalPrimeAnalyticProvider.Provider (A := A) (P := P) (R := R) theta := by
  obtain ⟨Cg, hCg, hgrowth⟩ := exists_uniform_finiteOrder_polynomial K hcomplex
  let degree : ℕ := 2 * Fintype.card (InfinitePlace K)
  let Cq := primeThetaConductorConstant
    (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (MovingRecipe.primeBackgrounds theta)
  have hCq : 1 ≤ Cq := primeThetaConductorConstant_one_le _ _
  intro normBox hnormBox
  let D : ℝ := 1 + Real.log Cq + normBox
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg hCq
    dsimp only [D]
    linarith
  let H : ℝ := 1 + Real.log Cg + (5 / 8 : ℝ) * D + eulerLogSize K + 3 * (degree : ℝ)
  have hH : 0 < H := by
    have hlog := Real.log_nonneg hCg
    have heuler := eulerLogSize_nonneg K
    have hdegree : (0 : ℝ) ≤ degree := Nat.cast_nonneg _
    dsimp only [H]
    linarith
  refine ⟨H, hH, ?_⟩
  intro kappa _ _ Z hZ boundary moving correction slot sector remaining u
    hcorrection hslot hu hne hbudget
  let chi := CanonicalNormalizedPrimeAtoms.originalCharacter moving correction slot sector u
  have hc : FiniteOrder correction := by
    rcases hcorrection with h | h
    · rw [h]
      exact IsOfFinOrder.one
    · exact htheta _ h
  have hfinite : FiniteOrder chi :=
    ((hc.mul moving.character_finite).mul
      (completeIdealRowCharacter_finite K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        P R sector u)).mul (htheta _ hslot)
  let analytic := finiteOrderBoundaryZeroFreeData chi hfinite hne
    ((kappa + 1) / 2) boundary Cg degree hCg (hgrowth chi hfinite hne)
  refine ⟨analytic, ?_⟩
  have hQone : 1 ≤ heckeConductorScale K chi :=
    one_le_actualConductorScale K chi (nonNorm_of_finiteOrder_ne_one K chi hfinite hne)
  have hscale : heckeConductorScale K chi ≤ Cq * Z ^ normBox :=
    MovingRecipe.original_character_scale_le_normBox theta moving correction slot
      sector remaining u Z normBox hcorrection hslot hu (zero_lt_one.trans hZ).le hbudget
  have hlog : Real.log (heckeConductorScale K chi) ≤ D * (1 + Real.log Z) :=
    logQ_le_of_norm_polynomial _ Cq Z Z normBox
      (zero_lt_one.trans_le hQone) hCq (zero_lt_one.trans hZ) le_rfl hZ.le hnormBox hscale
  change 1 + Real.log Cg + (5 / 8 : ℝ) * Real.log (heckeConductorScale K chi) +
    eulerLogSize K + 3 * (degree : ℝ) ≤ H * (1 + Real.log Z)
  have h := conductor_height_budget Cg D (eulerLogSize K) (heckeConductorScale K chi)
    Z 1 0 degree hCg (eulerLogSize_nonneg K) hZ.le (by norm_num) (by norm_num)
    (by simpa only [Real.rpow_zero, mul_one] using hlog)
  simpa only [Real.rpow_zero, mul_one, H] using h

end HeckeSkeleton.Moments.EngineInduction
