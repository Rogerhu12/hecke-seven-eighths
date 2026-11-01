import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialInverse
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondParentRadialBudget

/-!
# Actual initial production scalars

This file uses the literal `SecondAdaptiveProduction` parent and its
actual common/divisor/sector indices. The squared source normalization
is restored before its physical scalar is estimated. Its factor is
exactly c_K Z^m N(g/d)/X²; the independent overlap is never counted in
that scalar. The provider's genuine radial factor costs a uniformly
chosen small power.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialProduction

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers CanonicalChildren CanonicalNormPools ActualDivisorSectors
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)
variable (W : SchwartzMap ℝ ℂ) (hbase : 1 < C.base)
variable (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℝ)

def rowCap : {r : ℝ // 0 < r} :=
  ⟨C.base ^ m, Real.rpow_pos_of_pos (zero_lt_one.trans hbase) m⟩

def parent : SecondParentProduction.Data K S σ Θ ψ :=
  ProviderInitialInverse.parentData K S C Θ ψ hν W hbase hW (rowCap K S C hbase m)

variable (H : ProviderInitialSource.Cutoff K S)
local notation "X" => C.base ^ C.length
local notation "T" => parent K S C Θ ψ hν W hbase hW m
local notation "Idx" => ProviderInitialSource.Index K S D Γ X H

def parentIndex (i : Idx) : SecondAdaptiveRetained.IndexAt K S D Γ T H :=
  ⟨i.1, i.2.1, i.2.2.1⟩

theorem parent_radius : (T).radius.val = C.base ^ (-m) := by
  simp only [parent, ProviderInitialInverse.parentData, rowCap,
    InverseRowMajorant.rowRadius]
  exact (Real.rpow_neg (zero_lt_one.trans hbase).le m).symm

def positiveScalar (eps : ℝ) (i : Idx) : ℝ :=
  SecondAdaptiveProduction.weightAt K S D Γ T H
      (parentIndex K S D Γ C Θ ψ hν W hbase hW m H i) *
    SecondParentProduction.radialScale K S D Γ
      (SecondAdaptiveRetained.dataAt K S D Γ T H
        (parentIndex K S D Γ C Θ ψ hν W hbase hW m H i))
      (SecondAdaptiveRetained.oldIndexAt K S D Γ T H
        (parentIndex K S D Γ C Θ ψ hν W hbase hW m H i)) ^ eps *
    ‖(moebius i.2.2.2.val : ℂ)‖

theorem positiveScalar_nonneg (eps : ℝ) (i : Idx) :
    0 ≤ positiveScalar K S D Γ C Θ ψ hν W hbase hW m H eps i := by
  unfold positiveScalar
  exact mul_nonneg
    (mul_nonneg (SecondAdaptiveProduction.weightAt_nonneg K S D Γ T H _)
      (Real.rpow_nonneg (SecondParentProduction.radialScale_pos K S D Γ _ _).le _))
    (norm_nonneg _)

/-- The actual common factorization, after the original inverse
normalization, leaves one residual norm and two column denominators. -/
theorem normalized_weight_le (i : Idx) :
    X⁻¹ * SecondAdaptiveProduction.weightAt K S D Γ T H
      (parentIndex K S D Γ C Θ ψ hν W hbase hW m H i) ≤
      ActualPoissonScale.fieldConstant K * C.base ^ m *
        height K Sset (ProviderInitialSource.residual K S D Γ X H i) / X ^ 2 := by
  letI : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) :=
    fun v => borel (v.adicCompletion K)
  letI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) :=
    fun _ => ⟨rfl⟩
  have hX : 0 < X := Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _
  have hm : ‖(moebius (IdealMobiusMask.primeProduct i.2.1.val) : ℂ)‖ ≤ 1 := by
    simp only [IdealMobiusMask.moebius_primeProduct, Int.cast_pow, Int.cast_neg,
      Int.cast_one, norm_pow, norm_neg, norm_one, one_pow, le_refl]
  have hs := SecondParentRetained.sourceScalar_norm_le K S
    (ProviderInitialInverse.family K S C Θ ψ hν W) (ProviderInitialInverse.unitTriple K)
    hX (T).radius i.2.1.val i.1.val (FirstInversePoisson.unitIdeal K S)
    (ProviderInitialSource.unitDivisor K S)
  change _ ≤ SecondPoissonNormalization.outerFactor K S (T).radius
    (sIntegerMaskGenerator K Sset i.2.1.val) / (X / height K Sset i.1.val) at hs
  have hweight : SecondAdaptiveProduction.weightAt K S D Γ T H
      (parentIndex K S D Γ C Θ ψ hν W hbase hW m H i) ≤
        SecondPoissonNormalization.outerFactor K S (T).radius (sIntegerMaskGenerator K Sset i.2.1.val) /
          (X / height K Sset i.1.val) := by
    change ‖(moebius (IdealMobiusMask.primeProduct i.2.1.val) : ℂ)‖ *
      ‖SecondParentRetained.sourceScalar K S
        (ProviderInitialInverse.family K S C Θ ψ hν W) (ProviderInitialInverse.unitTriple K)
        hX (T).radius i.2.1.val i.1.val (FirstInversePoisson.unitIdeal K S)
        (ProviderInitialSource.unitDivisor K S)‖ ≤ _
    exact (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans (by simpa only [one_mul] using hs)
  have hfactor :
      height K Sset (ProviderInitialSource.divisor K S D Γ X H i) *
        height K Sset (ProviderInitialSource.residual K S D Γ X H i) = height K Sset i.1.val := by
    have he := congrArg (fun I : Ideal (𝓞 K) => (I.absNorm : ℝ))
      (ProviderInitialSource.common_factorization K S D Γ X H i)
    simpa only [map_mul, Nat.cast_mul, height, ProviderInitialSource.common] using he
  apply (mul_le_mul_of_nonneg_left hweight (inv_nonneg.mpr hX.le)).trans_eq
  dsimp only [SecondPoissonNormalization.outerFactor]
  rw [show (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset i.2.1.val)).val =
    height K Sset (ProviderInitialSource.divisor K S D Γ X H i) from
      (divisorIdeal_norm K S (sIntegerMaskGenerator K Sset i.2.1.val)).symm]
  change X⁻¹ * ((ActualPoissonScale.fieldConstant K /
    ((C.base ^ m)⁻¹ * height K Sset (ProviderInitialSource.divisor K S D Γ X H i))) /
      (X / height K Sset i.1.val)) = _
  rw [ProviderInitialGeometry.normalized_scalar (C.base ^ m) X
    (height K Sset (ProviderInitialSource.divisor K S D Γ X H i)) (height K Sset i.1.val)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _) hX (height_pos K Sset _)
    (height_pos K Sset _) (ActualPoissonScale.fieldConstant K)]
  rw [← hfactor, mul_div_cancel_left₀ _ (height_pos K Sset _).ne']

/-- Choose the radial small power uniformly, before the initial
profile, family, masks, frequency, overlap and norm boxes. -/
theorem exists_uniform_scalar_bound (A pi : ℝ) (hA : 0 ≤ A) (hpi : 0 < pi) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ {σ₀ : Type*} [DecidableEq σ₀]
      (C₀ : CanonicalBlock.ColumnData K S σ₀)
      (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ : HeckeCharacter K)
      (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ C₀.background)
      (W₀ : SchwartzMap ℝ ℂ) (hbase₀ : 1 < C₀.base)
      (hW₀ : tsupport W₀ ⊆ Set.Icc (1 : ℝ) 2) (m : ℝ)
      (H₀ : ProviderInitialSource.Cutoff K S)
      (P : Finset (ProviderInitialSource.Index K S D Γ (C₀.base ^ C₀.length) H₀))
      (b : SecondMobiusGeometry.Index (C₀.base ^ C₀.length)) (h : ℝ)
      (j : ProviderInitialBoxes.BoxIndex C₀.base A),
      0 ≤ m → C₀.length ≤ A → 0 ≤ h → 2 ≤ C₀.base ^ h →
      4 * C₀.base ^ C₀.length ≤ C₀.base ^ A →
      ∀ i ∈ ProviderInitialBoxes.boxed K S D Γ (C₀.base ^ C₀.length) H₀ P b C₀.base A j,
      (C₀.base ^ C₀.length)⁻¹ *
        positiveScalar K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m H₀ eps i ≤
        ActualPoissonScale.fieldConstant K *
          C₀.base ^ (m - 2 * C₀.length + ProviderInitialBoxes.length C₀.base j 0 -
            ProviderInitialBoxes.length C₀.base j 1 + 2 * h + pi) := by
  obtain ⟨eps, heps, hr⟩ := SecondParentRadialBudget.exists_uniform_small_power K S D Γ A pi hA hpi
  refine ⟨eps, heps, ?_⟩
  intro σ₀ _ C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m H₀ P b h j hm hL hh hwidth hcap i hi
  let T₀ := parent K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m
  let k := parentIndex K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m H₀ i
  let Ti := SecondAdaptiveRetained.dataAt K S D Γ T₀ H₀ k
  let ki := SecondAdaptiveRetained.oldIndexAt K S D Γ T₀ H₀ k
  have hrad : SecondParentProduction.radialScale K S D Γ Ti ki ^ eps ≤ C₀.base ^ pi :=
    hr Ti C₀.base (-m) C₀.length hbase₀.le (by linarith) hL
      (parent_radius K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m).le le_rfl ki
  have hw := normalized_weight_le K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m H₀ i
  have hres := ProviderInitialBoxes.residual_norm K S D Γ (C₀.base ^ C₀.length) H₀
    P b C₀.base A h hbase₀ hh hwidth hcap j i hi
  have hz : 0 < C₀.base := zero_lt_one.trans hbase₀
  have hfield : 0 ≤ ActualPoissonScale.fieldConstant K := ActualPoissonScale.fieldConstant_nonneg K
  have hres0 : 0 ≤ height K Sset
      (ProviderInitialSource.residual K S D Γ (C₀.base ^ C₀.length) H₀ i) := (height_pos K Sset _).le
  have hweight0 : 0 ≤ (C₀.base ^ C₀.length)⁻¹ *
      SecondAdaptiveProduction.weightAt K S D Γ T₀ H₀ k :=
    mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hz.le _))
      (SecondAdaptiveProduction.weightAt_nonneg K S D Γ T₀ H₀ k)
  have hmu := HeckePort.IdealMobiusDivisorSum.norm_ideal_moebius_le_one i.2.2.2.val
  have hprod := mul_le_mul hrad hmu (norm_nonneg _) (Real.rpow_nonneg hz.le _)
  rw [mul_one] at hprod
  calc
    _ = ((C₀.base ^ C₀.length)⁻¹ * SecondAdaptiveProduction.weightAt K S D Γ T₀ H₀ k) *
        (SecondParentProduction.radialScale K S D Γ Ti ki ^ eps * ‖(moebius i.2.2.2.val : ℂ)‖) := by
      unfold positiveScalar
      ring
    _ ≤ (ActualPoissonScale.fieldConstant K * C₀.base ^ m *
        height K Sset (ProviderInitialSource.residual K S D Γ (C₀.base ^ C₀.length) H₀ i) /
        (C₀.base ^ C₀.length) ^ 2) * C₀.base ^ pi :=
      mul_le_mul hw hprod
        (mul_nonneg
          (Real.rpow_nonneg (SecondParentProduction.radialScale_pos K S D Γ Ti ki).le _)
          (norm_nonneg _))
        (hweight0.trans hw)
    _ ≤ (ActualPoissonScale.fieldConstant K * C₀.base ^ m *
        C₀.base ^ (ProviderInitialBoxes.length C₀.base j 0 -
          ProviderInitialBoxes.length C₀.base j 1 + 2 * h) /
        (C₀.base ^ C₀.length) ^ 2) * C₀.base ^ pi := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hres
        (mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K) (Real.rpow_nonneg hz.le _))
    _ = _ := by
      rw [ProviderInitialGeometry.physical_power_identity C₀.base m C₀.length _ _ hz,
        mul_assoc, ← Real.rpow_add hz]
      congr 2
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialProduction

end
