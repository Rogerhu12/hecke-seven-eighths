import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSecondErrorBridge
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorTailBudget

/-!
# The whole actual second error under the first spectral measure

This is the literal error from the first production energy, with the
constructed fine second cutoff. The original first index, original
assigned marks, two Mobius factors and both spectral integrals remain.
Its finite total is bounded by exactly the principalTotal and tailTotal
already estimated from the sharp first source count. The reciprocal
physical radius is proved equal to Z^(-H), rather than supplied as a
source identity.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorTotal

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstErrorIntegration FirstCenteredErrorIntegrals
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "φ₀" => Physical.ActualGramMajorantDraft.rowBallArchTest K S 1
local notation "h₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily K S 1
local notation "hlc₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_locallyConstant K S 1
local notation "hcs₀" => Physical.ActualGramMajorantDraft.rowBallFiniteFamily_compactSupport K S 1

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))

def rowCaps (Z H : ℝ) (hZ : 0 < Z) :
    OuterIndex K S D T → {r : ℝ // 0 < r} :=
  fun _ => ⟨Z ^ H, Real.rpow_pos_of_pos hZ _⟩

theorem rowRadius_caps (Z H : ℝ) (hZ : 0 < Z) (o : OuterIndex K S D T) :
    InverseRowMajorant.rowRadius (rowCaps K S D T Z H hZ o) =
      ⟨Z ^ (-H), Real.rpow_pos_of_pos hZ _⟩ := by
  apply Subtype.ext
  change (Z ^ H)⁻¹ = Z ^ (-H)
  exact (Real.rpow_neg hZ.le H).symm

variable (U : FirstErrorSource.Index K S D T → {r : ℝ // 0 < r})

def centerPairs (i : FirstErrorSource.Index K S D T) (_J : Finset σ) :
    Finset (Ext × Ext) :=
  FirstSecondErrorBridge.completePairs K S (U i)

variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (I : Finset (FirstErrorSource.Index K S D T)) (side : Bool)
variable (W : SchwartzMap ℝ ℂ) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℕ) (coordinate : CommonKernel.LogPlane → ℝ)

def total (Z kappa H tau : ℝ) (hZ : 0 < Z) : ℝ :=
  (Z ^ kappa * ((T.columns.slots.powerset.card : ℝ) *
    (InverseRowMajorant.rowCovolume K S)⁻¹) * mellinMass W hW) *
    ∑ i ∈ I, ∑ J ∈ T.columns.slots.powerset,
      mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 *
        spectralAverage (MellinSeparation.density W hW) m coordinate
          (fun s => FirstSecondReduction.errorAt K S D Γ hΓ μv
            T Θ ψ G hν hG hbase (rowCaps K S D T Z H hZ) (U i) J s
            (FirstSecondErrorBridge.cutoff K S D T
              (rowCaps K S D T Z H hZ) (U i) Z tau) i.1 i.2)

/-- Actual finite aggregation after the two common integrals. This
comparison requires no cutoff identity, error bound or energy estimate. -/
theorem total_le_principal_add_tail (Z kappa H tau : ℝ) (hZ : 0 < Z)
    (hc : Continuous coordinate) :
    total K S D Γ hΓ μv T U Θ ψ G hν hG hbase I side W hW m coordinate
      Z kappa H tau hZ ≤
    FirstErrorPhysicalBudget.principalTotal K S D Γ hΓ μv
      T Θ ψ G hν hG I side (fun i => (U i).val) W hW m coordinate
      φ₀ h₀ hlc₀ hcs₀ Z kappa H (-(1 / 2 : ℝ)) hZ +
    FirstErrorTailBudget.tailTotal K S D Γ hΓ μv
      T Θ ψ G hν hG I side (fun i => (U i).val) (centerPairs K S D T U)
      W hW m coordinate φ₀ h₀ hlc₀ hcs₀ Z kappa H (-(1 / 2 : ℝ)) tau hZ := by
  have hout : 0 ≤
      Z ^ kappa * ((T.columns.slots.powerset.card : ℝ) *
        (InverseRowMajorant.rowCovolume K S)⁻¹) * mellinMass W hW :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.mpr (InverseRowMajorant.rowCovolume_pos K S).le)))
      (mellinMass_nonneg W hW)
  unfold total FirstErrorPhysicalBudget.principalTotal FirstErrorTailBudget.tailTotal
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hout
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro J hJ
  have hb := FirstSecondErrorBridge.spectralAverage_errorAt_le
    K S D Γ hΓ μv T Θ ψ G hν hG hbase (rowCaps K S D T Z H hZ) (U i) J
    Z tau i (MellinSeparation.density W hW) m coordinate hc
  rw [rowRadius_caps K S D T Z H hZ i.1] at hb
  have hw : 0 ≤ mobiusWeight K S D T i * ‖mark K S D T side i J‖ ^ 2 :=
    mul_nonneg (mobiusWeight_nonneg K S D T i) (sq_nonneg _)
  simpa only [centerPairs] using
    (mul_le_mul_of_nonneg_left hb hw).trans_eq (mul_add _ _ _)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualErrorTotal

end
