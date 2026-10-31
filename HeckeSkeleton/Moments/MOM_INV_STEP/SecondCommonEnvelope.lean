import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPositiveChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

/-!
# The second genuine common density and its physical normalization

The all-radius profile estimate removes the actual bare row from the
Fourier envelope using N(k) at least one. Arbitrary additional Fourier
decay remains available for the child test seminorm. Independently, the
actual d₂-divisor identity turns the entire second scalar cost into one
factor N(g/d₂)/(rX), exactly the third frozen-triple coordinate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondCommonEnvelope

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools CommonKernel
  SecondOverlapColumns SecondPoissonNormalization FirstCommonEnvelope ActualDivisorSectors
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def radialScale (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (X Y : {r : ℝ // 0 < r}) : ℝ :=
  r.val * (sIntegerElementNorm K Sset d).val * X.val * Y.val

theorem radialScale_pos (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (X Y : {r : ℝ // 0 < r}) : 0 < radialScale K S r d X Y :=
  mul_pos (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property)
    X.property) Y.property

theorem outerRadius_power_le (ε : ℝ) (hε : 0 ≤ ε)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (k : Ext)
    (X Y : {r : ℝ // 0 < r}) :
    (outerRadius K S r d k X Y).val ^ (-ε) ≤ radialScale K S r d X Y ^ ε := by
  have hk := height_one_le K Sset k
  have hp := radialScale_pos K S r d X Y
  have hpow : (k.val.val.absNorm : ℝ) ^ (-ε) ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos zero_lt_one hk (neg_nonpos.mpr hε)
  change ((k.val.val.absNorm : ℝ) / radialScale K S r d X Y) ^ (-ε) ≤ _
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ (k.val.val.absNorm : ℝ)) hp.le,
    Real.rpow_neg hp.le, div_inv_eq_mul]
  exact (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le ε)).trans_eq (one_mul _)

/-- The physical normalization has exactly one copy of the residual
common norm. It is never replaced by a square of the triple mass. -/
theorem scalar_cost_eq (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (g : Ext) (hg : Squarefree g.val.val)
    (hd : (divisorIdeal K S d).val.val ∣ g.val.val)
    (X : ℝ) (hX : 0 < X) :
    outerFactor K S r d / (X / height K Sset g) =
      ActualPoissonScale.fieldConstant K *
        height K Sset (residual K S g (divisorIdeal K S d)) / (r.val * X) := by
  have hn := congrArg (height K Sset)
    (divisor_factorization K S g (divisorIdeal K S d) hg hd)
  rw [height_mul] at hn
  have hdN : height K Sset (divisorIdeal K S d) = (sIntegerElementNorm K Sset d).val :=
    divisorIdeal_norm K S d
  rw [hdN] at hn
  unfold outerFactor
  rw [← hn]
  field_simp [r.property.ne', hX.ne', (sIntegerElementNorm K Sset d).property.ne',
    (height_pos K Sset (residual K S g (divisorIdeal K S d))).ne']
  <;> ring

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

/-- Constants precede every actual source, divisor, bare row and radius.
The wide logarithmic cutoff is the fixed one proved above. -/
theorem exists_second_density_common_envelope
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ φ : SchwartzMap V ℂ, ∀ r : {r : ℝ // 0 < r}, ∀ d : NonzeroRingElements OS,
      ∀ k : Ext, ∀ X Y : {r : ℝ // 0 < r}, ∀ ξ : LogPlane,
        ‖SecondPhysicalEnergy.density K S Γ
          (profile K S μv ν φ h hlc hcs r d k X Y) ξ‖ ≤
          (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * radialScale K S r d X Y ^ ε) *
            frequencyEnvelope m ξ := by
  let p := (volume : Measure LogPlane).integrablePower
  have hfinite := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  obtain ⟨s, A, hA, hb⟩ := exists_orbitalDensity_weighted_smallPower_bound
    K Sset Γ (sIntegerFiniteFourierTestFunction K S μv h) hfinite.1.continuous hfinite.2
    secondCutoff secondCutoff_contDiff secondCutoff_hasCompactSupport ε hε (p + m)
  refine ⟨s, A, hA, fun φ r d k X Y ξ => ?_⟩
  have hR := outerRadius_power_le K S ε hε.le r d k X Y
  have hsmall := (hb φ (outerRadius K S r d k X Y) ξ).trans
    (mul_le_mul_of_nonneg_left hR (mul_nonneg hA (apply_nonneg _ _)))
  have hdiv : ‖SecondPhysicalEnergy.density K S Γ
      (profile K S μv ν φ h hlc hcs r d k X Y) ξ‖ ≤
      (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * radialScale K S r d X Y ^ ε) /
        (1 + ‖ξ‖) ^ (p + m) := by
    apply (le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) (p + m))).mpr
    rw [mul_comm]
    exact hsmall
  simpa only [frequencyEnvelope, fourierEnvelope,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖), Real.rpow_natCast,
    pow_add, div_eq_mul_inv, mul_inv_rev, p, mul_assoc, mul_comm, mul_left_comm] using hdiv

variable {σ : Type*} [DecidableEq σ] {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

theorem actual_sourceScalar_norm_le
    (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hX : 0 < C.base ^ C.columnLength γ) (r : {r : ℝ // 0 < r})
    (g j : Ext) (hg : Squarefree g.val.val) (dk : NonzeroRingElements OS)
    (δ : Finset (HeightOneSpectrum OS))
    (hδ : δ ⊆ SecondSourceMasks.commonMask K S D g) :
    ‖SecondParentRetained.sourceScalar K S C γ hX r δ g j dk‖ ≤
      ActualPoissonScale.fieldConstant K *
        height K Sset (residual K S g (divisorIdeal K S (sIntegerMaskGenerator K Sset δ))) /
          (r.val * C.base ^ C.columnLength γ) := by
  apply (SecondParentRetained.sourceScalar_norm_le K S C γ hX r δ g j dk).trans_eq
  exact scalar_cost_eq K S r (sIntegerMaskGenerator K Sset δ) g hg
    (SecondSourceMasks.actual_divisor_dvd K S D g hg δ hδ) _ hX

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondCommonEnvelope

end
