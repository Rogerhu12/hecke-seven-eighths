import HeckeSkeleton.HighBinSupport.ActualOrbitalRapidDecay
import HeckeSkeleton.SmallRadius.SLocalRadialMellinIntegral
import HeckeGeneral.Bridge.TraceSchwartzFourier
import HeckeGeneral.Bridge.SLocalFiniteFourier
/-!
The actual physical additive Mellin transform has arbitrary vertical decay
on every fixed line 0 < Re(z) <= 1. The finite Fourier support theorem and
the infinite Schwartz Fourier theorem supply the transformed tensor; its
Mellin estimates are derived in ActualOrbitalRapidDecay. No Fourier closure,
log-profile decay, or high-row bound is postulated as data.
-/

noncomputable section
namespace HighBinBoundary.ActualAdditive

open MeasureTheory Complex NumberField IsDedekindDomain
open NumberField.AdelicFourier NumberField.StandardAddChar
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K S₀
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
set_option quotPrecheck false in
local notation "A" => ((p : S₀) → p.val.adicCompletion K)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) →
  Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The literal finite part of additiveFourier, including all Haar masses. -/
def finiteFourierProfile (W : AdditiveProbeTest K S₀) (y : A) : ℂ :=
  ∏ p : S₀,
    ((μ p).real (p.val.adicCompletionIntegers K : Set (p.val.adicCompletion K)) : ℂ)⁻¹ *
      fourierIntegral (psiLocal K p.val) (μ p) (W.finiteTest p) (y p)

/-- The actual finite transforms retain locally constant compact support.
The outside-S extension is used only to invoke the proved adelic closure;
the resulting function is precisely the original finite product. -/
theorem finiteFourierProfile_locallyConstant_compactSupport
    (W : AdditiveProbeTest K S₀) :
    IsLocallyConstant (finiteFourierProfile K S μ W) ∧
      HasCompactSupport (finiteFourierProfile K S μ W) := by
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
  letI : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  let ν : Measure (FiniteAdeleRing (𝓞 K) K) := Measure.addHaar
  let μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K) :=
    fun v => if hv : v ∈ S then μ ⟨v, hv⟩ else Measure.addHaar
  letI (v : HeightOneSpectrum (𝓞 K)) : (μv v).IsAddHaarMeasure := by
    dsimp only [μv]
    split <;> infer_instance
  let h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ :=
    fun v => if hv : v ∈ S then W.finiteTest ⟨v, hv⟩ else 0
  have hlc : ∀ v ∈ S, IsLocallyConstant (h v) := by
    intro v hv
    simpa only [h, dif_pos hv] using W.finite_locallyConstant ⟨v, hv⟩
  have hcs : ∀ v ∈ S, HasCompactSupport (h v) := by
    intro v hv
    simpa only [h, dif_pos hv] using W.finite_compactSupport ⟨v, hv⟩
  have hf := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  have heq : sIntegerFiniteFourierTestFunction K S μv h =
      finiteFourierProfile K S μ W := by
    funext y
    unfold sIntegerFiniteFourierTestFunction finiteFourierProfile
    apply Finset.prod_congr rfl
    intro p _
    have hp : p.val ∈ S := p.property
    dsimp only [μv, h]
    simp only [dif_pos hp] <;> rfl
  rwa [heq] at hf

/-- The physical Fourier integrand is exactly the transformed Schwartz tensor. -/
theorem additiveFourier_eq_tensor (W : AdditiveProbeTest K S₀) (x : G) :
    additiveFourier K S₀ μ W x =
      sLocalTensorTestFunction K S₀ (traceSchwartzFourier K W.infiniteTest)
        (finiteFourierProfile K S μ W) x := by
  unfold additiveFourier sLocalTensorTestFunction finiteFourierProfile
  congr 1
  exact (mixedTraceSchwartzFourier_apply K W.infiniteTest
    (x.1 : mixedEmbedding.mixedSpace K)).symm

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- Exact dictionary for the physical Mellin integral and the original
norm-one Haar. The logarithmic substitution cancels du/u literally. -/
theorem additiveMellin_eq_orbitalMellin (W : AdditiveProbeTest K S₀) (z : ℂ) :
    additiveMellin K S₀ μ W z =
      ActualOrbital.orbitalMellin K S₀ (traceSchwartzFourier K W.infiniteTest)
        (finiteFourierProfile K S μ W) z := by
  rw [additiveMellin_eq_log_integral]
  unfold ActualOrbital.orbitalMellin
  apply integral_congr_ae
  filter_upwards [] with v
  have hp : (Real.exp v : ℂ) ^ z = Complex.exp ((v : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
      ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  rw [hp]
  congr 1
  unfold sUnitOrbitalProfile sUnitOrbitalIntegral
  apply integral_congr_ae
  filter_upwards [] with u
  rw [additiveFourier_eq_tensor]
  congr 1
  exact mul_comm _ _

variable [IsTotallyComplex K]
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]

include Γ in
/-- Actual arbitrary-order vertical decay of the additive Mellin transform.
The entire bound is independent of arithmetic rows, Z, T and contour boxes. -/
theorem exists_additiveMellin_rapid_bound (W : AdditiveProbeTest K S₀)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      (1 + |t|) ^ n * ‖additiveMellin K S₀ μ W ((σ : ℂ) + t * I)‖ ≤ D := by
  obtain ⟨hc, hs⟩ := finiteFourierProfile_locallyConstant_compactSupport K S μ W
  obtain ⟨D, hD, hb⟩ := ActualOrbital.exists_orbitalMellin_rapid_bound K S₀ Γ
    (traceSchwartzFourier K W.infiniteTest) (finiteFourierProfile K S μ W)
    hc.continuous hs σ hσ hσ1 n
  exact ⟨D, hD, fun t => by rw [additiveMellin_eq_orbitalMellin]; exact hb t⟩

include Γ in
/-- The actual z-profile is continuous at all heights of its fixed line. -/
theorem additiveMellin_continuous_line (W : AdditiveProbeTest K S₀)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Continuous (fun t : ℝ => additiveMellin K S₀ μ W ((σ : ℂ) + t * I)) := by
  obtain ⟨hc, hs⟩ := finiteFourierProfile_locallyConstant_compactSupport K S μ W
  simp_rw [additiveMellin_eq_orbitalMellin]
  exact ActualOrbital.orbitalMellin_continuous_line K S₀ Γ
    (traceSchwartzFourier K W.infiniteTest) (finiteFourierProfile K S μ W)
    hc.continuous hs σ hσ hσ1

#print axioms finiteFourierProfile_locallyConstant_compactSupport
#print axioms additiveMellin_eq_orbitalMellin
#print axioms exists_additiveMellin_rapid_bound
#print axioms additiveMellin_continuous_line

end HighBinBoundary.ActualAdditive

namespace HighBinBoundary.ActualAdditiveBorel

open MeasureTheory Complex NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- Transport back to the literal Borel structures and Haar measures of
ProbeMeasures. Borel uniqueness removes a representation choice; the Haar
measures and their masses remain exactly those supplied in the probe. -/
theorem exists_additiveMellin_rapid_bound_actualBorel
    (m : (p : S₀) → MeasurableSpace (p.val.adicCompletion K))
    (hm : ∀ p, @BorelSpace (p.val.adicCompletion K) inferInstance (m p))
    (μ : (p : S₀) → @Measure (p.val.adicCompletion K) (m p))
    (hμ : ∀ p, letI := m p; (μ p).IsAddHaarMeasure)
    (W : AdditiveProbeTest K S₀)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (n : ℕ) :
    letI (p : S₀) : MeasurableSpace (p.val.adicCompletion K) := m p
    letI (p : S₀) : BorelSpace (p.val.adicCompletion K) := hm p
    letI (p : S₀) : (μ p).IsAddHaarMeasure := hμ p
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ,
      (1 + |t|) ^ n * ‖additiveMellin K S₀ μ W ((σ : ℂ) + t * I)‖ ≤ D := by
  have heq : m = fun p : S₀ => LanglandsTunnell.TateLocal.localBorel K p.val := by
    funext p
    exact (hm p).measurable_eq
  subst m
  letI (p : S₀) : (μ p).IsAddHaarMeasure := hμ p
  exact ActualAdditive.exists_additiveMellin_rapid_bound K S μ
    (⊤ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) W σ hσ hσ1 n

/-- Continuity with the original arbitrary probe Borel structures. -/
theorem additiveMellin_continuous_line_actualBorel
    (m : (p : S₀) → MeasurableSpace (p.val.adicCompletion K))
    (hm : ∀ p, @BorelSpace (p.val.adicCompletion K) inferInstance (m p))
    (μ : (p : S₀) → @Measure (p.val.adicCompletion K) (m p))
    (hμ : ∀ p, letI := m p; (μ p).IsAddHaarMeasure)
    (W : AdditiveProbeTest K S₀)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    letI (p : S₀) : MeasurableSpace (p.val.adicCompletion K) := m p
    letI (p : S₀) : BorelSpace (p.val.adicCompletion K) := hm p
    letI (p : S₀) : (μ p).IsAddHaarMeasure := hμ p
    Continuous (fun t : ℝ => additiveMellin K S₀ μ W ((σ : ℂ) + t * I)) := by
  have heq : m = fun p : S₀ => LanglandsTunnell.TateLocal.localBorel K p.val := by
    funext p
    exact (hm p).measurable_eq
  subst m
  letI (p : S₀) : (μ p).IsAddHaarMeasure := hμ p
  exact ActualAdditive.additiveMellin_continuous_line K S μ
    (⊤ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) W σ hσ hσ1

#print axioms exists_additiveMellin_rapid_bound_actualBorel
#print axioms additiveMellin_continuous_line_actualBorel

end HighBinBoundary.ActualAdditiveBorel
