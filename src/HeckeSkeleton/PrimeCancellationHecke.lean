import HeckeSkeleton.PrimeCancellationCounting
import PrimeCancellationPaired
import HeckeGeneral.Analysis.IdealDerivativeEulerLog
import HeckeGeneral.Analysis.IdealMobiusDeletion
import HeckeGeneral.Analysis.HeckeEndpointTarget
import HeckeSkeleton.HeckeUniformStripGrowth
import HeckeSkeleton.HeckeDeletedEulerControl

/-!
# Actual Hecke input for prime cancellation

The function in `deletedSlotData` is the project's `heckeDeletedContinuation`.
Its coefficients are the project's `primeCoefficient`, with the indicated
finite Euler factors removed.  The prime-power Euler identity, absolute
convergence, prime counting, and a uniform central logarithm are proved here
from the existing arithmetic and Euler-series theorems.

The zero boundary is the actual packet boundary.  The non-norm condition is
retained explicitly: the principal character has a pole and cannot satisfy
the entire-function input of the cancellation theorem.  Polynomial growth
can either be supplied on the actual continuation or obtained below from
the existing totally-complex, fixed-infinity-type strip theorem.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationHecke

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.IdealMobiusReciprocal
open HeckeSkeleton.ActualEulerLogarithm
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeDeletedEulerControl
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellationPrimeSeries
open scoped Classical Topology BigOperators

variable (K : Type) [Field K] [NumberField K]

theorem nonNorm_of_finiteOrder_ne_one (χ : HeckeCharacter K)
    (hχ : FiniteOrder χ) (hne : χ ≠ 1) :
    ∀ t : ℝ, χ ≠ heckeNormTwist K t := by
  intro t heq
  let v : InfinitePlace K := Classical.choice inferInstance
  have hz := heckeRadialParameter_finiteOrder K v hχ
  rw [heq, heckeRadialParameter_normTwist] at hz
  have ht : t = 0 := by linarith
  apply hne
  simpa [ht, heckeNormTwist] using heq

theorem finiteOrder_infinityType_zero
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : FiniteOrder χ) :
    (fun v => heckeRadialParameter K v χ) = 0 ∧ heckeArchWeight K χ = 0 := by
  constructor
  · funext v
    exact heckeRadialParameter_finiteOrder K v hχ
  · funext v
    rw [heckeArchWeight_of_complex K χ v (hcomplex v)]
    exact heckeComplexWeight_finiteOrder K v (hcomplex v) hχ

/-- Fixed Euler deletions preserve ramified coefficient zeros. -/
def deletedCoefficient (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : HeightOneSpectrum (𝓞 K) → ℂ :=
  deletePrimes K S (primeCoefficient K χ)

theorem norm_deletedCoefficient_le_one (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ p, ‖deletedCoefficient K χ S p‖ ≤ 1 :=
  norm_deletePrimes_le_one K S _ (norm_primeCoefficient_le_one K χ)

@[simp] theorem deletedCoefficient_empty (χ : HeckeCharacter K) :
    deletedCoefficient K χ ∅ = primeCoefficient K χ := by
  funext p
  simp [deletedCoefficient, deletePrimes]

@[simp] theorem deletedContinuation_empty (χ : HeckeCharacter K) :
    heckeDeletedContinuation K χ ∅ = heckeContinuation K χ := by
  funext s
  simp [heckeDeletedContinuation, heckeEulerDeletionPolynomial, finiteEulerPolynomial]

/-- The reciprocal Euler identity identifies the deleted *original* series;
inversion is injective even at zero, so this does not introduce a nonzero premise. -/
theorem deletedContinuation_eq_series (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ S s =
      idealDirichletSeries K (nonzeroIdealCoefficient (deletedCoefficient K χ S)) s := by
  apply inv_injective
  have hP : heckeEulerDeletionPolynomial K χ S s =
      ∏ p ∈ S, (1 - primeIdealRatio K (primeCoefficient K χ) s p) := by
    simp only [heckeEulerDeletionPolynomial, finiteEulerPolynomial,
      eulerPolynomial, primeIdealRatio, residueCard, Complex.ofReal_natCast]
  calc
    (heckeDeletedContinuation K χ S s)⁻¹ =
        ∑' I, excludedTerm K S (primeCoefficient K χ) s I := by
      rw [heckeDeletedContinuation, hP, heckeContinuation_eq_series K χ hs]
      exact (excluded_series_eq_inverse K S _ (norm_primeCoefficient_le_one K χ) hs).symm
    _ = ∑' I, term K (deletedCoefficient K χ S) s I := by
      simp only [deletedCoefficient, term_deletePrimes]
    _ = _ := moebius_series_eq_inverse K _ (norm_deletedCoefficient_le_one K χ S) hs

/-- Equality on the open Euler half-plane also identifies its derivatives. -/
theorem deleted_logDerivative_eq_primePowerSeries (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    deriv (heckeDeletedContinuation K χ S) s / heckeDeletedContinuation K χ S s =
      -primePowerLogSeries K (deletedCoefficient K χ S) 1 s := by
  have heq : heckeDeletedContinuation K χ S =ᶠ[𝓝 s]
      idealDirichletSeries K (nonzeroIdealCoefficient (deletedCoefficient K χ S)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with w hw
    exact deletedContinuation_eq_series K χ S hw
  rw [heq.deriv_eq, deletedContinuation_eq_series K χ S hs]
  exact idealDirichletSeries_logDerivative_eq_primePowerSeries K _
    (norm_deletedCoefficient_le_one K χ S) hs

/-- Reindex the project's `(prime,n)` series to the core's `(n,prime)` series,
including the exact positive-base complex-power normalization. -/
theorem primePowerTerm_eq (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (np : ℕ × HeightOneSpectrum (𝓞 K)) :
    primePowerCoefficient (primeNorm K) a np *
        (primePowerNorm (primeNorm K) np : ℂ) ^ (-s) =
      primePowerLogTerm K a 1 s (np.2, np.1) := by
  simp only [primePowerCoefficient, primePowerNorm, primeNorm, primePowerLogTerm,
    primeIdealRatio, pow_one, Complex.ofReal_pow, Complex.ofReal_natCast, mul_pow]
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  ring

/-- Absolute convergence is inherited from the proved actual ideal logarithmic
majorant, rather than postulated in a model record. -/
theorem absolute_primePowerSeries (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    Summable (fun np : ℕ × HeightOneSpectrum (𝓞 K) =>
      ‖primePowerCoefficient (primeNorm K) a np‖ *
        (primePowerNorm (primeNorm K) np) ^ (-(2 : ℝ))) := by
  have h : Summable (fun np : ℕ × HeightOneSpectrum (𝓞 K) =>
      ‖primePowerLogTerm K a 1 2 (np.2, np.1)‖) := by
    simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.swap] using
      (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).summable_iff.mpr
        (absolutelySummable_primePowerLogTerm K a ha 1 (s := 2) (by norm_num))
  have heq (np : ℕ × HeightOneSpectrum (𝓞 K)) :
      ‖primePowerCoefficient (primeNorm K) a np‖ *
          (primePowerNorm (primeNorm K) np) ^ (-(2 : ℝ)) =
        ‖primePowerLogTerm K a 1 2 (np.2, np.1)‖ := by
    rw [← primePowerTerm_eq K a 2 np, norm_mul]
    have hp : 0 < primePowerNorm (primeNorm K) np := by
      exact pow_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
        (primeNorm_ge_two K np.2)) _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    norm_num
  exact h.congr (fun np => (heq np).symm)

theorem deleted_euler (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    (∑' np : ℕ × HeightOneSpectrum (𝓞 K),
      primePowerCoefficient (primeNorm K) (deletedCoefficient K χ S) np *
        (primePowerNorm (primeNorm K) np : ℂ) ^ (-s)) =
      -deriv (heckeDeletedContinuation K χ S) s / heckeDeletedContinuation K χ S s := by
  simp_rw [primePowerTerm_eq]
  have hswap : (∑' np : ℕ × HeightOneSpectrum (𝓞 K),
      primePowerLogTerm K (deletedCoefficient K χ S) 1 s (np.2, np.1)) =
      primePowerLogSeries K (deletedCoefficient K χ S) 1 s := by
    simpa only [primePowerLogSeries, Equiv.prodComm_apply, Prod.swap] using
      (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).tsum_eq
        (fun pn => primePowerLogTerm K (deletedCoefficient K χ S) 1 s pn)
  rw [hswap, neg_div, deleted_logDerivative_eq_primePowerSeries K χ S hs, neg_neg]

/-- The central Euler logarithm has a common bound for all characters and
all finite deletions: deleting coefficients does not enlarge the majorant. -/
def eulerLogSize : ℝ := (3 / 2 : ℝ) *
  ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(2 : ℝ))

theorem eulerLogSize_nonneg : 0 ≤ eulerLogSize K := by
  unfold eulerLogSize
  exact mul_nonneg (by norm_num)
    (tsum_nonneg (fun I => Real.rpow_nonneg (idealNorm_pos K I).le _))

theorem deleted_centerLog_bound (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (t : ℝ) :
    ‖idealEulerLog K (deletedCoefficient K χ S) ((2 : ℂ) + t * Complex.I)‖ ≤
      eulerLogSize K :=
  idealEulerLog_norm_le K _ (norm_deletedCoefficient_le_one K χ S)
    2 (by norm_num) _ (by simp)

theorem deleted_centerLog_exp (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (t : ℝ) :
    Complex.exp (idealEulerLog K (deletedCoefficient K χ S) ((2 : ℂ) + t * Complex.I)) =
      heckeDeletedContinuation K χ S ((2 : ℂ) + t * Complex.I) := by
  rw [exp_idealEulerLog_eq_series K _ (norm_deletedCoefficient_le_one K χ S)
      _ (by simp), deletedContinuation_eq_series K χ S (by simp)]

/-- The common packet boundary itself excludes every actual zero to its
right. The Euler half-plane handles Re(s)>1; no seed theorem is used. -/
theorem continuation_ne_zero_of_packet_boundary
    (ω χ : HeckeCharacter K) (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s : ℂ) (hs : B < s.re) : heckeContinuation K χ s ≠ 0 := by
  by_cases hright : 1 < s.re
  · exact heckeContinuation_ne_zero K χ hright
  intro hzero
  have hd := differentiable_heckeContinuation_of_nonNorm K χ hχ
  have hlim : Tendsto (heckeContinuation K χ) (𝓝[≠] s) (𝓝 0) := by
    simpa only [hzero] using
      ((hd.continuous.continuousAt : ContinuousAt (heckeContinuation K χ) s).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hpos : 0 < meromorphicOrderAt (heckeContinuation K χ) s :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ((hd.analyticAt s).meromorphicAt)).mp hlim
  have hb := hboundary ⟨χ, hpacket⟩ s.re ⟨s, rfl, hpos⟩
    (hB.trans hs.le) (le_of_not_gt hright)
  exact (not_le_of_gt hs) hb

theorem deleted_entire (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) :
    Differentiable ℂ (heckeDeletedContinuation K χ S) := by
  have hP : Differentiable ℂ (heckeEulerDeletionPolynomial K χ S) :=
    fun s => (heckeEulerDeletionPolynomial_analyticAt K χ S s).differentiableAt
  exact hP.mul (differentiable_heckeContinuation_of_nonNorm K χ hχ)

theorem deleted_ne_zero_of_packet_boundary
    (ω χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (s : ℂ) (hs : B < s.re) : heckeDeletedContinuation K χ S s ≠ 0 :=
  mul_ne_zero (heckeEulerDeletionPolynomial_ne_zero K χ S (by linarith))
    (continuation_ne_zero_of_packet_boundary K ω χ hpacket hχ B hB hboundary s hs)

/-- All analytic fields for the genuine deleted continuation. -/
def deletedZeroFreeData
    (ω χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeDeletedContinuation K χ S s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    ZeroFreeData (heckeDeletedContinuation K χ S) B where
  C := C
  Q := Q
  p := p
  k := k
  A := eulerLogSize K
  C_one := hC
  Q_one := hQ
  p_nonneg := hp
  entire := deleted_entire K χ S hχ
  zeroFree := deleted_ne_zero_of_packet_boundary K ω χ S hpacket hχ B hB hboundary
  centerLog := fun t => idealEulerLog K (deletedCoefficient K χ S) ((2 : ℂ) + t * Complex.I)
  centerLog_exp := deleted_centerLog_exp K χ S
  centerLog_bound := deleted_centerLog_bound K χ S
  polynomial := hpoly

/-- Concrete prime slots. No analytic cancellation or Euler identity is a
model field: the original Euler series constructs both arithmetic inputs. -/
def deletedSlotData
    (ω χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeDeletedContinuation K χ S s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    SlotData (HeightOneSpectrum (𝓞 K)) B (primeCountConstant K) where
  norm := primeNorm K
  coefficient := deletedCoefficient K χ S
  function := heckeDeletedContinuation K χ S
  arithmetic := actualPrimeArithmetic K _ (norm_deletedCoefficient_le_one K χ S)
  analytic := deletedZeroFreeData K ω χ S hpacket hχ B hB hboundary C Q p k hC hQ hp hpoly
  absolute := absolute_primePowerSeries K _ (norm_deletedCoefficient_le_one K χ S)
  euler := fun _ hs => deleted_euler K χ S hs

/-- The precise loss exposed to the moment-model uniformity contract. -/
theorem deletedSlotData_height
    (ω χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeDeletedContinuation K χ S s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    let d := deletedSlotData K ω χ S hpacket hχ B hB hboundary C Q p k hC hQ hp hpoly
    heightConstant d.analytic + 3 * (d.analytic.k : ℝ) =
      1 + Real.log C + p * Real.log Q + eulerLogSize K + 3 * (k : ℝ) := rfl

/-- The common moment-model entry point. All finite original masks may be
handled by the paired core, while the L-function uses the empty fixed deletion. -/
def emptySlotData
    (ω χ : HeckeCharacter K)
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeContinuation K χ s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    SlotData (HeightOneSpectrum (𝓞 K)) B (primeCountConstant K) :=
  deletedSlotData K ω χ ∅ hpacket hχ B hB hboundary C Q p k hC hQ hp
    (by simpa only [deletedContinuation_empty] using hpoly)

@[simp] theorem emptySlotData_coefficient
    (ω χ : HeckeCharacter K)
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeContinuation K χ s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    (emptySlotData K ω χ hpacket hχ B hB hboundary C Q p k hC hQ hp hpoly).coefficient =
      primeCoefficient K χ := deletedCoefficient_empty K χ

theorem emptySlotData_height
    (ω χ : HeckeCharacter K)
    (hpacket : χ ∈ HeckePacket K ω)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (B : ℝ) (hB : 1 / 2 ≤ B)
    (hboundary : ∀ η : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω η,
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (C Q p : ℝ) (k : ℕ) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hp : 0 ≤ p)
    (hpoly : ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖heckeContinuation K χ s‖ ≤ C * Q ^ p * (2 + |s.im|) ^ k) :
    let d := emptySlotData K ω χ hpacket hχ B hB hboundary C Q p k hC hQ hp hpoly
    heightConstant d.analytic + 3 * (d.analytic.k : ℝ) =
      1 + Real.log C + p * Real.log Q + eulerLogSize K + 3 * (k : ℝ) := rfl

/-- Actual conductor positivity follows from the already proved functional
equation, and integrality promotes it to Q≥1. -/
theorem one_le_actualConductorScale (χ : HeckeCharacter K)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) :
    1 ≤ heckeConductorScale K χ := by
  obtain ⟨ε, Λ, Λd, hQ, _, _, _, _, _, _, _, _⟩ :=
    exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
  exact HeckeUniformStripGrowth.one_le_conductorScale_of_pos K χ hQ

/-- Join the fixed-type strip to the Euler half-plane. The common constant
is chosen before the character, its conductor, and the contour buffer. -/
theorem exists_uniform_fixedType_rightHalfPlane_polynomial
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ χ : HeckeCharacter K,
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, 1 / 2 ≤ s.re →
        ‖heckeContinuation K χ s‖ ≤ C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨A, _, hA⟩ := HeckeUniformStripGrowth.exists_uniform_fixedType_strip_bound
    K hcomplex τ m (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨E, _, hE⟩ := HeckeUniformStripGrowth.exists_uniform_rightHalfPlane_bound
    K (9 / 8) (by norm_num)
  let C : ℝ := max 1 (max A E)
  have hC : 1 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_max_left A E).trans (le_max_right 1 (max A E))
  have hEC : E ≤ C := (le_max_right A E).trans (le_max_right 1 (max A E))
  refine ⟨C, hC, ?_⟩
  intro χ hχ hτ hm s hs
  have hQ := one_le_actualConductorScale K χ hχ
  have hQnon : 0 ≤ heckeConductorScale K χ := zero_le_one.trans hQ
  by_cases hright : s.re ≤ 9 / 8
  · have hb := hA χ hχ hτ hm s ⟨by linarith, by linarith⟩
    have hb' : ‖heckeContinuation K χ s‖ ≤
        A * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      simpa only [show (1 / 2 : ℝ) + 1 / 8 = 5 / 8 by norm_num] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hQnon _)) (by positivity))
  · have hQpow : 1 ≤ heckeConductorScale K χ ^ (5 / 8 : ℝ) :=
      Real.one_le_rpow hQ (by norm_num)
    have hHpow : 1 ≤ (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
      one_le_pow₀ (by linarith [abs_nonneg s.im])
    calc
      ‖heckeContinuation K χ s‖ ≤ E := hE χ s (by linarith)
      _ ≤ C := hEC
      _ ≤ C * heckeConductorScale K χ ^ (5 / 8 : ℝ) :=
        le_mul_of_one_le_right (zero_le_one.trans hC) hQpow
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hQnon _)) hHpow

/-- Fixed finite deletion costs a fixed multiplicative constant. -/
theorem exists_uniform_deleted_fixedType_polynomial
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ χ : HeckeCharacter K,
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, 1 / 2 ≤ s.re →
        ‖heckeDeletedContinuation K χ S s‖ ≤
          C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
            (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fixedType_rightHalfPlane_polynomial K hcomplex τ m
  let D := max 1 (deletionUpperConstant K S)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D * C, one_le_mul_of_one_le_of_one_le hD hC, ?_⟩
  intro χ hχ hτ hm s hs
  have hdel : ‖heckeEulerDeletionPolynomial K χ S s‖ ≤ D :=
    (norm_heckeEulerDeletionPolynomial_le K S χ s (by linarith)).trans (le_max_right _ _)
  rw [heckeDeletedContinuation, norm_mul]
  calc
    _ ≤ D * (C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
        (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K))) :=
      mul_le_mul hdel (hb χ hχ hτ hm s hs) (norm_nonneg _) (zero_le_one.trans hD)
    _ = _ := by ring

/-- All nonprincipal finite-order characters have one common infinity type
over the totally complex field; the model need not supply infinity parameters. -/
theorem exists_uniform_finiteOrder_polynomial
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ χ : HeckeCharacter K,
      FiniteOrder χ → χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
        ‖heckeContinuation K χ s‖ ≤ C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fixedType_rightHalfPlane_polynomial K hcomplex 0 0
  refine ⟨C, hC, ?_⟩
  intro χ hfinite hne
  obtain ⟨hτ, hm⟩ := finiteOrder_infinityType_zero K hcomplex χ hfinite
  exact hb χ (nonNorm_of_finiteOrder_ne_one K χ hfinite hne) hτ hm

theorem exists_uniform_deleted_finiteOrder_polynomial
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ χ : HeckeCharacter K,
      FiniteOrder χ → χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
        ‖heckeDeletedContinuation K χ S s‖ ≤
          C * heckeConductorScale K χ ^ (5 / 8 : ℝ) *
            (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_deleted_fixedType_polynomial K hcomplex 0 0 S
  refine ⟨C, hC, ?_⟩
  intro χ hfinite hne
  obtain ⟨hτ, hm⟩ := finiteOrder_infinityType_zero K hcomplex χ hfinite
  exact hb χ (nonNorm_of_finiteOrder_ne_one K χ hfinite hne) hτ hm

#print axioms deletedContinuation_eq_series
#print axioms absolute_primePowerSeries
#print axioms deleted_euler
#print axioms deletedSlotData
#print axioms exists_uniform_finiteOrder_polynomial
#print axioms exists_uniform_deleted_finiteOrder_polynomial

end HeckeSkeleton.PrimeCancellationHecke
