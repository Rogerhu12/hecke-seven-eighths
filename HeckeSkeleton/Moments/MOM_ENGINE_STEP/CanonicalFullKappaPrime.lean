import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingSupportWindows
import HeckeGeneral.Analysis.PrimePolynomialAbsoluteBound
import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import PrimeCancellationPairedProfiles
import PrimeCancellationMaskCount
import PrimeCancellationUniformity

/-!
# The actual single-prime input on the full kappa interval

The analytic input below consists of the original Euler series and
zero-free analytic data for the actual Hecke coefficient. It contains
no estimate for a prime polynomial or a normalized descendant. The
proved prime-cancellation theorem chooses its finite Schwartz orders
before every character, profile, mask, scale and Fourier parameter.

The original complete moving mask supplies its own sparse deletion
bound. All primes of the fixed bad support, the complete row and the
full moving/remaining support are retained. The endpoint kappa = 1
uses the unconditional absolute estimate and needs no zero-free data.

The contour buffer and analytic height costs are explicit. Enlarging
the common profile radius pays them; the resulting normalized prime
cost is one. The enlarged radius must still be charged to every
pre-removal profile in the same Fourier kernel.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open PrimeCancellation.Analytic PrimeCancellation.Paired
open PrimeCancellation.UniformProfiles PrimeCancellation.PairedProfiles

variable {K : Type} [Field K] [NumberField K]

/-- Original single-character analytic data. Both the coefficient and
the continued function are the actual ones. The underlying SlotData
contains Euler, convergence, zero-free and elementary counting data,
not a bound on a prime sum. -/
structure OriginalPrimeAnalyticData (χ : HeckeCharacter K) (β degree : ℝ) where
  slot : SlotData (HeightOneSpectrum (𝓞 K)) β degree
  norm_eq : ∀ p, slot.norm p = (Ideal.absNorm p.asIdeal : ℝ)
  coefficient_eq : ∀ p, slot.coefficient p = primeCoefficient K χ p
  function_eq : slot.function = heckeContinuation K χ

namespace CanonicalFullKappaPrime

local instance canonicalFullKappaPrimeCountable : Countable (HeightOneSpectrum (𝓞 K)) :=
  (primeNonzeroIdeal_injective K).countable

/-- The orders are chosen by the proved uniform Mellin estimate, before
the field, characters and profiles are supplied. -/
def orders : Finset (ℕ × ℕ) :=
  Classical.choose exists_uniform_masked_prime_seminorm_bound

def analyticCoefficient : ℝ :=
  Classical.choose (Classical.choose_spec exists_uniform_masked_prime_seminorm_bound)

theorem analyticCoefficient_pos : 0 < analyticCoefficient :=
  (Classical.choose_spec
    (Classical.choose_spec exists_uniform_masked_prime_seminorm_bound)).1

theorem zero_mem_orders : (0, 0) ∈ orders :=
  (Classical.choose_spec
    (Classical.choose_spec exists_uniform_masked_prime_seminorm_bound)).2.1

def endpointCoefficient (K : Type) [Field K] [NumberField K] : ℝ :=
  Classical.choose (exists_norm_primePolynomial_absolute_bound K)

theorem endpointCoefficient_pos : 0 < endpointCoefficient K :=
  (Classical.choose_spec (exists_norm_primePolynomial_absolute_bound K)).1

/-- Real and complex scalar structures give the identical finite
Schwartz seminorm value. No change of the original representative is
needed when calling the independent analytic core. -/
theorem sourceSeminorm_eq_complex (s : Finset (ℕ × ℕ)) (W : 𝓢(ℝ, ℂ)) :
    sourceSeminorm s W = s.sup (schwartzSeminormFamily ℂ ℝ ℂ) W := by
  rw [sourceSeminorm, Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
  rfl

theorem norm_le_orders (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖W x‖ ≤ orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) W :=
  (SchwartzMap.norm_le_seminorm ℂ W x).trans
    (Seminorm.le_finset_sup_apply zero_mem_orders)

/-- This factor is independent of the Fourier parameter whenever the
original analytic height and mask windows are. Its scale dependence
is kept visible instead of being called a fixed constant. -/
def cost (K : Type) [Field K] [NumberField K]
    (δ degree height mask : ℝ) : ℝ :=
  max 1 (max (endpointCoefficient K)
    (uniformConstant δ analyticCoefficient degree height + mask))

theorem one_le_cost (δ degree height mask : ℝ) :
    1 ≤ cost K δ degree height mask := le_max_left _ _

theorem cost_pos (δ degree height mask : ℝ) :
    0 < cost K δ degree height mask := zero_lt_one.trans_le (one_le_cost _ _ _ _)

theorem endpoint_le_cost (δ degree height mask : ℝ) :
    endpointCoefficient K ≤ cost K δ degree height mask :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem analytic_le_cost (δ degree height mask : ℝ) :
    uniformConstant δ analyticCoefficient degree height + mask ≤
      cost K δ degree height mask :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- Analytic height and the deleted-prime logarithm grow at most
linearly in one common original envelope. The endpoint constant and
the constant terms of the contour estimate are paid by its lower
bound one. -/
theorem cost_le_growth (δ degree height mask H₀ B₀ F : ℝ)
    (hdegree : 0 ≤ degree) (hF : 1 ≤ F)
    (hheight : height ≤ H₀ * F) (hmask : mask ≤ B₀ * F) :
    cost K δ degree height mask ≤ cost K δ degree H₀ B₀ * F := by
  have hlinear : 24 * analyticCoefficient * height / δ ^ 2 ≤
      (24 * analyticCoefficient * H₀ / δ ^ 2) * F := by
    calc
      _ = (24 * analyticCoefficient / δ ^ 2) * height := by ring
      _ ≤ (24 * analyticCoefficient / δ ^ 2) * (H₀ * F) :=
        mul_le_mul_of_nonneg_left hheight (by
          exact div_nonneg (mul_nonneg (by norm_num) analyticCoefficient_pos.le)
            (sq_nonneg δ))
      _ = _ := by ring
  have hrest : degree * (1 + Real.sqrt 2) + 2 * degree * Real.exp 4 ≤
      (degree * (1 + Real.sqrt 2) + 2 * degree * Real.exp 4) * F :=
    le_mul_of_one_le_right (by positivity) hF
  have hwhole : uniformConstant δ analyticCoefficient degree height + mask ≤
      (uniformConstant δ analyticCoefficient degree H₀ + B₀) * F := by
    calc
      _ = (24 * analyticCoefficient * height / δ ^ 2) +
          (degree * (1 + Real.sqrt 2) + 2 * degree * Real.exp 4) + mask := by
        unfold uniformConstant
        ring
      _ ≤ ((24 * analyticCoefficient * H₀ / δ ^ 2) * F) +
          ((degree * (1 + Real.sqrt 2) + 2 * degree * Real.exp 4) * F) +
          B₀ * F := add_le_add (add_le_add hlinear hrest) hmask
      _ = _ := by unfold uniformConstant; ring
  have hbase : cost K δ degree H₀ B₀ ≤ cost K δ degree H₀ B₀ * F :=
    le_mul_of_one_le_right (cost_pos δ degree H₀ B₀).le hF
  apply max_le
  · exact (one_le_cost δ degree H₀ B₀).trans hbase
  · apply max_le
    · exact (endpoint_le_cost δ degree H₀ B₀).trans hbase
    · exact hwhole.trans
        (mul_le_mul_of_nonneg_right (analytic_le_cost δ degree H₀ B₀)
          (zero_le_one.trans hF))

variable {ω ψ : HeckeCharacter K}

/-- Literal identity with the independently proved analytic prime sum.
It keeps the original support, all Boolean deletions and the original
ramified coefficient zeros. -/
theorem primePolynomial_eq_normalizedMaskedPrimeSum
    (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t β degree : ℝ)
    (raw : OriginalPrimeAnalyticData (d.rowCharacter u * d.slotCoefficient i) β degree)
    (W : 𝓢(ℝ, ℂ)) (hW : ∀ x, (d.geometry.slots i).profile t x = W x) :
    primePolynomial d i u Z t =
      normalizedMaskedPrimeSum raw.slot W (Z ^ (d.geometry.slots i).length)
        ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
        (fun p => d.commonMask u p.asIdeal) := by
  simp only [primePolynomial, normalizedMaskedPrimeSum, maskedPrimeSum,
    PrimeCancellationAux.maskedSum, raw.norm_eq, raw.coefficient_eq, hW, maskValue]

/-- The logarithmic deletion bound follows from actual ideal divisibility.
There is no finite-cardinality input at this interface. -/
theorem deleted_count_le_log
    (pool : Finset (HeightOneSpectrum (𝓞 K)))
    (keep : HeightOneSpectrum (𝓞 K) → Bool)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hdiv : ∀ p, keep p = false → p.asIdeal ∣ J.val) :
    ((pool.filter (fun p => keep p = false)).card : ℝ) ≤
      Real.log (idealNorm K J) / Real.log 2 := by
  apply PrimeCancellation.MaskCount.card_prime_divisors_le_log
    Ideal.absNorm (pool.filter (fun p => keep p = false)) J.val 2
    (Nat.pos_of_ne_zero (fun h => nonZeroDivisors.coe_ne_zero J
      (Ideal.absNorm_eq_zero_iff.mp h))) (by norm_num)
  · intro p _
    exact_mod_cast (show 2 ≤ Ideal.absNorm p.asIdeal from one_lt_primeIdeal_absNorm K p)
  · intro p hp
    exact hdiv p (Finset.mem_filter.mp hp).2

/-- Full kappa, with its exact contour loss. The only subcritical
analytic input is original single-character Euler/zero-free data.
The endpoint branch never calls that input. -/
theorem raw_prime_bound
    (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t κ δ degree height mask amplitude : ℝ)
    (hZ : 1 ≤ Z) (hκlo : 3 / 4 ≤ κ) (hκhi : κ ≤ 1)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4) (hamp : 0 ≤ amplitude)
    (W : 𝓢(ℝ, ℂ)) (hW : ∀ x, (d.geometry.slots i).profile t x = W x)
    (hsupport : Function.support (W : ℝ → ℂ) ⊆ Set.Ioo (1 : ℝ) 2)
    (hprofile : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hdiv : ∀ p, d.commonMask u p.asIdeal = false → p.asIdeal ∣ J.val)
    (hmask : Real.log (idealNorm K J) / Real.log 2 ≤ mask)
    (raw : ∀ _hκ : κ < 1,
      OriginalPrimeAnalyticData (d.rowCharacter u * d.slotCoefficient i) ((κ + 1) / 2) degree)
    (hheight : ∀ hκ : κ < 1,
      heightConstant (raw hκ).slot.analytic + 3 * ((raw hκ).slot.analytic.k : ℝ) ≤ height) :
    ‖primePolynomial d i u Z t‖ ^ 2 ≤
      (amplitude * cost K δ degree height mask) ^ 2 *
        Z ^ (κ * (d.geometry.slots i).length + 2 * δ * (d.geometry.slots i).length) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hP : 1 ≤ Z ^ (d.geometry.slots i).length :=
    Real.one_le_rpow hZ (d.geometry.slots i).length_pos.le
  have hcost : 0 ≤ cost K δ degree height mask := (cost_pos _ _ _ _).le
  by_cases hκ : κ = 1
  · have hb := (Classical.choose_spec (exists_norm_primePolynomial_absolute_bound K)).2
      d i u Z t amplitude hZ hamp
      (by simpa only [hW] using hsupport)
      (fun x => by rw [hW]; exact (norm_le_orders W x).trans hprofile)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simp only [mul_pow, Real.sq_sqrt (Real.rpow_nonneg hZpos.le _)] at hs
    calc
      _ ≤ (endpointCoefficient K * amplitude) ^ 2 *
          Z ^ (d.geometry.slots i).length := by simpa only [mul_pow] using hs
      _ ≤ (amplitude * cost K δ degree height mask) ^ 2 *
          Z ^ (κ * (d.geometry.slots i).length +
            2 * δ * (d.geometry.slots i).length) := by
        apply mul_le_mul
        · apply pow_le_pow_left₀ (mul_nonneg endpointCoefficient_pos.le hamp)
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_right (endpoint_le_cost δ degree height mask) hamp
        · apply Real.rpow_le_rpow_of_exponent_le hZ
          rw [hκ]
          nlinarith [(d.geometry.slots i).length_pos]
        · exact Real.rpow_nonneg hZpos.le _
        · exact sq_nonneg _
  · have hκlt : κ < 1 := lt_of_le_of_ne hκhi hκ
    let a := raw hκlt
    have hH : 0 ≤ height :=
      (add_nonneg (heightConstant_nonneg a.slot.analytic) (by positivity)).trans (hheight hκlt)
    have hB : 0 ≤ mask :=
      (div_nonneg (Real.log_nonneg (one_le_idealNorm K J)) (Real.log_nonneg (by norm_num))).trans hmask
    have hdeleted := (deleted_count_le_log
      ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
      (fun p => d.commonMask u p.asIdeal) J hdiv).trans hmask
    have hb := (Classical.choose_spec
      (Classical.choose_spec exists_uniform_masked_prime_seminorm_bound)).2.2 W
      (fun x hx => ⟨(hsupport hx).1.le, (hsupport hx).2.le⟩)
      ((κ + 1) / 2) δ degree height mask a.slot (hheight hκlt)
      (Z ^ (d.geometry.slots i).length)
      ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
      (fun p => d.commonMask u p.asIdeal)
      (by linarith) (by linarith) hδ hδhi hP
      (fun p hp => ((d.geometry.slots i).support_spec t _ p).mpr
        (by simpa only [a.norm_eq, hW] using hp)) hdeleted
    have hM : sourceSeminorm orders W ≤ amplitude := by
      rw [sourceSeminorm_eq_complex]
      exact hprofile
    have hU : 0 ≤ uniformConstant δ analyticCoefficient degree height + mask :=
      add_nonneg (uniformConstant_nonneg _ _ _ _ analyticCoefficient_pos.le
        a.slot.arithmetic.d_nonneg hH) hB
    have hb' : ‖maskedPrimeSum a.slot W (Z ^ (d.geometry.slots i).length)
        ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
        (fun p => d.commonMask u p.asIdeal)‖ ≤
        (amplitude * cost K δ degree height mask) *
          (Z ^ (d.geometry.slots i).length) ^ ((κ + 1) / 2 + δ) := by
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.rpow_nonneg hZpos.le _) _)
      calc
        _ ≤ (uniformConstant δ analyticCoefficient degree height + mask) * amplitude :=
          mul_le_mul_of_nonneg_left hM hU
        _ ≤ cost K δ degree height mask * amplitude :=
          mul_le_mul_of_nonneg_right (analytic_le_cost δ degree height mask) hamp
        _ = _ := mul_comm _ _
    have hn := PrimeCancellationAux.norm_normalized_sq_le_rpow
      (Z ^ (d.geometry.slots i).length) ((κ + 1) / 2 + δ)
      (amplitude * cost K δ degree height mask) (Real.rpow_pos_of_pos hZpos _)
      (mul_nonneg hamp hcost) _ hb'
    rw [primePolynomial_eq_normalizedMaskedPrimeSum d i u Z t
      ((κ + 1) / 2) degree a W hW]
    change ‖normalizedMaskedPrimeSum a.slot W (Z ^ (d.geometry.slots i).length)
      ((d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
      (fun p => d.commonMask u p.asIdeal)‖ ^ 2 ≤
        (amplitude * cost K δ degree height mask) ^ 2 *
          (Z ^ (d.geometry.slots i).length) ^ (2 * ((κ + 1) / 2 + δ) - 1) at hn
    rw [← Real.rpow_mul hZpos.le] at hn
    rw [show (d.geometry.slots i).length * (2 * ((κ + 1) / 2 + δ) - 1) =
      κ * (d.geometry.slots i).length + 2 * δ * (d.geometry.slots i).length by ring] at hn
    exact hn

/-- The factor used to enlarge the common profile radius. The contour
cost is paid at the fixed upper slot length, including its endpoint. -/
def radiusFactor (K : Type) [Field K] [NumberField K]
    (Z δ lengthBound degree height mask : ℝ) : ℝ :=
  cost K δ degree height mask * Z ^ (δ * lengthBound)

theorem radiusFactor_pos (Z δ lengthBound degree height mask : ℝ) (hZ : 0 < Z) :
    0 < radiusFactor K Z δ lengthBound degree height mask :=
  mul_pos (cost_pos _ _ _ _) (Real.rpow_pos_of_pos hZ _)

theorem one_le_radiusFactor (Z δ lengthBound degree height mask : ℝ)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hL : 0 ≤ lengthBound) :
    1 ≤ radiusFactor K Z δ lengthBound degree height mask := by
  simpa only [one_mul] using mul_le_mul (one_le_cost δ degree height mask)
    (Real.one_le_rpow hZ (mul_nonneg hδ hL)) zero_le_one
    ((cost_pos δ degree height mask).le)

/-- A fixed coefficient for one original profile. It is selected before
the source, base, height, row and Fourier parameter. -/
def envelopeConstant (K : Type) [Field K] [NumberField K]
    (δ degree H₀ B₀ η : ℝ) : ℝ :=
  max 1 (cost K δ degree H₀ B₀ *
    PrimeCancellationUniformity.logAbsorptionConstant 1 (η / 2))

theorem one_le_envelopeConstant (δ degree H₀ B₀ η : ℝ) :
    1 ≤ envelopeConstant K δ degree H₀ B₀ η := le_max_left _ _

/-- All scale growth in the original analytic height and complete-mask
logarithm is explicit. The logarithmic factor uses half the scale
budget; the contour buffer uses the other half. -/
theorem radiusFactor_le_profile_power
    (Z T δ lengthBound degree height mask H₀ B₀ η : ℝ) (h : ℕ)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) (hdegree : 0 ≤ degree) (hB₀ : 0 ≤ B₀)
    (hη : 0 < η) (hcontour : δ * lengthBound ≤ η / 2)
    (hheight : height ≤ H₀ * (1 + Real.log Z) * (1 + T) ^ h)
    (hmask : mask ≤ B₀ * (1 + Real.log Z)) :
    radiusFactor K Z δ lengthBound degree height mask ≤
      envelopeConstant K δ degree H₀ B₀ η * (1 + T) ^ h * Z ^ η := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hlog : 1 ≤ 1 + Real.log Z := by linarith [Real.log_nonneg hZ]
  have hpow : 1 ≤ (1 + T) ^ h := one_le_pow₀ (by linarith)
  have hF : 1 ≤ (1 + Real.log Z) * (1 + T) ^ h :=
    one_le_mul_of_one_le_of_one_le hlog hpow
  have hheight' : height ≤ H₀ * ((1 + Real.log Z) * (1 + T) ^ h) := by
    simpa only [mul_assoc] using hheight
  have hmask' : mask ≤ B₀ * ((1 + Real.log Z) * (1 + T) ^ h) := by
    apply hmask.trans
    simpa only [mul_assoc] using
      le_mul_of_one_le_right (mul_nonneg hB₀ (zero_le_one.trans hlog)) hpow
  have hgrowth := cost_le_growth δ degree height mask H₀ B₀
    ((1 + Real.log Z) * (1 + T) ^ h) hdegree hF hheight' hmask'
  have hlogsmall : 1 + Real.log Z ≤
      PrimeCancellationUniformity.logAbsorptionConstant 1 (η / 2) * Z ^ (η / 2) := by
    simpa only [pow_one] using
      PrimeCancellationUniformity.one_add_log_pow_le_rpow 1 (by linarith : 0 < η / 2) hZ
  have hC0 : 0 ≤ cost K δ degree H₀ B₀ := (cost_pos δ degree H₀ B₀).le
  calc
    _ ≤ (cost K δ degree H₀ B₀ * ((1 + Real.log Z) * (1 + T) ^ h)) *
        Z ^ (δ * lengthBound) :=
      mul_le_mul_of_nonneg_right hgrowth (Real.rpow_nonneg hZpos.le _)
    _ = (cost K δ degree H₀ B₀ * (1 + T) ^ h) * (1 + Real.log Z) *
        Z ^ (δ * lengthBound) := by ring
    _ ≤ (cost K δ degree H₀ B₀ * (1 + T) ^ h) *
        (PrimeCancellationUniformity.logAbsorptionConstant 1 (η / 2) * Z ^ (η / 2)) *
        Z ^ (δ * lengthBound) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogsmall
          (mul_nonneg hC0 (zero_le_one.trans hpow))) (Real.rpow_nonneg hZpos.le _)
    _ = (cost K δ degree H₀ B₀ *
        PrimeCancellationUniformity.logAbsorptionConstant 1 (η / 2)) *
        (1 + T) ^ h * Z ^ (η / 2 + δ * lengthBound) := by
      rw [Real.rpow_add hZpos]
      ring
    _ ≤ envelopeConstant K δ degree H₀ B₀ η *
        (1 + T) ^ h * Z ^ (η / 2 + δ * lengthBound) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hpow))
        (Real.rpow_nonneg hZpos.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (mul_nonneg (zero_le_one.trans (one_le_envelopeConstant _ _ _ _ _))
        (zero_le_one.trans hpow))

/-- The complete power of the enlarged radius is paid before choosing
the original data. In applications `N` is the full pre-removal profile
degree (both plain profiles and every slot, on both sides), or any
fixed larger degree used by the actual Fourier-kernel mass theorem.
It is not the number of removed slots. -/
theorem exists_full_profile_radius_bound
    (N h : ℕ) (ε lengthBound degree H₀ B₀ : ℝ)
    (hε : 0 < ε) (hdegree : 0 ≤ degree) (hB₀ : 0 ≤ B₀) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 1 ≤ C ∧
      ∀ Z T height mask : ℝ, 1 ≤ Z → 0 ≤ T →
        height ≤ H₀ * (1 + Real.log Z) * (1 + T) ^ h →
        mask ≤ B₀ * (1 + Real.log Z) →
        radiusFactor K Z δ lengthBound degree height mask ^ N ≤
          C ^ N * (1 + T) ^ (h * N) * Z ^ ε := by
  let η := ε / ((N : ℝ) + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  let δ := PrimeCancellationUniformity.contourBuffer η lengthBound
  have hδ : 0 < δ := PrimeCancellationUniformity.contourBuffer_pos hη
  have hδhi : δ ≤ 1 / 4 := PrimeCancellationUniformity.contourBuffer_le_quarter _ _
  have hcontour : δ * lengthBound ≤ η / 2 := by
    have hb := PrimeCancellationUniformity.contourBuffer_total_loss hη
      (le_refl lengthBound)
    change 2 * δ * lengthBound ≤ η at hb
    linarith
  let C := envelopeConstant K δ degree H₀ B₀ η
  refine ⟨δ, C, hδ, hδhi, one_le_envelopeConstant _ _ _ _ _, ?_⟩
  intro Z T height mask hZ hT hheight hmask
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hηN : η * (N : ℝ) ≤ ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr
    nlinarith
  have hb := radiusFactor_le_profile_power Z T δ lengthBound degree height mask
    H₀ B₀ η h hZ hT hdegree hB₀ hη hcontour hheight hmask
  calc
    _ ≤ (C * (1 + T) ^ h * Z ^ η) ^ N :=
      pow_le_pow_left₀ (radiusFactor_pos _ _ _ _ _ _ hZpos).le hb N
    _ = C ^ N * (1 + T) ^ (h * N) * Z ^ (η * (N : ℝ)) := by
      simp only [mul_pow, pow_mul, Real.rpow_mul_natCast hZpos.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hηN)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_envelopeConstant _ _ _ _ _)) _)
        (pow_nonneg (by linarith : 0 ≤ 1 + T) _))

/-- The exponent and the enlarged radius are exactly matched. This is
the bridge used by the actual capacity constructor, not a stronger
estimate assumed for an arbitrary normalized profile. -/
theorem raw_prime_bound_radius
    (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (Z t κ δ lengthBound degree height mask amplitude : ℝ)
    (hZ : 1 ≤ Z) (hκlo : 3 / 4 ≤ κ) (hκhi : κ ≤ 1)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
    (hlength : (d.geometry.slots i).length ≤ lengthBound) (hamp : 0 ≤ amplitude)
    (W : 𝓢(ℝ, ℂ)) (hW : ∀ x, (d.geometry.slots i).profile t x = W x)
    (hsupport : Function.support (W : ℝ → ℂ) ⊆ Set.Ioo (1 : ℝ) 2)
    (hprofile : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) W ≤ amplitude)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hdiv : ∀ p, d.commonMask u p.asIdeal = false → p.asIdeal ∣ J.val)
    (hmask : Real.log (idealNorm K J) / Real.log 2 ≤ mask)
    (raw : ∀ _hκ : κ < 1,
      OriginalPrimeAnalyticData (d.rowCharacter u * d.slotCoefficient i) ((κ + 1) / 2) degree)
    (hheight : ∀ hκ : κ < 1,
      heightConstant (raw hκ).slot.analytic + 3 * ((raw hκ).slot.analytic.k : ℝ) ≤ height) :
    ‖primePolynomial d i u Z t‖ ^ 2 ≤
      (amplitude * radiusFactor K Z δ lengthBound degree height mask) ^ 2 *
        Z ^ (κ * (d.geometry.slots i).length) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  apply (raw_prime_bound d i u Z t κ δ degree height mask amplitude
    hZ hκlo hκhi hδ hδhi hamp W hW hsupport hprofile J hdiv hmask raw hheight).trans
  calc
    _ ≤ (amplitude * cost K δ degree height mask) ^ 2 *
        Z ^ (κ * (d.geometry.slots i).length + 2 * δ * lengthBound) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hZ
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlength (by positivity))
    _ = _ := by
      simp only [radiusFactor, mul_pow, ← Real.rpow_mul_natCast hZpos.le]
      rw [Real.rpow_add hZpos]
      rw [show δ * lengthBound * (2 : ℝ) = 2 * δ * lengthBound by ring]
      ring

end CanonicalFullKappaPrime

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The actual deletion container includes the fixed S-primes, the
complete row, and every displayed or remaining mask prime. -/
def primeDeletionIdeal (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨A.cS * (u.val * (Q.moving.fullMaskSupport Q.remaining).val),
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero A.cS_ne_zero
      (mul_ne_zero (nonZeroDivisors.coe_ne_zero u)
        (nonZeroDivisors.coe_ne_zero (Q.moving.fullMaskSupport Q.remaining))))⟩

/-- Deleted primes are proved to divide the literal container. No
assumption about the final mask cardinality is used. -/
theorem deleted_prime_dvd (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) (hdeleted : (data ξ).commonMask u p.asIdeal = false) :
    p.asIdeal ∣ (Q.primeDeletionIdeal u).val := by
  by_contra hdiv
  have hS : p ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    intro hp
    apply hdiv
    exact dvd_mul_of_dvd_left
      (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
        (Finset.mem_coe.mp hp)) _
  have h6 : (6 : 𝓞 K) ∉ p.asIdeal := fun hp => hS (A.above_six p hp)
  have hu : ¬p.asIdeal ∣ u.val := by
    intro hp
    exact hdiv (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hp _) _)
  have hfull : ¬p.asIdeal ∣ (Q.moving.fullMaskSupport Q.remaining).val := by
    intro hp
    exact hdiv (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hp _) _)
  have hrow : completeIdealCommonMask K
      (A.Sf : Set (HeightOneSpectrum (𝓞 K))) u p.asIdeal = true := by
    simp only [completeIdealCommonMask, decide_eq_true_eq,
      HeckeSkeleton.PrimeCancellationIdealMask.prime_divisor_condition_iff,
      HeckeSkeleton.PrimeCancellationIdealMask.prime_isCoprime_iff_not_dvd]
    exact ⟨⟨hS, h6⟩, hu⟩
  have hcop : IsCoprime p.asIdeal (Q.moving.fullMaskSupport Q.remaining).val :=
    (HeckeSkeleton.PrimeCancellationIdealMask.prime_isCoprime_iff_not_dvd _ _).mpr hfull
  rw [Q.mask ξ u p.asIdeal, Q.moving.fullMaskSupport_mask Q.remaining,
    hrow, hcop] at hdeleted
  cases hdeleted

theorem primeDeletionIdeal_norm (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    idealNorm K (Q.primeDeletionIdeal u) =
      (Ideal.absNorm A.cS : ℝ) *
        (idealNorm K u * idealNorm K (Q.moving.fullMaskSupport Q.remaining)) := by
  simp only [primeDeletionIdeal, idealNorm, map_mul, Nat.cast_mul]

/-- A uniform original width supplies the row-independent logarithmic
mask window. The fixed bad ideal is paid in the constant term. -/
def primeMaskLogBound (A : SArithmeticData K) (Z width : ℝ) : ℝ :=
  (Real.log (Ideal.absNorm A.cS : ℝ) + width * Real.log Z) / Real.log 2

/-- The fixed coefficient of the complete-mask logarithm. Only the
original total-width box and the fixed bad ideal enter it. -/
def primeMaskCoefficient (A : SArithmeticData K) (widthBound : ℝ) : ℝ :=
  (Real.log (Ideal.absNorm A.cS : ℝ) + widthBound) / Real.log 2

theorem primeMaskCoefficient_nonneg (A : SArithmeticData K) (widthBound : ℝ)
    (hwidth : 0 ≤ widthBound) : 0 ≤ primeMaskCoefficient A widthBound := by
  have hnorm : 1 ≤ (Ideal.absNorm A.cS : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr A.cS_ne_zero)
  exact div_nonneg (add_nonneg (Real.log_nonneg hnorm) hwidth)
    (Real.log_nonneg (by norm_num))

theorem primeMaskLogBound_le (A : SArithmeticData K) (Z width widthBound : ℝ)
    (hZ : 1 ≤ Z) (hwidth : 0 ≤ widthBound) (hbox : width ≤ widthBound) :
    primeMaskLogBound A Z width ≤
      primeMaskCoefficient A widthBound * (1 + Real.log Z) := by
  have hnorm : 1 ≤ (Ideal.absNorm A.cS : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr A.cS_ne_zero)
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  have hfixed : 0 ≤ Real.log (Ideal.absNorm A.cS : ℝ) := Real.log_nonneg hnorm
  have hnum : Real.log (Ideal.absNorm A.cS : ℝ) + width * Real.log Z ≤
      (Real.log (Ideal.absNorm A.cS : ℝ) + widthBound) * (1 + Real.log Z) := by
    nlinarith [mul_le_mul_of_nonneg_right hbox hlog, mul_nonneg hfixed hlog]
  calc
    _ ≤ ((Real.log (Ideal.absNorm A.cS : ℝ) + widthBound) * (1 + Real.log Z)) /
        Real.log 2 := div_le_div_of_nonneg_right hnum (Real.log_nonneg (by norm_num))
    _ = _ := by unfold primeMaskCoefficient; ring

theorem primeDeletionIdeal_log_le (Z width : ℝ) (hZ : 0 < Z)
    (hbudget : Q.FullJointBudget Z width)
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u) :
    Real.log (idealNorm K (Q.primeDeletionIdeal u)) / Real.log 2 ≤
      primeMaskLogBound A Z width := by
  have hfixed : 0 < (Ideal.absNorm A.cS : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr A.cS_ne_zero)
  have hn := (Q.primeDeletionIdeal_norm u).trans_le
    (mul_le_mul_of_nonneg_left (hbudget ξ u hu) hfixed.le)
  have hlog := Real.log_le_log (idealNorm_pos K (Q.primeDeletionIdeal u)) hn
  rw [Real.log_mul hfixed.ne' (Real.rpow_pos_of_pos hZ width).ne',
    Real.log_rpow hZ] at hlog
  exact div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num))

/-- The full mask deletion count is now an internal consequence of
the original complete row/support budget. -/
theorem deleted_prime_count_le (Z width : ℝ) (hZ : 0 < Z)
    (hbudget : Q.FullJointBudget Z width)
    (ξ : X) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : (data ξ).allowedRow u)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ((pool.filter (fun p => (data ξ).commonMask u p.asIdeal = false)).card : ℝ) ≤
      primeMaskLogBound A Z width :=
  (CanonicalFullKappaPrime.deleted_count_le_log pool
    (fun p => (data ξ).commonMask u p.asIdeal) (Q.primeDeletionIdeal u)
    (Q.deleted_prime_dvd ξ u)).trans
      (Q.primeDeletionIdeal_log_le Z width hZ hbudget ξ u hu)

end CompleteMovingRowRecipe

namespace CanonicalFullKappaPrime

/-- The fixed bad ideal and original total-width box fill the mask
coefficient internally. The constants and contour are selected before
all moving data; the actual complete row/support mask keeps every
factor, including the full sixth root and remaining support. -/
theorem exists_complete_profile_radius_bound
    (A : SArithmeticData K) (N h : ℕ) (ε lengthBound degree H₀ widthBound : ℝ)
    (hε : 0 < ε) (hdegree : 0 ≤ degree) (hwidth : 0 ≤ widthBound) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 1 ≤ C ∧
      ∀ Z T width height : ℝ, 1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ H₀ * (1 + Real.log Z) * (1 + T) ^ h →
        radiusFactor K Z δ lengthBound degree height
          (CompleteMovingRowRecipe.primeMaskLogBound A Z width) ^ N ≤
          C ^ N * (1 + T) ^ (h * N) * Z ^ ε := by
  obtain ⟨δ, C, hδ, hδhi, hC, hbound⟩ := exists_full_profile_radius_bound
    (K := K) N h ε lengthBound degree H₀
    (CompleteMovingRowRecipe.primeMaskCoefficient A widthBound) hε hdegree
    (CompleteMovingRowRecipe.primeMaskCoefficient_nonneg A widthBound hwidth)
  refine ⟨δ, C, hδ, hδhi, hC, ?_⟩
  intro Z T width height hZ hT hbox hheight
  exact hbound Z T height (CompleteMovingRowRecipe.primeMaskLogBound A Z width)
    hZ hT hheight (CompleteMovingRowRecipe.primeMaskLogBound_le A Z width widthBound
      hZ hwidth hbox)

end CanonicalFullKappaPrime

namespace ActualAllocatedSource.Calibration

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {s : ActualAllocatedSource A V H k}
variable {ω ψ : HeckeCharacter K}
variable (D : s.Calibration (σ := σ) ω ψ)
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (Q : CompleteMovingRowRecipe A P R D.data)

/-- The common amplitude is enlarged before the actual length
selection. Its extra factor is independent of the Fourier parameter. -/
def fullKappaAmplitude (D : s.Calibration (σ := σ) ω ψ) (amplitude : V → ℝ)
    (δ lengthBound degree height width : ℝ) (ξ : V) : ℝ :=
  amplitude ξ * CanonicalFullKappaPrime.radiusFactor K s.base δ lengthBound degree height
    (CompleteMovingRowRecipe.primeMaskLogBound A s.base width)

theorem fullKappaAmplitude_pos (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
    (δ lengthBound degree height width : ℝ) (ξ : V) :
    0 < D.fullKappaAmplitude amplitude δ lengthBound degree height width ξ :=
  mul_pos (hamp ξ)
    (CanonicalFullKappaPrime.radiusFactor_pos _ _ _ _ _ _
      (zero_lt_one.trans s.base_gt_one))

theorem le_fullKappaAmplitude (amplitude : V → ℝ) (hamp : ∀ ξ, 0 ≤ amplitude ξ)
    (δ lengthBound degree height width : ℝ) (hδ : 0 ≤ δ) (hL : 0 ≤ lengthBound) (ξ : V) :
    amplitude ξ ≤ D.fullKappaAmplitude amplitude δ lengthBound degree height width ξ :=
  le_mul_of_one_le_right (hamp ξ)
    (CanonicalFullKappaPrime.one_le_radiusFactor _ _ _ _ _ _ s.base_gt_one.le hδ hL)

/-- Original profile windows and genuine single-character analytic
data fill the actual capacity atoms. The prime cost is exactly the
square of the enlarged amplitude, hence the normalized slot bound is
one. No completed child or pointwise prime estimate is an input. -/
def fullKappaCapacityAtoms
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ}
    (amplitude : V → ℝ) (hamp : ∀ ξ, 0 < amplitude ξ)
    (profiles : ∀ ξ, RawProfileWindow rowDomain heightDomain window
      (OriginalProfileAtomBounds.profileOrders CanonicalFullKappaPrime.orders)
      (D.data ξ) (amplitude ξ))
    (hwindow : window ⊆ Set.Ioo (1 : ℝ) 2)
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base, u ∈ rowDomain)
    (hheight : ∀ ξ, D.height ξ ∈ heightDomain)
    (δ lengthBound degree analyticHeight width : ℝ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
    (hlength : ∀ i, s.childLength i ≤ lengthBound)
    (hκlo : 3 / 4 ≤ D.parameters.κ) (hκhi : D.parameters.κ ≤ 1)
    (hbudget : Q.FullJointBudget s.base width)
    (raw : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows (D.data ξ) D.parameters s.base →
      ∀ i : Fin s.allocation.keep.card,
        OriginalPrimeAnalyticData ((D.data ξ).rowCharacter u *
          (D.data ξ).slotCoefficient
            (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i))
          ((D.parameters.κ + 1) / 2) degree)
    (hanalyticHeight : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters s.base,
      ∀ i : Fin s.allocation.keep.card,
        heightConstant (raw hκ ξ u hu i).slot.analytic +
          3 * ((raw hκ ξ u hu i).slot.analytic.k : ℝ) ≤ analyticHeight) :
    D.OriginalCapacityAtoms where
  leftAnnulus := 2
  rightAnnulus := 2
  leftAnnulus_one := by norm_num
  rightAnnulus_one := by norm_num
  left_window ξ u hu x hx :=
    (profiles ξ).original_left_profile_upper 2 (fun _ hx => (hwindow hx).2.le)
      u (hrows ξ u hu) (D.height ξ) (hheight ξ) x hx
  right_window ξ u hu x hx :=
    (profiles ξ).original_right_profile_upper 2 (fun _ hx => (hwindow hx).2.le)
      u (hrows ξ u hu) (D.height ξ) (hheight ξ) x hx
  primeBound ξ _ := (D.fullKappaAmplitude amplitude δ lengthBound degree analyticHeight width ξ) ^ 2
  primeBound_nonneg ξ _ := sq_nonneg _
  prime_bound ξ u hu i := by
    let j := lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i
    have hlen : ((D.data ξ).geometry.slots j).length = s.childLength i :=
      D.clipped_lengths ξ i
    have hprof : CanonicalFullKappaPrime.orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        ((profiles ξ).primeRep j (D.height ξ)) ≤ amplitude ξ := by
      apply Seminorm.finset_sup_apply_le (hamp ξ).le
      intro p hp
      exact (Seminorm.le_finset_sup_apply
        (Finset.mem_insert_of_mem hp)).trans ((profiles ξ).prime_bound j (D.height ξ) (hheight ξ))
    have hallowed : (D.data ξ).allowedRow u :=
      (((D.data ξ).rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
    have hb := CanonicalFullKappaPrime.raw_prime_bound_radius
      (D.data ξ) j u s.base (D.height ξ) D.parameters.κ δ lengthBound degree analyticHeight
      (CompleteMovingRowRecipe.primeMaskLogBound A s.base width) (amplitude ξ)
      s.base_gt_one.le hκlo hκhi hδ hδhi (hlen.trans_le (hlength i)) (hamp ξ).le
      ((profiles ξ).primeRep j (D.height ξ)) ((profiles ξ).prime_eq j (D.height ξ))
      (fun _ hx => hwindow ((profiles ξ).prime_support j (D.height ξ) (hheight ξ) hx))
      hprof (Q.primeDeletionIdeal u) (Q.deleted_prime_dvd ξ u)
      (Q.primeDeletionIdeal_log_le s.base width (zero_lt_one.trans s.base_gt_one)
        hbudget ξ u hallowed)
      (fun hκ => raw hκ ξ u hu i) (fun hκ => hanalyticHeight hκ ξ u hu i)
    simpa only [hlen, fullKappaAmplitude] using hb

end ActualAllocatedSource.Calibration

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.primePolynomial_eq_normalizedMaskedPrimeSum
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.deleted_count_le_log
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.raw_prime_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.raw_prime_bound_radius
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.exists_full_profile_radius_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalFullKappaPrime.exists_complete_profile_radius_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.deleted_prime_dvd
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.deleted_prime_count_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.fullKappaCapacityAtoms
