import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import HeckeGeneral.Analysis.HeckeSeries
import Mathlib.Topology.Order.Compact

/-!
# Fixed-character volume estimates and actual exceptional profile controls

The absolute estimate is unconditional and follows from the actual ideal
counting theorem. Its constant is independent of the Hecke character and
of the original profiles, their unit phases, the mask and the height.

The centered estimate has one explicit cross-task analytic boundary:
the original smoothed ideal sum for each character in a fixed finite
catalogue has a linear main term and a remainder bounded by a continuous
Schwartz seminorm. This is a statement about one original ideal sum,
before masks, rows, allocations or rectangles. The general-number-field
construction of that primitive is not supplied by MOM_BASE at its current
published revision. No final exceptional bound is used as an input here.

Finite supremum and continuity choose common original orders and a
constant before the original profiles. The genuine norm-power twist is
then constructed by `shapeSchwartz` with real exponent zero. Any real
power already present in the original profile remains inside its
displayed seminorm amplitude; it is not absorbed into a fixed constant.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.CenteredMomentCounting HeckePort.CenteredMomentVolume
open HeckePort.Moments HeckePort.Moments.Twist

variable {K : Type} [Field K] [NumberField K]

/-- The actual ideal monoid coefficient of the fixed original Hecke
character. Ramified primes retain their zero coefficient. -/
def coefficient (χ : HeckeCharacter K) : Ideal (𝓞 K) →* ℂ :=
  (idealCoefficientHom (primeCoefficient K χ)).toMonoidHom

theorem coefficient_norm (χ : HeckeCharacter K) (I : Ideal (𝓞 K)) :
    ‖coefficient χ I‖ ≤ 1 :=
  norm_idealCoefficient_le_one (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) I

@[simp] theorem coefficient_zero (χ : HeckeCharacter K) : coefficient χ ⊥ = 0 :=
  idealCoefficient_zero _

/-- Direct absolute counting needs no volume asymptotic or a supplied
Schwartz representative of the imaginary-power twist. -/
theorem twisted_sum_absolute
    (Ψ : Ideal (𝓞 K) → ℂ) (hΨ : ∀ I, ‖Ψ I‖ ≤ 1) (hΨ0 : Ψ ⊥ = 0)
    (R : Ideal (𝓞 K)) (W : ℝ → ℂ) (b P t X : ℝ)
    (hb : 0 ≤ b) (hP : 0 ≤ P) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ P) (hsupport : Function.support W ⊆ Set.Iic b) :
    ‖twistedMaskedSum Ψ R W t X‖ ≤ (idealCountConstant K * b * P) * X := by
  let f : Ideal (𝓞 K) → ℂ := fun I =>
    (if IsCoprime I R then (1 : ℂ) else 0) *
      (Ψ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
        W ((Ideal.absNorm I : ℝ) / X))
  have hzero : f ⊥ = 0 := by simp only [f, hΨ0, zero_mul, mul_zero]
  have hbound (I : Ideal (𝓞 K)) : ‖f I‖ ≤ P := by
    by_cases hI : I = ⊥
    · simpa only [hI, hzero, norm_zero] using hP
    · have hn : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
      have hnorm : 0 < (Ideal.absNorm I : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hphase : ‖(Ideal.absNorm I : ℂ) ^ (Complex.I * t)‖ = 1 := by
        simpa only [Complex.ofReal_natCast] using
          norm_cpow_imaginary (Ideal.absNorm I : ℝ) t hnorm
      have he : f I =
          ((if IsCoprime I R then (1 : ℂ) else 0) * Ψ I) *
            (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
              W ((Ideal.absNorm I : ℝ) / X) := by dsimp only [f]; ring
      rw [he, norm_mul, norm_mul, hphase, mul_one]
      exact (mul_le_mul (masked_coefficient_norm_le_one Ψ hΨ R I)
        (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul P)
  have hsupport' (I : Ideal (𝓞 K)) (hI : f I ≠ 0) :
      (Ideal.absNorm I : ℝ) ≤ b * X := by
    have hWne : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
      intro hz
      exact hI (by simp only [f, hz, mul_zero])
    exact (div_le_iff₀ hX).mp (hsupport hWne)
  have h := norm_tsum_ideal_ball f (b * X) P (mul_nonneg hb hX.le)
    hP hzero hbound hsupport'
  change ‖twistedMaskedSum Ψ R W t X‖ ≤ idealCountConstant K * P * (b * X) at h
  exact h.trans_eq (by ring)

/-- The two support endpoints are fixed before either amplitude. -/
def pairConstant (K : Type) [Field K] [NumberField K] (b₁ b₂ : ℝ) : ℝ :=
  (idealCountConstant K * b₁) * (idealCountConstant K * b₂)

theorem pairConstant_nonneg (b₁ b₂ : ℝ) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    0 ≤ pairConstant K b₁ b₂ := by
  have hcount := zero_le_one.trans (one_le_idealCountConstant K)
  exact mul_nonneg (mul_nonneg hcount hb₁) (mul_nonneg hcount hb₂)

/-- This is the original normalized product, with the two original
profile amplitudes still visible. No centered saving is claimed. -/
theorem normalized_product_absolute
    (χ : HeckeCharacter K) (R : Ideal (𝓞 K)) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ P₁ P₂ t X₁ X₂ Q : ℝ)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hp : X₁ * X₂ = Q)
    (hW₁ : ∀ y, ‖W₁ y‖ ≤ P₁) (hW₂ : ∀ y, ‖W₂ y‖ ≤ P₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖(Real.sqrt Q : ℂ)⁻¹ *
      (twistedMaskedSum (coefficient χ) R W₁ t X₁ *
        twistedMaskedSum (coefficient χ) R W₂ t X₂)‖ ≤
      (pairConstant K b₁ b₂ * (P₁ * P₂)) * Real.sqrt Q := by
  have h₁ := twisted_sum_absolute (coefficient χ) (coefficient_norm χ)
    (coefficient_zero χ) R W₁ b₁ P₁ t X₁ hb₁ hP₁ hX₁ hW₁ hs₁
  have h₂ := twisted_sum_absolute (coefficient χ) (coefficient_norm χ)
    (coefficient_zero χ) R W₂ b₂ P₂ t X₂ hb₂ hP₂ hX₂ hW₂ hs₂
  have hQ : 0 < Q := hp ▸ mul_pos hX₁ hX₂
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hd : Q / Real.sqrt Q = Real.sqrt Q := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith [Real.sq_sqrt hQ.le]
  have hcount := zero_le_one.trans (one_le_idealCountConstant K)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg Q), norm_mul]
  calc
    _ ≤ (Real.sqrt Q)⁻¹ *
        ((idealCountConstant K * b₁ * P₁ * X₁) *
          (idealCountConstant K * b₂ * P₂ * X₂)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h₁ h₂ (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hcount hb₁) hP₁) hX₁.le))
        (inv_nonneg.mpr hroot.le)
    _ = (pairConstant K b₁ b₂ * (P₁ * P₂)) * (Q / Real.sqrt Q) := by
      rw [← hp]
      unfold pairConstant
      ring
    _ = _ := by rw [hd]

/-- Unit phases on the actual original representatives cost nothing. -/
theorem phased_profile_norm_le (φ : 𝓢(ℝ, ℂ)) (c : ℂ) (hc : ‖c‖ = 1)
    (P : ℝ) (hP : SchwartzMap.seminorm ℂ 0 0 φ ≤ P) (y : ℝ) :
    ‖(c • φ) y‖ ≤ P := by
  simpa only [SchwartzMap.smul_apply, smul_eq_mul, norm_mul, hc, one_mul] using
    (SchwartzMap.norm_le_seminorm ℂ φ y).trans hP

/-- One positive interval contains the original fixed compact window,
including the empty-window case. -/
theorem exists_positive_interval (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ 1 ≤ b ∧ window ⊆ Set.Icc a b := by
  rcases window.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, zero_lt_one, le_rfl, Set.empty_subset _⟩
  · obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨b, hb⟩ := hcompact.bddAbove
    refine ⟨a, max 1 b, hpositive ha, le_max_left _ _, fun y hy => ?_⟩
    exact ⟨(isMinOn_iff.mp hmin) y hy, (hb hy).trans (le_max_right _ _)⟩

/-- The actual imaginary-power representative. The original real
power, if any, is already part of `φ`. -/
def twistedProfile (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  CanonicalLogProfiles.shapeSchwartz window hcompact hpositive 0 t φ hsupport

theorem twistedProfile_apply (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) (t y : ℝ) :
    twistedProfile window hcompact hpositive φ hsupport t y =
      (y : ℂ) ^ (Complex.I * t) * φ y := by
  rw [twistedProfile, CanonicalLogProfiles.shapeSchwartz_apply]
  by_cases hφ : φ y = 0
  · simp only [hφ, zero_mul, mul_zero]
  · have hy : 0 < y := hpositive (hsupport (subset_tsupport φ hφ))
    have hshape : CanonicalLogProfiles.normalShape 0 t y =
        (y : ℂ) ^ (Complex.I * t) := by
      rw [← profilePower_eq_cpow (Complex.I * (t : ℂ)) hy]
      change ((y ^ (0 : ℝ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ)) =
          Complex.exp ((Real.log y : ℂ) * (Complex.I * (t : ℂ)))
      simp only [Real.rpow_zero, Complex.ofReal_one, one_mul]
      congr 1
      ring
    rw [hshape, mul_comm]

section Primitive

variable {ι : Type*} [Fintype ι]
variable (χ : ι → HeckeCharacter K)
variable (density : ι → 𝓢(ℝ, ℂ) → ℂ)
variable (remainder : ι → Seminorm ℂ (𝓢(ℝ, ℂ)))

/-- The sole primitive estimate is the original single-character ideal
series. This definition only records that exact estimate. -/
def originalVolume
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 K), coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (i : ι) : IdealVolumeInput K (coefficient (χ i)) where
  density := density i
  error := remainder i
  error_nonneg φ := apply_nonneg (remainder i) φ
  volume := hvolume i

/-- Continuity and the finite fixed catalogue select all original
orders and the height degree before either original profile. -/
theorem exists_uniform_error_control
    (hcontinuous : ∀ i, Continuous (remainder i))
    (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
      ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (i : ι) (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) (t : ℝ),
        remainder i (twistedProfile window hcompact hpositive φ hsupport t) ≤
          C * orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ * (1 + ‖t‖) ^ n := by
  let p : Seminorm ℂ (𝓢(ℝ, ℂ)) := Finset.univ.sup remainder
  have hp : Continuous p := Seminorm.continuous_finsetSup (fun i _ => hcontinuous i)
  obtain ⟨s, D, hD, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) p hp
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hD
  obtain ⟨C₀, hC₀, hshape⟩ :=
    CanonicalLogProfiles.shapeSchwartz_finset_bound window hcompact hpositive 0 s
  let orders := insert (0, 0) (CanonicalLogProfiles.sourceOrders s)
  let C : ℝ := (D : ℝ) * (1 + C₀)
  have hC : 0 < C := mul_pos hDpos (by linarith)
  refine ⟨orders, Finset.mem_insert_self _ _, s.sup Prod.snd, C, hC,
    fun i φ hs t => ?_⟩
  have horders :
      (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply (Finset.mem_insert_of_mem hj)
  have hpi : remainder i ≤ p := Finset.le_sup (f := remainder) (Finset.mem_univ i)
  have hsemi := Seminorm.le_def.mp hbound
    (twistedProfile window hcompact hpositive φ hs t)
  have hcoeff : (D : ℝ) * C₀ ≤ C := by
    dsimp only [C]
    nlinarith [hDpos.le]
  have hP : 0 ≤ orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := apply_nonneg _ _
  calc
    _ ≤ p (twistedProfile window hcompact hpositive φ hs t) :=
      Seminorm.le_def.mp hpi _
    _ ≤ (D : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (twistedProfile window hcompact hpositive φ hs t) := hsemi
    _ ≤ (D : ℝ) *
        (C₀ * (1 + |t|) ^ (s.sup Prod.snd) *
          (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ) :=
      mul_le_mul_of_nonneg_left (hshape t φ hs) hDpos.le
    _ ≤ (D : ℝ) *
        (C₀ * (1 + |t|) ^ (s.sup Prod.snd) *
          orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left horders
          (mul_nonneg hC₀ (pow_nonneg (by positivity) _))) hDpos.le
    _ = ((D : ℝ) * C₀) *
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ * (1 + ‖t‖) ^ (s.sup Prod.snd) := by
      rw [Real.norm_eq_abs]
      ring
    _ ≤ C * orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ *
        (1 + ‖t‖) ^ (s.sup Prod.snd) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hP)
        (pow_nonneg (by positivity) _)

/-- Construct the actual control for every original pair from the raw
fixed-character primitive. All coefficients and orders precede `φ₁`,
`φ₂`, their seminorm amplitude and the moving height. -/
theorem exists_uniform_volume_controls
    (hcontinuous : ∀ i, Continuous (remainder i))
    (hvolume : ∀ i (φ : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
      ‖(∑' I : Ideal (𝓞 K), coefficient (χ i) I *
          φ ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density i φ‖ ≤ remainder i φ)
    (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    ∃ orders : Finset (ℕ × ℕ), (0, 0) ∈ orders ∧
      ∃ n : ℕ, ∃ C a b : ℝ, 0 < C ∧ 0 < a ∧ 1 ≤ b ∧
      ∀ (i : ι) (φ₁ φ₂ : 𝓢(ℝ, ℂ)),
        tsupport φ₁ ⊆ window → tsupport φ₂ ⊆ window →
        ∀ P : ℝ, 0 ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₁ ≤ P →
        orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ₂ ≤ P →
        ∃ H : ExceptionalVolumeControl (coefficient (χ i)) φ₁ φ₂,
          H.lower₁ = a ∧ H.lower₂ = a ∧ H.upper₁ = b ∧ H.upper₂ = b ∧
          H.bound₁ = P ∧ H.bound₂ = P ∧ H.order₁ = n ∧ H.order₂ = n ∧
          H.error₁ = C * P ∧ H.error₂ = C * P := by
  obtain ⟨orders, hzero, n, C, hC, herror⟩ :=
    exists_uniform_error_control remainder hcontinuous window hcompact hpositive
  obtain ⟨a, b, ha, hb, hwindow⟩ := exists_positive_interval window hcompact hpositive
  refine ⟨orders, hzero, n, C, a, b, hC, ha, hb,
    fun i φ₁ φ₂ hs₁ hs₂ P hP hP₁ hP₂ => ?_⟩
  let V := originalVolume χ density remainder hvolume i
  have hnorm (φ : 𝓢(ℝ, ℂ))
      (hφ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ P) (y : ℝ) : ‖φ y‖ ≤ P :=
    (SchwartzMap.norm_le_seminorm ℂ φ y).trans
      ((Seminorm.le_finset_sup_apply hzero).trans hφ)
  have herr (φ : 𝓢(ℝ, ℂ)) (hs : tsupport φ ⊆ window)
      (hφ : orders.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ P) (t : ℝ) :
      V.error (twistedProfile window hcompact hpositive φ hs t) ≤
        (C * P) * (1 + ‖t‖) ^ n :=
    (herror i φ hs t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hφ hC.le) (pow_nonneg (by positivity) _))
  refine ⟨{
    coefficient_norm := coefficient_norm (χ i)
    coefficient_zero := coefficient_zero (χ i)
    volume := V
    lower₁ := a
    upper₁ := b
    lower₂ := a
    upper₂ := b
    bound₁ := P
    bound₂ := P
    lower₁_pos := ha
    lower₂_pos := ha
    upper₁_nonneg := zero_le_one.trans hb
    upper₂_nonneg := zero_le_one.trans hb
    bound₁_nonneg := hP
    bound₂_nonneg := hP
    support₁ := fun y hy => hwindow (hs₁ (subset_tsupport φ₁ hy))
    support₂ := fun y hy => hwindow (hs₂ (subset_tsupport φ₂ hy))
    profile₁ := twistedProfile window hcompact hpositive φ₁ hs₁
    profile₂ := twistedProfile window hcompact hpositive φ₂ hs₂
    profile₁_eq := twistedProfile_apply window hcompact hpositive φ₁ hs₁
    profile₂_eq := twistedProfile_apply window hcompact hpositive φ₂ hs₂
    norm₁ := hnorm φ₁ hP₁
    norm₂ := hnorm φ₂ hP₂
    order₁ := n
    order₂ := n
    error₁ := C * P
    error₂ := C * P
    error₁_nonneg := mul_nonneg hC.le hP
    error₂_nonneg := mul_nonneg hC.le hP
    error₁_bound := herr φ₁ hs₁ hP₁
    error₂_bound := herr φ₂ hs₂ hP₂
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Primitive

end HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.twisted_sum_absolute
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.normalized_product_absolute
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.exists_uniform_error_control
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalExceptionalVolume.exists_uniform_volume_controls
