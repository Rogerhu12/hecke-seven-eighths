import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SixthPowerDivisorIdentity
import HeckeGeneral.Analysis.ExteriorIdealCounting
import HeckeGeneral.Analysis.IndependentAmplifierOptimization

/-!
# Amplification over complete ideal rows

The arithmetic amplifier acts on the actual ideal indices.  Prime
valuations modulo six recover the base row and the multiplier, so summing
over all base rows costs no extra row-count factor.  The analytic seed in
the last theorem is confined to the strict short-scale region and controls
one common majorant for every divisor scale of the same pulled-back profile.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- A unitary Euler coefficient remains bounded by one after any integer
power.  The ramified value is exactly zero, including under inversion. -/
theorem norm_heckeIdealCoefficient_zpow_le_one
    (χ : HeckeCharacter K) (I : NonzeroIdeal K) (e : ℤ) :
    ‖heckeIdealCoefficient K χ I ^ e‖ ≤ 1 := by
  have hprime (p : HeightOneSpectrum (𝓞 K)) : ‖primeCoefficient K χ p ^ e‖ ≤ 1 := by
    unfold primeCoefficient
    split_ifs
    · simp only [norm_zpow, Circle.norm_coe, one_zpow, le_refl]
    · by_cases he : e = 0 <;> simp [he, zero_zpow]
  have hvalue (J : Ideal (𝓞 K)) :
      ‖primeIdealValue (primeCoefficient K χ) J ^ e‖ ≤ 1 := by
    unfold primeIdealValue
    split_ifs
    · exact hprime _
    · simp
  have hprod (F : Multiset (Ideal (𝓞 K))) :
      ‖(F.map (primeIdealValue (primeCoefficient K χ))).prod ^ e‖ ≤ 1 := by
    induction F using Multiset.induction with
    | empty => simp
    | cons J F ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_zpow, norm_mul]
      exact (mul_le_mul (hvalue J) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hI : I.val ≠ (⊥ : Ideal (𝓞 K)) := by
    simpa only [Ideal.zero_eq_bot] using nonZeroDivisors.coe_ne_zero I
  simpa only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient,
    if_neg hI] using hprod (normalizedFactors I.val)

theorem norm_inverseRowCoefficient_le_one (d : MomentData K ω ψ)
    (u I : NonzeroIdeal K) : ‖inverseRowCoefficient d u I‖ ≤ 1 := by
  have hm : ‖maskValue d u I.val‖ ≤ 1 := by
    unfold maskValue
    split_ifs <;> norm_num
  have hμ := IdealMobiusReciprocal.norm_moebius_le_one K I
  have hη := norm_heckeIdealCoefficient_le_one K d.inverseBackground I
  have hχ := norm_heckeIdealCoefficient_zpow_le_one (d.rowCharacter u) I d.direction
  simp only [inverseRowCoefficient, norm_mul]
  exact (mul_le_mul
    ((mul_le_mul ((mul_le_mul hμ hη (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)) hχ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    hm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def inverseDivisorCoefficient (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (A : Finset (HeightOneSpectrum (𝓞 K))) : ℂ :=
  inverseRowCoefficient d u (squarefreeIdeal K A) *
    (Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹

theorem norm_inverseDivisorCoefficient_le_one (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (A : Finset (HeightOneSpectrum (𝓞 K))) :
    ‖inverseDivisorCoefficient d u A‖ ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt (idealNorm K (squarefreeIdeal K A)) :=
    Real.one_le_sqrt.mpr (one_le_idealNorm K _)
  have hinv : ‖(Real.sqrt (idealNorm K (squarefreeIdeal K A)) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ hsqrt
  rw [inverseDivisorCoefficient, norm_mul]
  exact (mul_le_mul (norm_inverseRowCoefficient_le_one d u _) hinv
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The constant is independent of the profile, every character, the row,
and the particular amplifier.  All its divisor coefficients retain their
actual row and fixed-place zeros. -/
theorem inverseDivisorCoefficient_mass_small_power {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : MomentData K ω ψ) (u a : NonzeroIdeal K),
      (∑ A ∈ (idealPrimeSupport K a).powerset, ‖inverseDivisorCoefficient d u A‖) ≤
        C * idealNorm K a ^ δ := by
  obtain ⟨C, hC, hbound⟩ := exists_two_pow_card_le_idealNorm_rpow K hδ
  refine ⟨C, hC, ?_⟩
  intro d u a
  calc
    _ ≤ ∑ _A ∈ (idealPrimeSupport K a).powerset, (1 : ℝ) :=
      Finset.sum_le_sum fun A _ => norm_inverseDivisorCoefficient_le_one d u A
    _ = (2 : ℝ) ^ (idealPrimeSupport K a).card := by simp
    _ ≤ C * idealNorm K (squarefreeIdeal K (idealPrimeSupport K a)) ^ δ :=
      hbound (idealPrimeSupport K a)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (idealNorm_pos K _).le
        (idealNorm_squarefreeIdeal_le_of_primeSupport_subset K a _ (Finset.Subset.refl _))
        hδ.le) hC.le

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem ideal_sixth_descendant_norm_le (u : NonzeroIdeal K) (a : ExteriorIdeal K S)
    {U P : ℝ} (hu : idealNorm K u ≤ U) (ha : idealNorm K a.val ≤ P) :
    idealNorm K (u * a.val ^ 6) ≤ U * P ^ 6 := by
  have hn : idealNorm K (u * a.val ^ 6) = idealNorm K u * idealNorm K a.val ^ 6 := by
    change (Ideal.absNorm (u.val * a.val.val ^ 6) : ℝ) =
      (Ideal.absNorm u.val : ℝ) * (Ideal.absNorm a.val.val : ℝ) ^ 6
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  rw [hn]
  exact mul_le_mul hu (pow_le_pow_left₀ (idealNorm_pos K _).le ha 6)
    (pow_nonneg (idealNorm_pos K _).le _) ((idealNorm_pos K _).le.trans hu)

/-- The pair of a sixth-free complete ideal and its multiplier embeds in
the complete-row sum.  Unit sectors stay outside this map and are summed
only once by the source-level adapter. -/
theorem sum_sixth_descendant_majorants_le
    (d : MomentData K ω ψ) (hrows : d.allowedRow = completeIdealIsExterior K S)
    (R : Finset (NonzeroIdeal K)) (F : Finset (ExteriorIdeal K S))
    {U P H : ℝ}
    (hR : ∀ u ∈ R, d.allowedRow u ∧ SixthPowerFreeIdeal u ∧ idealNorm K u ≤ U)
    (hF : ∀ a ∈ F, idealNorm K a.val ≤ P) (hH : U * P ^ 6 ≤ H)
    (B : NonzeroIdeal K → ℝ) (hB : ∀ u, 0 ≤ B u) :
    (∑ u ∈ R, ∑ a ∈ F, B (u * a.val ^ 6)) ≤ ∑ v ∈ d.rows H, B v := by
  let f : NonzeroIdeal K × ExteriorIdeal K S → NonzeroIdeal K :=
    fun x => x.1 * x.2.val ^ 6
  have hinj : Set.InjOn f (R.product F) := by
    intro x hx y hy hxy
    obtain ⟨hxR, _⟩ := Finset.mem_product.mp hx
    obtain ⟨hyR, _⟩ := Finset.mem_product.mp hy
    have h := sixthPowerFree_mul_sixth_unique (hR x.1 hxR).2.1
      (hR y.1 hyR).2.1 hxy
    exact Prod.ext h.1 (Subtype.ext h.2)
  have himage : (R.product F).image f ⊆ d.rows H := by
    intro v hv
    obtain ⟨⟨u, a⟩, hmem, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu, ha⟩ := Finset.mem_product.mp hmem
    apply (d.rows_spec H _).mpr
    constructor
    · rw [hrows]
      exact completeIdealIsExterior_mul_sixth S u a (by simpa only [← hrows] using (hR u hu).1)
    · exact (ideal_sixth_descendant_norm_le S u a (hR u hu).2.2 (hF a ha)).trans hH
  rw [← Finset.sum_product R F (fun x => B (f x))]
  exact Finset.sum_le_sum_of_injOn f hinj himage (fun _ _ => le_rfl)
    (fun v _ _ => hB v)

/-- Average the exact divisor identity over all actual allowed ideal
multipliers and then inject the pair index into complete ideal rows. -/
theorem completeIdeal_amplification_to_majorant {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : MomentData K ω ψ),
      d.allowedRow = completeIdealIsExterior K S →
      d.commonMask = completeIdealCommonMask K S →
      (∀ u (a : ExteriorIdeal K S), d.allowedRow u →
        d.rowCharacter (u * a.val ^ 6) = d.rowCharacter u) →
      ∀ (R : Finset (NonzeroIdeal K)) (F : Finset (ExteriorIdeal K S))
        (U P H D : ℝ) (B : NonzeroIdeal K → ℝ),
        1 ≤ P → U * P ^ 6 ≤ H → 0 < D →
        (∀ u ∈ R, d.allowedRow u ∧ SixthPowerFreeIdeal u ∧ idealNorm K u ≤ U) →
        (∀ a ∈ F, idealNorm K a.val ≤ P) →
        (∀ u, 0 ≤ B u) →
        (∀ v ∈ d.rows H, ∀ r : ℝ, 0 < r → r ≤ D →
          ‖inversePolynomial (sixthRootInverseData d) v r 0‖ ^ 2 ≤ B v) →
        (F.card : ℝ) * ∑ u ∈ R, ‖inversePolynomial d u D 0‖ ^ 2 ≤
          C * P ^ (2 * δ) * ∑ v ∈ d.rows H, B v := by
  obtain ⟨C, hC, hmass⟩ := inverseDivisorCoefficient_mass_small_power (K := K)
    (ω := ω) (ψ := ψ) hδ
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro d hrows hmask hchar R F U P H D B hP hPH hD hR hF hB hrow
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have heach (u : NonzeroIdeal K) (hu : u ∈ R)
      (a : ExteriorIdeal K S) (ha : a ∈ F) :
      ‖inversePolynomial d u D 0‖ ^ 2 ≤ (C * P ^ δ) ^ 2 * B (u * a.val ^ 6) := by
    rw [← inversePolynomial_sixthRoot_eq d (hR u hu).2.1 D 0,
      inversePolynomial_sixth_power_divisor_identity (sixthRootInverseData d) hmask u a
        (hchar u a (hR u hu).1) (sixthRootInverseData_profile_sixth d u a.val) hD 0]
    apply norm_sum_mul_sq_le_mass_sq
      (idealPrimeSupport K a.val).powerset (inverseDivisorCoefficient (sixthRootInverseData d) u)
      (fun A => inversePolynomial (sixthRootInverseData d) (u * a.val ^ 6)
        (D / idealNorm K (squarefreeIdeal K A)) 0) (hB _)
    · exact (hmass (sixthRootInverseData d) u a.val).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (idealNorm_pos K _).le (hF a ha) hδ.le) hC.le)
    · intro A _hA
      apply hrow (u * a.val ^ 6)
      · apply (d.rows_spec H _).mpr
        constructor
        · rw [hrows]
          exact completeIdealIsExterior_mul_sixth S u a (by
            simpa only [← hrows] using (hR u hu).1)
        · exact (ideal_sixth_descendant_norm_le S u a (hR u hu).2.2 (hF a ha)).trans hPH
      · exact div_pos hD (idealNorm_pos K _)
      · exact div_le_self hD.le (one_le_idealNorm K _)
  have hsum := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (heach u hu))
  have hsum' : (F.card : ℝ) * ∑ u ∈ R, ‖inversePolynomial d u D 0‖ ^ 2 ≤
      (C * P ^ δ) ^ 2 * ∑ u ∈ R, ∑ a ∈ F, B (u * a.val ^ 6) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] using hsum
  have hpow : (C * P ^ δ) ^ 2 = C ^ 2 * P ^ (2 * δ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hP0 δ 2]
    norm_num only [Nat.cast_ofNat]
    rw [show δ * (2 : ℝ) = 2 * δ by ring]
  calc
    _ ≤ (C * P ^ δ) ^ 2 * ∑ u ∈ R, ∑ a ∈ F, B (u * a.val ^ 6) := hsum'
    _ ≤ (C * P ^ δ) ^ 2 * ∑ v ∈ d.rows H, B v :=
      mul_le_mul_of_nonneg_left
        (sum_sixth_descendant_majorants_le S d hrows R F hR hF hPH B hB) (sq_nonneg _)
    _ = _ := by rw [hpow]

variable (S)

/-- Optimize the actual ideal amplifier with uniform polynomial height
control.  The seed is used only at complete row scale H and at strictly
shorter polynomial scales.  All constants precede the original U,D and
the entire source-family index. -/
theorem completeIdeal_independent_energy {ι : Type*}
    (family : ι → MomentData K ω ψ) (height : ι → ℝ)
    (hheight0 : ∀ i, 0 ≤ height i)
    (hrows : ∀ i, (family i).allowedRow = completeIdealIsExterior K S)
    (hmask : ∀ i, (family i).commonMask = completeIdealCommonMask K S)
    (hchar : ∀ i u (a : ExteriorIdeal K S), (family i).allowedRow u →
      (family i).rowCharacter (u * a.val ^ 6) = (family i).rowCharacter u)
    (hMI : CompleteIdealScaleSupSeed family height)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ C A h : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧
      ∀ i U D, 1 ≤ U → 1 ≤ D → height i ≤ (U * D) ^ h →
        ∀ R : Finset (NonzeroIdeal K),
          (∀ u ∈ R, (family i).allowedRow u ∧ SixthPowerFreeIdeal u ∧ idealNorm K u ≤ U) →
          (∑ u ∈ R, ‖inversePolynomial (family i) u D 0‖ ^ 2) ≤
            C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) *
              (U * D) ^ ε * (1 + height i) ^ A := by
  have hc1 : 0 < 1 + c := by linarith
  let a : ℝ := ε / (2 * (1 + c))
  let e : ℝ := ε / (6 * (1 + c))
  let gap : ℝ := c / (1 + c)
  let L : ℝ := 5 + 2 * a + 6 * e
  have ha : 0 < a := div_pos hε (by positivity)
  have he : 0 < e := div_pos hε (by positivity)
  have hgap : 0 < gap := div_pos hc hc1
  have hgap1 : gap < 1 := by
    dsimp [gap]
    exact (div_lt_one hc1).mpr (by linarith)
  have hcg : (1 + c) * (1 - gap) = 1 := by
    dsimp [gap]
    field_simp [ne_of_gt hc1]
    ring
  have heε : e ≤ ε := div_le_self hε.le (by linarith : 1 ≤ 6 * (1 + c))
  have hUL : 1 + e - L / 6 ≤ 1 / 6 := by dsimp [L]; linarith
  have hDL : (1 + c) * (L / 6) ≤ 5 * (1 + c) / 6 + ε := by
    have heq : (1 + c) * (L / 6) = 5 * (1 + c) / 6 + ε / 3 := by
      dsimp [L, a, e]
      field_simp [ne_of_gt hc1]
      ring
    rw [heq]
    linarith
  obtain ⟨Cₘ, hCₘ, hamp⟩ := completeIdeal_amplification_to_majorant (K := K)
    (ω := ω) (ψ := ψ) S ha
  obtain ⟨k, P₀, hk, _hP₀, hcount⟩ := exists_exteriorAmplifierIdeals_linear_lower K S
  obtain ⟨Cᵢ, A, h, H₀, hCᵢ, hA, hh, _hH₀, hmajorant⟩ := hMI gap e hgap hgap1 he
  let A₀ : ℝ := max 1 (max P₀ H₀)
  have hA₀ : 1 ≤ A₀ := le_max_left _ _
  have hAP : P₀ ≤ A₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hAH : H₀ ≤ A₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hApos : 0 < A₀ := lt_of_lt_of_le zero_lt_one hA₀
  let C : ℝ := (Cₘ * Cᵢ / k) * A₀ ^ L
  have hC : 0 < C := mul_pos (div_pos (mul_pos hCₘ hCᵢ) hk)
    (Real.rpow_pos_of_pos hApos L)
  refine ⟨C, A, h / 2, hC, hA, by positivity, ?_⟩
  intro i U D hU hD hheight R hR
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let P := independentAmplifierSize A₀ U D c
  have hPA : A₀ ≤ P := independentAmplifierSize_ge hApos.le
  have hP : 1 ≤ P := hA₀.trans hPA
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hH : H₀ ≤ U * P ^ 6 := by
    have hP6 : P ≤ P ^ 6 := le_self_pow₀ hP (by decide)
    have hPU : P ^ 6 ≤ U * P ^ 6 := by nlinarith [pow_nonneg hPpos.le 6]
    exact hAH.trans (hPA.trans (hP6.trans hPU))
  have hscale : D ≤ (U * P ^ 6) ^ (1 - gap) :=
    independentAmplifierSize_scale hA₀ hU hDpos hgap1 hcg
  have hUH : U ≤ U * P ^ 6 := by
    have hp6 : 1 ≤ P ^ 6 := one_le_pow₀ hP
    nlinarith
  have hH1 : 1 ≤ U * P ^ 6 := hU.trans hUH
  have hH0 : 0 ≤ U * P ^ 6 := zero_le_one.trans hH1
  have hDH : D ≤ U * P ^ 6 := hscale.trans (by
    calc
      (U * P ^ 6) ^ (1 - gap) ≤ (U * P ^ 6) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
      _ = _ := Real.rpow_one _)
  have hproduct : U * D ≤ (U * P ^ 6) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hUH hDH hDpos.le hH0
  have hheightH : height i ≤ (U * P ^ 6) ^ h := by
    calc
      height i ≤ (U * D) ^ (h / 2) := hheight
      _ ≤ ((U * P ^ 6) ^ 2) ^ (h / 2) :=
        Real.rpow_le_rpow (mul_nonneg hUpos.le hDpos.le) hproduct (by positivity)
      _ = (U * P ^ 6) ^ h := by
        rw [← Real.rpow_natCast_mul hH0 2 (h / 2)]
        congr 1
        ring
  obtain ⟨B, hB, hrow, hsum⟩ := hmajorant i (U * P ^ 6) hH hheightH
  let F := exteriorAmplifierIdeals K S P
  have hF : ∀ a ∈ F, idealNorm K a.val ≤ P :=
    norm_le_of_mem_exteriorAmplifierIdeals K S hPpos.le
  have hcard : k * P ≤ (F.card : ℝ) := hcount P (hAP.trans hPA)
  have hmain := hamp (family i) (hrows i) (hmask i) (hchar i)
    R F U P (U * P ^ 6) D B hP le_rfl hDpos hR hF hB
    (fun v hv r hr hrD => hrow v hv r hr (hrD.trans hscale))
  have hsum0 : 0 ≤ ∑ u ∈ R, ‖inversePolynomial (family i) u D 0‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcombined : k * P * (∑ u ∈ R, ‖inversePolynomial (family i) u D 0‖ ^ 2) ≤
      Cₘ * P ^ (2 * a) * (Cᵢ * (U * P ^ 6) ^ (1 + e) * (1 + height i) ^ A) :=
    (mul_le_mul_of_nonneg_right hcard hsum0).trans
      (hmain.trans (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hCₘ.le (Real.rpow_nonneg hPpos.le _))))
  have hnormalize :
      Cₘ * P ^ (2 * a) * (Cᵢ * (U * P ^ 6) ^ (1 + e) * (1 + height i) ^ A) =
      (k * P) * (((Cₘ * Cᵢ / k) * (U ^ (1 + e) * P ^ L)) * (1 + height i) ^ A) := by
    rw [Real.mul_rpow hUpos.le (pow_nonneg hPpos.le 6),
      ← Real.rpow_natCast_mul hPpos.le 6 (1 + e)]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (Cₘ * Cᵢ) * U ^ (1 + e) * (P ^ (2 * a) * P ^ (6 * (1 + e))) *
          (1 + height i) ^ A := by ring
      _ = (Cₘ * Cᵢ) * U ^ (1 + e) * P ^ (L + 1) * (1 + height i) ^ A := by
        rw [← Real.rpow_add hPpos,
          show 2 * a + 6 * (1 + e) = L + 1 by dsimp [L]; ring]
      _ = _ := by
        rw [Real.rpow_add hPpos, Real.rpow_one]
        field_simp [ne_of_gt hk]
  have hnormalized := (mul_le_mul_iff_right₀ (mul_pos hk hPpos)).mp
    (hcombined.trans_eq hnormalize)
  have hheightfactor : 0 ≤ (1 + height i) ^ A :=
    Real.rpow_nonneg (by linarith [hheight0 i]) _
  calc
    _ ≤ ((Cₘ * Cᵢ / k) * (U ^ (1 + e) * P ^ L)) * (1 + height i) ^ A := hnormalized
    _ ≤ ((Cₘ * Cᵢ / k) *
        (A₀ ^ L * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) * (U * D) ^ ε)) *
          (1 + height i) ^ A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (independentAmplifierSize_energy hApos hU hD heε hε.le hUL hDL)
          (div_pos (mul_pos hCₘ hCᵢ) hk).le) hheightfactor
    _ = _ := by dsimp [C]; ring

end HeckeSkeleton.Moments.UniformAmplify
