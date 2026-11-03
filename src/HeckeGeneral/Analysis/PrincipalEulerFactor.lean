import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.IdealEulerProduct
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The principal Euler factor, from its literal local formula

At the principal residue `u = 1, w = 1, z = 1/6`, write `Q` for the norm of an
exterior prime and
`v = Q⁻¹`, `D = ψ(p) Q^{-s}`, `E = ϑ(p)^6 Q^{3-6s}` with `ϑ = thetaPeriod`.
The literal local sum `localProbeEulerSum` gives the closed form

  `H_p = (1 - v²) (1 - vE - (1 - v)D) / ((1 - E)(1 - D))`.

For `Re s > 1/2` one has `|D|, |E| < 1`, so the convex combination
`vE + (1 - v)D` has modulus `< 1` and every factor is nonzero.  Moreover
`H_p - 1 ≪ Q^{-2} + Q^{-1-σ} + Q^{3-6σ}`, which is summable for `σ > 2/3`.
Hence the actual `principalCorrection` is analytic and zero-free on
`Re s > 2/3` and bounded on every closed right half-plane inside it.

No enlargement of the excluded set and no contraction `|H - 1| ≤ 1/2` is
used.  The compensation factor also has the closed form
`G_p + H_p = (1-v)²(1+v)(E - vDE - (1-v)D²) / (D(1-D)(1-E))`.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped BigOperators ComplexConjugate Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- `v = Q⁻¹` at an exterior prime. -/
def principalLocalV (p : ExteriorPrime K S) : ℂ := ((p.val.asIdeal.absNorm : ℂ))⁻¹

/-- `D = ψ(p) Q^{-s}`. -/
def principalLocalD (ψ : HeckeCharacter K) (p : ExteriorPrime K S) (s : ℂ) : ℂ :=
  primeCoefficient K ψ p.val * (p.val.asIdeal.absNorm : ℂ) ^ (-s)

/-- `E = ϑ(p)^6 Q^{3-6s}` for the theta-period character `ϑ`. -/
def principalLocalE (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
    (s : ℂ) : ℂ :=
  primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 * (p.val.asIdeal.absNorm : ℂ) ^ (3 - 6 * s)

/-! ### Elementary local facts -/

/-- The trivial character has prime coefficient `1` at every prime. -/
private theorem primeCoefficient_one_eq (v : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K 1 v = 1 := by
  rw [primeCoefficient_of_unramified K 1 v (unramifiedAt_one K v)]
  rfl

/-- An unramified coefficient lies on the unit circle. -/
private theorem norm_primeCoefficient_eq_one (ψ : HeckeCharacter K)
    (v : HeightOneSpectrum (𝓞 K)) (hψ : UnramifiedAt K ψ v) :
    ‖primeCoefficient K ψ v‖ = 1 := by
  rw [primeCoefficient_of_unramified K ψ v hψ]
  exact Circle.norm_coe _

omit [Fintype S] in
private theorem absNorm_pos' (p : ExteriorPrime K S) : 0 < p.val.asIdeal.absNorm :=
  lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)

omit [Fintype S] in
private theorem two_le_absNorm (p : ExteriorPrime K S) :
    (2 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ) := by
  have h : 2 ≤ p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
  exact_mod_cast h

omit [Fintype S] in
private theorem absNorm_complex_ne_zero (p : ExteriorPrime K S) :
    ((p.val.asIdeal.absNorm : ℂ)) ≠ 0 := by
  exact_mod_cast (absNorm_pos' K S p).ne'

omit [Fintype S] in
private theorem inv_absNorm_pos (p : ExteriorPrime K S) :
    0 < ((p.val.asIdeal.absNorm : ℝ))⁻¹ :=
  inv_pos.mpr (by linarith [two_le_absNorm K S p])

omit [Fintype S] in
private theorem inv_absNorm_le_half (p : ExteriorPrime K S) :
    ((p.val.asIdeal.absNorm : ℝ))⁻¹ ≤ 1 / 2 := by
  have h2 := two_le_absNorm K S p
  have h : ((p.val.asIdeal.absNorm : ℝ))⁻¹ * (p.val.asIdeal.absNorm : ℝ) = 1 :=
    inv_mul_cancel₀ (by linarith)
  nlinarith [inv_absNorm_pos K S p]

omit [Fintype S] in
private theorem principalLocalV_eq_ofReal (p : ExteriorPrime K S) :
    principalLocalV K S p = ((((p.val.asIdeal.absNorm : ℝ))⁻¹ : ℝ) : ℂ) := by
  simp [principalLocalV]

omit [Fintype S] in
private theorem norm_principalLocalV (p : ExteriorPrime K S) :
    ‖principalLocalV K S p‖ = ((p.val.asIdeal.absNorm : ℝ))⁻¹ := by
  rw [principalLocalV_eq_ofReal, Complex.norm_of_nonneg (inv_absNorm_pos K S p).le]

omit [Fintype S] in
private theorem norm_one_sub_principalLocalV (p : ExteriorPrime K S) :
    ‖1 - principalLocalV K S p‖ = 1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹ := by
  have h : (1 : ℂ) - principalLocalV K S p =
      ((1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹ : ℝ) : ℂ) := by
    simp [principalLocalV]
  have h0 : (0 : ℝ) ≤ 1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹ := by
    linarith [inv_absNorm_le_half K S p]
  rw [h, Complex.norm_of_nonneg h0]

omit [Fintype S] in
private theorem norm_one_sub_principalLocalV_sq_le (p : ExteriorPrime K S) :
    ‖1 - principalLocalV K S p ^ 2‖ ≤ 1 := by
  have hx0 := inv_absNorm_pos K S p
  have hx1 := inv_absNorm_le_half K S p
  have h : (1 : ℂ) - principalLocalV K S p ^ 2 =
      ((1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    simp [principalLocalV]
  have h0 : (0 : ℝ) ≤ 1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹ ^ 2 := by nlinarith
  rw [h, Complex.norm_of_nonneg h0]
  nlinarith

private theorem one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have hz1 : z = 1 := (sub_eq_zero.mp h).symm
  rw [hz1, norm_one] at hz
  exact lt_irrefl _ hz

omit [Fintype S] in
private theorem norm_principalLocalV_lt_one (p : ExteriorPrime K S) :
    ‖principalLocalV K S p‖ < 1 := by
  rw [norm_principalLocalV]
  linarith [inv_absNorm_le_half K S p]

omit [Fintype S] in
private theorem norm_principalLocalD_le (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
    (s : ℂ) : ‖principalLocalD K S ψ p s‖ ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) := by
  unfold principalLocalD
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (absNorm_pos' K S p), Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (norm_primeCoefficient_le_one K ψ p.val)

omit [Fintype S] in
private theorem norm_principalLocalD_eq (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
    (hψ : UnramifiedAt K ψ p.val) (s : ℂ) :
    ‖principalLocalD K S ψ p s‖ = ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) := by
  unfold principalLocalD
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (absNorm_pos' K S p), Complex.neg_re,
    norm_primeCoefficient_eq_one K ψ p.val hψ, one_mul]

private theorem norm_principalLocalE_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) :
    ‖principalLocalE K S P ψ p s‖ ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re) := by
  unfold principalLocalE
  have hre : (3 - 6 * s).re = 3 - 6 * s.re := by simp
  rw [norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos (absNorm_pos' K S p), hre]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K _ p.val))

omit [Fintype S] in
/-- `Q^a ≤ 2^b` for `a ≤ b ≤ 0`, since `Q ≥ 2`. -/
private theorem absNorm_rpow_le_two_rpow (p : ExteriorPrime K S) {a b : ℝ} (hab : a ≤ b)
    (hb : b ≤ 0) : ((p.val.asIdeal.absNorm : ℝ)) ^ a ≤ (2 : ℝ) ^ b := by
  have h2 := two_le_absNorm K S p
  calc ((p.val.asIdeal.absNorm : ℝ)) ^ a ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ b :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hab
    _ ≤ (2 : ℝ) ^ b := Real.rpow_le_rpow_of_nonpos (by norm_num) h2 hb

omit [Fintype S] in
private theorem norm_principalLocalD_lt_one (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
    {s : ℂ} (hs : 0 < s.re) : ‖principalLocalD K S ψ p s‖ < 1 :=
  (norm_principalLocalD_le K S ψ p s).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_absNorm K S p]) (by linarith))

private theorem norm_principalLocalE_lt_one (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖principalLocalE K S P ψ p s‖ < 1 :=
  (norm_principalLocalE_le K S P ψ p s).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_absNorm K S p]) (by linarith))

omit [Fintype S] in
private theorem absNorm_cpow_neg_six_mul_sixth (p : ExteriorPrime K S) :
    ((p.val.asIdeal.absNorm : ℂ)) ^ (-6 * (1 / 6 : ℂ)) = principalLocalV K S p := by
  show _ = ((p.val.asIdeal.absNorm : ℂ))⁻¹
  rw [show (-6 * (1 / 6 : ℂ)) = -1 by norm_num]
  exact Complex.cpow_neg_one _

omit [Fintype S] in
private theorem absNorm_cpow_neg_one (p : ExteriorPrime K S) :
    ((p.val.asIdeal.absNorm : ℂ)) ^ (-(1 : ℂ)) = principalLocalV K S p := by
  show _ = ((p.val.asIdeal.absNorm : ℂ))⁻¹
  exact Complex.cpow_neg_one _

/-- The literal local sum at the principal residue `χ = 1, w = 1, z = 1/6`. -/
private theorem localProbeEulerSum_principal (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) :
    localProbeEulerSum K S P ψ 1 p s 1 (1 / 6) =
      (1 + principalLocalV K S p) / (1 - principalLocalV K S p) +
        (1 + principalLocalV K S p) *
            (principalLocalE K S P ψ p s - principalLocalD K S ψ p s) /
          (1 - principalLocalE K S P ψ p s) := by
  have hQ := absNorm_complex_ne_zero K S p
  have h1v := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalV_lt_one K S p)
  have hInv : ((p.val.asIdeal.absNorm : ℂ))⁻¹ = principalLocalV K S p := rfl
  have hE : primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
      ((p.val.asIdeal.absNorm : ℂ)) ^ (4 - 6 * s) * principalLocalV K S p =
        principalLocalE K S P ψ p s := by
    unfold principalLocalE principalLocalV
    rw [show (3 : ℂ) - 6 * s = (4 - 6 * s) - 1 by ring, Complex.cpow_sub (4 - 6 * s) 1 hQ,
      Complex.cpow_one, div_eq_mul_inv, mul_assoc]
  have hD : primeCoefficient K ψ p.val * ((p.val.asIdeal.absNorm : ℂ)) ^ (-s) =
      principalLocalD K S ψ p s := rfl
  have hQv : ((p.val.asIdeal.absNorm : ℂ)) * principalLocalV K S p = 1 := mul_inv_cancel₀ hQ
  have hQvv : (((p.val.asIdeal.absNorm : ℂ)) - 1) * principalLocalV K S p *
      principalLocalV K S p / (1 - principalLocalV K S p) = principalLocalV K S p := by
    rw [div_eq_iff h1v]
    linear_combination principalLocalV K S p * hQv
  unfold localProbeEulerSum
  simp only [absNorm_cpow_neg_six_mul_sixth K S p, absNorm_cpow_neg_one K S p, hInv, hE, hD,
    primeCoefficient_one_eq, map_one, mul_one, one_mul]
  rw [hQvv, div_self h1v]
  ring

/-- (A) The closed form of the literal principal local correction. -/
theorem localPrincipalCorrection_eq_closedForm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) {s : ℂ} (hs : 1 / 2 < s.re) :
    localPrincipalCorrection K S P ψ p s =
      (1 - principalLocalV K S p ^ 2) *
          (1 - principalLocalV K S p * principalLocalE K S P ψ p s -
            (1 - principalLocalV K S p) * principalLocalD K S ψ p s) /
        ((1 - principalLocalE K S P ψ p s) * (1 - principalLocalD K S ψ p s)) := by
  have h1v := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalV_lt_one K S p)
  have h1E := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalE_lt_one K S P ψ p hs)
  have h1D := one_sub_ne_zero_of_norm_lt_one
    (norm_principalLocalD_lt_one K S ψ p (by linarith : (0 : ℝ) < s.re))
  have hInv : ((p.val.asIdeal.absNorm : ℂ))⁻¹ = principalLocalV K S p := rfl
  have hD : primeCoefficient K ψ p.val * ((p.val.asIdeal.absNorm : ℂ)) ^ (-s) =
      principalLocalD K S ψ p s := rfl
  unfold localPrincipalCorrection
  simp only [localProbeEulerSum_principal K S P ψ p s, hInv, hD]
  field_simp
  ring

/-- Every principal local factor is nonzero on `Re s > 1/2`. -/
theorem localPrincipalCorrection_ne_zero (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) {s : ℂ} (hs : 1 / 2 < s.re) :
    localPrincipalCorrection K S P ψ p s ≠ 0 := by
  rw [localPrincipalCorrection_eq_closedForm K S P ψ p hs]
  have hx0 := inv_absNorm_pos K S p
  have hx1 := inv_absNorm_le_half K S p
  have hvn := norm_principalLocalV K S p
  have h1vn := norm_one_sub_principalLocalV K S p
  have hE := norm_principalLocalE_lt_one K S P ψ p hs
  have hD := norm_principalLocalD_lt_one K S ψ p (by linarith : (0 : ℝ) < s.re)
  have h1E := one_sub_ne_zero_of_norm_lt_one hE
  have h1D := one_sub_ne_zero_of_norm_lt_one hD
  have h1v2 : 1 - principalLocalV K S p ^ 2 ≠ 0 := by
    apply one_sub_ne_zero_of_norm_lt_one
    rw [norm_pow, hvn]
    nlinarith
  have hK : 1 - principalLocalV K S p * principalLocalE K S P ψ p s -
      (1 - principalLocalV K S p) * principalLocalD K S ψ p s ≠ 0 := by
    rw [sub_sub]
    apply one_sub_ne_zero_of_norm_lt_one
    calc ‖principalLocalV K S p * principalLocalE K S P ψ p s +
          (1 - principalLocalV K S p) * principalLocalD K S ψ p s‖
        ≤ ‖principalLocalV K S p * principalLocalE K S P ψ p s‖ +
          ‖(1 - principalLocalV K S p) * principalLocalD K S ψ p s‖ := norm_add_le _ _
      _ = ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖principalLocalE K S P ψ p s‖ +
          (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) * ‖principalLocalD K S ψ p s‖ := by
        rw [norm_mul, norm_mul, hvn, h1vn]
      _ < ((p.val.asIdeal.absNorm : ℝ))⁻¹ * 1 + (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) * 1 :=
        add_lt_add (mul_lt_mul_of_pos_left hE hx0) (mul_lt_mul_of_pos_left hD (by linarith))
      _ = 1 := by ring
  exact div_ne_zero (mul_ne_zero h1v2 hK) (mul_ne_zero h1E h1D)

/-- The local size `H_p - 1 ≪ Q^{-2} + Q^{-1-σ} + Q^{3-6σ}`, uniformly in the
target, the probe data and the prime on `Re s ≥ σ₀ > 1/2`. -/
theorem norm_localPrincipalCorrection_sub_one_le {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
      (s : ℂ), σ₀ ≤ s.re →
      ‖localPrincipalCorrection K S P ψ p s - 1‖ ≤
        C * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) +
          ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) +
          ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re)) := by
  obtain ⟨d₀, hd₀_def⟩ : ∃ d : ℝ, d = (2 : ℝ) ^ (-σ₀) := ⟨_, rfl⟩
  obtain ⟨e₀, he₀_def⟩ : ∃ e : ℝ, e = (2 : ℝ) ^ (3 - 6 * σ₀) := ⟨_, rfl⟩
  have hd₀ : d₀ < 1 := by
    rw [hd₀_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have he₀ : e₀ < 1 := by
    rw [he₀_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hc : 0 < (1 - e₀) * (1 - d₀) := mul_pos (by linarith) (by linarith)
  refine ⟨3 / ((1 - e₀) * (1 - d₀)), div_nonneg (by norm_num) hc.le, ?_⟩
  intro P ψ p s hs
  have hs' : 1 / 2 < s.re := lt_of_lt_of_le hσ₀ hs
  have hQ2 := two_le_absNorm K S p
  have hQpos : (0 : ℝ) < (p.val.asIdeal.absNorm : ℝ) := by linarith
  have hx0 := inv_absNorm_pos K S p
  have hx1 := inv_absNorm_le_half K S p
  have hvn := norm_principalLocalV K S p
  have hv2n := norm_one_sub_principalLocalV_sq_le K S p
  have hDle := norm_principalLocalD_le K S ψ p s
  have hEle := norm_principalLocalE_le K S P ψ p s
  have hDd : ‖principalLocalD K S ψ p s‖ ≤ d₀ := by
    rw [hd₀_def]
    exact hDle.trans (absNorm_rpow_le_two_rpow K S p (by linarith) (by linarith))
  have hEe : ‖principalLocalE K S P ψ p s‖ ≤ e₀ := by
    rw [he₀_def]
    exact hEle.trans (absNorm_rpow_le_two_rpow K S p (by linarith) (by linarith))
  have h1E : 1 - principalLocalE K S P ψ p s ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by linarith)
  have h1D : 1 - principalLocalD K S ψ p s ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by linarith)
  have hv2 : ((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) =
      (((p.val.asIdeal.absNorm : ℝ))⁻¹) ^ 2 := by
    rw [Real.rpow_neg hQpos.le, Real.rpow_two, inv_pow]
  have hvD : ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) =
      ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) := by
    rw [sub_eq_add_neg, Real.rpow_add hQpos, Real.rpow_neg_one]
  have hA : 0 ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) := Real.rpow_nonneg hQpos.le _
  have hB : 0 ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) := Real.rpow_nonneg hQpos.le _
  have hC' : 0 ≤ ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re) := Real.rpow_nonneg hQpos.le _
  rw [localPrincipalCorrection_eq_closedForm K S P ψ p hs']
  set v := principalLocalV K S p with hv_def
  set E := principalLocalE K S P ψ p s with hE_def
  set D := principalLocalD K S ψ p s with hD_def
  have hid : (1 - v ^ 2) * (1 - v * E - (1 - v) * D) / ((1 - E) * (1 - D)) - 1 =
      ((E - v ^ 2) * (1 - D) - (1 - v ^ 2) * v * (E - D)) / ((1 - E) * (1 - D)) := by
    rw [div_sub_one (mul_ne_zero h1E h1D)]
    congr 1
    ring
  have hnum : ‖(E - v ^ 2) * (1 - D) - (1 - v ^ 2) * v * (E - D)‖ ≤
      3 * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) +
        ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) +
        ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re)) := by
    have h1 : ‖E - v ^ 2‖ ≤ ‖E‖ + ((p.val.asIdeal.absNorm : ℝ))⁻¹ ^ 2 := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_pow, hvn]
    have h2 : ‖1 - D‖ ≤ 1 + ‖D‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_one]
    have h4 : ‖E - D‖ ≤ ‖E‖ + ‖D‖ := norm_sub_le _ _
    have hD1 : ‖D‖ ≤ 1 := by linarith
    have hx1' : ((p.val.asIdeal.absNorm : ℝ))⁻¹ ≤ 1 := by linarith
    have hxD : ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖D‖ ≤
        ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) := by
      rw [← hvD]
      exact mul_le_mul_of_nonneg_left hDle hx0.le
    calc ‖(E - v ^ 2) * (1 - D) - (1 - v ^ 2) * v * (E - D)‖
        ≤ ‖(E - v ^ 2) * (1 - D)‖ + ‖(1 - v ^ 2) * v * (E - D)‖ := norm_sub_le _ _
      _ = ‖E - v ^ 2‖ * ‖1 - D‖ +
          ‖1 - v ^ 2‖ * ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖E - D‖ := by
        simp only [norm_mul, hvn]
      _ ≤ (‖E‖ + ((p.val.asIdeal.absNorm : ℝ))⁻¹ ^ 2) * (1 + ‖D‖) +
          1 * ((p.val.asIdeal.absNorm : ℝ))⁻¹ * (‖E‖ + ‖D‖) := by gcongr
      _ ≤ 3 * ‖E‖ + 2 * ((p.val.asIdeal.absNorm : ℝ))⁻¹ ^ 2 +
          ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖D‖ := by
        nlinarith [mul_nonneg (norm_nonneg E) (sub_nonneg.mpr hD1),
          mul_nonneg (norm_nonneg E) (sub_nonneg.mpr hx1'),
          mul_nonneg (sq_nonneg ((p.val.asIdeal.absNorm : ℝ))⁻¹) (sub_nonneg.mpr hD1)]
      _ ≤ 3 * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) +
          ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - s.re) +
          ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re)) := by
        rw [hv2]
        linarith
  have hden : (1 - e₀) * (1 - d₀) ≤ ‖1 - E‖ * ‖1 - D‖ := by
    have hE' : 1 - e₀ ≤ ‖1 - E‖ := by
      have := norm_sub_norm_le (1 : ℂ) E
      rw [norm_one] at this
      linarith
    have hD' : 1 - d₀ ≤ ‖1 - D‖ := by
      have := norm_sub_norm_le (1 : ℂ) D
      rw [norm_one] at this
      linarith
    exact mul_le_mul hE' hD' (by linarith) (norm_nonneg _)
  rw [hid, norm_div, norm_mul]
  refine (div_le_div₀ (by positivity) hnum hc hden).trans (le_of_eq ?_)
  ring

/-! ### Summability over exterior primes -/

omit [Fintype S] in
private theorem summable_absNorm_rpow {a : ℝ} (ha : a < -1) :
    Summable (fun p : ExteriorPrime K S => ((p.val.asIdeal.absNorm : ℝ)) ^ a) := by
  have h := absolutelySummable_primeIdealRatio K (fun _ => (1 : ℂ)) (fun _ => by simp)
    (s := ((-a : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; linarith)
  have hinj : Function.Injective (fun p : ExteriorPrime K S => p.val) := Subtype.val_injective
  refine (h.comp_injective hinj).congr (fun p => ?_)
  simp only [Function.comp_apply, primeIdealRatio, one_mul]
  rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos' K S p)]
  simp

omit [Fintype S] in
private theorem summable_principalBound (C : ℝ) {σ : ℝ} (hσ : 2 / 3 < σ) :
    Summable (fun p : ExteriorPrime K S => C * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) +
      ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - σ) +
      ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * σ))) :=
  (((summable_absNorm_rpow K S (a := -2) (by norm_num)).add
    (summable_absNorm_rpow K S (a := -1 - σ) (by linarith))).add
    (summable_absNorm_rpow K S (a := 3 - 6 * σ) (by linarith))).mul_left C

omit [Fintype S] in
private theorem principalBound_mono (p : ExteriorPrime K S) {C σ τ : ℝ} (hC : 0 ≤ C)
    (hστ : σ ≤ τ) :
    C * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) + ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - τ) +
      ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * τ)) ≤
    C * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) + ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - σ) +
      ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * σ)) := by
  have h1 : (1 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ) := by linarith [two_le_absNorm K S p]
  have ha := Real.rpow_le_rpow_of_exponent_le h1 (show -1 - τ ≤ -1 - σ by linarith)
  have hb := Real.rpow_le_rpow_of_exponent_le h1 (show 3 - 6 * τ ≤ 3 - 6 * σ by linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hC

/-- A summable majorant for `H_p - 1`, uniform on a closed half-plane `Re s ≥ σ₁ > 2/3`. -/
private theorem exists_summable_majorant {σ₁ : ℝ} (hσ₁ : 2 / 3 < σ₁) :
    ∃ u : ExteriorPrime K S → ℝ, Summable u ∧ (∀ p, 0 ≤ u p) ∧
      ∀ (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S) (s : ℂ),
        σ₁ ≤ s.re → ‖localPrincipalCorrection K S P ψ p s - 1‖ ≤ u p := by
  obtain ⟨C, hC0, hC⟩ := norm_localPrincipalCorrection_sub_one_le K S (σ₀ := σ₁) (by linarith)
  refine ⟨fun p => C * (((p.val.asIdeal.absNorm : ℝ)) ^ (-2 : ℝ) +
      ((p.val.asIdeal.absNorm : ℝ)) ^ (-1 - σ₁) + ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * σ₁)),
    summable_principalBound K S C hσ₁, fun p => ?_, fun P ψ p s hs => ?_⟩
  · exact mul_nonneg hC0 (by positivity)
  · exact (hC P ψ p s hs).trans (principalBound_mono K S p hC0 hs)

private theorem summable_norm_localPrincipalCorrection_sub_one (P : ProbeData K S)
    (ψ : HeckeCharacter K) {s : ℂ} (hs : 2 / 3 < s.re) :
    Summable (fun p : ExteriorPrime K S => ‖localPrincipalCorrection K S P ψ p s - 1‖) := by
  obtain ⟨u, hu, -, hbu⟩ := exists_summable_majorant K S hs
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hbu P ψ p s le_rfl) hu

/-- (B) The principal Euler product converges on `Re s > 2/3`. -/
theorem multipliable_localPrincipalCorrection (P : ProbeData K S) (ψ : HeckeCharacter K)
    {s : ℂ} (hs : 2 / 3 < s.re) :
    Multipliable (fun p : ExteriorPrime K S => localPrincipalCorrection K S P ψ p s) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_localPrincipalCorrection_sub_one K S P ψ hs)
  simpa only [add_sub_cancel] using h

/-- (B) The actual principal correction has no zero on `Re s > 2/3`. -/
theorem principalCorrection_ne_zero (P : ProbeData K S) (ψ : HeckeCharacter K)
    {s : ℂ} (hs : 2 / 3 < s.re) : principalCorrection K S P ψ s ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun p : ExteriorPrime K S => localPrincipalCorrection K S P ψ p s - 1)
    (fun p => by
      simpa only [add_sub_cancel] using
        localPrincipalCorrection_ne_zero K S P ψ p (by linarith : (1 / 2 : ℝ) < s.re))
    (summable_norm_localPrincipalCorrection_sub_one K S P ψ hs)
  unfold principalCorrection
  simpa only [add_sub_cancel] using h

/-! ### Holomorphy -/

omit [Fintype S] in
private theorem differentiableAt_principalLocalD (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
    (s : ℂ) : DifferentiableAt ℂ (fun s => principalLocalD K S ψ p s) s := by
  have hQ := absNorm_complex_ne_zero K S p
  unfold principalLocalD
  refine DifferentiableAt.const_mul (DifferentiableAt.const_cpow ?_ (Or.inl hQ)) _
  fun_prop

private theorem differentiableAt_principalLocalE (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) :
    DifferentiableAt ℂ (fun s => principalLocalE K S P ψ p s) s := by
  have hQ := absNorm_complex_ne_zero K S p
  unfold principalLocalE
  refine DifferentiableAt.const_mul (DifferentiableAt.const_cpow ?_ (Or.inl hQ)) _
  fun_prop

/-- Each local factor is holomorphic on `Re s > 1/2`, through the closed form. -/
private theorem differentiableOn_localPrincipalCorrection (P : ProbeData K S)
    (ψ : HeckeCharacter K) (p : ExteriorPrime K S) :
    DifferentiableOn ℂ (fun s => localPrincipalCorrection K S P ψ p s)
      (rightHalfPlane (1 / 2)) := by
  have hcf : DifferentiableOn ℂ (fun s => (1 - principalLocalV K S p ^ 2) *
      (1 - principalLocalV K S p * principalLocalE K S P ψ p s -
        (1 - principalLocalV K S p) * principalLocalD K S ψ p s) /
      ((1 - principalLocalE K S P ψ p s) * (1 - principalLocalD K S ψ p s)))
      (rightHalfPlane (1 / 2)) := by
    intro s hs
    have hs' : (1 / 2 : ℝ) < s.re := hs
    have hD := differentiableAt_principalLocalD K S ψ p s
    have hE := differentiableAt_principalLocalE K S P ψ p s
    have h1E := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalE_lt_one K S P ψ p hs')
    have h1D := one_sub_ne_zero_of_norm_lt_one
      (norm_principalLocalD_lt_one K S ψ p (by linarith : (0 : ℝ) < s.re))
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ ?_ (mul_ne_zero h1E h1D)
    · exact (differentiableAt_const _).mul
        (((differentiableAt_const _).sub ((differentiableAt_const _).mul hE)).sub
          ((differentiableAt_const _).mul hD))
    · exact ((differentiableAt_const _).sub hE).mul ((differentiableAt_const _).sub hD)
  exact hcf.congr (fun s hs => localPrincipalCorrection_eq_closedForm K S P ψ p hs)

/-- The Euler product is a locally uniform limit of holomorphic partial products on
`Re s > σ₁` for every `σ₁ > 2/3`. -/
private theorem differentiableOn_principalCorrection_of_lt (P : ProbeData K S)
    (ψ : HeckeCharacter K) {σ₁ : ℝ} (hσ₁ : 2 / 3 < σ₁) :
    DifferentiableOn ℂ (principalCorrection K S P ψ) (rightHalfPlane σ₁) := by
  obtain ⟨u, hu, -, hbu⟩ := exists_summable_majorant K S hσ₁
  have hsub : rightHalfPlane σ₁ ⊆ rightHalfPlane (1 / 2) := by
    intro s hs
    have h : σ₁ < s.re := hs
    show (1 / 2 : ℝ) < s.re
    linarith
  have hdiff : ∀ p : ExteriorPrime K S,
      DifferentiableOn ℂ (fun s => localPrincipalCorrection K S P ψ p s) (rightHalfPlane σ₁) :=
    fun p => (differentiableOn_localPrincipalCorrection K S P ψ p).mono hsub
  have hbound : ∀ᶠ p in Filter.cofinite, ∀ s ∈ rightHalfPlane σ₁,
      ‖localPrincipalCorrection K S P ψ p s - 1‖ ≤ u p := by
    refine Filter.Eventually.of_forall (fun p s hs => ?_)
    have h : σ₁ < s.re := hs
    exact hbu P ψ p s h.le
  have hloc := Summable.hasProdLocallyUniformlyOn_one_add (isOpen_rightHalfPlane σ₁) hu hbound
    (fun p => ((hdiff p).sub_const 1).continuousOn)
  simp only [add_sub_cancel] at hloc
  have hF : ∀ᶠ F : Finset (ExteriorPrime K S) in Filter.atTop, DifferentiableOn ℂ
      (fun s => ∏ p ∈ F, localPrincipalCorrection K S P ψ p s) (rightHalfPlane σ₁) :=
    Filter.Eventually.of_forall (fun F => DifferentiableOn.fun_finsetProd (fun p _ => hdiff p))
  exact (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hloc).differentiableOn hF
    (isOpen_rightHalfPlane σ₁)

/-- (B) The actual principal correction is analytic on `Re s > 2/3`. -/
theorem analyticOnNhd_principalCorrection (P : ProbeData K S) (ψ : HeckeCharacter K) :
    AnalyticOnNhd ℂ (principalCorrection K S P ψ) (rightHalfPlane (2 / 3)) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_rightHalfPlane (2 / 3))
  intro s₀ hs₀
  have hs₀' : (2 / 3 : ℝ) < s₀.re := hs₀
  have hσ : (2 / 3 : ℝ) < (2 / 3 + s₀.re) / 2 := by linarith
  have hmem : s₀ ∈ rightHalfPlane ((2 / 3 + s₀.re) / 2) := by
    show (2 / 3 + s₀.re) / 2 < s₀.re
    linarith
  exact ((differentiableOn_principalCorrection_of_lt K S P ψ hσ).differentiableAt
    ((isOpen_rightHalfPlane _).mem_nhds hmem)).differentiableWithinAt

/-- The principal correction is bounded on every closed half-plane `Re s ≥ σ₁ > 2/3`. -/
theorem exists_norm_principalCorrection_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    {σ₁ : ℝ} (hσ₁ : 2 / 3 < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → ‖principalCorrection K S P ψ s‖ ≤ C := by
  obtain ⟨u, hu, hu0, hbu⟩ := exists_summable_majorant K S hσ₁
  refine ⟨Real.exp (∑' p, u p), (Real.exp_pos _).le, fun s hs => ?_⟩
  have hb : ∀ p : ExteriorPrime K S, ‖localPrincipalCorrection K S P ψ p s‖ ≤ 1 + u p := by
    intro p
    have h1 := hbu P ψ p s hs
    have h2 := norm_sub_norm_le (localPrincipalCorrection K S P ψ p s) 1
    rw [norm_one] at h2
    linarith
  have hmult := multipliable_localPrincipalCorrection K S P ψ (lt_of_lt_of_le hσ₁ hs)
  have htend := hmult.hasProd.norm
  unfold principalCorrection
  refine le_of_tendsto' htend (fun F => ?_)
  calc ∏ p ∈ F, ‖localPrincipalCorrection K S P ψ p s‖ ≤ ∏ p ∈ F, (1 + u p) :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => hb p)
    _ ≤ Real.exp (∑ p ∈ F, u p) := Real.prod_one_add_le_exp_sum F hu0
    _ ≤ Real.exp (∑' p, u p) := Real.exp_le_exp.mpr (hu.sum_le_tsum F (fun p _ => hu0 p))

/-! ### The compensation factor -/

/-- (C) The compensation factor at the principal residue, for an unramified
target: `G_p + H_p` has the displayed closed form, with no division by the
local sum or by `H_p`. -/
theorem localCompensated_add_principal_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    (p : ExteriorPrime K S) (hψ : UnramifiedAt K ψ p.val) {s : ℂ} (hs : 1 / 2 < s.re) :
    localCompensatedEulerCorrection K S P ψ 1 p s 1 (1 / 6) + localPrincipalCorrection K S P ψ p s =
      (1 - principalLocalV K S p) ^ 2 * (1 + principalLocalV K S p) *
        (principalLocalE K S P ψ p s -
          principalLocalV K S p * principalLocalD K S ψ p s * principalLocalE K S P ψ p s -
          (1 - principalLocalV K S p) * principalLocalD K S ψ p s ^ 2) /
        (principalLocalD K S ψ p s * (1 - principalLocalD K S ψ p s) *
          (1 - principalLocalE K S P ψ p s)) := by
  have h1v := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalV_lt_one K S p)
  have h1E := one_sub_ne_zero_of_norm_lt_one (norm_principalLocalE_lt_one K S P ψ p hs)
  have h1D := one_sub_ne_zero_of_norm_lt_one
    (norm_principalLocalD_lt_one K S ψ p (by linarith : (0 : ℝ) < s.re))
  have hDne : principalLocalD K S ψ p s ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_principalLocalD_eq K S ψ p hψ s]
    exact (Real.rpow_pos_of_pos (by linarith [two_le_absNorm K S p]) _).ne'
  have hconj : conj (primeCoefficient K ψ p.val) * ((p.val.asIdeal.absNorm : ℂ)) ^ s =
      (principalLocalD K S ψ p s)⁻¹ := by
    unfold principalLocalD
    rw [mul_inv, Complex.cpow_neg, inv_inv,
      Complex.inv_eq_conj (norm_primeCoefficient_eq_one K ψ p.val hψ)]
  have hD : primeCoefficient K ψ p.val * ((p.val.asIdeal.absNorm : ℂ)) ^ (-s) =
      principalLocalD K S ψ p s := rfl
  rw [localPrincipalCorrection_eq_closedForm K S P ψ p hs]
  unfold localCompensatedEulerCorrection localMarkedProbeEulerSum
  simp only [localProbeEulerSum_principal K S P ψ p s, absNorm_cpow_neg_six_mul_sixth K S p,
    absNorm_cpow_neg_one K S p, hconj, hD, primeCoefficient_one_eq, map_one, mul_one, one_mul]
  field_simp
  ring

/-- (D) `G_p = -H_p + O(Q^{-σ})` uniformly on `Re s ≥ 3/4` for unramified targets. -/
theorem norm_localCompensated_add_principal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : ProbeData K S) (ψ : HeckeCharacter K) (p : ExteriorPrime K S)
      (s : ℂ), UnramifiedAt K ψ p.val → 3 / 4 ≤ s.re →
      ‖localCompensatedEulerCorrection K S P ψ 1 p s 1 (1 / 6) +
          localPrincipalCorrection K S P ψ p s‖ ≤
        C * ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) := by
  obtain ⟨d₀, hd₀_def⟩ : ∃ d : ℝ, d = (2 : ℝ) ^ (-(3 / 4 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨e₀, he₀_def⟩ : ∃ e : ℝ, e = (2 : ℝ) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hd₀ : d₀ < 1 := by
    rw [hd₀_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have he₀ : e₀ < 1 := by
    rw [he₀_def]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hc : 0 < (1 - d₀) * (1 - e₀) := mul_pos (by linarith) (by linarith)
  refine ⟨(9 / 2) / ((1 - d₀) * (1 - e₀)), div_nonneg (by norm_num) hc.le, ?_⟩
  intro P ψ p s hψ hs
  have hs' : 1 / 2 < s.re := by linarith
  have hQ2 := two_le_absNorm K S p
  have hQpos : (0 : ℝ) < (p.val.asIdeal.absNorm : ℝ) := by linarith
  have hx0 := inv_absNorm_pos K S p
  have hx1 := inv_absNorm_le_half K S p
  have hvn := norm_principalLocalV K S p
  have h1vn := norm_one_sub_principalLocalV K S p
  have hDn := norm_principalLocalD_eq K S ψ p hψ s
  have hEle := norm_principalLocalE_le K S P ψ p s
  have hy0 : 0 < ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) := Real.rpow_pos_of_pos hQpos _
  have hyd : ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) ≤ d₀ := by
    rw [hd₀_def]
    exact absNorm_rpow_le_two_rpow K S p (by linarith) (by norm_num)
  have hEy : ((p.val.asIdeal.absNorm : ℝ)) ^ (3 - 6 * s.re) ≤
      ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) * ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) := by
    rw [← Real.rpow_add hQpos]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hEe : ‖principalLocalE K S P ψ p s‖ ≤ e₀ := by
    rw [he₀_def]
    exact hEle.trans (absNorm_rpow_le_two_rpow K S p (by linarith) (by norm_num))
  have hDne : principalLocalD K S ψ p s ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact hy0.ne'
  have h1E : 1 - principalLocalE K S P ψ p s ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by linarith)
  have h1D : 1 - principalLocalD K S ψ p s ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one (by linarith)
  rw [localCompensated_add_principal_eq K S P ψ p hψ hs']
  set v := principalLocalV K S p with hv_def
  set E := principalLocalE K S P ψ p s with hE_def
  set D := principalLocalD K S ψ p s with hD_def
  set y := ((p.val.asIdeal.absNorm : ℝ)) ^ (-s.re) with hy_def
  have hnum : ‖E - v * D * E - (1 - v) * D ^ 2‖ ≤ 3 * y * ‖D‖ := by
    have h1 : ‖E - v * D * E - (1 - v) * D ^ 2‖ ≤
        ‖E‖ + ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖D‖ * ‖E‖ +
          (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) * ‖D‖ ^ 2 := by
      calc ‖E - v * D * E - (1 - v) * D ^ 2‖
          ≤ ‖E - v * D * E‖ + ‖(1 - v) * D ^ 2‖ := norm_sub_le _ _
        _ ≤ ‖E‖ + ‖v * D * E‖ + ‖(1 - v) * D ^ 2‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
        _ = ‖E‖ + ((p.val.asIdeal.absNorm : ℝ))⁻¹ * ‖D‖ * ‖E‖ +
            (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) * ‖D‖ ^ 2 := by
          simp only [norm_mul, norm_pow, hvn, h1vn]
    rw [hDn] at h1 ⊢
    have hE2 : ‖E‖ ≤ y * y := hEle.trans hEy
    have hy1 : y ≤ 1 := by linarith
    have hxy : ((p.val.asIdeal.absNorm : ℝ))⁻¹ * y ≤ 1 := by nlinarith
    have hxyE : ((p.val.asIdeal.absNorm : ℝ))⁻¹ * y * ‖E‖ ≤ ‖E‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hxy
    have hxy2 : 0 ≤ ((p.val.asIdeal.absNorm : ℝ))⁻¹ * y ^ 2 := by positivity
    nlinarith
  have hA : ‖(1 - v) ^ 2 * (1 + v)‖ ≤ 3 / 2 := by
    rw [norm_mul, norm_pow, h1vn]
    have h1 : ‖1 + v‖ ≤ 1 + ((p.val.asIdeal.absNorm : ℝ))⁻¹ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_one, hvn]
    have h2 : (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) ^ 2 ≤ 1 := by nlinarith
    calc (1 - ((p.val.asIdeal.absNorm : ℝ))⁻¹) ^ 2 * ‖1 + v‖
        ≤ 1 * (1 + ((p.val.asIdeal.absNorm : ℝ))⁻¹) :=
          mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
      _ ≤ 3 / 2 := by linarith
  have hden1 : 1 - d₀ ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one, hDn] at this
    linarith
  have hden2 : 1 - e₀ ≤ ‖1 - E‖ := by
    have := norm_sub_norm_le (1 : ℂ) E
    rw [norm_one] at this
    linarith
  have hDlow : (1 - d₀) * (1 - e₀) * ‖D‖ ≤ ‖D * (1 - D) * (1 - E)‖ := by
    rw [norm_mul, norm_mul]
    have h := mul_le_mul hden1 hden2 (by linarith) (norm_nonneg _)
    calc (1 - d₀) * (1 - e₀) * ‖D‖ ≤ ‖1 - D‖ * ‖1 - E‖ * ‖D‖ :=
          mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = ‖D‖ * ‖1 - D‖ * ‖1 - E‖ := by ring
  have hpos : 0 < ‖D * (1 - D) * (1 - E)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (mul_ne_zero hDne h1D) h1E)
  have hCc : (9 / 2) / ((1 - d₀) * (1 - e₀)) * ((1 - d₀) * (1 - e₀)) = 9 / 2 :=
    div_mul_cancel₀ _ hc.ne'
  rw [norm_div, div_le_iff₀ hpos]
  calc ‖(1 - v) ^ 2 * (1 + v) * (E - v * D * E - (1 - v) * D ^ 2)‖
      ≤ 3 / 2 * (3 * y * ‖D‖) := by
        rw [norm_mul]
        exact mul_le_mul hA hnum (norm_nonneg _) (by norm_num)
    _ = (9 / 2) / ((1 - d₀) * (1 - e₀)) * ((1 - d₀) * (1 - e₀)) * y * ‖D‖ := by
        rw [hCc]
        ring
    _ = (9 / 2) / ((1 - d₀) * (1 - e₀)) * y * ((1 - d₀) * (1 - e₀) * ‖D‖) := by ring
    _ ≤ (9 / 2) / ((1 - d₀) * (1 - e₀)) * y * ‖D * (1 - D) * (1 - E)‖ :=
        mul_le_mul_of_nonneg_left hDlow
          (mul_nonneg (div_nonneg (by norm_num) hc.le) hy0.le)

end HeckeGeneral.ThetaSkeleton.Physical
