import HeckeGeneral.Analysis.TInputRanges

/-!
Agreement of the rational row correction with the literal extracted local
Euler expression on the positive-w region. The nonvanishing needed for
cancellation is derived from prime norms and character coefficient bounds.
No agreement is asserted on the removable W=1 locus of the literal formula.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical ComplexConjugate BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

omit [Fintype S] in
private theorem rowCompatibility_norm_pos (p : ExteriorPrime K S) :
    0 < p.val.asIdeal.absNorm :=
  lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)

omit [Fintype S] in
private theorem rowCompatibility_one_lt_norm (p : ExteriorPrime K S) :
    (1 : ℝ) < (p.val.asIdeal.absNorm : ℝ) := by
  exact_mod_cast one_lt_primeIdeal_absNorm K p.val

private theorem rowCompatibility_one_sub_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    1 - a ≠ 0 := by
  intro h
  have ha1 : a = 1 := (sub_eq_zero.mp h).symm
  rw [ha1, norm_one] at ha
  exact lt_irrefl _ ha

private theorem rowCompatibility_twisted_cpow_le {n : ℕ} (hn : 0 < n)
    {a t : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖a * (n : ℂ) ^ t‖ ≤ (n : ℝ) ^ t.re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha

omit [Fintype S] in
private theorem rowCompatibility_V_lt_one (p : ExteriorPrime K S)
    {z : ℂ} (hz : 0 < z.re) :
    ‖(p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (rowCompatibility_norm_pos K S p)]
  have hre : (-6 * z : ℂ).re = -6 * z.re := by simp
  rw [hre]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (rowCompatibility_one_lt_norm K S p) (by linarith)

omit [Fintype S] in
private theorem rowCompatibility_W_lt_one (χ : HeckeCharacter K)
    (p : ExteriorPrime K S) {w : ℂ} (hw : 0 < w.re) :
    ‖primeCoefficient K χ p.val * (p.val.asIdeal.absNorm : ℂ) ^ (-w)‖ < 1 := by
  refine (rowCompatibility_twisted_cpow_le (rowCompatibility_norm_pos K S p)
    (norm_primeCoefficient_le_one K χ p.val)).trans_lt ?_
  simp only [Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (rowCompatibility_one_lt_norm K S p) (by linarith)

omit [Fintype S] in
private theorem rowCompatibility_D_lt_one (ψ χ : HeckeCharacter K)
    (p : ExteriorPrime K S) {s : ℂ} (hs : 0 < s.re) :
    ‖primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
  have ha : ‖primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    have hψ := norm_primeCoefficient_le_one K ψ p.val
    have hχ := norm_primeCoefficient_le_one K χ p.val
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul hψ hχ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine (rowCompatibility_twisted_cpow_le
    (rowCompatibility_norm_pos K S p) ha).trans_lt ?_
  simp only [Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (rowCompatibility_one_lt_norm K S p) (by linarith)

private theorem rowCompatibility_E_lt_one (P : ProbeData K S)
    (ψ : HeckeCharacter K) (p : ExteriorPrime K S) {s z : ℂ}
    (hsz : 4 < 6 * s.re + 6 * z.re) :
    ‖primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
      (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ < 1 := by
  have hQpos : 0 < (p.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast rowCompatibility_norm_pos K S p
  have ha : ‖primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _)
      (norm_primeCoefficient_le_one K _ p.val)
  have hre₁ : (4 - 6 * s : ℂ).re = 4 - 6 * s.re := by simp
  have hre₂ : (-6 * z : ℂ).re = -6 * z.re := by simp
  have hnorm :
      ‖primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
        (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
        (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ ≤
        (p.val.asIdeal.absNorm : ℝ) ^ (4 - 6 * s.re - 6 * z.re) := by
    calc
      _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (4 - 6 * s).re *
          ‖(p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (rowCompatibility_twisted_cpow_le (rowCompatibility_norm_pos K S p) ha)
          (norm_nonneg _)
      _ = (p.val.asIdeal.absNorm : ℝ) ^ (4 - 6 * s.re - 6 * z.re) := by
        rw [Complex.norm_natCast_cpow_of_pos (rowCompatibility_norm_pos K S p),
          hre₁, hre₂, ← Real.rpow_add hQpos]
        congr 1 <;> ring
  exact hnorm.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg
    (rowCompatibility_one_lt_norm K S p) (by linarith))

/-- On the positive region the continued correction is the literal local
sum with its three extracted factors. All cancellation denominators are
proved nonzero from the displayed real-part inequalities. -/
theorem localRowCorrection_eq_literal_of_positive (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) {s w z : ℂ}
    (hs : 0 < s.re) (hw : 0 < w.re) (hz : 0 < z.re)
    (hsz : 4 < 6 * s.re + 6 * z.re) :
    localRowCorrection K S P ψ χ p s w z =
      let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
      let V := q ^ (-6 * z)
      let W := primeCoefficient K χ p.val * q ^ (-w)
      let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-s)
      localProbeEulerSum K S P ψ χ p s w z * (1 - V) * (1 - W) / (1 - D) := by
  have hV := rowCompatibility_one_sub_ne_zero (rowCompatibility_V_lt_one K S p hz)
  have hW := rowCompatibility_one_sub_ne_zero (rowCompatibility_W_lt_one K S χ p hw)
  have hD := rowCompatibility_one_sub_ne_zero (rowCompatibility_D_lt_one K S ψ χ p hs)
  have hE := rowCompatibility_one_sub_ne_zero (rowCompatibility_E_lt_one K S P ψ p hsz)
  simpa only [localRowCorrection, localProbeEulerSum] using
    (rowEulerLiteral_eq_rational (p.val.asIdeal.absNorm : ℂ)
      (p.val.asIdeal.absNorm : ℂ)⁻¹
      ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
      (primeCoefficient K χ p.val * (p.val.asIdeal.absNorm : ℂ) ^ (-w))
      (primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
        (p.val.asIdeal.absNorm : ℂ) ^ (-s))
      (primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
        (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
        (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) hV hW hE hD).symm

/-- Compatibility on the open initial calibration domain. -/
theorem localRowCorrection_eq_literal_of_initial (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) {s w z : ℂ}
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    localRowCorrection K S P ψ χ p s w z =
      let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
      let V := q ^ (-6 * z)
      let W := primeCoefficient K χ p.val * q ^ (-w)
      let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-s)
      localProbeEulerSum K S P ψ χ p s w z * (1 - V) * (1 - W) / (1 - D) := by
  exact localRowCorrection_eq_literal_of_positive K S P ψ χ p
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- Compatibility on the existing positive-w Euler region. -/
theorem localRowCorrection_eq_literal_of_rowEulerRegion (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) {v : ℂ × ℂ × ℂ}
    (hv : v ∈ rowEulerRegion) :
    localRowCorrection K S P ψ χ p v.1 v.2.1 v.2.2 =
      let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
      let V := q ^ (-6 * v.2.2)
      let W := primeCoefficient K χ p.val * q ^ (-v.2.1)
      let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-v.1)
      localProbeEulerSum K S P ψ χ p v.1 v.2.1 v.2.2 *
        (1 - V) * (1 - W) / (1 - D) := by
  rcases hv with ⟨hs, hw, hz, _, hsz, _⟩
  exact localRowCorrection_eq_literal_of_positive K S P ψ χ p
    (by linarith) hw hz (by linarith)

/-- Local compatibility also preserves the whole row correction, including
all finite exceptional factors. Equality of products here needs no separate
multipliability assumption because their functions agree at every prime. -/
theorem rowCorrection_eq_literal_of_positive (P : ProbeData K S)
    (ψ : HeckeCharacter K) (E : RowEulerData K S P)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) {s w z : ℂ}
    (hs : 0 < s.re) (hw : 0 < w.re) (hz : 0 < z.re)
    (hsz : 4 < 6 * s.re + 6 * z.re) :
    rowCorrection K S P ψ E Q u s w z =
      ∏' p : ExteriorPrime K S,
        if hp : p ∈ rowExceptionalPrimes K S Q u then
          finiteEulerRationalValue (E.exceptionalFactor Q u ⟨p, hp⟩)
            (p.val.asIdeal.absNorm : ℝ) s w z
        else
          let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
          let V := q ^ (-6 * z)
          let W := primeCoefficient K (E.rows.character u) p.val * q ^ (-w)
          let D := primeCoefficient K ψ p.val *
            conj (primeCoefficient K (E.rows.character u) p.val) * q ^ (-s)
          localProbeEulerSum K S P ψ (E.rows.character u) p s w z *
            (1 - V) * (1 - W) / (1 - D) := by
  unfold rowCorrection
  apply congrArg (fun f : ExteriorPrime K S → ℂ => ∏' p, f p)
  funext p
  by_cases hp : p ∈ rowExceptionalPrimes K S Q u
  · simp only [dif_pos hp]
  · simp only [dif_neg hp]
    exact localRowCorrection_eq_literal_of_positive K S P ψ (E.rows.character u) p hs hw hz hsz

end HeckeGeneral.ThetaSkeleton.Physical
