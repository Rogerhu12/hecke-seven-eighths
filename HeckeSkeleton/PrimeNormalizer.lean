import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeSkeleton.WindowPIT

/-!
# The prime normalizer

Both normalizer obligations of `Principal.lean` (PR-NORMALIZER-POSITIVE and
PR-NORMALIZER-SMALLPOWER) follow from one analytic input: the prime ideal
theorem in a fixed ratio window, `window_prime_lower` (obligation PR-WINDOW-PIT).
The deduction is complete: every slot sum is a positive real of size at least
`c · X^{1/6} / log X` with `X = primeScale g Z`, the slot number is even, and
`(X^{1/6})^slots = Z^{1/36}` cancels the prefactor, so `primeNormalizer` is a positive
real bounded below by a constant times `(log X)^(-slots)`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeNormalizer

open NumberField IsDedekindDomain Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Primes outside `S` of norm at most `2X`: the envelope that `primeWindow` filters. -/
def windowPrimes (X : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePrimeEnvelope K (dyadicIdealSupport K X)).filter (fun p => p ∉ S)

-- OBLIGATION PR-WINDOW-PIT | revised §6.1 (normalizer windows); Landau's prime ideal theorem.
-- Estimated size 6,000–8,000 lines: smoothed explicit formula for prime ideals from a
-- zero-free region of ζ_K (Axiom: Re s > 31/32), then removal of prime powers and of S.
-- A Chebyshev-type bound is not enough: the window is a fixed ratio interval.
theorem window_prime_lower (w : SmoothAnnularTest)
    (hre : ∀ y, (w.toFun y).im = 0) (hnn : ∀ y, 0 ≤ (w.toFun y).re)
    (hne : ∃ y, w.toFun y ≠ 0) (hsupp : Function.support w.toFun ⊆ Set.Ioo 1 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re :=
  HeckeSkeleton.WindowPIT.window_prime_lower K S w hre hnn hne hsupp

section Derivation

variable (g : PrimeWindowGeometry)

/-- The real value of a slot sum (empty ray filter). -/
def slotReal (Z : ℝ) (i : Fin g.slots) : ℝ :=
  ∑ p ∈ windowPrimes K S (primeScale g Z),
    ((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z)).re *
      (p.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ))

omit [Fintype S] in
theorem sum_primeWindow (Z : ℝ) (i : Fin g.slots) (f : HeightOneSpectrum (𝓞 K) → ℂ) :
    ∑ p ∈ primeWindow K S g ∅ Z i, f p.val =
      ∑ p ∈ windowPrimes K S (primeScale g Z),
        if (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) ≠ 0 then f p else 0 := by
  dsimp only [primeWindow]
  rw [Finset.sum_image (by
    intro a _ b _ h
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv)]
  dsimp only
  rw [Finset.sum_attach, windowPrimes, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h1 : p ∈ S
  · simp [h1]
  · by_cases h2 : (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) = 0
    · simp [h1, h2]
    · simp [h1, h2]

omit [Fintype S] in
theorem normalizerSlot_eq (Z : ℝ) (i : Fin g.slots) :
    normalizerSlot K S g ∅ Z i = (slotReal K S g Z i : ℂ) := by
  have hterm : ∀ p : HeightOneSpectrum (𝓞 K),
      (if (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) ≠ 0 then
        (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) *
          (p.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) else 0) =
        ((((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z)).re *
          (p.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) := by
    intro p
    set a := (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / primeScale g Z) with ha
    have hw : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [ha, g.real_valued i])
    have hpow : (p.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) =
        (((p.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
      simp
    by_cases h0 : a = 0
    · simp [h0]
    · simp only [ne_eq, h0, not_false_eq_true, ↓reduceIte]
      rw [hpow, Complex.ofReal_mul, ← hw]
  unfold normalizerSlot slotReal
  simp only [windowWeight]
  rw [sum_primeWindow K S g Z i (fun p => (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) /
      primeScale g Z) * (p.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ))), Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun p _ => hterm p)

theorem primeScale_pow (Z : ℝ) (hZ : 0 ≤ Z) :
    (primeScale g Z ^ (1 / 6 : ℝ)) ^ g.slots = Z ^ (1 / 36 : ℝ) := by
  have hslots : (g.slots : ℝ) ≠ 0 := by exact_mod_cast g.slots_pos.ne'
  unfold primeScale
  rw [← Real.rpow_mul hZ, ← Real.rpow_natCast, ← Real.rpow_mul hZ]
  congr 1
  field_simp
  norm_num

/-- Each slot is eventually at least `c · X^{1/6} / log X`, `X = primeScale g Z`. -/
theorem slotReal_lower (i : Fin g.slots) :
    ∃ c Z₀ : ℝ, 0 < c ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      1 < primeScale g Z ∧
      c * primeScale g Z ^ (1 / 6 : ℝ) / Real.log (primeScale g Z) ≤ slotReal K S g Z i := by
  obtain ⟨c, X₀, hc, hX₀, hpit⟩ := window_prime_lower K S (g.weight i) (g.real_valued i)
    (g.nonnegative i) (g.nonzero i) (g.support_annular i)
  have hslots : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hs0 : (g.slots : ℝ) ≠ 0 := hslots.ne'
  have hexp : (0 : ℝ) < (1 / 6 : ℝ) / g.slots := div_pos (by norm_num) hslots
  refine ⟨c * (2 : ℝ) ^ (-(5 / 6 : ℝ)), X₀ ^ (6 * (g.slots : ℝ)),
    mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _),
    Real.one_lt_rpow hX₀ (by linarith), fun Z hZ => ?_⟩
  have hZpos : 0 < Z := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hZ
  have hXX₀ : X₀ ≤ primeScale g Z := by
    have h1 : (X₀ ^ (6 * (g.slots : ℝ))) ^ ((1 / 6 : ℝ) / g.slots) = X₀ := by
      rw [← Real.rpow_mul (by linarith)]
      have : 6 * (g.slots : ℝ) * ((1 / 6 : ℝ) / g.slots) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc X₀ = (X₀ ^ (6 * (g.slots : ℝ))) ^ ((1 / 6 : ℝ) / g.slots) := h1.symm
      _ ≤ Z ^ ((1 / 6 : ℝ) / g.slots) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hZ hexp.le
  set X := primeScale g Z with hXdef
  have hX1 : 1 < X := lt_of_lt_of_le hX₀ hXX₀
  have hXpos : 0 < X := by linarith
  refine ⟨hX1, ?_⟩
  have hsum := hpit X hXX₀
  -- every term with a nonzero weight has norm below 2X
  have hterm : ∀ p ∈ windowPrimes K S X,
      ((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / X)).re * (2 * X) ^ (-(5 / 6 : ℝ)) ≤
        ((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / X)).re *
          (p.asIdeal.absNorm : ℝ) ^ (-(5 / 6 : ℝ)) := by
    intro p _
    by_cases h0 : (g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / X) = 0
    · simp [h0]
    · have hmem := g.support_annular i h0
      have hN1 : X < (p.asIdeal.absNorm : ℝ) := by
        have := (lt_div_iff₀ hXpos).mp hmem.1
        linarith
      have hN2 : (p.asIdeal.absNorm : ℝ) < 2 * X := (div_lt_iff₀ hXpos).mp hmem.2
      apply mul_le_mul_of_nonneg_left _ (g.nonnegative i _)
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hN2.le (by norm_num)
  have h2X : (2 * X) ^ (-(5 / 6 : ℝ)) * X = (2 : ℝ) ^ (-(5 / 6 : ℝ)) * X ^ (1 / 6 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hXpos.le, mul_assoc]
    congr 1
    rw [← Real.rpow_add_one hXpos.ne']
    norm_num
  calc c * (2 : ℝ) ^ (-(5 / 6 : ℝ)) * X ^ (1 / 6 : ℝ) / Real.log X
      = c * ((2 : ℝ) ^ (-(5 / 6 : ℝ)) * X ^ (1 / 6 : ℝ)) / Real.log X := by ring
    _ = c * ((2 * X) ^ (-(5 / 6 : ℝ)) * X) / Real.log X := by rw [h2X]
    _ = (2 * X) ^ (-(5 / 6 : ℝ)) * (c * X / Real.log X) := by ring
    _ ≤ (2 * X) ^ (-(5 / 6 : ℝ)) *
        ∑ p ∈ windowPrimes K S X, ((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / X)).re :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by linarith) _)
    _ = ∑ p ∈ windowPrimes K S X,
        ((g.weight i).toFun ((p.asIdeal.absNorm : ℝ) / X)).re * (2 * X) ^ (-(5 / 6 : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    _ ≤ slotReal K S g Z i := Finset.sum_le_sum hterm

theorem primeNormalizer_eq (Z : ℝ) (hZ : 0 < Z) :
    primeNormalizer K S g ∅ Z =
      ((Z ^ (-(1 / 36 : ℝ)) * ∏ i, slotReal K S g Z i : ℝ) : ℂ) := by
  unfold primeNormalizer
  rw [g.slots_even.neg_one_pow, one_mul]
  simp only [normalizerSlot_eq]
  have hZc : (Z : ℂ) ^ (-(1 / 36 : ℂ)) = ((Z ^ (-(1 / 36 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hZ.le]
    simp
  rw [hZc, Complex.ofReal_mul, Complex.ofReal_prod]

/-- A common threshold for all slots. -/
theorem exists_common_threshold :
    ∃ c : Fin g.slots → ℝ, ∃ Z₀ : ℝ, (∀ i, 0 < c i) ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      1 < primeScale g Z ∧ ∀ i,
        c i * primeScale g Z ^ (1 / 6 : ℝ) / Real.log (primeScale g Z) ≤ slotReal K S g Z i := by
  choose c Z₀ hc hZ₀ hlow using fun i => slotReal_lower K S g i
  let i₀ : Fin g.slots := ⟨0, g.slots_pos⟩
  have hle : ∀ j, Z₀ j ≤ ∑ i, Z₀ i := fun j =>
    Finset.single_le_sum (fun k _ => (zero_lt_one.trans (hZ₀ k)).le) (Finset.mem_univ j)
  refine ⟨c, ∑ i, Z₀ i, hc, lt_of_lt_of_le (hZ₀ i₀) (hle i₀), fun Z hZ =>
    ⟨(hlow i₀ Z (le_trans (hle i₀) hZ)).1, fun i => (hlow i Z (le_trans (hle i) hZ)).2⟩⟩

/-- PR-NORMALIZER-POSITIVE, from PR-WINDOW-PIT. -/
theorem normalizer_positive :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → 0 < (primeNormalizer K S g ∅ Z).re := by
  obtain ⟨c, Z₀, hc, hZ₀, hlow⟩ := exists_common_threshold K S g
  refine ⟨Z₀, hZ₀.le, fun Z hZ => ?_⟩
  have hZpos : 0 < Z := by linarith
  obtain ⟨hX1, hb⟩ := hlow Z hZ
  have hXpos : 0 < primeScale g Z := by linarith
  have hlog : 0 < Real.log (primeScale g Z) := Real.log_pos hX1
  rw [primeNormalizer_eq K S g Z hZpos, Complex.ofReal_re]
  apply mul_pos (Real.rpow_pos_of_pos hZpos _)
  apply Finset.prod_pos
  intro i _
  exact lt_of_lt_of_le (div_pos (mul_pos (hc i) (Real.rpow_pos_of_pos hXpos _)) hlog) (hb i)

/-- PR-NORMALIZER-SMALLPOWER, from PR-WINDOW-PIT. -/
theorem normalizer_smallPower : ∀ ε : ℝ, 0 < ε →
    (fun Z => (primeNormalizer K S g ∅ Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε) := by
  intro ε hε
  obtain ⟨c, Z₀, hc, hZ₀, hlow⟩ := exists_common_threshold K S g
  have hCpos : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
  have hbound : (fun Z => (primeNormalizer K S g ∅ Z)⁻¹) =O[atTop]
      (fun Z : ℝ => Real.log Z ^ (g.slots : ℝ)) := by
    apply IsBigO.of_bound (∏ i, c i)⁻¹
    filter_upwards [eventually_ge_atTop Z₀] with Z hZ
    have hZpos : 0 < Z := by linarith
    have hZ1 : 1 < Z := by linarith
    obtain ⟨hX1, hb⟩ := hlow Z hZ
    have hXpos : 0 < primeScale g Z := by linarith
    have hlogX : 0 < Real.log (primeScale g Z) := Real.log_pos hX1
    have hlogZ : 0 < Real.log Z := Real.log_pos hZ1
    have hlogXZ : Real.log (primeScale g Z) ≤ Real.log Z := by
      unfold primeScale
      rw [Real.log_rpow hZpos]
      have hslots : (1 : ℝ) ≤ g.slots := by exact_mod_cast g.slots_pos
      have h1 : (1 / 6 : ℝ) / g.slots ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith
    set L := Real.log (primeScale g Z) with hL
    have hLs : 0 < L ^ g.slots := pow_pos hlogX _
    have hprod : (∏ i, c i) * (L ^ g.slots)⁻¹ ≤
        Z ^ (-(1 / 36 : ℝ)) * ∏ i, slotReal K S g Z i := by
      have hle : ∏ i, (c i * primeScale g Z ^ (1 / 6 : ℝ) / L) ≤ ∏ i, slotReal K S g Z i :=
        Finset.prod_le_prod₀
          (fun i _ => (div_pos (mul_pos (hc i) (Real.rpow_pos_of_pos hXpos _)) hlogX).le)
          (fun i _ => hb i)
      have hval : Z ^ (-(1 / 36 : ℝ)) * ∏ i, (c i * primeScale g Z ^ (1 / 6 : ℝ) / L) =
          (∏ i, c i) * (L ^ g.slots)⁻¹ := by
        rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, primeScale_pow g Z hZpos.le, Real.rpow_neg hZpos.le]
        have hZr : Z ^ (1 / 36 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hZpos _).ne'
        have hLs' : L ^ g.slots ≠ 0 := hLs.ne'
        field_simp
      rw [← hval]
      exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hZpos.le _)
    have hlow' : 0 < (∏ i, c i) * (L ^ g.slots)⁻¹ := mul_pos hCpos (inv_pos.mpr hLs)
    have hNpos : 0 < Z ^ (-(1 / 36 : ℝ)) * ∏ i, slotReal K S g Z i := lt_of_lt_of_le hlow' hprod
    rw [primeNormalizer_eq K S g Z hZpos, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos), Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hlogZ _), Real.rpow_natCast]
    calc (Z ^ (-(1 / 36 : ℝ)) * ∏ i, slotReal K S g Z i)⁻¹
        ≤ ((∏ i, c i) * (L ^ g.slots)⁻¹)⁻¹ := inv_anti₀ hlow' hprod
      _ = (∏ i, c i)⁻¹ * L ^ g.slots := by rw [mul_inv, inv_inv]
      _ ≤ (∏ i, c i)⁻¹ * Real.log Z ^ g.slots :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogX.le hlogXZ _)
            (inv_nonneg.mpr hCpos.le)
  exact hbound.trans (isLittleO_log_rpow_rpow_atTop (g.slots : ℝ) hε).isBigO

end Derivation

end HeckeSkeleton.PrimeNormalizer
