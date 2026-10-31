import ExpansionDetector.IdealDirichletProduct
import ExpansionDetector.IdealTerminal

/-! The detector source is a genuine finite two-ideal sum even on a line
where the unsmoothed Dirichlet series need not converge. Finite support,
not continuation of a Cauchy product, justifies this identity. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open UniqueFactorizationMonoid
open scoped NumberField Classical BigOperators
variable {K : Type*} [Field K] [NumberField K]

def nonzeroTerminalSet (H : ℝ) : Finset (Ideal (𝓞 K)) :=
  (terminalIdealSet H).filter (fun I => I ≠ 0)

lemma mem_nonzeroTerminalSet (H : ℝ) (I : Ideal (𝓞 K)) :
    I ∈ nonzeroTerminalSet H ↔ Ideal.absNorm I ≤ ⌈2 * H⌉₊ ∧ I ≠ 0 := by
  simp only [nonzeroTerminalSet, Finset.mem_filter, mem_terminalIdealSet]

lemma large_norm_of_outside_nonzeroTerminalSet (H : ℝ) (I : Ideal (𝓞 K))
    (hI : I ≠ 0) (h : I ∉ nonzeroTerminalSet H) : 2 * H < (Ideal.absNorm I : ℝ) := by
  have hn : ⌈2 * H⌉₊ < Ideal.absNorm I := by
    apply Nat.lt_of_not_ge
    intro hh
    exact h ((mem_nonzeroTerminalSet H I).mpr ⟨hh, hI⟩)
  exact (Nat.le_ceil (2 * H)).trans_lt (by exact_mod_cast hn)

/-- Finite-support regrouping by the actual ideal multiplication fiber. -/
theorem finite_coefficient_pair_identity
    (w : Ideal (𝓞 K) →*₀ ℂ) (V : ℝ → ℂ) (D H : ℝ) (k : Ideal (𝓞 K) → ℂ)
    (hk : ∀ I : Ideal (𝓞 K), 2 * H < (Ideal.absNorm I : ℝ) → k I = 0) :
    (∑ I ∈ terminalIdealSet H, coefficient V D I * w I * k I) =
      ∑ d ∈ nonzeroTerminalSet H, ∑ a ∈ nonzeroTerminalSet H,
        ((moebius d : ℂ) * V ((Ideal.absNorm d : ℝ) / D) * w d) * w a * k (d * a) := by
  let F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p =>
    ((moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ) / D) * w p.1) * w p.2 * k (p.1 * p.2)
  have hfzero (p : Ideal (𝓞 K) × Ideal (𝓞 K))
      (hp : p ∉ nonzeroTerminalSet H ×ˢ nonzeroTerminalSet H) : F p = 0 := by
    rcases p with ⟨d, a⟩
    by_cases hd0 : d = 0
    · subst d
      simp only [F, map_zero, mul_zero, zero_mul]
    by_cases ha0 : a = 0
    · subst a
      simp only [F, map_zero, mul_zero, zero_mul]
    have hNd : (1 : ℝ) ≤ Ideal.absNorm d := by
      exact_mod_cast Nat.succ_le_iff.mpr
        (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0))
    have hNa : (1 : ℝ) ≤ Ideal.absNorm a := by
      exact_mod_cast Nat.succ_le_iff.mpr
        (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha0))
    have hlarge : 2 * H < (Ideal.absNorm (d * a) : ℝ) := by
      rw [map_mul, Nat.cast_mul]
      by_cases hd : d ∈ nonzeroTerminalSet H
      · have ha : a ∉ nonzeroTerminalSet H := fun ha => hp (Finset.mem_product.mpr ⟨hd, ha⟩)
        have hh := large_norm_of_outside_nonzeroTerminalSet H a ha0 ha
        exact hh.trans_le (le_mul_of_one_le_left (by positivity) hNd)
      · have hh := large_norm_of_outside_nonzeroTerminalSet H d hd0 hd
        exact hh.trans_le (le_mul_of_one_le_right (by positivity) hNa)
    simp only [F, hk _ hlarge, mul_zero]
  have hp : HasSum F (∑ p ∈ nonzeroTerminalSet H ×ˢ nonzeroTerminalSet H, F p) :=
    hasSum_sum_of_ne_finset_zero hfzero
  have hg := hp.tsum_fiberwise (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) => p.1 * p.2)
  have hgroup : HasSum (fun I : Ideal (𝓞 K) => coefficient V D I * w I * k I)
      (∑ p ∈ nonzeroTerminalSet H ×ˢ nonzeroTerminalSet H, F p) := by
    apply hg.congr_fun
    intro I
    symm
    change (∑' p : IdealMulFiber I, F p.val) = _
    have heq (p : IdealMulFiber I) : F p.val =
        (((moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) * w p.val.1) *
          w p.val.2) * k I := by dsimp [F]; rw [p.property]
    simp_rw [heq]
    rw [tsum_mul_right, convolution_fiber_eq]
  have hsource : HasSum (fun I : Ideal (𝓞 K) => coefficient V D I * w I * k I)
      (∑ I ∈ terminalIdealSet H, coefficient V D I * w I * k I) := by
    apply hasSum_sum_of_ne_finset_zero
    intro I hI
    have hn : ⌈2 * H⌉₊ < Ideal.absNorm I := by
      simpa only [mem_terminalIdealSet, not_le] using hI
    have hh : 2 * H < (Ideal.absNorm I : ℝ) :=
      (Nat.le_ceil (2 * H)).trans_lt (by exact_mod_cast hn)
    rw [hk I hh, mul_zero]
  have heq := hsource.unique hgroup
  simpa only [Finset.sum_product, F] using heq

def terminalProfile (V T : ℝ → ℂ) (D H Y q : ℝ) : ℂ :=
  (Real.exp (-q / Y) : ℂ) * (1 - V (2 * q / D)) * T (q / H)

/-- The literal finite terminal detector source equals its literal two-ideal
product form. The same inverse coefficient is used in both formulations. -/
theorem finite_terminal_as_pair
    (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ) (D H Y : ℝ) (hH : 0 < H)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑ I ∈ terminalIdealSet H,
      terminalTerm w V T D H (fun n => (n : ℂ) ^ (-s) * (Real.exp (-(n : ℝ) / Y) : ℂ)) I) =
      ∑ d ∈ nonzeroTerminalSet H, ∑ a ∈ nonzeroTerminalSet H,
        ((moebius d : ℂ) * V ((Ideal.absNorm d : ℝ) / D) * idealDirichletWeight w s d) *
          idealDirichletWeight w s a *
            terminalProfile V T D H Y ((Ideal.absNorm d : ℝ) * Ideal.absNorm a) := by
  have h := finite_coefficient_pair_identity (idealDirichletWeight w s) V D H
    (fun I => terminalProfile V T D H Y (Ideal.absNorm I)) (by
      intro I hI
      have hz := hTzero ((Ideal.absNorm I : ℝ) / H) ((le_div_iff₀ hH).mpr hI.le)
      simp only [terminalProfile, hz, mul_zero])
  calc
    _ = ∑ I ∈ terminalIdealSet H,
        coefficient V D I * idealDirichletWeight w s I *
          terminalProfile V T D H Y (Ideal.absNorm I) := by
      apply Finset.sum_congr rfl
      intro I _
      simp only [terminalTerm, smoothedTerm, idealDirichletWeight_apply, terminalProfile]
      ring
    _ = _ := by simpa only [map_mul, Nat.cast_mul] using h

end ExpansionDetector.IdealCutoff
