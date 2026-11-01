import ExpansionDetector.IdealCutoff

/-! The terminal source is an actual finite ideal sum, while the two errors
are the full infinite smoothed series and the full exponential remainder.
This is the form needed by the Gamma zero detector. -/
noncomputable section
namespace ExpansionDetector.IdealCutoff
open scoped NumberField Classical BigOperators
variable {K : Type*} [Field K] [NumberField K]

def terminalIdealSet (H : ℝ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le ⌈2 * H⌉₊).toFinset

@[simp] lemma mem_terminalIdealSet (H : ℝ) (I : Ideal (𝓞 K)) :
    I ∈ terminalIdealSet H ↔ Ideal.absNorm I ≤ ⌈2 * H⌉₊ := by
  simp [terminalIdealSet]

lemma terminal_zero_outside (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (hH : 0 < H) (kernel : ℕ → ℂ)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (I : Ideal (𝓞 K)) (hI : I ∉ terminalIdealSet H) :
    terminalTerm w V T D H kernel I = 0 := by
  have hnat : ⌈2 * H⌉₊ < Ideal.absNorm I := by
    simpa only [mem_terminalIdealSet, not_le] using hI
  have hreal : 2 * H ≤ (Ideal.absNorm I : ℝ) :=
    (Nat.le_ceil (2 * H)).trans (by exact_mod_cast hnat.le)
  have hz : T ((Ideal.absNorm I : ℝ) / H) = 0 :=
    hTzero _ ((le_div_iff₀ hH).mpr hreal)
  simp [terminalTerm, hz]

/-- The terminal cutoff makes this support finite by the actual norm
finiteness theorem for integral ideals of a number field. -/
theorem terminal_tsum_eq_sum (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (hH : 0 < H) (kernel : ℕ → ℂ)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) :
    (∑' I : Ideal (𝓞 K), terminalTerm w V T D H kernel I) =
      ∑ I ∈ terminalIdealSet H, terminalTerm w V T D H kernel I := by
  exact tsum_eq_sum (fun I hI => terminal_zero_outside w V T D H hH kernel hTzero I hI)

lemma terminal_pointwise_identity (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ)
    (D H : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (kernel : ℕ → ℂ) (I : Ideal (𝓞 K)) :
    terminalTerm w V T D H kernel I =
      smoothedTerm w V D kernel I - (if I = 1 then kernel 1 else 0) -
        terminalRemainder w V T D H kernel I := by
  have h := smoothedTerm_tail w V D hD hV hVzero kernel I
  unfold terminalTerm terminalRemainder
  rw [← h]
  ring

/-- Exact infinite identity, followed by exact finite support reduction.
The errors are the same series estimated by the Mellin identity and the
exponential tail theorem. -/
theorem finite_terminal_identity_of_summable
    (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ) (D H : ℝ)
    (hD : 2 ≤ D) (hH : 0 < H)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (kernel : ℕ → ℂ)
    (hsm : Summable (smoothedTerm w V D kernel))
    (hrem : Summable (terminalRemainder w V T D H kernel)) :
    (∑ I ∈ terminalIdealSet H, terminalTerm w V T D H kernel I) =
      (∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I) - kernel 1 -
        ∑' I : Ideal (𝓞 K), terminalRemainder w V T D H kernel I := by
  rw [← terminal_tsum_eq_sum w V T D H hH kernel hTzero]
  simp_rw [terminal_pointwise_identity w V T D H hD hV hVzero kernel]
  have hu := (hasSum_ite_eq (1 : Ideal (𝓞 K)) (kernel 1)).summable
  rw [(hsm.sub hu).tsum_sub hrem, hsm.tsum_sub hu]
  simp

/-- A finite terminal source is large whenever the actual smoothed series
and the actual terminal remainder are small. These are raw errors with
explicit definitions, and are not hypotheses about a witness or spike. -/
theorem finite_terminal_lower_of_summable
    (w : Ideal (𝓞 K) →*₀ ℂ) (V T : ℝ → ℂ) (D H : ℝ)
    (hD : 2 ≤ D) (hH : 0 < H)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (kernel : ℕ → ℂ)
    (hsm : Summable (smoothedTerm w V D kernel))
    (hrem : Summable (terminalRemainder w V T D H kernel))
    (ε₁ ε₂ c : ℝ) (hunit : c + ε₁ + ε₂ ≤ ‖kernel 1‖)
    (hcontour : ‖∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I‖ ≤ ε₁)
    (htail : ‖∑' I : Ideal (𝓞 K), terminalRemainder w V T D H kernel I‖ ≤ ε₂) :
    c ≤ ‖∑ I ∈ terminalIdealSet H, terminalTerm w V T D H kernel I‖ := by
  have hi := finite_terminal_identity_of_summable w V T D H hD hH hV hVzero hTzero kernel hsm hrem
  have he : kernel 1 = (∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I) -
      (∑' I : Ideal (𝓞 K), terminalRemainder w V T D H kernel I) -
        (∑ I ∈ terminalIdealSet H, terminalTerm w V T D H kernel I) := by rw [hi]; ring
  have hn := norm_sub_le
    ((∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I) -
      ∑' I : Ideal (𝓞 K), terminalRemainder w V T D H kernel I)
    (∑ I ∈ terminalIdealSet H, terminalTerm w V T D H kernel I)
  rw [← he] at hn
  have hn' := norm_sub_le (∑' I : Ideal (𝓞 K), smoothedTerm w V D kernel I)
    (∑' I : Ideal (𝓞 K), terminalRemainder w V T D H kernel I)
  linarith

end ExpansionDetector.IdealCutoff
