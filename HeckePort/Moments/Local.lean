import HeckePort.Moments.Unequal

/-!
# Local correlations of equal prime-power moduli

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Local.lean` (revision `fd4aeeb2`).

The `Domain` section (full correlations of a modulus with itself are the correlations on the
residue ring) is verbatim.  The prime-power part is stated for an arbitrary prime element `p` of
`𝓞 K` and a residue character `ψ` modulo `p` lifted to the character of modulus `p ^ i`
(openai: `ψ = actualSextic (span {p}) ^ i`, and `supported_power_character_mk` is the hypothesis
`hχ`); the criterion for `ψ = 1` (openai: `6 ∣ i`, from `actualSextic_order_six`) is the
hypothesis `hψ1 : ψ = 1 ↔ triv`.  The results are
* `powerReduction_multiplicity`: the fibers of `𝓞/(p^i) → 𝓞/(p)` have `N p ^ (i - 1)` elements,
* `equal_prime_power_formula`, `equal_prime_power_unit_norm`, `equal_prime_power_norm_le`.
-/

noncomputable section
open scoped BigOperators Classical NumberField
namespace HeckePort.Moments.Local
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Fourier

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
theorem scaledResidue_one (q : A) (x : Residue q) :
    scaledResidue q 1 q (mul_one q).symm x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [scaledResidue_mk, one_mul]

theorem fullCorrelation_equal_divided (q k : A) (hq : q ≠ 0)
    [Fintype (Residue q)] (χ : MulChar (Residue q) ℂ) :
    fullModulusCorrelation q q χ χ (q * k) =
      fullCorrelation (fun x : Residue q => x) (fun y : Residue q => y) χ χ
        (Ideal.Quotient.mk _ k) := by
  have hs (x y : Residue q) :
      scaledResidue q q (q * q) rfl x - scaledResidue q q (q * q) (mul_comm _ _) y =
        Ideal.Quotient.mk _ (q * k) ↔ x - y = Ideal.Quotient.mk _ k := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence, ← map_sub, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rw [show q * x - q * y - q * k = q * (x - y - k) by ring]
    exact mul_dvd_mul_iff_left hq
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [hs]

end Domain

variable {K : Type*} [Field K] [NumberField K]

theorem powerReduction_multiplicity (p : 𝓞 K) {i : ℕ} (hi : 1 ≤ i)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] :
    reductionMultiplicity (frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))) =
      Ideal.absNorm (Ideal.span {p}) ^ (i - 1) := by
  have hcard (a : 𝓞 K) [Fintype (Residue a)] :
      Fintype.card (Residue a) = Ideal.absNorm (Ideal.span {a}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  apply reductionMultiplicity_eq_pow _ (Ideal.Quotient.factor_surjective _) (c := i)
  · rw [← hcard p]
    exact Fintype.card_pos
  · exact hi
  · rw [hcard, ← Ideal.span_singleton_pow, map_pow]
  · exact hcard p

theorem equal_prime_power_formula {i : ℕ} (p : 𝓞 K) [(Ideal.span {p}).IsMaximal] (hp0 : p ≠ 0)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] (hi : 1 ≤ i)
    (χi : MulChar (Residue (p ^ i)) ℂ) (ψ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : 𝓞 K, χi (Ideal.Quotient.mk _ x) = ψ (Ideal.Quotient.mk _ x))
    (triv : Prop) (hψ1 : ψ = 1 ↔ triv) (k : 𝓞 K) :
    fullModulusCorrelation (p ^ i) (p ^ i) χi χi (p ^ i * k) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) *
        (if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
         else if triv then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1) := by
  let : Field (Residue p) := Ideal.Quotient.field (Ideal.span {p})
  let π := frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have hχ' (x : Residue (p ^ i)) : χi x = ψ (π x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hχ x
  have hred := fullCorrelation_reduction_unit_right π hπ
    (1 : (Residue (p ^ i))ˣ) 1 (Ideal.Quotient.mk _ k) ψ ψ
  simp only [Units.val_one, map_one, one_mul] at hred
  have hk : Ideal.Quotient.mk (Ideal.span {p}) k = 0 ↔ p ∣ k := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [fullCorrelation_equal_divided _ _ (pow_ne_zero i hp0)]
  have hχfun : (χi : Residue (p ^ i) → ℂ) = (fun x => ψ (π x)) := funext hχ'
  rw [hχfun, hred]
  have he : fullCorrelation (fun x : Residue p => x) (fun x => x) ψ ψ
      (π (Ideal.Quotient.mk _ k)) = localCorrelation ψ 1 1 (Ideal.Quotient.mk _ k) := by
    simp only [localCorrelation, one_mul, π, frequencyReduction_mk]
  rw [he]
  rw [localCorrelation_units ψ one_ne_zero one_ne_zero, div_self one_ne_zero, map_one, one_mul,
    hk, hψ1, hcard]
  have hm : (reductionMultiplicity π : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) := by
    rw [powerReduction_multiplicity p hi, Nat.cast_pow]
  rw [hm]

theorem equal_prime_power_unit_norm {i : ℕ} (p : 𝓞 K) [(Ideal.span {p}).IsMaximal] (hp0 : p ≠ 0)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] (hi : 1 ≤ i)
    (χi : MulChar (Residue (p ^ i)) ℂ) (ψ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : 𝓞 K, χi (Ideal.Quotient.mk _ x) = ψ (Ideal.Quotient.mk _ x))
    (triv : Prop) (hψ1 : ψ = 1 ↔ triv) (hi6 : ¬ triv) (k : 𝓞 K) (hk : ¬ p ∣ k) :
    ‖fullModulusCorrelation (p ^ i) (p ^ i) χi χi (p ^ i * k)‖ =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) := by
  rw [equal_prime_power_formula p hp0 hi χi ψ hχ triv hψ1 k, ite_eq_right hk, ite_eq_right hi6]
  simp

theorem equal_prime_power_norm_le {i : ℕ} (p : 𝓞 K) [(Ideal.span {p}).IsMaximal] (hp0 : p ≠ 0)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] (hi : 1 ≤ i)
    (χi : MulChar (Residue (p ^ i)) ℂ) (ψ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : 𝓞 K, χi (Ideal.Quotient.mk _ x) = ψ (Ideal.Quotient.mk _ x))
    (triv : Prop) (hψ1 : ψ = 1 ↔ triv) (k : 𝓞 K) :
    ‖fullModulusCorrelation (p ^ i) (p ^ i) χi χi (p ^ i * k)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ i := by
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hN : (2 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) := by
    let : Field (Residue p) := Ideal.Quotient.field (Ideal.span {p})
    exact_mod_cast (show 2 ≤ Ideal.absNorm (Ideal.span {p}) from by
      rw [← hcard]
      exact Fintype.one_lt_card)
  have hsub (a : ℝ) (ha : 0 ≤ a) (haN : a ≤ Ideal.absNorm (Ideal.span {p})) :
      ‖(Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    have he : (Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ) =
        ((Ideal.absNorm (Ideal.span {p}) : ℝ) - a : ℝ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr haN)]
    linarith
  rw [equal_prime_power_formula p hp0 hi χi ψ hχ triv hψ1 k, norm_mul, norm_pow]
  have hnorm : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)‖ =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by simp
  rw [hnorm]
  have hb : ‖(if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
      else if triv then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    split_ifs
    · simpa using hsub 1 (by norm_num) (by linarith)
    · simpa using hsub 2 (by norm_num) hN
    · simpa using (show (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) by linarith)
  calc
    _ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) * Ideal.absNorm (Ideal.span {p}) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hi]

end HeckePort.Moments.Local

end
