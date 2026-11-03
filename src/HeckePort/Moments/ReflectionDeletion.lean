import HeckePort.Moments.NaturalPrimitive
import HeckeGeneral.Analysis.IdealSummability

/-!
# Deleting finitely many primes from a reflected ideal sum

Port of the arithmetic part of openai/math `OAI/NumberTheory/DirichletL/Moments/ReflectionDeletion.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

openai works with `HeckeFamily.Character` `η`, whose ideal coefficient `idealCoeff η` is a
multiplicative function on ideals of norm at most one, with `η.excludePrimes S` having coefficient
`I ↦ if I is prime to every P ∈ S then idealCoeff η I else 0`
(`deleted_coefficient`), and with `HeckeDyadic.polynomial η false F X 0 0 =
(√X)⁻¹ ∑' I, idealCoeff η I * F (N I / X)` (`polynomial_plain`).  Here `idealCoeff η` is an
arbitrary function `a : Ideal (𝓞 K) → ℂ` with `IdealCoeff a` (multiplicative, norm at most
one), `excl S a` is the deleted coefficient, and `plainPoly a F X` is the plain polynomial.
Nonzero ideals are `{I // I ≠ ⊥}`; the summability of `N(I)⁻²` is
`HeckeGeneral.Analysis.summable_ideal_norm_rpow`.

Ported verbatim in shape: the splitting of ideals into a `S`-smooth and a `S`-outside part
(`splitEquiv`), `restoration_plain`, `normalized_restoration`, `finite_deletion_plain`,
`normalized_finite_deletion(_moebius)` and `deletion_reflection`; the latter takes the reflection
identity for the undeleted character as the hypothesis `hreflect`, exactly as openai does.

Not ported (`ℤ[ω]`-specific analytic input): `reflected_decayTwo` and
`reflected_normalized_restoration` (they use `paperRadialFourier`, the cubic radial Fourier
transform), and `primitive_deleted_reflection(_absolute)` (they use the Gauss-sum plain reflection
of `ComparisonReflection`, which in turn rests on the finite unit group `ℤ[ω]ˣ` of order six
and the radial Poisson formula for `ℤ[ω]`; the general-field analogue is the theta reflection
of the skeleton, TH-REFL-*).
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum

variable {K : Type*} [Field K] [NumberField K]

/-- Nonzero ideals. -/
abbrev NI (K : Type*) [Field K] [NumberField K] := {I : Ideal (𝓞 K) // I ≠ ⊥}

def inorm (I : NI K) : ℝ := Ideal.absNorm I.val

lemma inorm_pos (I : NI K) : 0 < inorm I := by
  unfold inorm
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => I.property (Ideal.absNorm_eq_zero_iff.mp hz))

def outside (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal (𝓞 K))) := {I : NI K // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal (𝓞 K))) := {I : NI K // outside S I.val}

def extract (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ((normalizedFactors I).filter (· ∉ S)).prod

lemma extract_factors (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) : extract S I ≠ ⊥ :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) : residual S I ≠ ⊥ :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal (𝓞 K))) (I : NI K) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal (𝓞 K))) (I : Ideal (𝓞 K)) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (I : NI K) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (I : Ideal (𝓞 K)) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    NI K ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

lemma outside_iff_coprime (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (I : NI K) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal (𝓞 K)) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal (𝓞 K))))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

/-- The properties of `idealCoeff η` used by openai's file. -/
structure IdealCoeff (a : Ideal (𝓞 K) → ℂ) : Prop where
  map_one : a 1 = 1
  mul : ∀ I J, a (I * J) = a I * a J
  norm_le_one : ∀ I, ‖a I‖ ≤ 1

/-- The coefficient of `η.excludePrimes S` (openai `deleted_coefficient`). -/
def excl (S : Finset (Ideal (𝓞 K))) (a : Ideal (𝓞 K) → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if outside S I then a I else 0

/-- openai `HeckeDyadic.polynomial η false F X 0 0` (`polynomial_plain`). -/
def plainPoly (a : Ideal (𝓞 K) → ℂ) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑' I : NI K, a I.val * F (inorm I / X)

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ^ 2 * ‖F x‖ ≤ C

lemma inverse_norm_sq_summable : Summable (fun I : NI K => (inorm I ^ 2)⁻¹) := by
  have h := (HeckeGeneral.Analysis.summable_ideal_norm_rpow K (σ := 2) (by norm_num)).subtype
    {I : Ideal (𝓞 K) | I ≠ ⊥}
  refine Summable.congr h (fun I => ?_)
  simp only [Function.comp_apply, inorm]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI K => ‖F (inorm I / X)‖) := by
  obtain ⟨C, hC, hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C * X ^ 2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (inorm_pos I) hX
  have h : ‖F (inorm I / X)‖ ≤ C / (inorm I / X) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (F : ℝ → ℂ) (hF : DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI K => a I.val * F (inorm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha.norm_le_one I.val)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI K × NI K => ‖F (inorm p.1 * inorm p.2 / X)‖) := by
  obtain ⟨C, hC, hb⟩ := hF
  have hs := (inverse_norm_sq_summable (K := K)).mul_of_nonneg (inverse_norm_sq_summable (K := K))
    (fun I => by have := inorm_pos I; positivity) (fun I => by have := inorm_pos I; positivity)
  apply (hs.mul_left (C * X ^ 2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (inorm_pos p.1) (inorm_pos p.2)) hX
  have h : ‖F (inorm p.1 * inorm p.2 / X)‖ ≤ C / (inorm p.1 * inorm p.2 / X) ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      a (p.1.val.val * p.2.val.val) * F (inorm p.1.val * inorm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val, p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha.norm_le_one _)

lemma outside_plain_tsum (a : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, a I.val.val * F (inorm I.val / X)) =
      ∑' I : NI K, excl S a I.val * F (inorm I / X) := by
  have he := tsum_subtype {I : NI K | outside S I.val}
    (fun I : NI K => a I.val * F (inorm I / X))
  change (∑' I : OutsideIdeal S, a I.val.val * F (inorm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  unfold excl
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, a (D.val.val * J.val.val) *
      F (inorm D.val * inorm J.val / X)) =
    a D.val.val *
      ∑' I : NI K, excl S a I.val * F (inorm I / (X / inorm D.val)) := by
  rw [← outside_plain_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [ha.mul, mul_assoc]
  congr 2
  have := (inorm_pos D.val).ne'
  field_simp

lemma restoration_plain_summable {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => a D.val.val *
      ∑' I : NI K, excl S a I.val * F (inorm I / (X / inorm D.val))) := by
  exact (restricted_pair_summable ha S F hF X hX).prod.congr
    (fun D => restoration_inner ha S F X D)

theorem restoration_plain {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI K, a I.val * F (inorm I / X)) =
      ∑' D : SmoothIdeal S, a D.val.val *
        ∑' I : NI K, excl S a I.val * F (inorm I / (X / inorm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI K => a I.val * F (inorm I / X))
  have hp := (restricted_pair_summable ha S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      inorm ((splitEquiv S hS).symm p) = inorm p.1.val * inorm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    a (p.1.val.val * p.2.val.val) * F (inorm p.1.val * inorm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner ha S F X D)

lemma normalization_factor (X N : ℝ) (hX : 0 < X) (hN : 0 < N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X / N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (a : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (F : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (D : SmoothIdeal S) :
    a D.val.val / (Real.sqrt (inorm D.val) : ℂ) *
      plainPoly (excl S a) F (X / inorm D.val) =
    (Real.sqrt X : ℂ)⁻¹ * (a D.val.val *
      ∑' I : NI K, excl S a I.val * F (inorm I / (X / inorm D.val))) := by
  unfold plainPoly
  have h := normalization_factor X (inorm D.val) hX (inorm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (a D.val.val *
    ∑' I : NI K, excl S a I.val * F (inorm I / (X / inorm D.val))) * h

theorem normalized_restoration {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => a D.val.val / (Real.sqrt (inorm D.val) : ℂ) *
      plainPoly (excl S a) F (X / inorm D.val)) ∧
    plainPoly a F X =
      ∑' D : SmoothIdeal S, a D.val.val / (Real.sqrt (inorm D.val) : ℂ) *
        plainPoly (excl S a) F (X / inorm D.val) := by
  constructor
  · apply ((restoration_plain_summable ha S F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term a S F X hX D).symm
  · unfold plainPoly
    rw [restoration_plain ha S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term a S F X hX D).symm

def outsideSum (a : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI K, (if outside S I.val then a I.val else 0) * F (inorm I / X)

lemma outsideSum_summable {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (S : Finset (Ideal (𝓞 K)))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI K => (if outside S I.val then a I.val else 0) * F (inorm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha.norm_le_one I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal (𝓞 K))) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal (𝓞 K)) (hP : Prime P) (hPS : P ∉ S) (I : Ideal (𝓞 K)) :
    outside S (P * I) ↔ outside S I := by
  have hn (Q : Ideal (𝓞 K)) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal (𝓞 K)) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI K, if P ∣ I.val then
      (if outside S I.val then a I.val else 0) * F (inorm I / X) else 0) =
    a P * outsideSum a S F (X / (P.absNorm : ℝ)) := by
  let f : NI K → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then a I.val else 0) * F (inorm I / X) else 0
  let g : NI K → ℂ := fun I => a P *
    ((if outside S I.val then a I.val else 0) * F (inorm I / (X / (P.absNorm : ℝ))))
  let e : NI K → NI K := fun I => ⟨P * I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI K) : f (e I) = g I := by
    have hn : inorm (e I) = (P.absNorm : ℝ) * inorm I := by
      simp only [inorm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      ha.mul, g]
    change (if outside S I.val then a P * a I.val else 0) *
      F (inorm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J, hJ⟩ := hd
      have hj : J ≠ ⊥ := by intro hz; exact I.property (by rw [hJ, hz, Ideal.mul_bot])
      have hei : e ⟨J, hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J, hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J, hj⟩, hg⟩, hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal (𝓞 K)) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    outsideSum a (insert P S) F X = outsideSum a S F X -
      a P * outsideSum a S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable ha S F hF X hX
  have hd : Summable (fun I : NI K => if P ∣ I.val then
      (if outside S I.val then a I.val else 0) * F (inorm I / X) else 0) := by
    exact hs.indicator {I : NI K | P ∣ I.val}
  rw [← prime_shift_tsum ha S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ ⊥ := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    outsideSum a S F X = ∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card * a (∏ P ∈ D, P) *
      (∑' I : NI K, a I.val * F (inorm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty =>
    have h1 := ha.map_one
    rw [Ideal.one_eq_top] at h1
    simp [outsideSum, outside, h1]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert ha S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, ha.mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D, Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D, Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (a : Ideal (𝓞 K) → ℂ) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0 < X) (D : NI K) :
    a D.val / (Real.sqrt (inorm D) : ℂ) * plainPoly a F (X / inorm D) =
    (Real.sqrt X : ℂ)⁻¹ * (a D.val *
      ∑' I : NI K, a I.val * F (inorm I / (X / inorm D))) := by
  unfold plainPoly
  have h := normalization_factor X (inorm D) hX (inorm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (a D.val *
    ∑' I : NI K, a I.val * F (inorm I / (X / inorm D))) * h

theorem normalized_finite_deletion {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    plainPoly (excl S a) F X =
      ∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card *
        (a (∏ P ∈ D, P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D, P) : ℝ) : ℂ)) *
        plainPoly a F (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)) := by
  have he : (∑' I : NI K, excl S a I.val * F (inorm I / X)) = outsideSum a S F X := by
    apply tsum_congr
    intro I
    rfl
  unfold plainPoly
  rw [he, finite_deletion_plain ha S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term a F X hX ⟨∏ P ∈ D, P, subset_product_nonzero D hDS⟩
  dsimp only [inorm] at ht
  dsimp only [plainPoly, inorm] at *
  linear_combination -(-1 : ℂ) ^ D.card * ht

lemma subset_product_moebius (D : Finset (Ideal (𝓞 K))) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D, P) : ℂ) = (-1 : ℂ) ^ D.card := by
  have hf : normalizedFactors (∏ P ∈ D, P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D, P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius {a : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F)
    (X : ℝ) (hX : 0 < X) :
    plainPoly (excl S a) F X =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D, P) : ℂ) *
        (a (∏ P ∈ D, P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D, P) : ℝ) : ℂ)) *
        plainPoly a F (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)) := by
  rw [normalized_finite_deletion ha S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

def reflectedTerm (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D, P) : ℂ) * a (∏ P ∈ D, P) * ai H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D, P) : ℝ) * inorm H.val) : ℂ) *
    plainPoly (excl S ai) F (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val))

lemma reflectedTerm_eq (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal (𝓞 K))) (H : SmoothIdeal S) :
    reflectedTerm a ai S F X Q D H =
      ((moebius (∏ P ∈ D, P) : ℂ) *
        (a (∏ P ∈ D, P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D, P) : ℝ) : ℂ))) *
      (ai H.val.val / (Real.sqrt (inorm H.val) : ℂ) *
        plainPoly (excl S ai) F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ))) / inorm H.val)) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ))) / inorm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

/-- openai `deletion_reflection`: the reflection identity of the undeleted pair `(a, ai)` is the
hypothesis `hreflect`. -/
theorem deletion_reflection {a ai : Ideal (𝓞 K) → ℂ} (hai : IdealCoeff ai)
    (S : Finset (Ideal (𝓞 K))) (ha : IdealCoeff a)
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hreflect : ∀ Y : ℝ, 0 < Y → plainPoly a W Y = G * plainPoly ai F (Q / Y))
    (X : ℝ) (hX : 0 < X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm a ai S F X Q D)) ∧
    plainPoly (excl S a) W X =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm a ai S F X Q D H := by
  have hnorm (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D, P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration hai S hS F hF
      (Q / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D, P) : ℂ) *
      (a (∏ P ∈ D, P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D, P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq a ai S F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius ha S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration hai S hS F hF (Q / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

end HeckePort.Moments

end
