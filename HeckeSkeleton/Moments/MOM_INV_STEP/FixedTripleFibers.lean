module

public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr

/-!
# Reconstruction fibers at a fixed puncture triple

This is the second-transform fiber argument of
`openai/math/lean/OAI/NumberTheory/DirichletL/Inversion/SecondFibers.lean`,
for the actual integral ideals of an arbitrary number field.

Rows retain both their ideal and their sector. Multiplication by the two
fixed row factors acts through an explicit sector equivalence; there is no
assumption of a multiplicative choice of generators in the ring of integers.
The count holds at every fixed sector, even for an infinite sector type.
A finite sector sum can therefore be restored by its actual finite cardinal.

The source filters retain the original slot lists and the original-support
predicate supplied by the caller. The explicit signed zero factors below
force a squarefree child label before they are bounded by one. The divisor
bound separates the child-label weight from the frozen-triple weight before
any positive ranges are enlarged.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers

open NumberField IsDedekindDomain
open DedekindZetaZeroFree.LargeSieve
open scoped BigOperators Classical NumberField

variable (K : Type*) [Field K] [NumberField K]

@[ext] structure OuterTriple where
  q0 : Ideal (𝓞 K)
  quotient : Ideal (𝓞 K)
  residual : Ideal (𝓞 K)

@[ext] structure SecondTuple (Sector : Type*) (Jo Jn : ℕ) where
  outer : OuterTriple K
  core : Fin 8 → Ideal (𝓞 K)
  commonResidual : Ideal (𝓞 K)
  cubeResidual : Ideal (𝓞 K)
  secondCube : Ideal (𝓞 K)
  extractedCommon : Ideal (𝓞 K)
  frequency : Ideal (𝓞 K) × Sector
  oldAssigned : Fin Jo → HeightOneSpectrum (𝓞 K)
  newAssigned : Fin Jn → HeightOneSpectrum (𝓞 K)

variable {K} {Sector : Type*}

/-- Exact arithmetic relations in the second reconstruction. The eight
core factors are `J, C, d₂, s, b₁, A₁, A₂, dₖ`; the three frozen ideals are
`q₀, t', g'/d₂`. The sector action is fixed independently of the source tuple. -/
structure Valid
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    {Jo Jn : ℕ} (x : SecondTuple K Sector Jo Jn)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) : Prop where
  outer_eq : x.outer = γ
  label : x.core 0 * x.core 1 * x.core 2 * x.commonResidual = f
  j_split : x.core 3 * x.cubeResidual = x.core 0
  b_split : x.core 4 * x.secondCube = γ.q0 ^ 2 * x.cubeResidual ^ 2 * x.core 3
  a1 : x.core 5 ∣ (x.core 4 * x.secondCube).radical
  a2 : x.core 6 ∣ (x.core 4 * x.secondCube).radical
  d : x.core 7 ∣ x.core 1 * (x.core 4 * x.secondCube).radical
  extracted_eq : x.core 2 * γ.residual = x.extractedCommon
  row_eq : x.core 7 * x.core 2 * x.frequency.1 = k.1
  sector_eq : sectorTransport (x.core 7) (x.core 2) x.frequency.2 = k.2
  old_dvd : ∀ i, (x.oldAssigned i).asIdeal ∣ γ.q0 * f * γ.quotient
  new_dvd : ∀ i, (x.newAssigned i).asIdeal ∣ f * γ.residual

variable {sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}

local instance : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)

lemma divisors_mul_image (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I * J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1 * p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A, B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I * J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

lemma divisor_card_pos (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

/-- Every fixed positive divisor power has an arbitrarily small norm
exponent. This uses the repository's proved ideal divisor estimate. -/
theorem exists_divisor_power_bound (p : ℕ) (hp : 0 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ I : Ideal (𝓞 K),
      ((idealDivisors I).card : ℝ) ^ p ≤ B * (Ideal.absNorm I : ℝ) ^ ε := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨B₀, hB₀, hb⟩ := ideal_divisor_count_le_rpow K
    (ε / (p : ℝ)) (div_pos hε hpR)
  refine ⟨B₀ ^ p, one_le_pow₀ hB₀, ?_⟩
  intro I
  have hdiv : ((idealDivisors I).card : ℝ) ≤
      B₀ * (Ideal.absNorm I : ℝ) ^ (ε / (p : ℝ)) := by
    simpa only [idealDivisorCount] using hb I
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv p
  have hexp : ((Ideal.absNorm I : ℝ) ^ (ε / (p : ℝ))) ^ p =
      (Ideal.absNorm I : ℝ) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      div_mul_cancel₀ _ (ne_of_gt hpR)]
  simpa only [mul_pow, hexp] using hpow

/-- Exactly the frozen-triple part of the reconstruction divisor bound. -/
def tripleDivisorWeight (slotCap : ℕ) (γ : OuterTriple K) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ) ^ (5 + 2 * slotCap) *
    ((idealDivisors γ.quotient).card : ℝ) ^ (2 * slotCap) *
    ((idealDivisors γ.residual).card : ℝ) ^ (2 * slotCap)

theorem tripleDivisorWeight_nonneg (slotCap : ℕ) (γ : OuterTriple K) :
    0 ≤ tripleDivisorWeight slotCap γ := by
  unfold tripleDivisorWeight
  positivity

theorem exists_triple_weight_small_power (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ γ : OuterTriple K,
      γ.q0 ≠ 0 → γ.quotient ≠ 0 → γ.residual ≠ 0 →
      tripleDivisorWeight slotCap γ ≤
        B * ((Ideal.absNorm γ.q0 : ℝ) * (Ideal.absNorm γ.quotient : ℝ) *
          (Ideal.absNorm γ.residual : ℝ)) ^ ε := by
  obtain ⟨A, hA, hp⟩ := exists_divisor_power_bound
    (K := K) (5 + 2 * slotCap) (by omega) ε hε
  refine ⟨A ^ 3, one_le_pow₀ hA, ?_⟩
  intro γ hq ht hr
  have hsmall (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
      ((idealDivisors I).card : ℝ) ^ (2 * slotCap) ≤ A * (Ideal.absNorm I : ℝ) ^ ε := by
    apply le_trans _ (hp I)
    apply pow_le_pow_right₀
    · exact_mod_cast divisor_card_pos I hI
    · omega
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hright (I : Ideal (𝓞 K)) : 0 ≤ A * (Ideal.absNorm I : ℝ) ^ ε :=
    mul_nonneg hA0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpair := mul_le_mul (hp γ.q0) (hsmall γ.quotient ht)
    (pow_nonneg (Nat.cast_nonneg _) _) (hright γ.q0)
  have hall := mul_le_mul hpair (hsmall γ.residual hr)
    (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (hright γ.q0) (hright γ.quotient))
  calc
    _ ≤ (A * (Ideal.absNorm γ.q0 : ℝ) ^ ε) *
        (A * (Ideal.absNorm γ.quotient : ℝ) ^ ε) *
        (A * (Ideal.absNorm γ.residual : ℝ) ^ ε) := hall
    _ = A ^ 3 * ((Ideal.absNorm γ.q0 : ℝ) * (Ideal.absNorm γ.quotient : ℝ) *
        (Ideal.absNorm γ.residual : ℝ)) ^ ε := by
      rw [Real.mul_rpow (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _), Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      ring

lemma poisson_divisor_source (d C R rest B : Ideal (𝓞 K))
    (hR : R * rest = B.radical) (hd : d ∣ C * rest) : d ∣ C * B.radical := by
  apply hd.trans
  rw [← hR]
  exact mul_dvd_mul_left C (dvd_mul_left rest R)

lemma core_dvd_label {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) (i : Fin 4) :
    x.core ⟨i.val, by omega⟩ ∣ f := by
  have hJ : x.core 0 ∣ f := by
    rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  fin_cases i
  · exact hJ
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact (show x.core 3 ∣ x.core 0 from ⟨x.cubeResidual, hx.j_split.symm⟩).trans hJ

lemma common_label_dvd {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) :
    x.core 1 * x.core 0 ∣ f := by
  refine ⟨x.core 2 * x.commonResidual, ?_⟩
  rw [← hx.label]
  ring

theorem child_label_norm_eq {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    Ideal.absNorm f = Ideal.absNorm (x.core 1) * Ideal.absNorm (x.core 0) *
      Ideal.absNorm (x.core 2) * Ideal.absNorm x.commonResidual := by
  rw [← hx.label]
  simp only [map_mul]
  ring

theorem child_row_norm_eq {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    Ideal.absNorm k.1 = Ideal.absNorm (x.core 7) * Ideal.absNorm (x.core 2) *
      Ideal.absNorm x.frequency.1 := by
  rw [← hx.row_eq]
  simp only [map_mul]

theorem second_common_norm_eq {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    Ideal.absNorm x.extractedCommon =
      Ideal.absNorm (x.core 2) * Ideal.absNorm γ.residual := by
  rw [← hx.extracted_eq, map_mul]

theorem second_divisor_norm_le_common {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hg : x.extractedCommon ≠ 0) :
    Ideal.absNorm (x.core 2) ≤ Ideal.absNorm x.extractedCommon := by
  exact Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hg (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm (show x.core 2 ∣ x.extractedCommon from
      ⟨γ.residual, hx.extracted_eq.symm⟩))

lemma cube_product_dvd_square {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) :
    x.core 4 * x.secondCube ∣ (γ.q0 * x.core 0)^2 := by
  refine ⟨x.core 3, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

lemma cube_radical_dvd {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) :
    (x.core 4 * x.secondCube).radical ∣ γ.q0 * x.core 0 := by
  apply Ideal.dvd_iff_le.mpr
  have hle := Ideal.radical_mono (Ideal.dvd_iff_le.mp (cube_product_dvd_square hx))
  rw [Ideal.radical_pow (γ.q0 * x.core 0) (by decide : (2 : ℕ) ≠ 0)] at hle
  exact Ideal.le_radical.trans hle

lemma cube_factor_dvd_target {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) :
    x.core 4 ∣ (γ.q0 * f)^2 :=
  (dvd_mul_right _ _).trans ((cube_product_dvd_square hx).trans
    (pow_dvd_pow_of_dvd (mul_dvd_mul_left _ (core_dvd_label hx 0)) 2))

lemma core_dvd_outer_label {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k) (i : Fin 3) :
    x.core ⟨i.val+5, by omega⟩ ∣ γ.q0 * f := by
  have hrad : (x.core 4 * x.secondCube).radical ∣ γ.q0 * f :=
    (cube_radical_dvd hx).trans (mul_dvd_mul_left _ (core_dvd_label hx 0))
  fin_cases i
  · exact hx.a1.trans hrad
  · exact hx.a2.trans hrad
  · apply hx.d.trans
    apply (mul_dvd_mul_left (x.core 1) (cube_radical_dvd hx)).trans
    convert mul_dvd_mul_left γ.q0 (common_label_dvd hx) using 1
    ring

lemma core_ne_zero {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (i : Fin 8) : x.core i ≠ 0 := by
  have hd : x.core i ∣ (γ.q0*f)^2 := by
    by_cases hi : i.val < 4
    · exact (core_dvd_label hx ⟨i.val, hi⟩).trans
        ((dvd_mul_left _ _).trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
    · by_cases hi4 : i.val = 4
      · have he : i = 4 := Fin.ext hi4
        simpa only [he] using cube_factor_dvd_target hx
      · have he : (⟨(i.val-5)+5, by omega⟩ : Fin 8) = i := by
          apply Fin.ext
          dsimp
          omega
        exact (he ▸ core_dvd_outer_label hx ⟨i.val-5, by omega⟩).trans
          (dvd_pow_self _ (by decide : 2 ≠ 0))
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (pow_ne_zero 2 (mul_ne_zero hq hf)) hd

theorem valid_key_injective {Jo Jn : ℕ} (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) {x y : SecondTuple K Sector Jo Jn}
    (hx : Valid sectorTransport x γ f k) (hy : Valid sectorTransport y γ f k)
    (hc : x.core = y.core) (ho : x.oldAssigned = y.oldAssigned)
    (hn : x.newAssigned = y.newAssigned) : x = y := by
  have hcore (i : Fin 8) : x.core i = y.core i := congrFun hc i
  have hv : x.commonResidual = y.commonResidual := by
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero (core_ne_zero hx hf hq 0) (core_ne_zero hx hf hq 1))
      (core_ne_zero hx hf hq 2))
    exact hx.label.trans (by simpa only [hcore] using hy.label.symm)
  have hj : x.cubeResidual = y.cubeResidual := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 3)
    exact hx.j_split.trans (by simpa only [hcore] using hy.j_split.symm)
  have hb : x.secondCube = y.secondCube := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 4)
    exact hx.b_split.trans (by simpa only [hcore, hj] using hy.b_split.symm)
  have hg : x.extractedCommon = y.extractedCommon := by
    rw [← hx.extracted_eq, ← hy.extracted_eq, hcore]
  have hr : x.frequency = y.frequency := by
    apply Prod.ext
    · apply mul_left_cancel₀ (mul_ne_zero (core_ne_zero hx hf hq 7)
        (core_ne_zero hx hf hq 2))
      exact hx.row_eq.trans (by simpa only [hcore] using hy.row_eq.symm)
    · apply (sectorTransport (x.core 7) (x.core 2)).injective
      exact hx.sector_eq.trans (by simpa only [hcore] using hy.sector_eq.symm)
  exact SecondTuple.ext (hx.outer_eq.trans hy.outer_eq.symm) hc hv hj hb hg hr ho hn

theorem valid_tuple_card_le {Jo Jn : ℕ} (T : Finset (SecondTuple K Sector Jo Jn))
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid sectorTransport x γ f k) :
    T.card ≤ (idealDivisors f).card^4 * (idealDivisors ((γ.q0*f)^2)).card *
      (idealDivisors (γ.q0*f)).card^3 *
      (idealDivisors (γ.q0*f*γ.quotient)).card^Jo *
      (idealDivisors (f*γ.residual)).card^Jn := by
  let D := idealDivisors f
  let E := idealDivisors ((γ.q0*f)^2)
  let F := idealDivisors (γ.q0*f)
  let A := idealDivisors (γ.q0*f*γ.quotient)
  let B := idealDivisors (f*γ.residual)
  let Target := (Fin 4 → D) × E × (Fin 3 → F) × (Fin Jo → A) × (Fin Jn → B)
  let encode (x : T) : Target :=
    (fun i => ⟨x.val.core ⟨i.val, by omega⟩,
      (mem_idealDivisors hf).mpr (core_dvd_label (hT x.val x.property) i)⟩,
    ⟨x.val.core 4, (mem_idealDivisors (pow_ne_zero 2 (mul_ne_zero hq hf))).mpr
      (cube_factor_dvd_target (hT x.val x.property))⟩,
    (fun i => ⟨x.val.core ⟨i.val+5, by omega⟩,
      (mem_idealDivisors (mul_ne_zero hq hf)).mpr (core_dvd_outer_label (hT x.val x.property) i)⟩),
    (fun i => ⟨(x.val.oldAssigned i).asIdeal,
      (mem_idealDivisors (mul_ne_zero (mul_ne_zero hq hf) ht)).mpr
        ((hT x.val x.property).old_dvd i)⟩),
    (fun i => ⟨(x.val.newAssigned i).asIdeal,
      (mem_idealDivisors (mul_ne_zero hf hr)).mpr ((hT x.val x.property).new_dvd i)⟩))
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply valid_key_injective γ f k hf hq (hT x.val x.property) (hT y.val y.property)
    · funext i
      fin_cases i
      · exact congrArg (fun z : Target => (z.1 0).val) he
      · exact congrArg (fun z : Target => (z.1 1).val) he
      · exact congrArg (fun z : Target => (z.1 2).val) he
      · exact congrArg (fun z : Target => (z.1 3).val) he
      · exact congrArg (fun z : Target => z.2.1.val) he
      · exact congrArg (fun z : Target => (z.2.2.1 0).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 1).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 2).val) he
    · funext i
      apply HeightOneSpectrum.ext
      exact congrArg (fun z : Target => (z.2.2.2.1 i).val) he
    · funext i
      apply HeightOneSpectrum.ext
      exact congrArg (fun z : Target => (z.2.2.2.2 i).val) he
  simpa only [Target, D, E, F, A, B, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using Fintype.card_le_of_injective encode hi

lemma divisor_card_sq_le (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (idealDivisors (I^2)).card ≤ (idealDivisors I).card^2 := by
  simpa only [pow_two] using divisor_card_mul_le I I hI hI

theorem valid_tuple_card_le_separated {Jo Jn : ℕ} (T : Finset (SecondTuple K Sector Jo Jn))
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid sectorTransport x γ f k) :
    T.card ≤ (idealDivisors f).card^(9+Jo+Jn) * (idealDivisors γ.q0).card^(5+Jo) *
      (idealDivisors γ.quotient).card^Jo * (idealDivisors γ.residual).card^Jn := by
  let df := (idealDivisors f).card
  let dq := (idealDivisors γ.q0).card
  let dt := (idealDivisors γ.quotient).card
  let dr := (idealDivisors γ.residual).card
  have hqf : (idealDivisors (γ.q0*f)).card ≤ dq*df := divisor_card_mul_le _ _ hq hf
  have hsq : (idealDivisors ((γ.q0*f)^2)).card ≤ (dq*df)^2 :=
    (divisor_card_sq_le _ (mul_ne_zero hq hf)).trans (Nat.pow_le_pow_left hqf 2)
  have hold : (idealDivisors (γ.q0*f*γ.quotient)).card ≤ dq*df*dt :=
    (divisor_card_mul_le _ _ (mul_ne_zero hq hf) ht).trans (Nat.mul_le_mul_right _ hqf)
  have hnew : (idealDivisors (f*γ.residual)).card ≤ df*dr := divisor_card_mul_le _ _ hf hr
  apply (valid_tuple_card_le T γ f k hf hq ht hr hT).trans
  calc
    _ ≤ df^4 * (dq*df)^2 * (dq*df)^3 * (dq*df*dt)^Jo * (df*dr)^Jn := by
      gcongr
    _ = _ := by
      dsimp [df, dq, dt, dr]
      simp only [mul_pow, pow_add]
      ring

theorem valid_tuple_card_le_slot_cap {Jo Jn : ℕ} (T : Finset (SecondTuple K Sector Jo Jn))
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid sectorTransport x γ f k) (slotCap : ℕ) (ho : Jo ≤ 2*slotCap) (hn : Jn ≤ 2*slotCap) :
    T.card ≤ (idealDivisors f).card^(9+4*slotCap) * (idealDivisors γ.q0).card^(5+2*slotCap) *
      (idealDivisors γ.quotient).card^(2*slotCap) * (idealDivisors γ.residual).card^(2*slotCap) := by
  apply (valid_tuple_card_le_separated T γ f k hf hq ht hr hT).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos γ.q0 hq) (by omega)))
    (pow_le_pow_right₀ (divisor_card_pos γ.quotient ht) ho))
    (pow_le_pow_right₀ (divisor_card_pos γ.residual hr) hn)

theorem valid_label_squarefree {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k)
    (hJ : Squarefree (x.core 0)) (hC : Squarefree (x.core 1))
    (hg : Squarefree x.extractedCommon) (hv : Squarefree x.commonResidual)
    (hJC : IsCoprime (x.core 0) (x.core 1))
    (hgmask : IsCoprime x.extractedCommon (x.core 1 * x.core 0))
    (hvmask : IsCoprime x.commonResidual (x.extractedCommon * x.core 1 * x.core 0)) :
    Squarefree f := by
  have hdg : x.core 2 ∣ x.extractedCommon := ⟨γ.residual, hx.extracted_eq.symm⟩
  have hdJC : IsCoprime (x.core 2) (x.core 0 * x.core 1) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : (x.core 0 * x.core 1) * x.core 2 ∣
      x.extractedCommon * x.core 1 * x.core 0 := by
    convert mul_dvd_mul_left (x.core 0 * x.core 1) hdg using 1
    ring
  have hvJCd := hvmask.of_isCoprime_of_dvd_right hdiv
  rw [← hx.label]
  exact squarefree_mul_iff.mpr ⟨hvJCd.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨hdJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime, hJ, hC⟩,
      hg.squarefree_of_dvd hdg⟩, hv⟩

/-- The exact cube identity behind the count of the first frozen ideal.
The remaining squarefree factor is the odd cube support `s`. -/
theorem cube_quotient_label_square {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    (γ.q0 * x.core 0) ^ 2 = (x.core 4 * x.secondCube) * x.core 3 := by
  rw [hx.b_split, ← hx.j_split]
  ring

theorem cube_quotient_label_norm_eq {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    Ideal.absNorm γ.q0 ^ 2 * Ideal.absNorm (x.core 0) ^ 2 =
      Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube * Ideal.absNorm (x.core 3) := by
  have hn := congrArg (fun I : Ideal (𝓞 K) => Ideal.absNorm I)
    (cube_quotient_label_square hx)
  simpa only [map_mul, map_pow, mul_pow] using hn

/-- The odd cube support is contained in the first conductor. After this
local digit fact is supplied, the source gives the sharper `q₀` norm budget
which charges the conductor half-length and subtracts the label length. -/
theorem cube_quotient_label_norm_le {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (R : Ideal (𝓞 K))
    (hR : R ≠ 0) (hs : x.core 3 ∣ R) :
    Ideal.absNorm γ.q0 ^ 2 * Ideal.absNorm (x.core 0) ^ 2 ≤
      Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube * Ideal.absNorm R := by
  rw [cube_quotient_label_norm_eq hx]
  apply Nat.mul_le_mul_left
  exact Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hR (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hs)

/-- The reconstructed label `J` divides the original cube product, giving
the structural label-length cap before any annular errors are introduced. -/
theorem cube_label_dvd_original_product {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) :
    x.core 0 ∣ x.core 4 * x.secondCube := by
  refine ⟨γ.q0 ^ 2 * x.cubeResidual, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

theorem cube_label_norm_le {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k) (hb : x.core 4 * x.secondCube ≠ 0) :
    Ideal.absNorm (x.core 0) ≤ Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube := by
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm (cube_label_dvd_original_product hx))
  simpa only [map_mul] using hn

theorem cube_quotient_norm_sq_le {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) :
    Ideal.absNorm γ.q0 ^ 2 ≤ Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube := by
  have hj0 : x.cubeResidual ≠ 0 := by
    intro hz
    have he := hx.j_split
    rw [hz, mul_zero] at he
    exact core_ne_zero hx hf hq 0 he.symm
  have hp0 : x.core 4 * x.secondCube ≠ 0 := by
    rw [hx.b_split]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hj0))
      (core_ne_zero hx hf hq 3)
  have hdiv : γ.q0^2 ∣ x.core 4 * x.secondCube := by
    rw [hx.b_split]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hp0 (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [map_pow, map_mul] using hn

theorem cube_quotient_norm_le {Jo Jn : ℕ} {x : SecondTuple K Sector Jo Jn}
    {γ : OuterTriple K} {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (N : ℕ)
    (hpair : Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2) :
    Ideal.absNorm γ.q0 ≤ N := by
  have hh := (cube_quotient_norm_sq_le hx hf hq).trans hpair
  nlinarith

def originalSource {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) : Finset (SecondTuple K Sector Jo Jn) :=
  source.filter fun x => (∀ i, x.oldAssigned i ∈ oldLists i) ∧
    (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x

def sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) : Finset (OuterTriple K) :=
  (originalSource source oldLists newLists keep).image SecondTuple.outer

theorem mem_sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) :
    γ ∈ sourceTriples source oldLists newLists keep ↔
      ∃ x ∈ source, (∀ i, x.oldAssigned i ∈ oldLists i) ∧
        (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x ∧ x.outer = γ := by
  simp only [sourceTriples, originalSource, Finset.mem_image, Finset.mem_filter]
  aesop

theorem sourceTriples_property {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (P : OuterTriple K → Prop)
    (hP : ∀ x ∈ originalSource source oldLists newLists keep, P x.outer)
    (γ : OuterTriple K) (hγ : γ ∈ sourceTriples source oldLists newLists keep) : P γ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
  exact hP x hx

/-- The frozen-triple count is a count of distinct triples, with all three
norm bounds obtained from original source witnesses. Reconstruction
multiplicity is kept in the separate fixed-triple fiber bound. -/
theorem sourceTriples_card_le_norm_box {Jo Jn : ℕ}
    (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (Xq Xt Xr : ℝ)
    (hsource : ∀ x ∈ originalSource source oldLists newLists keep,
      (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
      (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
      (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr) :
    (sourceTriples source oldLists newLists keep).card ≤
      (boundedNormIdeals K Xq).card * (boundedNormIdeals K Xt).card *
        (boundedNormIdeals K Xr).card := by
  let T := sourceTriples source oldLists newLists keep
  let Q := boundedNormIdeals K Xq
  let U := boundedNormIdeals K Xt
  let R := boundedNormIdeals K Xr
  have hb (γ : T) : (Ideal.absNorm γ.val.q0 : ℝ) ≤ Xq ∧
      (Ideal.absNorm γ.val.quotient : ℝ) ≤ Xt ∧
      (Ideal.absNorm γ.val.residual : ℝ) ≤ Xr :=
    sourceTriples_property source oldLists newLists keep
      (fun δ => (Ideal.absNorm δ.q0 : ℝ) ≤ Xq ∧
        (Ideal.absNorm δ.quotient : ℝ) ≤ Xt ∧ (Ideal.absNorm δ.residual : ℝ) ≤ Xr)
      hsource γ.val γ.property
  let encode (γ : T) : Q × U × R :=
    (⟨γ.val.q0, mem_boundedNormIdeals.mpr (hb γ).1⟩,
      ⟨γ.val.quotient, mem_boundedNormIdeals.mpr (hb γ).2.1⟩,
      ⟨γ.val.residual, mem_boundedNormIdeals.mpr (hb γ).2.2⟩)
  have hinj : Function.Injective encode := by
    intro γ δ h
    apply Subtype.ext
    apply OuterTriple.ext
    · exact congrArg (fun p : Q × U × R => p.1.val) h
    · exact congrArg (fun p : Q × U × R => p.2.1.val) h
    · exact congrArg (fun p : Q × U × R => p.2.2.val) h
  simpa only [T, Q, U, R, Fintype.card_coe, Fintype.card_prod, Nat.mul_assoc] using
    Fintype.card_le_of_injective encode hinj

/-- The ordinary norm count is applied once to the distinct frozen
triples. Its constant is uniform in all original slot lists and supports. -/
theorem exists_sourceTriples_count_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Jo Jn : ℕ}
      (source : Finset (SecondTuple K Sector Jo Jn))
      (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
      (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
      (keep : SecondTuple K Sector Jo Jn → Prop) (Xq Xt Xr : ℝ),
      1 ≤ Xq → 1 ≤ Xt → 1 ≤ Xr →
      (∀ x ∈ originalSource source oldLists newLists keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr) →
      ((sourceTriples source oldLists newLists keep).card : ℝ) ≤ C * Xq * Xt * Xr := by
  obtain ⟨A, hA, hcount⟩ := exists_ideal_count_bound K
  refine ⟨A ^ 3, one_le_pow₀ hA, ?_⟩
  intro Jo Jn source oldLists newLists keep Xq Xt Xr hq ht hr hsource
  have hcard : ((sourceTriples source oldLists newLists keep).card : ℝ) ≤
      ((boundedNormIdeals K Xq).card : ℝ) * ((boundedNormIdeals K Xt).card : ℝ) *
        ((boundedNormIdeals K Xr).card : ℝ) := by
    exact_mod_cast sourceTriples_card_le_norm_box source oldLists newLists keep
      Xq Xt Xr hsource
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hq0 : 0 ≤ A * Xq := mul_nonneg hA0 (le_trans zero_le_one hq)
  have ht0 : 0 ≤ A * Xt := mul_nonneg hA0 (le_trans zero_le_one ht)
  have hpair := mul_le_mul (hcount Xq hq) (hcount Xt ht) (Nat.cast_nonneg _) hq0
  have hall := mul_le_mul hpair (hcount Xr hr) (Nat.cast_nonneg _) (mul_nonneg hq0 ht0)
  calc
    _ ≤ ((boundedNormIdeals K Xq).card : ℝ) * ((boundedNormIdeals K Xt).card : ℝ) *
        ((boundedNormIdeals K Xr).card : ℝ) := hcard
    _ ≤ (A * Xq) * (A * Xt) * (A * Xr) := hall
    _ = A ^ 3 * Xq * Xt * Xr := by ring

/-- After dividing by its already extracted norm count, the measure on
distinct frozen triples has only a prescribed small-power mass. The
reconstruction label divisor weight is absent from this outer measure. -/
theorem exists_sourceTriples_normalized_mass_bound (slotCap : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (source : Finset (SecondTuple K Sector Jo Jn))
      (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
      (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
      (keep : SecondTuple K Sector Jo Jn → Prop) (Xq Xt Xr : ℝ),
      1 ≤ Xq → 1 ≤ Xt → 1 ≤ Xr →
      (∀ x ∈ originalSource source oldLists newLists keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr) →
      (∀ x ∈ originalSource source oldLists newLists keep,
        x.outer.q0 ≠ 0 ∧ x.outer.quotient ≠ 0 ∧ x.outer.residual ≠ 0) →
      (∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight slotCap γ) /
        (Xq * Xt * Xr) ≤ C * (Xq * Xt * Xr) ^ ε := by
  obtain ⟨A, hA, hcount⟩ := exists_sourceTriples_count_bound (K := K) (Sector := Sector)
  obtain ⟨B, hB, hweight⟩ := exists_triple_weight_small_power (K := K) slotCap ε hε
  refine ⟨A * B, mul_pos (lt_of_lt_of_le zero_lt_one hA)
    (lt_of_lt_of_le zero_lt_one hB), ?_⟩
  intro Jo Jn source oldLists newLists keep Xq Xt Xr hq ht hr hsource hsource0
  have hq0 : 0 ≤ Xq := le_trans zero_le_one hq
  have ht0 : 0 ≤ Xt := le_trans zero_le_one ht
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hXpos : 0 < Xq * Xt * Xr :=
    mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hq) (lt_of_lt_of_le zero_lt_one ht))
      (lt_of_lt_of_le zero_lt_one hr)
  have hpoint (γ : OuterTriple K) (hγ : γ ∈ sourceTriples source oldLists newLists keep) :
      tripleDivisorWeight slotCap γ ≤ B * (Xq * Xt * Xr) ^ ε := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
    have hb := hsource x hx
    have hz := hsource0 x hx
    have hpair := mul_le_mul hb.1 hb.2.1 (Nat.cast_nonneg _) hq0
    have hprod := mul_le_mul hpair hb.2.2 (Nat.cast_nonneg _) (mul_nonneg hq0 ht0)
    apply (hweight x.outer hz.1 hz.2.1 hz.2.2).trans
    apply mul_le_mul_of_nonneg_left _ hB0
    exact Real.rpow_le_rpow
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      hprod hε.le
  apply (div_le_iff₀ hXpos).mpr
  calc
    _ ≤ ∑ _γ ∈ sourceTriples source oldLists newLists keep, B * (Xq * Xt * Xr) ^ ε :=
      Finset.sum_le_sum hpoint
    _ = ((sourceTriples source oldLists newLists keep).card : ℝ) *
        (B * (Xq * Xt * Xr) ^ ε) := by simp
    _ ≤ (A * Xq * Xt * Xr) * (B * (Xq * Xt * Xr) ^ ε) :=
      mul_le_mul_of_nonneg_right (hcount source oldLists newLists keep Xq Xt Xr hq ht hr hsource)
        (mul_nonneg hB0 (Real.rpow_nonneg hXpos.le _))
    _ = (A * B * (Xq * Xt * Xr) ^ ε) * (Xq * Xt * Xr) := by ring

theorem sourceTriples_cube_norm_le {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (N : ℕ)
    (hsrc : ∀ x ∈ originalSource source oldLists newLists keep,
      ∃ f k, Valid sectorTransport x x.outer f k ∧ f ≠ 0 ∧ x.outer.q0 ≠ 0 ∧
        Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2)
    (γ : OuterTriple K) (hγ : γ ∈ sourceTriples source oldLists newLists keep) :
    Ideal.absNorm γ.q0 ≤ N := by
  apply sourceTriples_property source oldLists newLists keep
    (fun γ => Ideal.absNorm γ.q0 ≤ N) ?_ γ hγ
  intro x hx
  obtain ⟨f, k, hv, hf, hq, hpair⟩ := hsrc x hx
  exact cube_quotient_norm_le hv hf hq N hpair

def secondFiber
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)) {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector) :
    Finset (SecondTuple K Sector Jo Jn) :=
  (originalSource source oldLists newLists keep).filter (fun x => Valid sectorTransport x γ f k)

theorem secondFiber_outer_mem {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (x : SecondTuple K Sector Jo Jn) (hx : x ∈ secondFiber sectorTransport source oldLists newLists keep γ f k) :
    γ ∈ sourceTriples source oldLists newLists keep := by
  obtain ⟨hsrc, hv⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_image.mpr ⟨x, hsrc, hv.outer_eq⟩

theorem secondFiber_empty_of_not_sourceTriple {Jo Jn : ℕ}
    (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hγ : γ ∉ sourceTriples source oldLists newLists keep) :
    secondFiber sectorTransport source oldLists newLists keep γ f k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hγ (secondFiber_outer_mem source oldLists newLists keep γ f k x hx)

theorem secondFiber_card_le {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (slotCap : ℕ) (ho : Jo ≤ 2*slotCap) (hn : Jn ≤ 2*slotCap) :
    (secondFiber sectorTransport source oldLists newLists keep γ f k).card ≤
      (idealDivisors f).card^(9+4*slotCap) * (idealDivisors γ.q0).card^(5+2*slotCap) *
      (idealDivisors γ.quotient).card^(2*slotCap) * (idealDivisors γ.residual).card^(2*slotCap) :=
  valid_tuple_card_le_slot_cap _ γ f k hf hq ht hr
    (fun _x hx => (Finset.mem_filter.mp hx).2) slotCap ho hn

theorem secondFiber_weight_bound {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop) (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (slotCap : ℕ) (ho : Jo ≤ 2*slotCap) (hn : Jn ≤ 2*slotCap)
    (w : SecondTuple K Sector Jo Jn → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ secondFiber sectorTransport source oldLists newLists keep γ f k, ‖w x‖ ≤ C) :
    (∑ x ∈ secondFiber sectorTransport source oldLists newLists keep γ f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(9+4*slotCap) *
        ((idealDivisors γ.q0).card : ℝ)^(5+2*slotCap) *
        ((idealDivisors γ.quotient).card : ℝ)^(2*slotCap) *
        ((idealDivisors γ.residual).card : ℝ)^(2*slotCap) := by
  calc
    _ ≤ ∑ _x ∈ secondFiber sectorTransport source oldLists newLists keep γ f k, C := Finset.sum_le_sum hw
    _ = ((secondFiber sectorTransport source oldLists newLists keep γ f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(9+4*slotCap) * (idealDivisors γ.q0).card^(5+2*slotCap) *
        (idealDivisors γ.quotient).card^(2*slotCap) * (idealDivisors γ.residual).card^(2*slotCap) : ℕ) * C :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (secondFiber_card_le source oldLists newLists keep γ f k hf hq ht hr slotCap ho hn)) hC
    _ = _ := by push_cast; ring

/-- The zero factor of a common ideal puncture. -/
def idealCoprimeMask (R n : Ideal (𝓞 K)) : ℂ :=
  if IsCoprime n R then 1 else 0

@[simp] theorem idealCoprimeMask_ne_zero (R n : Ideal (𝓞 K)) :
    idealCoprimeMask R n ≠ 0 ↔ IsCoprime n R := by
  by_cases h : IsCoprime n R <;> simp [idealCoprimeMask, h]

theorem norm_idealCoprimeMask_le_one (R n : Ideal (𝓞 K)) :
    ‖idealCoprimeMask R n‖ ≤ 1 := by
  unfold idealCoprimeMask
  split_ifs <;> norm_num

/-- Passing to a radical preserves the exact coprimality predicate. -/
theorem isCoprime_radical_right_iff (A B : Ideal (𝓞 K)) :
    IsCoprime A B.radical ↔ IsCoprime A B := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro h
    apply Ideal.radical_eq_top.mp
    rw [Ideal.radical_sup]
    have hs : A.radical ⊔ B.radical = ⊤ := by
      apply top_unique
      rw [← h]
      exact sup_le_sup Ideal.le_radical le_rfl
    rw [hs, Ideal.radical_top]
  · intro h
    apply top_unique
    rw [← h]
    exact sup_le_sup le_rfl Ideal.le_radical

/-- The new common puncture depends only on the old puncture and the
frozen triple. It has no dependence on the new row or the averaged label. -/
def childPuncture (R : Ideal (𝓞 K)) (γ : OuterTriple K) : Ideal (𝓞 K) :=
  R * (γ.q0 * γ.quotient * γ.residual).radical

/-- All three frozen-triple zero factors survive exactly in the child
puncture, with overlapping prime supports allowed. -/
theorem childPuncture_mask (R n : Ideal (𝓞 K)) (γ : OuterTriple K) :
    idealCoprimeMask (childPuncture R γ) n =
      idealCoprimeMask R n * idealCoprimeMask γ.q0 n *
        idealCoprimeMask γ.quotient n * idealCoprimeMask γ.residual n := by
  simp only [idealCoprimeMask, childPuncture, IsCoprime.mul_right_iff,
    isCoprime_radical_right_iff]
  by_cases hR : IsCoprime n R <;>
    by_cases hq : IsCoprime n γ.q0 <;>
    by_cases ht : IsCoprime n γ.quotient <;>
    by_cases hr : IsCoprime n γ.residual <;> simp [hR, hq, ht, hr]

/-- The radical norm budget charges the old radical and the three frozen
ideals once each. It does not charge the averaged child label or its row. -/
theorem childPuncture_radical_norm_le (R : Ideal (𝓞 K)) (γ : OuterTriple K)
    (hR : R ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0)
    (hr : γ.residual ≠ 0) :
    Ideal.absNorm (childPuncture R γ).radical ≤
      Ideal.absNorm R.radical * Ideal.absNorm γ.q0 *
        Ideal.absNorm γ.quotient * Ideal.absNorm γ.residual := by
  have hrad : R.radical ≠ 0 := by
    intro hz
    apply hR
    have hle : R ≤ R.radical := Ideal.le_radical
    rw [hz] at hle
    exact le_bot_iff.mp hle
  have hprod : R.radical * (γ.q0 * γ.quotient * γ.residual) ≠ 0 :=
    mul_ne_zero hrad (mul_ne_zero (mul_ne_zero hq ht) hr)
  have heq : (childPuncture R γ).radical =
      (R.radical * (γ.q0 * γ.quotient * γ.residual)).radical := by
    simp only [childPuncture, Ideal.radical_mul, Ideal.radical_inf, Ideal.radical_idem]
  have hd : (childPuncture R γ).radical ∣
      R.radical * (γ.q0 * γ.quotient * γ.residual) := by
    rw [heq]
    exact Ideal.dvd_iff_le.mpr Ideal.le_radical
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hprod (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hd)
  simpa only [map_mul, Nat.mul_assoc] using hn

/-- The three source zeros which force the reconstructed child label to
be squarefree. They are retained on the signed outer scalar. -/
def labelZero {Jo Jn : ℕ} (x : SecondTuple K Sector Jo Jn) : ℂ :=
  idealCoprimeMask (x.core 1) (x.core 0) *
    idealCoprimeMask (x.core 1 * x.core 0) x.extractedCommon *
    idealCoprimeMask (x.extractedCommon * x.core 1 * x.core 0) x.commonResidual

/-- A live signed scalar supplies the original zeros, so its associated
child label is squarefree before the positive label range is enlarged. -/
theorem valid_label_squarefree_of_scalar_ne_zero {Jo Jn : ℕ}
    {x : SecondTuple K Sector Jo Jn} {γ : OuterTriple K}
    {f : Ideal (𝓞 K)} {k : Ideal (𝓞 K) × Sector}
    (hx : Valid sectorTransport x γ f k)
    (hJ : Squarefree (x.core 0)) (hC : Squarefree (x.core 1))
    (hg : Squarefree x.extractedCommon) (hv : Squarefree x.commonResidual)
    (scalar : ℂ) (hscalar : scalar * labelZero x ≠ 0) : Squarefree f := by
  have hz : labelZero x ≠ 0 := (mul_ne_zero_iff.mp hscalar).2
  simp only [labelZero, mul_ne_zero_iff, idealCoprimeMask_ne_zero, and_assoc] at hz
  exact valid_label_squarefree hx hJ hC hg hv hz.1 hz.2.1 hz.2.2

/-- After the squarefree-label and puncture information has been used,
the retained outer zero factor is a contraction. -/
theorem norm_labelZero_le_one {Jo Jn : ℕ} (x : SecondTuple K Sector Jo Jn) :
    ‖labelZero x‖ ≤ 1 := by
  simp only [labelZero, norm_mul]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 := by
      gcongr <;> exact norm_idealCoprimeMask_le_one _ _
    _ = 1 := by norm_num

end HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers

end
