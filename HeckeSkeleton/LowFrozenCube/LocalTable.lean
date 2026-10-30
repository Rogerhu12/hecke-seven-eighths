import HeckeSkeleton.LowFrozenCube.LocalCoefficients

/-!
# Explicit local-table progressions and their frozen majorant

The spherical scalar is the literal three-residue formula from the supplied
paper: its residue-zero sequence is geometric, its residue-one sequence is
the same geometric sequence times the first Whittaker scalar, and its
residue-two sequence is zero. The ordinary local coefficient uses the
exceptional digit 4 for positive valuations and arbitrary known zero-value
Gauss scalars. The cube progression and its product majorant are proved here.
-/

namespace HeckeSkeleton.LowFrozenCube.LocalTable

open scoped BigOperators Classical

noncomputable section

/-- Here `first` is `q^(-1/2) * gamma₂`; keeping it as a scalar makes clear
that the progression identity is independent of the Gauss normalization. -/
def sphericalScalar (q first : ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (q⁻¹) ^ (e / 3)
  else if e % 3 = 1 then (q⁻¹) ^ (e / 3) * first
  else 0

def ordinaryScalar (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e : ℕ) : ℂ :=
  if e = 0 then atZero j
  else if j = 4 then prefactor * sphericalScalar q first e
  else 0

@[simp] theorem sphericalScalar_zero (q first : ℂ) :
    sphericalScalar q first 0 = 1 := by simp [sphericalScalar]

@[simp] theorem sphericalScalar_one (q first : ℂ) :
    sphericalScalar q first 1 = first := by simp [sphericalScalar]

@[simp] theorem sphericalScalar_three (q first : ℂ) :
    sphericalScalar q first 3 = q⁻¹ := by simp [sphericalScalar]

theorem sphericalScalar_add_cube (q first : ℂ) (e x : ℕ) :
    sphericalScalar q first (e + 3 * x) =
      sphericalScalar q first e * (q⁻¹) ^ x := by
  have hmod : (e + 3 * x) % 3 = e % 3 := by omega
  have hdiv : (e + 3 * x) / 3 = e / 3 + x := by omega
  simp only [sphericalScalar, hmod, hdiv, pow_add]
  split_ifs <;> ring

theorem sphericalScalar_residue_two (q first : ℂ) (e : ℕ)
    (he : e % 3 = 2) : sphericalScalar q first e = 0 := by
  simp [sphericalScalar, he]

theorem ordinaryScalar_add_cube (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e x : ℕ) (he : 0 < e) :
    ordinaryScalar q first prefactor atZero j (e + 3 * x) =
      ordinaryScalar q first prefactor atZero j e * (q⁻¹) ^ x := by
  have he0 : e ≠ 0 := by omega
  have hex0 : e + 3 * x ≠ 0 := by omega
  simp only [ordinaryScalar, if_neg he0, if_neg hex0]
  split_ifs
  · rw [sphericalScalar_add_cube]
    ring
  · ring

/-- The forbidden residue is genuinely zero in the explicit local table. -/
theorem ordinaryScalar_residue_two (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e : ℕ) (he : e % 3 = 2) : ordinaryScalar q first prefactor atZero j e = 0 := by
  have he0 : e ≠ 0 := by omega
  simp [ordinaryScalar, he0, sphericalScalar_residue_two q first e he]

theorem ordinaryScalar_nonzero_admissible (q first prefactor : ℂ)
    (atZero : ℕ → ℂ) (j e : ℕ)
    (he : ordinaryScalar q first prefactor atZero j e ≠ 0) :
    AdmissibleExponent e := by
  have hmod : e % 3 < 3 := Nat.mod_lt _ (by decide)
  have hn : e % 3 ≠ 2 := by
    intro h
    exact he (ordinaryScalar_residue_two q first prefactor atZero j e h)
  unfold AdmissibleExponent
  omega

theorem ordinaryScalar_positive_only_four (q first prefactor : ℂ)
    (atZero : ℕ → ℂ) (j e : ℕ) (he : 0 < e) (hj : j ≠ 4) :
    ordinaryScalar q first prefactor atZero j e = 0 := by
  simp [ordinaryScalar, ne_of_gt he, hj]

/-- The exact local coefficient, including its phase, factors before any
absolute-value estimate. The canonical zero branch is handled separately. -/
theorem ordinaryScalar_frozen (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e : ℕ) (he : AdmissibleExponent e) :
    ordinaryScalar q first prefactor atZero j e =
      ordinaryScalar q first prefactor atZero j (frozenMin e) *
        (q⁻¹) ^ frozenCubeExp e := by
  by_cases h0 : e = 0
  · simp [h0]
  · have hm : 0 < frozenMin e := by
      have hm0 : frozenMin e ≠ 0 := by
        intro hm
        exact h0 ((frozenMin_eq_zero_iff e).mp hm)
      omega
    calc
      ordinaryScalar q first prefactor atZero j e =
          ordinaryScalar q first prefactor atZero j
            (frozenMin e + 3 * frozenCubeExp e) :=
        congrArg (ordinaryScalar q first prefactor atZero j)
          (frozenExponent_decomposition e he)
      _ = _ := ordinaryScalar_add_cube q first prefactor atZero j
        (frozenMin e) (frozenCubeExp e) hm

theorem ordinaryScalar_frozen_norm (q : ℝ) (hq : 0 < q)
    (first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ)
    (he : AdmissibleExponent e) :
    ‖ordinaryScalar (q : ℂ) first prefactor atZero j e‖ =
      ‖ordinaryScalar (q : ℂ) first prefactor atZero j (frozenMin e)‖ /
        q ^ frozenCubeExp e := by
  rw [ordinaryScalar_frozen (q : ℂ) first prefactor atZero j e he,
    norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq]
  simp only [inv_pow, div_eq_mul_inv]

variable {ι : Type*}

def localProduct (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (digit exponent : ι → ℕ) : ℂ :=
  ∏ p ∈ s, ordinaryScalar (q p : ℂ) (first p) (prefactor p) (atZero p)
    (digit p) (exponent p)

def minimumMajorant (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (digit exponent : ι → ℕ) : ℝ :=
  ∏ p ∈ s, ‖ordinaryScalar (q p : ℂ) (first p) (prefactor p) (atZero p)
    (digit p) (frozenMin (exponent p))‖

def cubeNorm (s : Finset ι) (q : ι → ℝ) (exponent : ι → ℕ) : ℝ :=
  ∏ p ∈ s, q p ^ frozenCubeExp (exponent p)

theorem minimumMajorant_nonneg (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ) :
    0 ≤ minimumMajorant s q first prefactor atZero digit exponent :=
  Finset.prod_nonneg (fun _ _ => norm_nonneg _)

theorem cubeNorm_pos (s : Finset ι) (q : ι → ℝ) (exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p) : 0 < cubeNorm s q exponent :=
  Finset.prod_pos (fun p hp => pow_pos (hq p hp) _)

/-- A nonzero product of local coefficients gives all admissible valuations,
so the admissibility restriction is itself supplied by the local table. -/
theorem localProduct_nonzero_admissible (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hprod : localProduct s q first prefactor atZero digit exponent ≠ 0)
    (p : ι) (hp : p ∈ s) : AdmissibleExponent (exponent p) := by
  apply ordinaryScalar_nonzero_admissible (q p : ℂ) (first p) (prefactor p)
    (atZero p) (digit p) (exponent p)
  intro hz
  apply hprod
  exact Finset.prod_eq_zero hp hz

/-- This is the whole finite local product's exact frozen norm, rather than
an assumed C/N(x) bound for an already assembled coefficient. -/
theorem localProduct_frozen_norm (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p)
    (he : ∀ p ∈ s, AdmissibleExponent (exponent p)) :
    ‖localProduct s q first prefactor atZero digit exponent‖ =
      minimumMajorant s q first prefactor atZero digit exponent /
        cubeNorm s q exponent := by
  unfold localProduct minimumMajorant cubeNorm
  rw [norm_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact ordinaryScalar_frozen_norm (q p) (hq p hp) (first p) (prefactor p)
    (atZero p) (digit p) (exponent p) (he p hp)

/-- The remaining unit characters and norm phases may be kept as one bounded
phase. Their norm bound and the explicit table imply the exact frozen budget. -/
theorem phased_localProduct_norm_le (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p)
    (he : ∀ p ∈ s, AdmissibleExponent (exponent p))
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1) :
    ‖phase * localProduct s q first prefactor atZero digit exponent‖ ≤
      minimumMajorant s q first prefactor atZero digit exponent /
        cubeNorm s q exponent := by
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖localProduct s q first prefactor atZero digit exponent‖ :=
      mul_le_mul_of_nonneg_right hphase (norm_nonneg _)
    _ = _ := by rw [one_mul, localProduct_frozen_norm s q first prefactor atZero digit exponent hq he]

end

end HeckeSkeleton.LowFrozenCube.LocalTable
