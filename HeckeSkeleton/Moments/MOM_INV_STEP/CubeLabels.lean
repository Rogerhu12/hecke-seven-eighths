import HeckeSkeleton.Moments.MOM_INV_STEP.CubeAlgebra
import HeckeGeneral.Arithmetic.IdealMobiusMask

/-!
# Cube labels of the actual nonzero ideal product

The exponent vector is `primeExponents (b₁ * b₂)`. In particular the
decomposition does not require principal ideals or prime generators.
The retained ideal is squarefree, and its odd and even-double factors are
coprime. `LocalSource` separately treats the value of a row on numerator
labels; reciprocity between the two descriptions is a further obligation.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels

open IsDedekindDomain HeckeGeneral.Arithmetic CubeAlgebra
open scoped BigOperators Classical nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem ideal_bit_product (B : Finset (HeightOneSpectrum R))
    (ε : HeightOneSpectrum R → Bool) :
    aLabel HeightOneSpectrum.asIdeal B ε =
      IdealMobiusMask.primeProduct (B.filter (fun p => ε p)) := by
  simp only [aLabel, CubeAlgebra.primeProduct, IdealMobiusMask.primeProduct,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  cases ε p <;> simp [bit]

theorem ideal_bit_product_squarefree (B : Finset (HeightOneSpectrum R))
    (ε : HeightOneSpectrum R → Bool) :
    Squarefree (aLabel HeightOneSpectrum.asIdeal B ε) := by
  rw [ideal_bit_product]
  exact IdealMobiusMask.squarefree_primeProduct _

theorem ideal_jLabel_squarefree (B : Finset (HeightOneSpectrum R))
    (v : HeightOneSpectrum R → ℕ) (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    Squarefree (jLabel HeightOneSpectrum.asIdeal B v ε₁ ε₂) :=
  ideal_bit_product_squarefree B (fun p => retained (parity (v p)) (ε₁ p) (ε₂ p))

theorem ideal_squarefreeLabel_squarefree (B : Finset (HeightOneSpectrum R))
    (v : HeightOneSpectrum R → ℕ) :
    Squarefree (squarefreeLabel HeightOneSpectrum.asIdeal B v) :=
  ideal_bit_product_squarefree B (fun p => parity (v p))

theorem ideal_j2Label_squarefree (B : Finset (HeightOneSpectrum R))
    (v : HeightOneSpectrum R → ℕ) (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    Squarefree (j2Label HeightOneSpectrum.asIdeal B v ε₁ ε₂) :=
  ideal_bit_product_squarefree B (fun p => evenDouble (v p) (ε₁ p) (ε₂ p))

theorem ideal_squarefreeLabel_coprime_j2Label (B : Finset (HeightOneSpectrum R))
    (v : HeightOneSpectrum R → ℕ) (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    IsCoprime (squarefreeLabel HeightOneSpectrum.asIdeal B v)
      (j2Label HeightOneSpectrum.asIdeal B v ε₁ ε₂) := by
  change IsCoprime
    (aLabel HeightOneSpectrum.asIdeal B (fun p => parity (v p)))
    (aLabel HeightOneSpectrum.asIdeal B (fun p => evenDouble (v p) (ε₁ p) (ε₂ p)))
  rw [ideal_bit_product, ideal_bit_product]
  unfold IdealMobiusMask.primeProduct
  apply IsCoprime.prod_left
  intro p hp
  apply IsCoprime.prod_right
  intro q hq
  apply Ideal.isCoprime_of_isMaximal
  intro hpq
  have heq : p = q := HeightOneSpectrum.asIdeal_injective hpq
  subst q
  exact Finset.disjoint_left.mp (squarefree_j2_support_disjoint B v ε₁ ε₂) hp hq

def cubePrimeSupport (b₁ b₂ : (Ideal R)⁰) : Finset (HeightOneSpectrum R) :=
  (primeExponents (b₁ * b₂)).support

def cubeMultiplicity (b₁ b₂ : (Ideal R)⁰) (p : HeightOneSpectrum R) : ℕ :=
  primeExponents (b₁ * b₂) p

def q0 (b₁ b₂ : (Ideal R)⁰) (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Ideal R :=
  b0Label HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (cubeMultiplicity b₁ b₂) ε₁ ε₂

def J2 (b₁ b₂ : (Ideal R)⁰) (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Ideal R :=
  j2Label HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (cubeMultiplicity b₁ b₂) ε₁ ε₂

def s (b₁ b₂ : (Ideal R)⁰) : Ideal R :=
  squarefreeLabel HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (cubeMultiplicity b₁ b₂)

def J (b₁ b₂ : (Ideal R)⁰) (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Ideal R :=
  jLabel HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (cubeMultiplicity b₁ b₂) ε₁ ε₂

/-- The part of the first primitive conductor supported at cube primes. -/
def R1 (b₁ b₂ : (Ideal R)⁰) (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Ideal R :=
  IdealMobiusMask.primeProduct ((cubePrimeSupport b₁ b₂).filter fun p =>
    conductorExponent (parity (cubeMultiplicity b₁ b₂ p)) (ε₁ p) (ε₂ p) ≠ 0)

theorem odd_conductor_digit_ne_zero (ε₁ ε₂ : Bool) :
    conductorExponent true ε₁ ε₂ ≠ 0 := by
  cases ε₁ <;> cases ε₂ <;> decide

/-- Every odd-multiplicity cube prime remains in the first conductor. -/
theorem s_dvd_R1 (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) : s b₁ b₂ ∣ R1 b₁ b₂ ε₁ ε₂ := by
  change aLabel HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (fun p => parity (cubeMultiplicity b₁ b₂ p)) ∣ R1 b₁ b₂ ε₁ ε₂
  rw [ideal_bit_product]
  unfold R1 IdealMobiusMask.primeProduct
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨hp, hodd⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp, ?_⟩
  rw [hodd]
  exact odd_conductor_digit_ne_zero (ε₁ p) (ε₂ p)

theorem cubeMultiplicity_pos (b₁ b₂ : (Ideal R)⁰) (p : HeightOneSpectrum R)
    (hp : p ∈ cubePrimeSupport b₁ b₂) : 0 < cubeMultiplicity b₁ b₂ p := by
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)

theorem cubeMultiplicity_eq_sum (b₁ b₂ : (Ideal R)⁰) (p : HeightOneSpectrum R) :
    cubeMultiplicity b₁ b₂ p = primeExponents b₁ p + primeExponents b₂ p := by
  simp only [cubeMultiplicity, primeExponents_mul, Finsupp.add_apply]

/-- The valuation formula and the cube digit use the same actual two
ideal multiplicities. -/
theorem cube_conductor_digit (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) (p : HeightOneSpectrum R) :
    conductorExponent (parity (cubeMultiplicity b₁ b₂ p)) (ε₁ p) (ε₂ p) =
    conductorExponent (parity (primeExponents b₁ p + primeExponents b₂ p))
      (ε₁ p) (ε₂ p) := by
  rw [cubeMultiplicity_eq_sum]

/-- `b₁ b₂ = q₀² J₂² s` for the actual nonzero integral ideals. -/
theorem actual_cube_decomposition (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    b₁.val * b₂.val = q0 b₁ b₂ ε₁ ε₂ ^ 2 * J2 b₁ b₂ ε₁ ε₂ ^ 2 * s b₁ b₂ := by
  have hrec : CubeAlgebra.primeProduct HeightOneSpectrum.asIdeal
      (cubePrimeSupport b₁ b₂) (cubeMultiplicity b₁ b₂) = b₁.val * b₂.val := by
    change (idealOfPrimeExponents (primeExponents (b₁ * b₂))).val = _
    rw [idealOfPrimeExponents_primeExponents]
    rfl
  rw [← hrec]
  exact cube_product_decomposition HeightOneSpectrum.asIdeal (cubePrimeSupport b₁ b₂)
    (cubeMultiplicity b₁ b₂) ε₁ ε₂ (cubeMultiplicity_pos b₁ b₂)

theorem J_eq_s_mul_J2 (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) :
    J b₁ b₂ ε₁ ε₂ = s b₁ b₂ * J2 b₁ b₂ ε₁ ε₂ :=
  jLabel_eq_squarefree_mul_j2 _ _ _ _ _

theorem J_squarefree (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Squarefree (J b₁ b₂ ε₁ ε₂) :=
  ideal_jLabel_squarefree _ _ _ _

theorem s_squarefree (b₁ b₂ : (Ideal R)⁰) : Squarefree (s b₁ b₂) :=
  ideal_squarefreeLabel_squarefree _ _

theorem J2_squarefree (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) : Squarefree (J2 b₁ b₂ ε₁ ε₂) :=
  ideal_j2Label_squarefree _ _ _ _

theorem s_coprime_J2 (b₁ b₂ : (Ideal R)⁰)
    (ε₁ ε₂ : HeightOneSpectrum R → Bool) : IsCoprime (s b₁ b₂) (J2 b₁ b₂ ε₁ ε₂) :=
  ideal_squarefreeLabel_coprime_j2Label _ _ _ _

end HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels

end
