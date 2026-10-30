import HeckeGeneral.Analysis.GlobalThetaData
import HeckeGeneral.Arithmetic.IdealFactorization
import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
import HeckeSkeleton.LowHybrid.PrimeArithmetic
import HeckeSkeleton.LowHybrid.Counting
import HeckeSkeleton.LowFrozenCube.PrimeProducts

/-!
# The actual exterior-ideal arithmetic for the low hybrid bound

The coordinates below are the multiplicities of the actual nonzero prime
ideals. Their inverse is the finite product of those prime-ideal powers.
The monoid multiplication agrees definitionally with `exteriorMul`.
-/

noncomputable section

namespace HeckeSkeleton.LowHybrid.ExteriorArithmetic

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Exterior ideals form the divisor-closed submonoid of nonzero ideals. -/
instance exteriorIdealCommMonoid : CommMonoid (ExteriorIdeal K S) where
  one := ⟨1, by
    intro p hp
    exact (p.prime.not_dvd_one hp).elim⟩
  mul := exteriorMul K S
  one_mul I := Subtype.ext (one_mul I.val)
  mul_one I := Subtype.ext (mul_one I.val)
  mul_assoc I J L := Subtype.ext (mul_assoc I.val J.val L.val)
  mul_comm I J := Subtype.ext (mul_comm I.val J.val)

theorem mul_eq (I J : ExteriorIdeal K S) : I * J = exteriorMul K S I J := rfl

@[simp] theorem exteriorMul_eq (I J : ExteriorIdeal K S) : exteriorMul K S I J = I * J := rfl

@[simp] theorem one_val : (1 : ExteriorIdeal K S).val = 1 := rfl

@[simp] theorem mul_val (I J : ExteriorIdeal K S) : (I * J).val = I.val * J.val := rfl

@[simp] theorem pow_val (I : ExteriorIdeal K S) (n : ℕ) : (I ^ n).val = I.val ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, mul_val, ih]

theorem underlying_injective : Function.Injective (fun I : ExteriorIdeal K S => I.val.val) :=
  fun I J h => Subtype.ext (Subtype.ext h)

/-- Divisibility in the exterior monoid is ordinary ideal divisibility. -/
theorem dvd_iff (I J : ExteriorIdeal K S) : I ∣ J ↔ I.val.val ∣ J.val.val := by
  constructor
  · rintro ⟨L, rfl⟩
    exact dvd_mul_right _ _
  · rintro ⟨L, hL⟩
    have hL0 : L ≠ 0 := by
      intro hz
      exact nonZeroDivisors.coe_ne_zero J.val (by rw [hL, hz, mul_zero])
    let L' : ExteriorIdeal K S := ⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, by
      intro p hp
      apply J.property p
      rw [hL]
      exact dvd_mul_of_dvd_right hp I.val.val⟩
    exact ⟨L', underlying_injective K S hL⟩

@[simp] theorem completedIdeal_eq (c n : ExteriorIdeal K S) :
    completedIdeal K S c n = c * n ^ 3 := by
  change c * (n * (n * n)) = c * n ^ 3
  simp only [pow_succ, pow_zero, mul_one, mul_assoc]

/-- Prime multiplicity is positive exactly when the prime divides the ideal. -/
theorem primeExponents_pos_iff (I : (Ideal (𝓞 K))⁰) (p : HeightOneSpectrum (𝓞 K)) :
    0 < primeExponents I p ↔ p.asIdeal ∣ I.val := by
  rw [primeExponents_apply, Multiset.count_pos,
    mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)]
  exact and_iff_right p.prime

theorem primeExponents_zero_of_mem (I : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) : primeExponents I.val p = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  exact I.property p ((primeExponents_pos_iff K I.val p).mp h) hp

/-- Restriction of the genuine ideal factorization to primes outside `S`. -/
def exponents (I : ExteriorIdeal K S) : ExteriorPrime K S →₀ ℕ :=
  (primeExponents I.val).comapDomain Subtype.val Subtype.val_injective.injOn

@[simp] theorem exponents_apply (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    exponents K S I p = primeExponents I.val p.val := rfl

theorem exponents_support (I : ExteriorIdeal K S) :
    ↑(primeExponents I.val).support ⊆
      Set.range (Subtype.val : ExteriorPrime K S → HeightOneSpectrum (𝓞 K)) := by
  intro p hp
  have hpos : 0 < primeExponents I.val p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  exact ⟨⟨p, I.property p ((primeExponents_pos_iff K I.val p).mp hpos)⟩, rfl⟩

/-- The finite product of an exterior prime-exponent vector. -/
def ofExponents (e : ExteriorPrime K S →₀ ℕ) : ExteriorIdeal K S :=
  ⟨idealOfPrimeExponents (e.mapDomain Subtype.val), by
    intro p hp
    have hpos := (primeExponents_pos_iff K
      (idealOfPrimeExponents (e.mapDomain Subtype.val)) p).mpr hp
    rw [primeExponents_idealOfPrimeExponents] at hpos
    by_contra hpS
    have hout : p ∉ Set.range (Subtype.val : ExteriorPrime K S → HeightOneSpectrum (𝓞 K)) := by
      rintro ⟨q, rfl⟩
      exact q.property hpS
    rw [Finsupp.mapDomain_of_notMem_range e p hout] at hpos
    exact Nat.lt_irrefl 0 hpos⟩

@[simp] theorem ofExponents_exponents (I : ExteriorIdeal K S) :
    ofExponents K S (exponents K S I) = I := by
  apply Subtype.ext
  change idealOfPrimeExponents
    (((primeExponents I.val).comapDomain Subtype.val
      Subtype.val_injective.injOn).mapDomain Subtype.val) = I.val
  rw [Finsupp.mapDomain_comapDomain _ Subtype.val_injective _ (exponents_support K S I),
    idealOfPrimeExponents_primeExponents]

@[simp] theorem exponents_ofExponents (e : ExteriorPrime K S →₀ ℕ) :
    exponents K S (ofExponents K S e) = e := by
  change (primeExponents (idealOfPrimeExponents (e.mapDomain Subtype.val))).comapDomain
    Subtype.val Subtype.val_injective.injOn = e
  rw [primeExponents_idealOfPrimeExponents, Finsupp.comapDomain_mapDomain _ Subtype.val_injective]

/-- Unique factorization of the actual exterior ideals as a monoid equivalence. -/
def coords : ExteriorIdeal K S ≃* Multiplicative (ExteriorPrime K S →₀ ℕ) where
  toFun I := Multiplicative.ofAdd (exponents K S I)
  invFun e := ofExponents K S e.toAdd
  left_inv := ofExponents_exponents K S
  right_inv e := congrArg Multiplicative.ofAdd (exponents_ofExponents K S e.toAdd)
  map_mul' I J := by
    apply congrArg Multiplicative.ofAdd
    change (primeExponents (I.val * J.val)).comapDomain Subtype.val
      Subtype.val_injective.injOn = _
    rw [primeExponents_mul, Finsupp.comapDomain_add_of_injective Subtype.val_injective]
    rfl

@[simp] theorem valuation_coords (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    valuation (coords K S) I p = primeExponents I.val p.val := rfl

@[simp] theorem coords_exteriorPrimeIdeal (p : ExteriorPrime K S) :
    coords K S (exteriorPrimeIdeal K S p) = Multiplicative.ofAdd (Finsupp.single p 1) := by
  apply congrArg Multiplicative.ofAdd
  ext q
  change (normalizedFactors p.val.asIdeal).count q.val.asIdeal = Finsupp.single p 1 q
  rw [normalizedFactors_irreducible p.val.irreducible, normalize_eq]
  by_cases h : p = q
  · subst q
    simp
  · have hpq : p.val.asIdeal ≠ q.val.asIdeal := by
      intro he
      exact h (Subtype.ext (HeightOneSpectrum.asIdeal_injective he))
    simp [hpq, Ne.symm hpq, h]

@[simp] theorem prime_coords (p : ExteriorPrime K S) :
    primeElement (coords K S) p = exteriorPrimeIdeal K S p := by
  apply (coords K S).injective
  simp [primeElement]

/-- Coordinate squarefreeness is exactly squarefreeness of the underlying ideal. -/
theorem coords_squarefree_iff (I : ExteriorIdeal K S) :
    PrimeArithmetic.Squarefree (coords K S) I ↔ Squarefree I.val.val := by
  rw [squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero I.val),
    Multiset.nodup_iff_count_le_one]
  constructor
  · intro h P
    by_cases hP : P ∈ normalizedFactors I.val.val
    · let p := HeightOneSpectrum.ofPrime (prime_of_normalized_factor P hP)
      have hpS : p ∉ S := I.property p (dvd_of_mem_normalizedFactors hP)
      exact h ⟨p, hpS⟩
    · simp [Multiset.count_eq_zero_of_notMem hP]
  · intro h p
    exact h p.val.asIdeal

private theorem actual_isRelPrime_iff (I J : Ideal (𝓞 K)) :
    IsRelPrime I J ↔ IsCoprime I J := by
  rw [← gcd_isUnit_iff_isRelPrime, Ideal.isUnit_iff,
    Ideal.isCoprime_iff_gcd, Ideal.one_eq_top]

/-- Disjoint exterior prime supports are precisely coprime underlying ideals. -/
theorem coords_coprime_iff (I J : ExteriorIdeal K S) :
    Coprime (coords K S) I J ↔ IsCoprime I.val.val J.val.val := by
  rw [← actual_isRelPrime_iff K, isRelPrime_iff_no_prime_factors
    (nonZeroDivisors.coe_ne_zero I.val)]
  constructor
  · intro h P hPI hPJ hP
    let p := HeightOneSpectrum.ofPrime hP
    let q : ExteriorPrime K S := ⟨p, I.property p hPI⟩
    have hi : 0 < primeExponents I.val p := (primeExponents_pos_iff K I.val p).mpr hPI
    have hj : 0 < primeExponents J.val p := (primeExponents_pos_iff K J.val p).mpr hPJ
    rcases h q with h | h <;> change primeExponents _ p = 0 at h <;> omega
  · intro h p
    by_cases hi : primeExponents I.val p.val = 0
    · exact Or.inl hi
    · right
      apply Nat.eq_zero_of_not_pos
      intro hj
      exact h ((primeExponents_pos_iff K I.val p.val).mp (Nat.pos_of_ne_zero hi))
        ((primeExponents_pos_iff K J.val p.val).mp hj) p.val.prime

/-- The positive natural absolute ideal norm. -/
def natNorm (I : ExteriorIdeal K S) : ℕ := I.val.val.absNorm

theorem one_le_natNorm (I : ExteriorIdeal K S) : 1 ≤ natNorm K S I := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  exact nonZeroDivisors.coe_ne_zero I.val (Ideal.absNorm_eq_zero_iff.mp h)

/-- The actual real absolute norm, packaged with its proved multiplicativity. -/
def normHom : ExteriorIdeal K S →* ℝ where
  toFun := exteriorNorm K S
  map_one' := by
    change ((1 : Ideal (𝓞 K)).absNorm : ℝ) = 1
    simp
  map_mul' I J := by
    change ((I.val.val * J.val.val).absNorm : ℝ) =
      (I.val.val.absNorm : ℝ) * (J.val.val.absNorm : ℝ)
    simp only [map_mul, Nat.cast_mul]

@[simp] theorem normHom_apply (I : ExteriorIdeal K S) :
    normHom K S I = exteriorNorm K S I := rfl

theorem normHom_natNorm (I : ExteriorIdeal K S) :
    normHom K S I = (natNorm K S I : ℝ) := rfl

theorem one_le_normHom (I : ExteriorIdeal K S) : 1 ≤ normHom K S I := by
  change (1 : ℝ) ≤ (natNorm K S I : ℝ)
  exact_mod_cast one_le_natNorm K S I

@[simp] theorem normHom_prime_coords (p : ExteriorPrime K S) :
    normHom K S (primeElement (coords K S) p) = (p.val.asIdeal.absNorm : ℝ) := by
  rw [prime_coords]
  rfl

/-- A single linear-counting constant for all exterior finite norm cutoffs. -/
def countConstant : ℝ :=
  Classical.choose (DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K)

theorem one_le_countConstant : 1 ≤ countConstant K :=
  (Classical.choose_spec
    (DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K)).1

theorem countConstant_pos : 0 < countConstant K :=
  lt_of_lt_of_le zero_lt_one (one_le_countConstant K)

theorem linearNormCounting : LinearNormCounting (natNorm K S) (countConstant K) := by
  intro N s hs
  by_cases hN : N = 0
  · subst N
    have hsempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have := one_le_natNorm K S I
      have := hs I hI
      omega
    simp [hsempty]
  · let t := s.image (fun I : ExteriorIdeal K S => I.val.val)
    have hcount := (Classical.choose_spec
      (DedekindZetaZeroFree.LargeSieve.exists_ideal_count_bound_finset K)).2.2
      (N : ℝ) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN) t
      (by
        intro J hJ
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
        exact_mod_cast hs I hI)
    have hcard : t.card = s.card := Finset.card_image_of_injective _ (underlying_injective K S)
    simpa only [hcard] using hcount

end HeckeSkeleton.LowHybrid.ExteriorArithmetic
