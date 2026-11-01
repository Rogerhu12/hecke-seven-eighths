import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedCorrelation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondAllocatedSource

/-!
# The sixth-power support of the actual complete correlations

The unequal-depth local theorem is stated in the product presentation
`g^j * g^d`.  This file identifies its two characters with the actual
generated ideal characters.  Changing a generator preserves the norm of
the complete correlation, and swapping the two complete quotients
conjugates the correlation and negates its original frequency.  Thus the
support theorem applies in both orders of the two actual multiplicities.

The product and live-row interfaces retain the original generators and
frequency.  Sixth divisibility is a conclusion of nonvanishing, rather
than an additional numerical premise on a proposed child.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments

section Ring

variable {R : Type*} [CommRing R]

/-- Swap the two original full quotients.  The target quotient changes
from `(u * v)` to `(v * u)`; comparison is made by their literal
divisibility congruences, without choosing residue representatives anew. -/
theorem fullModulusCorrelation_swap (u v : R)
    [Fintype (R ⧸ Ideal.span {u})] [Fintype (R ⧸ Ideal.span {v})]
    (χu : MulChar (R ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (R ⧸ Ideal.span {v}) ℂ) (h : R) :
    fullModulusCorrelation u v χu χv h =
      star (fullModulusCorrelation v u χv χu (-h)) := by
  classical
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq :
      scaledResidue u v (u * v) rfl x -
          scaledResidue v u (u * v) (mul_comm u v) y =
            Ideal.Quotient.mk (Ideal.span {u * v}) h ↔
      scaledResidue v u (v * u) rfl y -
          scaledResidue u v (v * u) (mul_comm v u) x =
            Ideal.Quotient.mk (Ideal.span {v * u}) (-h) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence, scaledResidue_congruence]
    have he : u * b - v * a - (-h) = -(v * a - u * b - h) := by ring
    rw [he, mul_comm v u, dvd_neg]
  simp only [map_neg] at heq ⊢
  by_cases hh : scaledResidue u v (u * v) rfl x -
      scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk (Ideal.span {u * v}) h
  · simp only [if_pos hh, if_pos (heq.mp hh), star_mul, star_star]
  · simp only [if_neg hh, if_neg ((not_congr heq).mp hh), star_zero]

end Ring

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The same exact swap for the source's generated ideal characters. -/
theorem generatedIdealCorrelation_swap
    (I J : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates J b) (h : A.R) :
    generatedIdealCorrelation (σ := σ) I J a b ha hb h =
      star (generatedIdealCorrelation (σ := σ) J I b a hb ha (-h)) := by
  letI : Finite (A.R ⧸ Ideal.span {a}) := by
    rw [ha.2]
    exact A.exteriorResidue_finite I
  letI : Finite (A.R ⧸ Ideal.span {b}) := by
    rw [hb.2]
    exact A.exteriorResidue_finite J
  letI : Fintype (A.R ⧸ Ideal.span {a}) := Fintype.ofFinite _
  letI : Fintype (A.R ⧸ Ideal.span {b}) := Fintype.ofFinite _
  change fullModulusCorrelation a b
      (generatedIdealCharacter (σ := σ) I a ha)
      (generatedIdealCharacter (σ := σ) J b hb) h =
    star (fullModulusCorrelation b a
      (generatedIdealCharacter (σ := σ) J b hb)
      (generatedIdealCharacter (σ := σ) I a ha) (-h))
  exact fullModulusCorrelation_swap a b _ _ h

theorem actualPrimePowerCorrelation_swap
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) :
    actualPrimePowerCorrelation C p m n h =
      star (actualPrimePowerCorrelation C p n m (-h)) :=
  generatedIdealCorrelation_swap (powerIdeal p m) (powerIdeal p n)
    (generator C p ^ m) (generator C p ^ n)
    (generator_power_generates C p m) (generator_power_generates C p n) h

local instance supportPrimePowerFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFinite C p n

local instance supportPrimePowerFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (n : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ n}) :=
  LocalFiniteSums.residueFintype C p n

local instance supportProductPowerFinite (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) :
    Finite (A.R ⧸ Ideal.span {generator C p ^ j * generator C p ^ d}) := by
  rw [← pow_add]
  exact supportPrimePowerFinite C p (j + d)

local instance supportProductPowerFintype (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j d : ℕ) :
    Fintype (A.R ⧸ Ideal.span {generator C p ^ j * generator C p ^ d}) :=
  Fintype.ofFinite _

/-- The product presentation has the literal same sextic values on every
original ring element, including all nonunit zeros. -/
theorem generatedIdealCharacter_product_power
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hn : j + d ≠ 0)
    (hg : A.Generates (powerIdeal p (j + d))
      (generator C p ^ j * generator C p ^ d)) :
    generatedIdealCharacter (σ := σ) (powerIdeal p (j + d))
        (generator C p ^ j * generator C p ^ d) hg =
      productPowerCharacter C p j d hn := by
  apply MulChar.ext'
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  have he := congrArg
    (fun χ : MulChar (A.R ⧸ Ideal.span {generator C p ^ (j + d)}) ℂ =>
      χ (Ideal.Quotient.mk _ x))
    (generatedIdealCharacter_prime_power C p (j + d) hn)
  rw [generatedIdealCharacter_mk, productPowerCharacter_mk]
  rw [generatedIdealCharacter_mk] at he
  exact he.trans (localMaskedCharacter_mk C p (j + d) hn x)

/-- The complete unequal-depth support theorem, now on the actual
generated ideal correlation rather than an independently given local
character. -/
theorem actualPrimePowerCorrelation_support_add
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (j d : ℕ) (hj : 0 < j) (hd : 0 < d) (h : A.R)
    (hne : actualPrimePowerCorrelation C p (j + d) j h ≠ 0) :
    ∃ k : A.R, h = generator C p ^ j * k ∧ 6 ∣ j ∧ ¬generator C p ∣ k := by
  have hg : A.Generates (powerIdeal p (j + d))
      (generator C p ^ j * generator C p ^ d) := by
    rw [← pow_add]
    exact generator_power_generates C p (j + d)
  have hnorm := generated_correlation_norm_generator_change (σ := σ)
    (powerIdeal p (j + d)) (powerIdeal p j)
    (generator C p ^ (j + d)) (generator C p ^ j)
    (generator C p ^ j * generator C p ^ d) (generator C p ^ j)
    (generator_power_generates C p (j + d)) (generator_power_generates C p j)
    hg (generator_power_generates C p j) h
  have hnew : generatedIdealCorrelation (σ := σ)
      (powerIdeal p (j + d)) (powerIdeal p j)
      (generator C p ^ j * generator C p ^ d) (generator C p ^ j)
      hg (generator_power_generates C p j) h ≠ 0 := by
    intro he
    apply hne
    apply norm_eq_zero.mp
    change ‖generatedIdealCorrelation (σ := σ)
      (powerIdeal p (j + d)) (powerIdeal p j)
      (generator C p ^ (j + d)) (generator C p ^ j)
      (generator_power_generates C p (j + d))
      (generator_power_generates C p j) h‖ = 0
    rw [← hnorm, he, norm_zero]
  change fullModulusCorrelation
    (generator C p ^ j * generator C p ^ d) (generator C p ^ j)
    (generatedIdealCharacter (σ := σ) (powerIdeal p (j + d))
      (generator C p ^ j * generator C p ^ d) hg)
    (generatedIdealCharacter (σ := σ) (powerIdeal p j) (generator C p ^ j)
      (generator_power_generates C p j)) h ≠ 0 at hnew
  rw [generatedIdealCharacter_product_power C p j d (by omega) hg,
    generatedIdealCharacter_prime_power C p j hj.ne'] at hnew
  exact actual_unequal_prime_power_support C p j d hj hd h hnew

/-- A nonzero actual correlation at distinct positive depths forces its
smaller depth to be a multiple of six.  Both orders of the two depths
refer to the same original frequency. -/
theorem actualPrimePowerCorrelation_six_of_ne
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (m n : ℕ) (h : A.R) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hne : actualPrimePowerCorrelation C p m n h ≠ 0) :
    6 ∣ min m n := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hswap : actualPrimePowerCorrelation C p n m (-h) ≠ 0 := by
      intro hz
      apply hne
      rw [actualPrimePowerCorrelation_swap, hz, star_zero]
    have he : n = m + (n - m) := by omega
    rw [he] at hswap
    obtain ⟨_, _, hsix, _⟩ := actualPrimePowerCorrelation_support_add C p
      m (n - m) hm (by omega) (-h) hswap
    simpa only [min_eq_left hlt.le] using hsix
  · have he : m = n + (m - n) := by omega
    rw [he] at hne
    obtain ⟨_, _, hsix, _⟩ := actualPrimePowerCorrelation_support_add C p
      n (m - n) hn (by omega) h hne
    simpa only [min_eq_right hgt.le] using hsix

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonvanishing in arbitrary original generators is transported to each
actual prime-power factor by a norm identity, not by replacing its
frequency or character. -/
theorem actual_product_correlation_nonzero_local_of_generates
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ)
      (primePowerProduct p m) (primePowerProduct p n) a b ha hb h ≠ 0)
    (i : ι) : actualPrimePowerCorrelation C (p i) (m i) (n i) h ≠ 0 := by
  have hnorm := generated_correlation_norm_generator_change (σ := σ)
    (primePowerProduct p m) (primePowerProduct p n)
    (primePowerProductGenerator C p m) (primePowerProductGenerator C p n) a b
    (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) ha hb h
  have hz : generatedIdealCorrelation (σ := σ)
      (primePowerProduct p m) (primePowerProduct p n)
      (primePowerProductGenerator C p m) (primePowerProductGenerator C p n)
      (primePowerProduct_generates C p m) (primePowerProduct_generates C p n) h ≠ 0 := by
    intro he
    apply hne
    apply norm_eq_zero.mp
    rw [hnorm, he, norm_zero]
  exact actual_product_correlation_nonzero_local C p hp m n h hz i

/-- The sixth-divisibility conclusion for each unequal positive pair in
the same complete product correlation and its supplied generators. -/
theorem actual_product_correlation_six_of_ne_of_generates
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b) (h : A.R)
    (hne : generatedIdealCorrelation (σ := σ)
      (primePowerProduct p m) (primePowerProduct p n) a b ha hb h ≠ 0)
    (i : ι) (hm : 0 < m i) (hn : 0 < n i) (hmn : m i ≠ n i) :
    6 ∣ min (m i) (n i) :=
  actualPrimePowerCorrelation_six_of_ne C (p i) (m i) (n i) h hm hn hmn
    (actual_product_correlation_nonzero_local_of_generates C p hp m n a b ha hb h hne i)

end Product

namespace ActualSecondCorrelationRows

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (R : ActualSecondCorrelationRows A σ H ι)

/-- Every live original row has nonzero actual local factors. -/
theorem live_local_correlation_nonzero
    (C : A.GeneralArithmeticContext σ η hS) (h : R.live) (i : ι) :
    actualPrimePowerCorrelation C (R.primes i)
      (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) ≠ 0 :=
  actual_product_correlation_nonzero_local_of_generates C R.primes
    R.primes_injective R.leftMultiplicity R.rightMultiplicity
    R.leftGenerator R.rightGenerator R.leftGenerates R.rightGenerates
    (R.frequency h.val) (Finset.mem_filter.mp h.property).2 i

/-- A live row supplies the exact local support condition used in the
second saving inequality; there is no additional support certificate. -/
theorem live_six_of_ne
    (C : A.GeneralArithmeticContext σ η hS) (h : R.live) (i : ι)
    (hm : 0 < R.leftMultiplicity i) (hn : 0 < R.rightMultiplicity i)
    (hmn : R.leftMultiplicity i ≠ R.rightMultiplicity i) :
    6 ∣ min (R.leftMultiplicity i) (R.rightMultiplicity i) :=
  actualPrimePowerCorrelation_six_of_ne C (R.primes i)
    (R.leftMultiplicity i) (R.rightMultiplicity i) (R.frequency h.val) hm hn hmn
    (R.live_local_correlation_nonzero C h i)

end ActualSecondCorrelationRows

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.actualPrimePowerCorrelation_six_of_ne
#print axioms HeckeSkeleton.Moments.EngineStep.actual_product_correlation_six_of_ne_of_generates
#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.live_six_of_ne
