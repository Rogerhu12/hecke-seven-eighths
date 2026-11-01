import HeckeSkeleton.LowFrozenCube.Valuations
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Canonical prime-coordinate factors

An ideal monoid with unique prime factorization is represented by a monoid
equivalence with finitely supported natural exponent vectors.  This file
constructs the supported and complementary factors from that equivalence.
The splitting identity and its uniqueness are theorems, not supplied fields.
No finiteness assumption is imposed on the prime type.
-/

namespace HeckeSkeleton.LowFrozenCube.PrimeCoordinates

open scoped Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def valuation (a : A) : ι →₀ ℕ := (coords a).toAdd

theorem valuation_injective : Function.Injective (valuation coords) := by
  intro a b h
  apply coords.injective
  exact congrArg Multiplicative.ofAdd h

@[simp] theorem valuation_one : valuation coords 1 = 0 := by
  simp [valuation]

@[simp] theorem valuation_mul (a b : A) :
    valuation coords (a * b) = valuation coords a + valuation coords b := by
  simp [valuation]

@[simp] theorem valuation_pow (a : A) (n : ℕ) :
    valuation coords (a ^ n) = n • valuation coords a := by
  simp [valuation]

@[simp] theorem valuation_mul_apply (a b : A) (p : ι) :
    valuation coords (a * b) p = valuation coords a p + valuation coords b p := by
  rw [valuation_mul]
  rfl

@[simp] theorem valuation_pow_apply (a : A) (n : ℕ) (p : ι) :
    valuation coords (a ^ n) p = n * valuation coords a p := by
  rw [valuation_pow]
  simp [Finsupp.smul_apply, nsmul_eq_mul]

/-- Lift any zero-preserving operation on exponents to the ideal monoid. -/
def mapExponents (f : ℕ → ℕ) (hf : f 0 = 0) (a : A) : A :=
  coords.symm (Multiplicative.ofAdd ((valuation coords a).mapRange f hf))

@[simp] theorem valuation_mapExponents (f : ℕ → ℕ) (hf : f 0 = 0)
    (a : A) (p : ι) :
    valuation coords (mapExponents coords f hf a) p = f (valuation coords a p) := by
  simp [valuation, mapExponents]

def Supported (s : Finset ι) (a : A) : Prop :=
  SupportedOn s (valuation coords a)

def Avoids (s : Finset ι) (a : A) : Prop :=
  AvoidsSupport s (valuation coords a)

def Coprime (a b : A) : Prop :=
  DisjointValuations (valuation coords a) (valuation coords b)

def supportedFactor (s : Finset ι) (a : A) : A :=
  coords.symm (Multiplicative.ofAdd
    ((valuation coords a).filter fun p => p ∈ s))

def awayFactor (s : Finset ι) (a : A) : A :=
  coords.symm (Multiplicative.ofAdd
    ((valuation coords a).filter fun p => p ∉ s))

def cubeSplit (s : Finset ι) (a : A) : A × A :=
  (supportedFactor coords s a, awayFactor coords s a)

@[simp] theorem valuation_supportedFactor (s : Finset ι) (a : A) (p : ι) :
    valuation coords (supportedFactor coords s a) p =
      if p ∈ s then valuation coords a p else 0 := by
  simp [valuation, supportedFactor, Finsupp.filter_apply]

@[simp] theorem valuation_awayFactor (s : Finset ι) (a : A) (p : ι) :
    valuation coords (awayFactor coords s a) p =
      if p ∈ s then 0 else valuation coords a p := by
  by_cases hp : p ∈ s <;> simp [valuation, awayFactor, Finsupp.filter_apply, hp]

theorem supportedFactor_supported (s : Finset ι) (a : A) :
    Supported coords s (supportedFactor coords s a) := by
  intro p hp
  simp [hp]

theorem awayFactor_avoids (s : Finset ι) (a : A) :
    Avoids coords s (awayFactor coords s a) := by
  intro p hp
  simp [hp]

/-- The complete cube has a canonical supported/away product decomposition. -/
theorem supported_mul_away (s : Finset ι) (a : A) :
    supportedFactor coords s a * awayFactor coords s a = a := by
  apply valuation_injective coords
  ext p
  by_cases hp : p ∈ s <;> simp [hp]

/-- Both factors are recovered from their product under the actual support
conditions.  In particular no splitting map has to be guessed. -/
theorem cubeSplit_mul (s : Finset ι) (x n : A)
    (hx : Supported coords s x) (hn : Avoids coords s n) :
    cubeSplit coords s (x * n) = (x, n) := by
  apply Prod.ext
  · apply valuation_injective coords
    ext p
    change valuation coords (supportedFactor coords s (x * n)) p =
      valuation coords x p
    by_cases hp : p ∈ s
    · simp [hp, hn p hp]
    · simp [hp, hx p hp]
  · apply valuation_injective coords
    ext p
    change valuation coords (awayFactor coords s (x * n)) p =
      valuation coords n p
    by_cases hp : p ∈ s
    · simp [hp, hn p hp]
    · simp [hp, hx p hp]

theorem supported_away_unique (s : Finset ι) (a x n : A)
    (hx : Supported coords s x) (hn : Avoids coords s n) (ha : a = x * n) :
    x = supportedFactor coords s a ∧ n = awayFactor coords s a := by
  have h := cubeSplit_mul coords s x n hx hn
  rw [← ha] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem coprime_of_avoids_supported (s : Finset ι) (P x : A)
    (hP : Avoids coords s P) (hx : Supported coords s x) :
    Coprime coords P x :=
  disjoint_supported_of_avoids hP hx

theorem coprime_symm (a b : A) : Coprime coords a b ↔ Coprime coords b a := by
  constructor <;> intro h p <;> exact (h p).symm

theorem coprime_mul_right (a b c : A) :
    Coprime coords a (b * c) ↔ Coprime coords a b ∧ Coprime coords a c := by
  change DisjointValuations (valuation coords a) (valuation coords (b * c)) ↔ _
  rw [valuation_mul]
  exact disjoint_add_right

theorem coprime_fullCube (s : Finset ι) (P x n : A)
    (hP : Avoids coords s P) (hx : Supported coords s x) :
    Coprime coords P (x * n) ↔ Coprime coords P n := by
  rw [coprime_mul_right]
  exact and_iff_right (coprime_of_avoids_supported coords s P x hP hx)

def minimumFactor (a : A) : A := mapExponents coords frozenMin frozenMin_zero a

def residualCubeFactor (a : A) : A :=
  mapExponents coords frozenCubeExp frozenCubeExp_zero a

/-- Exact ideal-valued freezing, using the canonical factors constructed
from all prime coordinates simultaneously. -/
theorem minimum_mul_residualCube (a : A)
    (ha : ∀ p, AdmissibleExponent (valuation coords a p)) :
    a = minimumFactor coords a * residualCubeFactor coords a ^ 3 := by
  apply valuation_injective coords
  ext p
  simp only [minimumFactor, residualCubeFactor, valuation_mul_apply,
    valuation_mapExponents, valuation_pow_apply]
  exact frozenExponent_decomposition _ (ha p)

theorem residualCubeFactor_supported (s : Finset ι) (a : A)
    (ha : Supported coords s a) : Supported coords s (residualCubeFactor coords a) := by
  intro p hp
  simp [residualCubeFactor, ha p hp]

theorem minimumFactor_supported (s : Finset ι) (a : A)
    (ha : Supported coords s a) : Supported coords s (minimumFactor coords a) := by
  intro p hp
  simp [minimumFactor, ha p hp]

theorem coprime_residualCubeFactor (s : Finset ι) (P a : A)
    (hP : Avoids coords s P) (ha : Supported coords s a) :
    Coprime coords P (residualCubeFactor coords a) :=
  coprime_of_avoids_supported coords s P _ hP
    (residualCubeFactor_supported coords s a ha)

/-- A genuine shared prime forces the symbol to zero by the sixth-power
collision law. This derives the whole-index overlap input from the symbol. -/
theorem symbol_zero_of_shared_prime
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (a b : A) (p : ι) (ha : valuation coords a p ≠ 0)
    (hb : valuation coords b p ≠ 0) : chi a b = 0 := by
  have hn : ¬ Coprime coords a b := by
    intro h
    exact (h p).elim ha hb
  have hz : (chi a b) ^ 6 = 0 := by simpa [hn] using h6 a b
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hz

end

end HeckeSkeleton.LowFrozenCube.PrimeCoordinates
