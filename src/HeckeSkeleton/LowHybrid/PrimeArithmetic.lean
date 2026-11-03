import HeckeSkeleton.LowHybrid.NormalFormFinite
import HeckeSkeleton.LowHybrid.Factorization
import HeckeSkeleton.LowHybrid.Masks
import HeckeSkeleton.LowFrozenCube.PrimeCoordinates

/-!
# Canonical arithmetic and completed-square data from prime coordinates

The finite Mobius expansion and the completed-square splitting are constructed
from unique prime factorization. They are not abstract normal-form inputs.
The only symbol assumptions in `arithmetic` are its elementary multiplicative
and sixth-power laws. The norm assumptions are multiplicativity and positivity.
-/

namespace HeckeSkeleton.LowHybrid.PrimeArithmetic

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates
open HeckeSkeleton.LowHybrid.NormalForm

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def support (a : A) : Finset ι := (valuation coords a).support

def mapTwo (f : ℕ → ℕ → ℕ) (hf : f 0 0 = 0) (a b : A) : A :=
  coords.symm (Multiplicative.ofAdd
    (Finsupp.zipWith f hf (valuation coords a) (valuation coords b)))

@[simp] theorem valuation_mapTwo (f : ℕ → ℕ → ℕ) (hf : f 0 0 = 0)
    (a b : A) (p : ι) :
    valuation coords (mapTwo coords f hf a b) p =
      f (valuation coords a p) (valuation coords b p) := by
  simp [valuation, mapTwo]

def quotient (d k : A) : A := mapTwo coords (fun a b => b - a) rfl d k

@[simp] theorem valuation_quotient (d k : A) (p : ι) :
    valuation coords (quotient coords d k) p =
      valuation coords k p - valuation coords d p := by
  simp [quotient]

theorem dvd_iff_coordinates_le (a b : A) :
    a ∣ b ↔ ∀ p, valuation coords a p ≤ valuation coords b p := by
  constructor
  · rintro ⟨c, rfl⟩ p
    simp only [valuation_mul_apply]
    omega
  · intro h
    refine ⟨quotient coords a b, ?_⟩
    apply valuation_injective coords
    ext p
    simp only [valuation_mul_apply, valuation_quotient]
    have hp := h p
    omega

theorem quotient_spec (d k : A) (h : d ∣ k) : d * quotient coords d k = k := by
  have hle := (dvd_iff_coordinates_le coords d k).mp h
  apply valuation_injective coords
  ext p
  simp only [valuation_mul_apply, valuation_quotient]
  have hp := hle p
  omega

def fromSupport (s : Finset ι) : A :=
  coords.symm (Multiplicative.ofAdd (Finsupp.onFinset s
    (fun p => if p ∈ s then (1 : ℕ) else 0)
    (by intro p hp; by_contra h; simp [h] at hp)))

@[simp] theorem valuation_fromSupport (s : Finset ι) (p : ι) :
    valuation coords (fromSupport coords s) p = if p ∈ s then 1 else 0 := by
  simp [valuation, fromSupport]

@[simp] theorem support_fromSupport (s : Finset ι) :
    support coords (fromSupport coords s) = s := by
  ext p
  simp [support]

theorem fromSupport_injective : Function.Injective (fromSupport coords) := by
  intro s t h
  simpa only [support_fromSupport] using congrArg (support coords) h

theorem fromSupport_dvd_iff (s : Finset ι) (a : A) :
    fromSupport coords s ∣ a ↔ s ⊆ support coords a := by
  rw [dvd_iff_coordinates_le coords]
  constructor
  · intro h p hp
    have hv : 1 ≤ valuation coords a p := by
      simpa [valuation, fromSupport, hp] using h p
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h p
    rw [valuation_fromSupport]
    by_cases hp : p ∈ s
    · have hv := Finsupp.mem_support_iff.mp (h hp)
      simp only [if_pos hp]
      omega
    · simp [hp]

theorem coprime_iff_disjoint_support (a b : A) :
    Coprime coords a b ↔ Disjoint (support coords a) (support coords b) := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro p ha hb
    have hap := Finsupp.mem_support_iff.mp ha
    have hbp := Finsupp.mem_support_iff.mp hb
    exact (h p).elim hap hbp
  · intro h p
    by_cases ha : valuation coords a p = 0
    · exact Or.inl ha
    · right
      by_contra hb
      exact Finset.disjoint_left.mp h (Finsupp.mem_support_iff.mpr ha)
        (Finsupp.mem_support_iff.mpr hb)

/-- The squarefree divisors of any ideal, constructed from its finite support. -/
def divisors (a : A) : Finset A := (support coords a).powerset.image (fromSupport coords)

def mobius (a : A) : ℂ := (-1 : ℂ) ^ (support coords a).card

theorem divisor_dvd (a d : A) (hd : d ∈ divisors coords a) : d ∣ a := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
  exact (fromSupport_dvd_iff coords s a).mpr (Finset.mem_powerset.mp hs)

theorem mobius_norm (a : A) : ‖mobius coords a‖ = 1 := by simp [mobius]

theorem mobius_expansion (p k : A) :
    (if Coprime coords p k then (1 : ℂ) else 0) =
      ∑ d ∈ divisors coords k, if d ∣ p then mobius coords d else 0 := by
  calc
    _ = (if Disjoint (support coords p) (support coords k) then (1 : ℂ) else 0) := by
      by_cases h : Coprime coords p k
      · have hd := (coprime_iff_disjoint_support coords p k).mp h
        simp [h, hd]
      · have hd : ¬ Disjoint (support coords p) (support coords k) :=
          fun hd => h ((coprime_iff_disjoint_support coords p k).mpr hd)
        simp [h, hd]
    _ = ∑ s ∈ (support coords k).powerset,
        if s ⊆ support coords p then (-1 : ℂ) ^ s.card else 0 :=
      support_coprime_mask_eq_row_divisor_sum (support coords p) (support coords k)
    _ = _ := by
      unfold divisors
      rw [Finset.sum_image (fun _ _ _ _ h => fromSupport_injective coords h)]
      apply Finset.sum_congr rfl
      intro s hs
      have hd := fromSupport_dvd_iff coords s p
      by_cases h : s ⊆ support coords p <;> simp [hd, h, mobius]

/-- All elementary arithmetic fields, including the Mobius formula, are
instantiated from the actual prime-coordinate equivalence. -/
def arithmetic (normI : A → ℝ) (hn : ∀ a, 0 ≤ normI a)
    (hnmul : ∀ a b, normI (a * b) = normI a * normI b)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0) :
    Arithmetic A where
  normI := normI
  norm_nonneg := hn
  norm_mul := hnmul
  symbol := symbol
  symbol_mul_left := hleft
  symbol_mul_right := hright
  cop := Coprime coords
  cop_symm := coprime_symm coords
  cop_mul_left := by
    intro a b c
    rw [coprime_symm coords (a * b) c, coprime_mul_right,
      coprime_symm coords c a, coprime_symm coords c b]
  cop_mul_right := coprime_mul_right coords
  six := h6
  divisors := divisors coords
  mu := mobius coords
  quotient := quotient coords
  divisor_dvd := divisor_dvd coords
  quotient_spec := quotient_spec coords
  mobius_expansion := mobius_expansion coords

def squarePart (b : A) : A := mapExponents coords (fun e => e / 2) rfl b
def commonPart (n b : A) : A :=
  mapTwo coords Factorization.commonExp (by rfl) n b
def leftPart (n b : A) : A := mapTwo coords Factorization.leftExp (by rfl) n b
def rightPart (n b : A) : A := mapTwo coords Factorization.rightExp (by rfl) n b

def completedSplit (x : A × A) : CompletedIndex A :=
  (squarePart coords x.2, commonPart coords x.1 x.2,
    leftPart coords x.1 x.2, rightPart coords x.1 x.2)

theorem completedSplit_reconstruct (x : A × A) :
    recombine (completedSplit coords x) = x := by
  rcases x with ⟨n, b⟩
  apply Prod.ext
  · apply valuation_injective coords
    ext p
    change valuation coords (commonPart coords n b * leftPart coords n b) p =
      valuation coords n p
    simp only [valuation_mul_apply]
    simp [commonPart, leftPart, valuation, mapTwo]
    exact (Factorization.split_left _ _).symm
  · apply valuation_injective coords
    ext p
    change valuation coords
      (commonPart coords n b * rightPart coords n b * squarePart coords b ^ 2) p =
      valuation coords b p
    simp only [valuation_mul_apply, valuation_pow_apply]
    rw [show valuation coords (commonPart coords n b) p =
        Factorization.commonExp (valuation coords n p) (valuation coords b p) from
      valuation_mapTwo coords Factorization.commonExp (by rfl) n b p]
    rw [show valuation coords (rightPart coords n b) p =
        Factorization.rightExp (valuation coords n p) (valuation coords b p) from
      valuation_mapTwo coords Factorization.rightExp (by rfl) n b p]
    rw [show valuation coords (squarePart coords b) p = valuation coords b p / 2 from
      valuation_mapExponents coords (fun e => e / 2) rfl b p]
    have h := Factorization.split_right (valuation coords n p) (valuation coords b p)
    have hb := Factorization.square_extraction (valuation coords b p)
    unfold Factorization.squareExp at hb
    omega

/-- Completion is now an explicit construction for arbitrary finite supports. -/
def completion (columns cubes : Finset A) : Completion columns cubes where
  split := completedSplit coords
  reconstruct := fun x _ => completedSplit_reconstruct coords x

def Squarefree (a : A) : Prop := ∀ p, valuation coords a p ≤ 1

theorem squarefree_of_dvd {a b : A} (ha : a ∣ b) (hb : Squarefree coords b) :
    Squarefree coords a := by
  intro p
  exact ((dvd_iff_coordinates_le coords a b).mp ha p).trans (hb p)

theorem completed_residual_squarefree (n b : A) (hn : Squarefree coords n) :
    Squarefree coords (leftPart coords n b * rightPart coords n b) := by
  intro p
  simp only [valuation_mul_apply]
  simp [leftPart, rightPart, valuation, mapTwo]
  exact Factorization.residual_exponent_le_one _ _ (hn p)

theorem squarefree_mem_divisors (a d : A) (hd : d ∈ divisors coords a) :
    Squarefree coords d := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
  intro p
  rw [valuation_fromSupport]
  split_ifs <;> omega

#print axioms mobius_expansion
#print axioms completedSplit_reconstruct
#print axioms completed_residual_squarefree

end
end HeckeSkeleton.LowHybrid.PrimeArithmetic
