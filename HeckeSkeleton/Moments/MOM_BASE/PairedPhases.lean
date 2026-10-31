import HeckeGeneral.Analysis.HeckeConjugation
import HeckeGeneral.Characters.UnramifiedPrimeCoefficientAlgebra

/-!
# Paired whole-product phases

The coefficient identities in Lemma 4.4 of `weil_seven_eighths_revised.tex`.
All characters below are actual continuous unitary Hecke characters.  The
Euler values retain their original ramified zeros.  In particular the
product of two zero-extended characters is identified with the coefficient
of their product only after its original presentation mask is inserted.

The finite-transform lemmas apply to literal finite tables of finite Hecke
twists.  They leave the background on its entire residual index and keep
each slot's inverse-background coefficient.  The two-transform formula is
the iterated finite-table identity, before estimating any prime sum.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE.Paired

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The two original ramification exclusions, before character cancellation. -/
def originalPrimeMask (ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if UnramifiedAt K ξ p ∧ UnramifiedAt K θ p then 1 else 0

theorem originalPrimeMask_mul (ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K ξ p * primeCoefficient K θ p =
      primeCoefficient K (ξ * θ) p * originalPrimeMask K ξ θ p := by
  by_cases hξ : UnramifiedAt K ξ p
  · by_cases hθ : UnramifiedAt K θ p
    · rw [originalPrimeMask, if_pos ⟨hξ, hθ⟩, mul_one,
        primeCoefficient_mul_right_unramified K ξ θ p hθ]
    · rw [primeCoefficient_of_ramified K θ p hθ]
      simp [originalPrimeMask, hθ]
  · rw [primeCoefficient_of_ramified K ξ p hξ]
    simp [originalPrimeMask, hξ]

theorem originalPrimeMask_norm_le_one (ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) : ‖originalPrimeMask K ξ θ p‖ ≤ 1 := by
  unfold originalPrimeMask
  split_ifs <;> simp

theorem originalPrimeMask_conjugate (ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) :
    originalPrimeMask K ξ⁻¹ θ⁻¹ p = originalPrimeMask K ξ θ p := by
  simp only [originalPrimeMask, unramifiedAt_inv_iff]

theorem norm_primeCoefficient_of_unramified (ω : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    ‖primeCoefficient K ω p‖ = 1 := by
  rw [primeCoefficient_of_unramified K ω p hω]
  exact Circle.norm_coe _

theorem primeCoefficient_ne_zero_of_unramified (ω : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    primeCoefficient K ω p ≠ 0 := by
  intro hz
  have hn := norm_primeCoefficient_of_unramified K ω p hω
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

theorem primeCoefficient_inverse_of_unramified (ω : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    primeCoefficient K ω⁻¹ p = (primeCoefficient K ω p)⁻¹ := by
  rw [primeCoefficient_of_unramified K ω⁻¹ p (hω.inv K),
    primeCoefficient_of_unramified K ω p hω]
  rfl

/-- Pointwise cancellation of the actual live background and its specified
relative slot coefficient.  The finite row and slot may both be ramified;
their original zeros remain on the right even if their product is unramified. -/
theorem paired_primeCoefficient (ω ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    primeCoefficient K (ω * ξ) p *
        ((primeCoefficient K ω p)⁻¹ * primeCoefficient K θ p) =
      primeCoefficient K (ξ * θ) p * originalPrimeMask K ξ θ p := by
  have hprod : primeCoefficient K (ω * ξ) p =
      primeCoefficient K ω p * primeCoefficient K ξ p := by
    rw [mul_comm ω ξ, primeCoefficient_mul_right_unramified K ξ ω p hω, mul_comm]
  rw [hprod]
  calc
    _ = (primeCoefficient K ω p * (primeCoefficient K ω p)⁻¹) *
        (primeCoefficient K ξ p * primeCoefficient K θ p) := by ring
    _ = primeCoefficient K ξ p * primeCoefficient K θ p := by
      rw [mul_inv_cancel₀ (primeCoefficient_ne_zero_of_unramified K ω p hω), one_mul]
    _ = _ := originalPrimeMask_mul K ξ θ p

/-- The same pairing using the actual Hecke character of the relative slot. -/
theorem paired_relativeCoefficient (ω ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    primeCoefficient K (ω * ξ) p * primeCoefficient K (ω⁻¹ * θ) p =
      primeCoefficient K (ξ * θ) p * originalPrimeMask K ξ θ p := by
  have hslot : primeCoefficient K (ω⁻¹ * θ) p =
      (primeCoefficient K ω p)⁻¹ * primeCoefficient K θ p := by
    rw [mul_comm ω⁻¹ θ,
      primeCoefficient_mul_right_unramified K θ ω⁻¹ p (hω.inv K),
      primeCoefficient_inverse_of_unramified K ω p hω, mul_comm]
  rw [hslot]
  exact paired_primeCoefficient K ω ξ θ p hω

/-- A fixed finite-ray twist unramified at the live prime adds no new zero
mask.  The row itself is still allowed to ramify there. -/
theorem paired_primeCoefficient_unramified_slot (ω ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p)
    (hθ : UnramifiedAt K θ p) :
    primeCoefficient K (ω * ξ) p *
        ((primeCoefficient K ω p)⁻¹ * primeCoefficient K θ p) =
      primeCoefficient K (ξ * θ) p := by
  rw [paired_primeCoefficient K ω ξ θ p hω, ← originalPrimeMask_mul K ξ θ p,
    primeCoefficient_mul_right_unramified K ξ θ p hθ]

theorem paired_relativeCoefficient_unramified_slot (ω ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p)
    (hθ : UnramifiedAt K θ p) :
    primeCoefficient K (ω * ξ) p * primeCoefficient K (ω⁻¹ * θ) p =
      primeCoefficient K (ξ * θ) p := by
  rw [paired_relativeCoefficient K ω ξ θ p hω, ← originalPrimeMask_mul K ξ θ p,
    primeCoefficient_mul_right_unramified K ξ θ p hθ]

/-- Every character actually left for prime cancellation has finite order. -/
theorem paired_finiteOrder (ξ θ : HeckeCharacter K)
    (hξ : FiniteOrder ξ) (hθ : FiniteOrder θ) : FiniteOrder (ξ * θ) :=
  hξ.mul hθ

/-- The manuscript permits a fixed finite linear combination in a slot.
Each summand retains its own original zero mask. -/
theorem paired_finite_slot {ι : Type*} (T : Finset ι)
    (a : ι → ℂ) (θ : ι → HeckeCharacter K) (ω ξ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    primeCoefficient K (ω * ξ) p *
        ((primeCoefficient K ω p)⁻¹ * ∑ i ∈ T, a i * primeCoefficient K (θ i) p) =
      ∑ i ∈ T, a i *
        (primeCoefficient K (ξ * θ i) p * originalPrimeMask K ξ (θ i) p) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    _ = a i * (primeCoefficient K (ω * ξ) p *
        ((primeCoefficient K ω p)⁻¹ * primeCoefficient K (θ i) p)) := by ring
    _ = _ := by rw [paired_primeCoefficient K ω ξ (θ i) p hω]

/-- One whole-product presentation.  Its finite factors are actual Hecke
characters; no assertion about a moment bound or a transformation is a field. -/
structure Presentation (ι : Type*) where
  background : HeckeCharacter K
  row : HeckeCharacter K
  row_finite : FiniteOrder row
  slot : ι → HeckeCharacter K
  slot_finite : ∀ i, FiniteOrder (slot i)

namespace Presentation

variable {K} {ι : Type*}

def plainCharacter (P : Presentation K ι) : HeckeCharacter K := P.background * P.row

def relativeCharacter (P : Presentation K ι) (i : ι) : HeckeCharacter K :=
  P.background⁻¹ * P.slot i

def actualFiniteCharacter (P : Presentation K ι) (i : ι) : HeckeCharacter K :=
  P.row * P.slot i

theorem actualFiniteCharacter_finite (P : Presentation K ι) (i : ι) :
    FiniteOrder (P.actualFiniteCharacter i) := P.row_finite.mul (P.slot_finite i)

theorem prime_pairing (P : Presentation K ι) (i : ι)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K P.background p) :
    primeCoefficient K P.plainCharacter p * primeCoefficient K (P.relativeCharacter i) p =
      primeCoefficient K (P.actualFiniteCharacter i) p * originalPrimeMask K P.row (P.slot i) p :=
  paired_relativeCoefficient K P.background P.row (P.slot i) p hω

/-- Finite transforms may twist the row and the finite part of each slot;
the live whole-product background is unchanged. -/
def finiteTwist (P : Presentation K ι) (η : HeckeCharacter K)
    (hη : FiniteOrder η) (τ : ι → HeckeCharacter K)
    (hτ : ∀ i, FiniteOrder (τ i)) : Presentation K ι where
  background := P.background
  row := P.row * η
  row_finite := P.row_finite.mul hη
  slot i := P.slot i * τ i
  slot_finite i := (P.slot_finite i).mul (hτ i)

@[simp] theorem finiteTwist_background (P : Presentation K ι) (η : HeckeCharacter K)
    (hη : FiniteOrder η) (τ : ι → HeckeCharacter K)
    (hτ : ∀ i, FiniteOrder (τ i)) :
    (P.finiteTwist η hη τ hτ).background = P.background := rfl

/-- Every member of the closed finite-twist class has the actual prime pairing. -/
theorem finiteTwist_prime_pairing (P : Presentation K ι) (η : HeckeCharacter K)
    (hη : FiniteOrder η) (τ : ι → HeckeCharacter K)
    (hτ : ∀ i, FiniteOrder (τ i)) (i : ι)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K P.background p) :
    let P' := P.finiteTwist η hη τ hτ
    FiniteOrder (P'.actualFiniteCharacter i) ∧
      primeCoefficient K P'.plainCharacter p * primeCoefficient K (P'.relativeCharacter i) p =
        primeCoefficient K (P'.actualFiniteCharacter i) p *
          originalPrimeMask K P'.row (P'.slot i) p := by
  exact ⟨(P.finiteTwist η hη τ hτ).actualFiniteCharacter_finite i,
    (P.finiteTwist η hη τ hτ).prime_pairing i p hω⟩

/-- Row-orientation reversal conjugates the background and every finite slot. -/
def conjugate (P : Presentation K ι) : Presentation K ι where
  background := P.background⁻¹
  row := P.row⁻¹
  row_finite := P.row_finite.inv
  slot i := (P.slot i)⁻¹
  slot_finite i := (P.slot_finite i).inv

@[simp] theorem conjugate_plainCharacter (P : Presentation K ι) :
    P.conjugate.plainCharacter = P.plainCharacter⁻¹ := by
  simp [conjugate, plainCharacter, mul_inv_rev, mul_comm]

@[simp] theorem conjugate_relativeCharacter (P : Presentation K ι) (i : ι) :
    P.conjugate.relativeCharacter i = (P.relativeCharacter i)⁻¹ := by
  simp [conjugate, relativeCharacter, mul_inv_rev, mul_comm]

@[simp] theorem conjugate_actualFiniteCharacter (P : Presentation K ι) (i : ι) :
    P.conjugate.actualFiniteCharacter i = (P.actualFiniteCharacter i)⁻¹ := by
  simp [conjugate, actualFiniteCharacter, mul_inv_rev, mul_comm]

theorem conjugate_prime_pairing (P : Presentation K ι) (i : ι)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K P.background p) :
    primeCoefficient K P.conjugate.plainCharacter p *
        primeCoefficient K (P.conjugate.relativeCharacter i) p =
      conj (primeCoefficient K (P.actualFiniteCharacter i) p) *
        originalPrimeMask K P.row (P.slot i) p := by
  rw [P.conjugate.prime_pairing i p (hω.inv K), conjugate_actualFiniteCharacter,
    primeCoefficient_inv]
  congr 1
  exact originalPrimeMask_conjugate K P.row (P.slot i) p

end Presentation

/-- A literal finite transform of the finite part leaves the paired live
background intact, including every zero in every table entry. -/
theorem finite_transform_prime_pairing {ι : Type*} (T : Finset ι)
    (a : ι → ℂ) (η : ι → HeckeCharacter K) (ω ξ θ : HeckeCharacter K)
    (p : HeightOneSpectrum (𝓞 K)) (hω : UnramifiedAt K ω p) :
    (∑ i ∈ T, a i * primeCoefficient K (ω * (ξ * η i)) p) *
        primeCoefficient K (ω⁻¹ * θ) p =
      ∑ i ∈ T, a i * (primeCoefficient K ((ξ * η i) * θ) p *
        originalPrimeMask K (ξ * η i) θ p) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_assoc, paired_relativeCoefficient K ω (ξ * η i) θ p hω]

/-- Both successive finite transforms are kept as actual table sums.
Their original individual slot coefficient is the same on the left. -/
theorem two_finite_transforms_prime_pairing {ι κ : Type*}
    (T : Finset ι) (U : Finset κ) (a : ι → κ → ℂ)
    (η : ι → HeckeCharacter K) (τ : κ → HeckeCharacter K)
    (ω ξ θ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K))
    (hω : UnramifiedAt K ω p) :
    (∑ i ∈ T, ∑ j ∈ U, a i j * primeCoefficient K (ω * ((ξ * η i) * τ j)) p) *
        primeCoefficient K (ω⁻¹ * θ) p =
      ∑ i ∈ T, ∑ j ∈ U, a i j *
        (primeCoefficient K (((ξ * η i) * τ j) * θ) p *
          originalPrimeMask K ((ξ * η i) * τ j) θ p) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  exact finite_transform_prime_pairing K U (a i) τ ω (ξ * η i) θ p hω

theorem two_finite_transforms_finiteOrder {ι κ : Type*}
    (ξ θ : HeckeCharacter K) (hξ : FiniteOrder ξ) (hθ : FiniteOrder θ)
    (η : ι → HeckeCharacter K) (hη : ∀ i, FiniteOrder (η i))
    (τ : κ → HeckeCharacter K) (hτ : ∀ j, FiniteOrder (τ j)) (i : ι) (j : κ) :
    FiniteOrder (((ξ * η i) * τ j) * θ) :=
  ((hξ.mul (hη i)).mul (hτ j)).mul hθ

/-- Character multiplication at an actual ideal is valid when the fixed
background is unramified at all of its prime divisors. -/
theorem idealCoefficient_character_mul (ξ ω : HeckeCharacter K) (I : NonzeroIdeal K)
    (hω : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K ω p) :
    heckeIdealCoefficient K (ξ * ω) I =
      heckeIdealCoefficient K ξ I * heckeIdealCoefficient K ω I := by
  have hI : I.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient, if_neg hI]
  rw [← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hprime := prime_of_normalized_factor P hP
  simp only [primeIdealValue, dif_pos hprime]
  exact primeCoefficient_mul_right_unramified K ξ ω (HeightOneSpectrum.ofPrime hprime)
    (hω _ (dvd_of_mem_normalizedFactors hP))

/-- The frozen whole-product background is a unit scalar on its original
unramified support. -/
theorem norm_idealCoefficient_of_unramified (ω : HeckeCharacter K) (I : NonzeroIdeal K)
    (hω : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → UnramifiedAt K ω p) :
    ‖heckeIdealCoefficient K ω I‖ = 1 := by
  have hI : I.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  simp only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient, if_neg hI]
  rw [Multiset.norm_prod_map]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  have hprime := prime_of_normalized_factor P hP
  simp only [primeIdealValue, dif_pos hprime]
  exact norm_primeCoefficient_of_unramified K ω (HeightOneSpectrum.ofPrime hprime)
    (hω _ (dvd_of_mem_normalizedFactors hP))

/-- Exact extraction before division or estimation.  Ramified zeros of the
row remain on the same actual ideals on both sides. -/
theorem whole_product_extraction (λ : HeckeCharacter K) (D A : NonzeroIdeal K) :
    heckeIdealCoefficient K λ (D * A) =
      heckeIdealCoefficient K λ D * heckeIdealCoefficient K λ A :=
  heckeIdealCoefficient_mul K λ D A

/-- A common background is cancelled on the whole product, before profiles
are separated.  This is the two-column identity preceding Lemma 4.3. -/
theorem whole_product_common_cancellation (ω : HeckeCharacter K)
    (A₁ A₂ C U₁ U₂ : NonzeroIdeal K)
    (hC : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C.val → UnramifiedAt K ω p) :
    heckeIdealCoefficient K ω (A₁ * C * U₁) *
        conj (heckeIdealCoefficient K ω (A₂ * C * U₂)) =
      (heckeIdealCoefficient K ω A₁ * conj (heckeIdealCoefficient K ω A₂)) *
        (heckeIdealCoefficient K ω U₁ * conj (heckeIdealCoefficient K ω U₂)) := by
  have hc : heckeIdealCoefficient K ω C * conj (heckeIdealCoefficient K ω C) = 1 := by
    rw [Complex.mul_conj', norm_idealCoefficient_of_unramified K ω C hC]
    norm_num
  simp only [heckeIdealCoefficient_mul, map_mul]
  calc
    _ = (heckeIdealCoefficient K ω A₁ * conj (heckeIdealCoefficient K ω A₂)) *
        (heckeIdealCoefficient K ω U₁ * conj (heckeIdealCoefficient K ω U₂)) *
          (heckeIdealCoefficient K ω C * conj (heckeIdealCoefficient K ω C)) := by ring
    _ = _ := by rw [hc, mul_one]

theorem frozen_background_norm_square (ω : HeckeCharacter K) (D A : NonzeroIdeal K)
    (hD : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ D.val → UnramifiedAt K ω p)
    (z : ℂ) :
    ‖heckeIdealCoefficient K ω (D * A) * z‖ ^ 2 =
      ‖heckeIdealCoefficient K ω A * z‖ ^ 2 := by
  rw [whole_product_extraction K ω D A, mul_assoc, norm_mul,
    norm_idealCoefficient_of_unramified K ω D hD, one_mul]

/-- An extracted actual row coefficient with its zeros is a contraction. -/
theorem frozen_row_norm_square_le (λ : HeckeCharacter K) (D A : NonzeroIdeal K)
    (z : ℂ) :
    ‖heckeIdealCoefficient K λ (D * A) * z‖ ^ 2 ≤
      ‖heckeIdealCoefficient K λ A * z‖ ^ 2 := by
  rw [whole_product_extraction K λ D A, mul_assoc, norm_mul]
  apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_heckeIdealCoefficient_le_one K λ D) (norm_nonneg (heckeIdealCoefficient K λ A * z))

/-- Finite Fourier tables can be expanded with the background still on
the entire residual ideal.  No unramifiedness is imposed on the finite factors. -/
theorem finite_transform_whole_background {ι : Type*} (T : Finset ι)
    (a : ι → ℂ) (ξ : ι → HeckeCharacter K) (ω : HeckeCharacter K)
    (A : NonzeroIdeal K)
    (hω : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ A.val → UnramifiedAt K ω p) :
    (∑ i ∈ T, a i * heckeIdealCoefficient K (ω * ξ i) A) =
      heckeIdealCoefficient K ω A * ∑ i ∈ T, a i * heckeIdealCoefficient K (ξ i) A := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_comm ω (ξ i), idealCoefficient_character_mul K (ξ i) ω A hω]
  ring

/-- Freezing a whole product commutes with both finite-table expansions. -/
theorem two_finite_transforms_whole_background {ι κ : Type*}
    (T : Finset ι) (U : Finset κ) (a : ι → κ → ℂ)
    (ξ : ι → κ → HeckeCharacter K) (ω : HeckeCharacter K)
    (D A : NonzeroIdeal K)
    (hω : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ (D * A).val →
      UnramifiedAt K ω p) :
    (∑ i ∈ T, ∑ j ∈ U, a i j * heckeIdealCoefficient K (ω * ξ i j) (D * A)) =
      heckeIdealCoefficient K ω D * heckeIdealCoefficient K ω A *
        ∑ i ∈ T, ∑ j ∈ U, a i j * heckeIdealCoefficient K (ξ i j) (D * A) := by
  rw [← heckeIdealCoefficient_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact finite_transform_whole_background K U (a i) (ξ i) ω (D * A) hω

def maskIndicator (b : Bool) : ℂ := if b then 1 else 0

@[simp] theorem maskIndicator_conjugate (b : Bool) :
    conj (maskIndicator b) = maskIndicator b := by
  cases b <;> simp [maskIndicator]

/-- The same original common mask and conjugated test accompany the
conjugated character in an actual finite ideal sum. -/
theorem masked_ideal_sum_conjugate (χ : HeckeCharacter K) (L : Finset (NonzeroIdeal K))
    (W : NonzeroIdeal K → ℂ) (mask : NonzeroIdeal K → Bool) :
    (∑ I ∈ L, heckeIdealCoefficient K χ⁻¹ I * conj (W I) * maskIndicator (mask I)) =
      conj (∑ I ∈ L, heckeIdealCoefficient K χ I * W I * maskIndicator (mask I)) := by
  simp only [map_sum, map_mul, heckeIdealCoefficient_inv, maskIndicator_conjugate]

/-- A real normalization is preserved by the same operation. -/
theorem normalized_masked_ideal_sum_conjugate (χ : HeckeCharacter K)
    (L : Finset (NonzeroIdeal K)) (W : NonzeroIdeal K → ℂ)
    (mask : NonzeroIdeal K → Bool) (N : ℝ) :
    (N : ℂ)⁻¹ *
        (∑ I ∈ L, heckeIdealCoefficient K χ⁻¹ I * conj (W I) * maskIndicator (mask I)) =
      conj ((N : ℂ)⁻¹ *
        (∑ I ∈ L, heckeIdealCoefficient K χ I * W I * maskIndicator (mask I))) := by
  rw [masked_ideal_sum_conjugate K χ L W mask, map_mul, map_inv₀, Complex.conj_ofReal]

/-- A reflected plain sum can be conjugated by itself inside the absolute
square of an uncentered product. -/
theorem one_plain_conjugation_norm_square (A B Q : ℂ) :
    ‖conj A * B * Q‖ ^ 2 = ‖A * B * Q‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_conj]

/-- Entire row-orientation reversal conjugates both rectangles and their
common slots together; it preserves the centered expression exactly. -/
theorem centered_orientation_norm_square (A B C D Q : ℂ) :
    ‖conj A * conj B * conj Q - conj C * conj D * conj Q‖ ^ 2 =
      ‖A * B * Q - C * D * Q‖ ^ 2 := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, Complex.norm_conj]

/-- Splitting off a common frozen background phase acts on both comparison
rectangles at once, with their common profiles still in place. -/
theorem centered_common_phase_norm_square (u A B C D Q : ℂ) (hu : ‖u‖ = 1) :
    ‖u * (A * B * Q) - u * (C * D * Q)‖ ^ 2 =
      ‖A * B * Q - C * D * Q‖ ^ 2 := by
  rw [← mul_sub, norm_mul, hu, one_mul]

end HeckeSkeleton.Moments.MOM_BASE.Paired
