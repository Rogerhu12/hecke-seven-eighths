import SIntegerSexticFiniteCorrelation

/-! SOURCE ONLY, UNRUN. Exact zero-frequency mass of the actual quotient
character. The unit-column formula retains the unit-ratio phase; it is
not a claim that distinct associate columns give the literal diagonal.
No Euler-phi or unit-count identification is assumed. -/
noncomputable section
namespace HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators

variable {R : Type*} [CommRing R] [Fintype R]

theorem affineCorrelation_one_one_zero (f : R → ℂ) :
    affineCorrelation f 1 1 0 = ∑ x : R, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
  unfold affineCorrelation
  rw [Fintype.sum_prod_type]
  simp only [one_mul, sub_eq_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.mul_conj']
  simp

theorem affineCorrelation_unit_columns_zero (f : R → ℂ)
    (hf : ∀ x y, f (x * y) = f x * f y) (u v : Rˣ) :
    affineCorrelation f (u : R) (v : R) 0 =
      starRingEnd ℂ (f (((u⁻¹ * v : Rˣ) : R))) *
        ∑ x : R, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
  let r : R := ((u⁻¹ * v : Rˣ) : R)
  have he (x y : R) : (v : R) * x - (u : R) * y = 0 ↔ y = r * x := by
    rw [sub_eq_zero]
    constructor
    · intro h
      apply (Units.mulLeft u).injective
      change (u : R) * y = (u : R) * (r * x)
      simpa [r, Units.val_mul, mul_assoc] using h.symm
    · intro h
      rw [h]
      simp [r, Units.val_mul, mul_assoc]
  unfold affineCorrelation
  rw [Fintype.sum_prod_type]
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [hf, map_mul]
  calc
    f x * (starRingEnd ℂ (f r) * starRingEnd ℂ (f x)) =
        starRingEnd ℂ (f r) * (f x * starRingEnd ℂ (f x)) := by ring
    _ = _ := by rw [Complex.mul_conj']; simp [r, Units.val_mul]

end HeckeGeneral.Arithmetic.PeriodicFourier

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)
local notation "Q" => S.integer K ⧸ I.map (algebraMap (𝓞 K) (S.integer K))
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ I hI hS h6

theorem sIntegerSexticIdealQuotientFunction_mul (x y : Q) :
    Φ (x * y) = Φ x * Φ y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul]
  simp only [sIntegerSexticIdealQuotientFunction_mk]
  exact sIntegerSexticIdealEvaluation_mul K S ζ hζ σ I hI hS h6 x y

/-- Exact diagonal mass, including I=top (the singleton zero ring).
Every term uses the actual zero-extended quotient character. -/
theorem sIntegerSexticFiniteCorrelation_one_one_zero :
    letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
    letI : Fintype Q := Fintype.ofFinite Q
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 1 1 0 =
      ∑ x : Q, ((‖Φ x‖ ^ 2 : ℝ) : ℂ) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI : Fintype Q := Fintype.ofFinite Q
  exact affineCorrelation_one_one_zero Φ

/-- For two quotient units, the phase is the conjugate of the actual
character at u^{-1}v; distinct associates need not have diagonal phase. -/
theorem sIntegerSexticFiniteCorrelation_unit_columns_zero (u v : Qˣ) :
    letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
    letI : Fintype Q := Fintype.ofFinite Q
    sIntegerSexticFiniteCorrelation K S ζ hζ σ I hI hS h6 (u : Q) (v : Q) 0 =
      starRingEnd ℂ (Φ (((u⁻¹ * v : Qˣ) : Q))) *
        ∑ x : Q, ((‖Φ x‖ ^ 2 : ℝ) : ℂ) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S I hI hS
  letI : Fintype Q := Fintype.ofFinite Q
  exact affineCorrelation_unit_columns_zero Φ
    (sIntegerSexticIdealQuotientFunction_mul K S ζ hζ σ I hI hS h6) u v

end HeckeGeneral.Characters
