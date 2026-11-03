import HeckeSkeleton.HighBinSupport.PrincipalPowerSupport
import HeckeSkeleton.HighBinSupport.FiniteLocalTable
/-!
# The literal prime-power Fourier sum equals the valuation table

This is the missing link between actual quotient-ring finite sums and the
explicit table used by the Euler-series calculation. The assumptions are
independent arithmetic data: a prime element, its quotient cardinality,
a primitive additive character, and compatibility with the specified
level-one character. No Gauss evaluation or local Euler identity is assumed.

For the actual S-integer character, the compatibility assertion is proved
in the project-only candidate `ActualInitialAbsolute.principalPower_character_compatible`.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

noncomputable section
namespace HighBin.PrincipalPowerGauss
open HighBin.FiniteResidueFourier HighBin.PrimePowerFourier
open HighBin.PrincipalPowerSupport HighBin.FiniteLocalTable
open scoped Classical

variable {A : Type*} [CommRing A] [IsDomain A]
variable (π : A) (n : ℕ) (hn : 1 ≤ n)
variable [(powerIdeal π 1).IsMaximal]
local instance : Field (PowerQuotient π 1) := Ideal.Quotient.field (powerIdeal π 1)
variable [Fintype (PowerQuotient π n)] [Fintype (PowerQuotient π 1)]

/-- Exact character-sum evaluation for every valuation and every power
of the specified sextic character, including its principal powers.
The zero extension at the prime remains present in every branch. -/
theorem fourier_eq_valuationGauss
    (hπ : Prime π) (v : A) (hv : ¬π ∣ v) (J r : ℕ)
    (χ : MulChar (PowerQuotient π 1) ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar (PowerQuotient π n) ℂ) (hψ : ψ.IsPrimitive)
    (φ : AddChar (PowerQuotient π 1) ℂ)
    (hc : Fintype.card (PowerQuotient π n) = Fintype.card (PowerQuotient π 1) ^ n)
    (hcompat : ∀ x : A,
      ψ (Ideal.Quotient.mk (powerIdeal π n) (π ^ (n - 1) * x)) =
        φ (Ideal.Quotient.mk (powerIdeal π 1) x)) :
    HighBin.FiniteResidueFourier.fourier ψ
      (fun x => (χ ^ r) (residueMap π n hn x))
      (Ideal.Quotient.mk (powerIdeal π n) (π ^ J * v)) =
        valuationGauss (Fintype.card (PowerQuotient π 1))
          (fun b => gaussSum (χ ^ b) φ)
          (χ (Ideal.Quotient.mk (powerIdeal π 1) v)) n r J := by
  have hk : (Nat.card {x : PowerQuotient π n // residueMap π n hn x = 0} : ℂ) =
      (Fintype.card (PowerQuotient π 1) : ℂ) ^ (n - 1) := by
    rw [residue_kernel_card π n hn hc, Nat.cast_pow]
  unfold valuationGauss
  by_cases hr : 6 ∣ r
  · rw [if_pos hr]
    have hχr : χ ^ r = 1 := orderOf_dvd_iff_pow_eq_one.mp (hχ.symm ▸ hr)
    rw [hχr]
    by_cases hJ : n ≤ J
    · rw [if_pos hJ, (zero_exact_valuation π hπ n v hv J).mpr hJ,
        principal_zero (residueMap π n hn) (residueMap_surjective π n hn) ψ, hk]
    · rw [if_neg hJ]
      by_cases he : J = n - 1
      · rw [if_pos he, he, principal_active_value π n hn hπ v hv ψ hψ, hk]
        ring
      · rw [if_neg he, mul_zero]
        exact fourier_vanishes_below π n hn hπ v hv J (by omega) ψ hψ
          (fun x => (1 : MulChar (PowerQuotient π 1) ℂ) x)
  · rw [if_neg hr]
    have hχr : χ ^ r ≠ 1 := by
      intro h
      apply hr
      simpa only [hχ] using orderOf_dvd_of_pow_eq_one h
    by_cases he : J = n - 1
    · rw [if_pos he, he]
      have hd : ∀ x : PowerQuotient π n,
          ψ (Ideal.Quotient.mk (powerIdeal π n) (π ^ (n - 1)) * x) =
            φ (residueMap π n hn x) := by
        intro x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [← map_mul, residueMap_mk]
        exact hcompat a
      have hf := unit_frequency_exact (residueMap π n hn) (residueMap_surjective π n hn)
        ψ φ (χ ^ r) hχr (Ideal.Quotient.mk (powerIdeal π n) (π ^ (n - 1)))
        (Ideal.Quotient.mk (powerIdeal π n) v) hd
      have hr0 : r ≠ 0 := by
        intro hz
        subst r
        exact hr (dvd_zero 6)
      have hmod : χ ^ (r % 6) = χ ^ r := by
        simpa only [hχ] using pow_mod_orderOf χ r
      calc
        _ = (Nat.card {x : PowerQuotient π n // residueMap π n hn x = 0} : ℂ) *
            ((χ ^ r)⁻¹ (Ideal.Quotient.mk (powerIdeal π 1) v) * gaussSum (χ ^ r) φ) := by
          simpa only [← map_mul, residueMap_mk] using hf
        _ = _ := by
          rw [hk, MulChar.inv_apply_eq_inv', MulChar.pow_apply' χ hr0, ← inv_pow, ← hmod]
    · rw [if_neg he, mul_zero]
      by_cases hJ : n ≤ J
      · exact nonprincipal_zero_range π n hn hπ v hv J hJ ψ (χ ^ r) hχr
      · exact fourier_vanishes_below π n hn hπ v hv J (by omega) ψ hψ
          (fun x => (χ ^ r) x)

#print axioms fourier_eq_valuationGauss
end HighBin.PrincipalPowerGauss
