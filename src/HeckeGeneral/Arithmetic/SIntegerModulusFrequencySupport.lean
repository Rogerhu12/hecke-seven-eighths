import HeckeGeneral.Arithmetic.SIntegerModulusValuation

/-!
# The actual inverse-modulus frequency lattice

The completed local bounds describe precisely those field frequencies whose
product with the given modulus is an S-integer. Zero is included.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The actual completed inverse-modulus balls cut out the field lattice c⁻¹OS. -/
theorem sIntegerModulusFrequencySupport_iff
    (c : S.integer K) (hc : c ≠ 0) (ξ : K) :
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Valued.v (algebraMap K (v.adicCompletion K) ξ) ≤
        WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ)) ↔
      (c : K) * ξ ∈ S.integer K := by
  constructor
  · intro h v hv
    have hξ : v.valuation K ξ ≤
        WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ) := by
      have hlocal := h v hv
      change Valued.v (ξ : v.adicCompletion K) ≤ _ at hlocal
      rw [valuedAdicCompletion_eq_valuation'] at hlocal
      exact hlocal
    rw [map_mul, sIntegerModulus_valuation K S c hc v hv]
    calc
      _ ≤ WithZero.exp (-(sIntegerModulusPrimeExponents K S c hc v : ℤ)) *
          WithZero.exp (sIntegerModulusPrimeExponents K S c hc v : ℤ) :=
        mul_le_mul_of_nonneg_left hξ zero_le
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · intro h v hv
    let a : S.integer K := ⟨(c : K) * ξ, h⟩
    have hcK : (c : K) ≠ 0 := by
      intro hz
      apply hc
      exact Subtype.ext hz
    have hquot : (a : K) / (c : K) = ξ := by
      change ((c : K) * ξ) / (c : K) = ξ
      field_simp [hcK] <;> ring
    simpa only [hquot] using
      sInteger_div_modulus_completion_valuation_le K S c hc a v hv

end HeckeGeneral.Arithmetic
