import SIntegerSexticSymbolZeroSupport
import SIntegerSexticLocalHilbertComparison

/-! SOURCE ONLY, UNRUN. Actual exterior Hilbert ratio on columns without
a common exterior prime divisor. Zero multiplicities are deduced from the
literal contracted ideals. The second branch uses actual Hilbert skew;
no reciprocity identity or local ratio is assumed. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem sIntegerSextic_local_hilbert_ratio
    (hmu : (primitiveRoots ((6 : ℕ+) : ℕ) K).Nonempty)
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (hcoprime : (Ideal.absNorm p.asIdeal).Coprime ((6 : ℕ+) : ℕ))
    (a b : NonzeroRingElements (S.integer K))
    (hab : ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
      p.asIdeal ∣ sIntegerModulusContraction K S b.val)) :
    σ ((finitePlaceHilbertSymbol K (6 : ℕ+) (by norm_num) hmu p
      (nonzeroSIntegerFieldUnit K S a)
      (nonzeroSIntegerFieldUnit K S b)).val : K) =
      (sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 a.val) ^
          idealPrimeMultiplicity K p (sIntegerModulusContraction K S b.val) /
        (sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 b.val) ^
          idealPrimeMultiplicity K p (sIntegerModulusContraction K S a.val) := by
  by_cases ha : p.asIdeal ∣ sIntegerModulusContraction K S a.val
  · have hb : ¬ p.asIdeal ∣ sIntegerModulusContraction K S b.val := fun hb => hab ⟨ha, hb⟩
    have hbResidue : sIntegerSexticResidueMap K S p hpS b.val ≠ 0 := by
      intro hz
      exact hb ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS b.val).mp hz)
    have hbMultiplicity := idealPrimeMultiplicity_eq_zero_of_not_dvd K p
      (sIntegerModulusContraction K S b.val)
      (sIntegerModulusContraction_ne_bot K S b.val b.property) hb
    rw [hbMultiplicity, pow_zero, one_div,
      finitePlaceHilbertSymbol_skew K (6 : ℕ+) (by norm_num) hmu p]
    have hswap := sIntegerSextic_local_hilbert_comparison K S ζ hζ σ
      hmu p hpS hp6 hcoprime b a hbResidue
    simpa only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, map_inv₀] using
      congrArg (fun z : ℂ => z⁻¹) hswap
  · have haResidue : sIntegerSexticResidueMap K S p hpS a.val ≠ 0 := by
      intro hz
      exact ha ((sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS a.val).mp hz)
    have haMultiplicity := idealPrimeMultiplicity_eq_zero_of_not_dvd K p
      (sIntegerModulusContraction K S a.val)
      (sIntegerModulusContraction_ne_bot K S a.val a.property) ha
    rw [haMultiplicity, pow_zero, div_one]
    exact sIntegerSextic_local_hilbert_comparison K S ζ hζ σ
      hmu p hpS hp6 hcoprime a b haResidue

end HeckeGeneral.Characters
