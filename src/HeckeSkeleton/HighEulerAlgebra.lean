import HeckeSkeleton.HighEulerCore
import HeckeGeneral.Analysis.PhysicalProbeContours
import HeckeGeneral.Characters.InfinityPacket

/-!
Local Euler algebra for the full high-bin range. The cancelled formula
records the removable-pole repair required by the current row continuation.
-/

noncomputable section

namespace HeckeSkeleton.HighEulerCharacters

open NumberField HeckeGeneral.Characters

variable (K : Type) [Field K] [NumberField K]

/-- The only pure norm twist of finite order is the trivial character.
This removes the nonzero-t part of HB-POLE; it does not prove row injectivity. -/
theorem finiteOrder_eq_normTwist_iff {χ : HeckeCharacter K}
    (hχ : FiniteOrder χ) (t : ℝ) :
    χ = heckeNormTwist K t ↔ χ = 1 ∧ t = 0 := by
  constructor
  · intro heq
    let v : InfinitePlace K := Classical.choice inferInstance
    have hz := heckeRadialParameter_finiteOrder K v hχ
    rw [heq, heckeRadialParameter_normTwist] at hz
    have ht : t = 0 := by linarith
    refine ⟨?_, ht⟩
    simpa [ht, heckeNormTwist] using heq
  · rintro ⟨rfl, rfl⟩
    simp [heckeNormTwist]

theorem finiteOrder_ne_normTwist_iff {χ : HeckeCharacter K}
    (hχ : FiniteOrder χ) :
    (∀ t : ℝ, χ ≠ heckeNormTwist K t) ↔ χ ≠ 1 := by
  constructor
  · intro h heq
    exact h 0 (by simpa [heckeNormTwist] using heq)
  · intro h t heq
    exact h ((finiteOrder_eq_normTwist_iff K hχ t).mp heq).1

end HeckeSkeleton.HighEulerCharacters

namespace HeckeSkeleton.HighEulerAlgebra

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open scoped ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The actual regular-prime row correction has the preceding closed error
formula. Abbreviations q,V,W,D,E are lets, not extra Euler data. -/
theorem localRowCorrection_sub_one (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) (s w z : ℂ)
    (hE : 1 - primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
      (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z) ≠ 0)
    (hD : 1 - primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-s) ≠ 0) :
    let q : ℂ := (p.val.asIdeal.absNorm : ℂ)
    let V := q ^ (-6 * z)
    let W := primeCoefficient K χ p.val * q ^ (-w)
    let D := primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) * q ^ (-s)
    let E := primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 * q ^ (4 - 6 * s) * V
    localRowCorrection K S P ψ χ p s w z - 1 =
      (-W * V + E * (1 - q⁻¹ + q⁻¹ * W - W ^ 2 + W ^ 2 * V) +
        D * (V + W - q * W * V + (q - 1) * W ^ 2 * V - E)) /
        ((1 - E) * (1 - D)) := by
  dsimp only
  unfold localRowCorrection
  dsimp only
  exact rowEulerRationalValue_sub_one _ _ _ _ _ _ hE hD

/-- The actual continued factor has the corrected value on W=1. -/
theorem localRowCorrection_at_W_one (P : ProbeData K S)
    (ψ χ : HeckeCharacter K) (p : ExteriorPrime K S) (s w z : ℂ)
    (hW : primeCoefficient K χ p.val *
      (p.val.asIdeal.absNorm : ℂ) ^ (-w) = 1)
    (hE : 1 - primeCoefficient K (thetaPeriod K S P ψ) p.val ^ 6 *
      (p.val.asIdeal.absNorm : ℂ) ^ (4 - 6 * s) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z) ≠ 0)
    (hD : 1 - primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
      (p.val.asIdeal.absNorm : ℂ) ^ (-s) ≠ 0) :
    localRowCorrection K S P ψ χ p s w z =
      (1 - (p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) /
        (1 - primeCoefficient K ψ p.val * conj (primeCoefficient K χ p.val) *
          (p.val.asIdeal.absNorm : ℂ) ^ (-s)) := by
  unfold localRowCorrection
  dsimp only
  rw [hW]
  exact rowEulerRationalValue_W_one _ _ _ _ _ hE hD

end HeckeSkeleton.HighEulerAlgebra

#print axioms HeckeSkeleton.HighEulerAlgebra.rowEulerRational_eq_cancelled
#print axioms HeckeSkeleton.HighEulerAlgebra.rowEulerCancelledValue_W_one
#print axioms HeckeSkeleton.HighEulerAlgebra.localRowCorrection_at_W_one
