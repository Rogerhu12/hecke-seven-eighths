import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolAllowanceTransport

set_option linter.unusedSectionVars false

/-!
# The first saving from the actual original ideal windows

The common lengths and active radical are computed from the literal
first block. Its positive-part allowance is therefore available by
definition. Three individual norm windows supply the active-radical,
opposite-common and extracted-factor lengths required by the ledger.

The direct, main-pool and valuation-error versions derive the moving
length bounds internally. They do not assume the final first-saving
inequality and do not modify any source, row, mask or allocation.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]

private theorem first_logLength_le_of_norm_le
    (Z : ℝ) (hZ : 1 < Z) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (x : ℝ) (h : (Ideal.absNorm I : ℝ) ≤ Z ^ x) : idealLogLength Z I ≤ x := by
  sorry

private theorem firstAllowance_max_div (c d R : ℝ) :
    max (3 * c - 5 * d - R) 0 / 6 ≤ firstAllowance c d R := by
  sorry

/-- The first saving is a theorem of original individual ideal norms.
The allowance and every common-support length are computed here. -/
theorem firstSaving_from_original_ideal_windows
    (Z : ℝ) (hZ : 1 < Z) (C D G : Ideal (𝓞 K))
    (hC : C ≠ 0) (hD : D ≠ 0) (hG : G ≠ 0)
    (D₀ w q wo ell stepσ δ : ℝ)
    (hw : 0 ≤ w) (hwo : 0 ≤ wo) (hell : 0 ≤ ell)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ) (hwσ : w ≤ 7 * stepσ / 3)
    (hactive : (Ideal.absNorm (firstActiveRadical C D) : ℝ) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm D : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z C - 2 * w + wo) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z C + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z C) D₀ w q wo
        (firstAllowance (idealLogLength Z C) (idealLogLength Z D)
          (idealLogLength Z (firstActiveRadical C D)))
        (idealLogLength Z G) ell := by
  sorry

variable {A : SArithmeticData K}
variable {ι κ : Type*} {I : ι → A.Exterior} {J : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock I J DE)

/-- The active norm is the actual quotient in this first transform;
the existing prime-power identity identifies its radical internally. -/
theorem firstSaving_from_original_norms
    (Z : ℝ) (hZ : 1 < Z) (G : A.Exterior)
    (D₀ w q wo ell stepσ δ : ℝ)
    (hw : 0 ≤ w) (hwo : 0 ≤ wo) (hell : 0 ≤ ell)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ) (hwσ : w ≤ 7 * stepσ / 3)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * w + wo) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ w q wo
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  sorry

/-- The genuine direct entrance has zero moving lengths. Its first
saving requires only the three original norm windows. -/
theorem direct_firstSaving_from_original_norms
    (Z : ℝ) (hZ : 1 < Z) (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1) 0 + 2 * stepσ)) :
    2 * idealLogLength Z DE.1 / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ 0 q 0
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) 0 := by
  sorry

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- The main pool length is paid by the original choice
`ell ≤ stepσ / 3`, rather than a new saving hypothesis. -/
theorem main_firstSaving_from_original_norms
    (pool : PowerScaleExteriorPool A bad Z ell eps)
    (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hpool : ell ≤ stepσ / 3) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * ell + ell) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + ell) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ ell q ell
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  sorry

/-- At valuations one, six and seven, both moving lengths use the
literal norm of the retained prime. The pool upper norm window and
`n ≤ 7` prove the ledger's moving-length constraint internally. -/
theorem residual_firstSaving_from_original_norms
    (pool : PowerScaleExteriorPool A bad Z ell eps) (p : pool.primes)
    (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ))
    (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hpool : ell ≤ stepσ / 3) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * ((n : ℝ) * idealLogLength Z p.val.val.asIdeal) +
        (amplifierMovingExponent n : ℝ) * idealLogLength Z p.val.val.asIdeal) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + (n : ℝ) * idealLogLength Z p.val.val.asIdeal) / 3 -
        3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ ((n : ℝ) * idealLogLength Z p.val.val.asIdeal) q
        ((amplifierMovingExponent n : ℝ) * idealLogLength Z p.val.val.asIdeal)
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  sorry

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstSaving_from_original_ideal_windows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.direct_firstSaving_from_original_norms
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.main_firstSaving_from_original_norms
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.residual_firstSaving_from_original_norms
