import ActualAdditiveGramResidueExpansion
import ActualExteriorGcdMobiusSum

/-!
UNCOMPILED / native 0. The actual Gram coefficient already imposes both
original ideal cutoffs after common-part and Mobius-divisor removal.
Consequently its finite residual-ideal sum equals the whole ideal-pair
sum, with any additional profile and chart coefficient retained. No
estimate for a larger complex sum is used to bound a subset.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramResidualSupportDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualAdditiveGramDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "E" => ExteriorIdeal K S

/-- The exact coefficient on C*(D*M_i), multiplied by the remaining
actual profile/correlation factor. Both inverse powers stay in it. -/
def actualGramResidualWeight (W : SmoothAnnularTest) (Y ν : ℝ)
    (C D : E) (B : E × E → ℂ) (mn : E × E) : ℂ :=
  actualAdditiveGramPairCoefficient K S (fun _ => 1) W Y ν
    (exteriorMul K S C (exteriorMul K S D mn.1))
    (exteriorMul K S C (exteriorMul K S D mn.2)) * B mn

theorem actualGramResidualWeight_mem_support (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (C D : E) (B : E × E → ℂ) (mn : E × E)
    (hmn : actualGramResidualWeight K S W Y ν C D B mn ≠ 0) :
    mn ∈ mobiusResidualPairs K S C D
      (additiveGramIdealSupport K S W Y) (additiveGramIdealSupport K S W Y) := by
  have h₁ : W.toFun (exteriorNorm K S
      (exteriorMul K S C (exteriorMul K S D mn.1)) / Y) ≠ 0 := by
    intro hz
    exact hmn (by simp only [actualGramResidualWeight,
      actualAdditiveGramPairCoefficient, hz, zero_mul, mul_zero])
  have h₂ : W.toFun (exteriorNorm K S
      (exteriorMul K S C (exteriorMul K S D mn.2)) / Y) ≠ 0 := by
    intro hz
    exact hmn (by simp only [actualGramResidualWeight,
      actualAdditiveGramPairCoefficient, hz, map_zero, mul_zero, zero_mul])
  apply (mem_mobiusResidualPairs K S C D _ _ mn).mpr
  exact ⟨(mem_additiveGramIdealSupport_iff K S W Y hY _).mpr
      ((div_le_iff₀ hY).mp (W.support h₁).2),
    (mem_additiveGramIdealSupport_iff K S W Y hY _).mpr
      ((div_le_iff₀ hY).mp (W.support h₂).2)⟩

/-- Convergence follows from the original annular support, including on
the enlarged residual family where the two ideals need not be coprime. -/
theorem actualGramResidualWeight_summable (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (C D : E) (B : E × E → ℂ) :
    Summable (actualGramResidualWeight K S W Y ν C D B) := by
  apply summable_of_hasFiniteSupport
  apply (mobiusResidualPairs K S C D
    (additiveGramIdealSupport K S W Y)
    (additiveGramIdealSupport K S W Y)).finite_toSet.subset
  intro mn hmn
  exact actualGramResidualWeight_mem_support K S W Y ν hY C D B mn hmn

/-- Exact extension of the actual finite sum to every exterior-ideal
pair. The arbitrary remaining factor is unchanged on every term. -/
theorem actualGramResidualWeight_sum_eq_tsum (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (C D : E) (B : E × E → ℂ) :
    (∑ mn ∈ mobiusResidualPairs K S C D
      (additiveGramIdealSupport K S W Y) (additiveGramIdealSupport K S W Y),
      actualGramResidualWeight K S W Y ν C D B mn) =
      ∑' mn : E × E, actualGramResidualWeight K S W Y ν C D B mn := by
  symm
  apply tsum_eq_sum
  intro mn hmn
  by_contra hne
  exact hmn (actualGramResidualWeight_mem_support K S W Y ν hY C D B mn hne)

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramResidualSupportDraft
