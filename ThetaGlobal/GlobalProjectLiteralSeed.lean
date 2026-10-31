import ThetaGlobal.GlobalProjectReflectedReindex
import ThetaGlobal.GlobalSkeletonDirect

/-!
# The actual high K-type source proves the literal marked seed

This is the final connection between the repository's canonical
automorphic Fourier identity and its coefficient-level marked theta
sum. The two series are evaluated from the same source, their common
nonzero scalar is cancelled, and their frequencies are reindexed using
the proved local support and coefficient dictionaries.

The hypotheses contain only the explicit one-place high K-type Mellin
data, one-place exterior digit tables, and arithmetic facts already
proved for the selected choice. No global seed or reflection identity
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal
open scoped NumberField Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)
local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

variable (θ : HeckeCharacter K) (C : FiniteFixedSource.Source R θ)
  (L : FiniteLocalHighK.Input R θ C)
  (H : GlobalProjectLocalDigitTables.Input R C.projected.base.factorization Adata)
  (hA : AllowedGeneratorInput K Sf Adata)
  (hS : conductorPlaces K θ ⊆ R.A.Sf)

include H hA hS in
/-- The literal fixed-profile seed is constructed from the actual
canonical source. This theorem supplies, rather than assumes, the seed
used by the subsequent annular deconvolution and regularizer removal. -/
theorem thetaRecipe_literal_seed
    (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (hk : heckeComplexWeight K w (R.A.complex_place w) θ ≠ 0) :
    ActualAnnularTransfer.LiteralSeed R θ C L Adata d w := by
  intro X hX
  let l : PositiveAxis := ⟨X⁻¹, inv_pos.mpr hX⟩
  have hs := (GlobalProjectFrequencySeed.actual_frequency_seed R θ C L
    (thetaRecipe_aligned K c) Adata H hS (QuotientGroup.mk d.rowUnit)
    (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.digits R d)
    (GlobalProjectMarkedSupport.marks R d) w hk l).2.2
  change (∑' ξ : ThetaReflectionData.Frequency R.A,
    GlobalProjectOrbitEvaluation.directTerm R θ C L (QuotientGroup.mk d.rowUnit)
      (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
      w l (Quotient.out ξ)) =
    ∑' ξ : ThetaReflectionData.Frequency R.A,
      GlobalProjectOrbitEvaluation.reflectedTerm R θ C L (QuotientGroup.mk d.rowUnit)
        (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.weight R Adata d)
        w l (Quotient.out ξ) at hs
  rw [GlobalSkeletonDirect.direct_sum_eq_completed K c θ C L H hS d w l,
    GlobalSkeletonReflected.reflected_sum_eq_literal K c θ C L H hA hS d w l] at hs
  simpa only [l, inv_inv, GlobalSkeletonReflected.literalTerm] using hs

include H hA hS in
/-- Absolute convergence of the full reflected literal seed, inherited
from the actual compact-domain Fourier mass estimates. -/
theorem thetaRecipe_literal_seed_absolute
    (d : MarkedDatum K Sf) (w : InfinitePlace K)
    (hk : heckeComplexWeight K w (R.A.complex_place w) θ ≠ 0)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun i : ReflectionIndex K Sf d =>
      ‖ReflectedArithmetic.reflectedCoefficient K Sf Adata d i θ *
        ActualAnnularTransfer.reflectedProfile R θ C L (QuotientGroup.mk d.rowUnit)
          (frequencyClass K Sf Adata d i) w (ReflectedLimitProject.argument K Sf d X i)‖) := by
  let l : PositiveAxis := ⟨X⁻¹, inv_pos.mpr hX⟩
  have hs := (GlobalProjectFrequencySeed.actual_frequency_seed R θ C L
    (thetaRecipe_aligned K c) Adata H hS (QuotientGroup.mk d.rowUnit)
    (GlobalProjectMarkedSupport.row R d) (GlobalProjectMarkedSupport.digits R d)
    (GlobalProjectMarkedSupport.marks R d) w hk l).2.1
  have ht := GlobalSkeletonReflected.reflected_norm_summable K c θ C L H hA hS d w l hs
  simpa only [l, inv_inv, GlobalSkeletonReflected.literalTerm] using ht

end HeckeSkeleton

#print axioms HeckeSkeleton.thetaRecipe_literal_seed
#print axioms HeckeSkeleton.thetaRecipe_literal_seed_absolute
