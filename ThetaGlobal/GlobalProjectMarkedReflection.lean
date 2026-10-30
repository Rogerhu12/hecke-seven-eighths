module

public import ThetaGlobal.GlobalProjectLiteralSeed

@[expose] public section

/-!
# Marked reflection from the actual source and the permitted local inputs

The literal fixed-profile seed and the actual annular transfer now meet
in one theorem. Finite Mellin admissibility is constructed from the same
source, cutoff vectors and Haar transport, so it is not an additional
hypothesis. The only local boundary is the one-place archimedean Mellin
package and the one-place exterior digit table.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal
open scoped NumberField Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

local notation "R" => thetaRecipe K c
local notation "Sf" => places K c
local notation "Adata" => arithmeticData K c

/-- The permitted exterior table is evaluated on the source selected
before the local high K-type vector is supplied. -/
abbrev LocalExteriorDigitInput :=
  GlobalProjectLocalDigitTables.Input R
    (thetaFiniteSource K c).projected.base.factorization Adata

theorem thetaRecipe_marked_reflection
    (θ : HeckeCharacter K) (C : FiniteFixedSource.Source R θ)
    (L : FiniteLocalHighK.Input R θ C)
    (H : GlobalProjectLocalDigitTables.Input R C.projected.base.factorization Adata)
    (hA : AllowedGeneratorInput K Sf Adata)
    (hS : conductorPlaces K θ ⊆ R.A.Sf)
    (w : InfinitePlace K)
    (hk : heckeComplexWeight K w (R.A.complex_place w) θ ≠ 0)
    (d : MarkedDatum K Sf) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    completedThetaSum K Sf Adata θ (rowElement K Sf Adata d)
      d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K Sf d,
        reflectedTerm K Sf Adata d i (FiniteLocalHighK.finiteMellinData R θ C L)
          θ V.toFun X := by
  have hM : FiniteMellinAdmissible K Sf (FiniteLocalHighK.finiteMellinData R θ C L) :=
    ProjectedFiniteMellin.targetFiniteMellinData_admissible R C.projected.base.factorization
      C.transport (FiniteLocalHighK.C₀ R θ C L) (FiniteLocalHighK.C₀_ne_zero R θ C L)
      (FiniteLocalHighK.A₀ R θ C L) (FiniteLocalHighK.A₀_pos R θ C L) θ
  exact ActualAnnularTransfer.marked_reflection_of_literal_seed R θ C L Adata d hM w
    (thetaRecipe_literal_seed K c θ C L H hA hS d w hk) V hX

/-- The same result at the skeleton's fixed source, with its actual
coefficient table and the exact local-input types used by the entry point. -/
theorem thetaFiniteSource_marked_reflection
    (L : LocalHighKMellinInput K c) (H : LocalExteriorDigitInput K c)
    (hA : AllowedGeneratorInput K Sf Adata)
    (hS : conductorPlaces K
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) ⊆ R.A.Sf)
    (w : InfinitePlace K)
    (hk : heckeComplexWeight K w (R.A.complex_place w)
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) ≠ 0)
    (d : MarkedDatum K Sf) (V : SmoothAnnularTest) {X : ℝ} (hX : 0 < X) :
    completedThetaSum K Sf Adata
      (thetaPeriod K Sf (probeData K c) (targetCharacter K c))
      (rowElement K Sf Adata d) d.puncture d.marks V.toFun X =
      ∑' i : ReflectionIndex K Sf d,
        reflectedTerm K Sf Adata d i (FiniteSkeletonSource.data K c L)
          (thetaPeriod K Sf (probeData K c) (targetCharacter K c)) V.toFun X :=
  thetaRecipe_marked_reflection K c
    (thetaPeriod K Sf (probeData K c) (targetCharacter K c))
    (thetaFiniteSource K c) L H hA hS w hk d V hX

end HeckeSkeleton

#print axioms HeckeSkeleton.thetaRecipe_marked_reflection
#print axioms HeckeSkeleton.thetaFiniteSource_marked_reflection
