import HeckeGeneral.Arithmetic.SUnitNormOneQuotient
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Group.Units

/-!
# Topology of the actual norm-one S-local quotient

The finite completions have their actual proper metric topology. Their unit
groups, and the mixed archimedean unit group, are closed subspaces of the
products containing a unit and its inverse. This gives Polish topology for
the finite product and its closed norm-one level.

Local compactness of the ambient product already follows from the general
Mathlib instances for units and finite products. Only the closed norm-one
level needs an additional instance here. The diagonal image is discrete in
the actual induced topology; its countability follows from second countability,
without choosing a topology on the abstract group of global S-units.

No measurable space or Haar measure is chosen here. A subsequent measure
construction must fix the canonical Borel structures on the norm-one group
and its quotient, and verify their compatibility with the quotient map.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain Topology

private theorem polishSpace_units (A : Type*) [Monoid A] [TopologicalSpace A]
    [T1Space A] [ContinuousMul A] [PolishSpace A] : PolishSpace Aˣ := by
  let : PolishSpace Aᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := A)).symm.isClosedEmbedding.polishSpace
  exact (Units.isClosedEmbedding_embedProduct (α := A)).polishSpace

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

instance polishSpace_sLocalMultiplicativeGroup :
    PolishSpace (sLocalMultiplicativeGroup K S) := by
  let : PolishSpace (mixedSpace K)ˣ := polishSpace_units (mixedSpace K)
  let : ∀ v : S, PolishSpace (v.val.adicCompletion K)ˣ :=
    fun v => polishSpace_units (v.val.adicCompletion K)
  change PolishSpace ((mixedSpace K)ˣ × ((v : S) → (v.val.adicCompletion K)ˣ))
  infer_instance

instance polishSpace_sLocalNormOneGroup : PolishSpace (sLocalNormOneGroup K S) :=
  (isClosed_sLocalNormOneGroup K S).polishSpace

instance locallyCompactSpace_sLocalNormOneGroup :
    LocallyCompactSpace (sLocalNormOneGroup K S) :=
  (isClosed_sLocalNormOneGroup K S).locallyCompactSpace

/-- Pull back the actual ambient discrete diagonal subgroup to the norm-one level. -/
theorem isDiscrete_sLocalNormOneGamma (Γ : Subgroup (S.unit K)) :
    IsDiscrete (sLocalNormOneGamma K S Γ : Set (sLocalNormOneGroup K S)) := by
  rw [sLocalNormOneGamma_eq_comap, Subgroup.coe_comap]
  exact (isDiscrete_sLocalDiagonal_map K S Γ).preimage
    continuous_subtype_val.continuousOn Subtype.val_injective

instance discreteTopology_sLocalNormOneGamma (Γ : Subgroup (S.unit K)) :
    DiscreteTopology (sLocalNormOneGamma K S Γ) :=
  SetLike.isDiscrete_iff_discreteTopology.mp (isDiscrete_sLocalNormOneGamma K S Γ)

/-- A discrete subspace of this second-countable group is countable. -/
instance countable_sLocalNormOneGamma (Γ : Subgroup (S.unit K)) :
    Countable (sLocalNormOneGamma K S Γ) :=
  (TopologicalSpace.separableSpace_iff_countable).mp inferInstance

-- The quotient's topological group, T2, and second-countable instances follow
-- from the existing quotient instances and the closed-image T1 instance in
-- SUnitNormOneQuotient. No duplicate quotient topology is introduced here.

end HeckeGeneral.Arithmetic
