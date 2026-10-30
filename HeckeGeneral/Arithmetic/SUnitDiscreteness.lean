import HeckeGeneral.Arithmetic.SUnitArchimedeanBalancing
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
The actual diagonal S-unit subgroup is closed and discrete in the product of
archimedean units and the units of the completions at S. Its topology is the
subspace topology inherited from that product. No topology is assigned to the
abstract S-unit domain to replace the image-discreteness argument.

The identity is isolated using the discrete mixed integer lattice and the open
local valuation subrings. Integrality at S together with the defining valuations
of an S-unit outside S gives a genuine global integer. Only finiteness of S is
needed, with no finite-generation, finite-index, or principal-ideal assumption.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The infinite coordinates already distinguish genuine global S-units. -/
theorem sLocalDiagonal_injective : Function.Injective (sLocalDiagonal K S) := by
  intro u w h
  apply Subtype.ext
  apply Units.ext
  apply mixedEmbedding_injective K
  exact congrArg (fun x : sLocalMultiplicativeGroup K S => (x.1 : mixedSpace K)) h

/-- Local integrality at S completes the global integrality of an S-unit. -/
theorem sUnit_integral_of_mem_localIntegers (u : S.unit K)
    (h : ∀ v : S, ((sLocalDiagonal K S u).2 v).val ∈
      v.val.adicCompletionIntegers K) :
    ((u : Kˣ) : K) ∈ (algebraMap (𝓞 K) K).range := by
  apply mem_integers_of_valuation_le_one K
  intro v
  by_cases hv : v ∈ S
  · have hl := h ⟨v, hv⟩
    change (((u : Kˣ) : K) : v.adicCompletion K) ∈ v.adicCompletionIntegers K at hl
    rw [mem_adicCompletionIntegers, adicCompletion.valued_coe] at hl
    exact hl
  · exact (Set.unit_valuation_eq_one S K u hv).le

variable [Finite S]

/-- An actual open neighborhood of the identity isolates the diagonal image. -/
theorem exists_sLocalDiagonal_identity_neighborhood :
    ∃ U : Set (sLocalMultiplicativeGroup K S), IsOpen U ∧ 1 ∈ U ∧
      ∀ u : S.unit K, sLocalDiagonal K S u ∈ U → u = 1 := by
  have h1 : (1 : mixedSpace K) ∈ mixedEmbedding.integerLattice K := by
    refine ⟨1, ?_⟩
    simp
  have hd : IsDiscrete (mixedEmbedding.integerLattice K : Set (mixedSpace K)) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  obtain ⟨W, hW, hWlattice⟩ :=
    isDiscrete_iff_forall_mem_exists_isOpen.mp hd 1 h1
  have hW1 : (1 : mixedSpace K) ∈ W := by
    have hm : (1 : mixedSpace K) ∈ W ∩ mixedEmbedding.integerLattice K := by
      rw [hWlattice]
      exact Set.mem_singleton _
    exact hm.1
  let U : Set (sLocalMultiplicativeGroup K S) :=
    {x | (x.1 : mixedSpace K) ∈ W} ∩
      ⋂ v : S, {x | (x.2 v).val ∈ v.val.adicCompletionIntegers K}
  have hU : IsOpen U := by
    refine (hW.preimage (Units.continuous_val.comp continuous_fst)).inter ?_
    apply isOpen_iInter_of_finite
    intro v
    exact (Valued.isOpen_valuationSubring (v.val.adicCompletion K)).preimage
      (Units.continuous_val.comp ((continuous_apply v).comp continuous_snd))
  refine ⟨U, hU, ?_, ?_⟩
  · constructor
    · exact hW1
    · apply Set.mem_iInter.mpr
      intro v
      change (1 : v.val.adicCompletion K) ∈ v.val.adicCompletionIntegers K
      exact (v.val.adicCompletionIntegers K).one_mem
  · intro u hu
    have har : mixedEmbedding K ((u : Kˣ) : K) ∈ W := hu.1
    have hlocal : ∀ v : S, ((sLocalDiagonal K S u).2 v).val ∈
        v.val.adicCompletionIntegers K := by
      intro v
      have hv : sLocalDiagonal K S u ∈
          {x : sLocalMultiplicativeGroup K S | (x.2 v).val ∈
            v.val.adicCompletionIntegers K} := Set.mem_iInter.mp hu.2 v
      exact hv
    obtain ⟨a, ha⟩ := sUnit_integral_of_mem_localIntegers K S u hlocal
    have hint : mixedEmbedding K ((u : Kˣ) : K) ∈ mixedEmbedding.integerLattice K := by
      refine ⟨a, ?_⟩
      change mixedEmbedding K (algebraMap (𝓞 K) K a) = _
      exact congrArg (mixedEmbedding K) ha
    have hemb : mixedEmbedding K ((u : Kˣ) : K) = 1 := by
      apply Set.mem_singleton_iff.mp
      rw [← hWlattice]
      exact ⟨har, hint⟩
    apply Subtype.ext
    apply Units.ext
    apply mixedEmbedding_injective K
    change mixedEmbedding K ((u : Kˣ) : K) = mixedEmbedding K 1
    simpa only [map_one] using hemb

/-- Discreteness is proved on the actual range with its induced topology. -/
theorem discreteTopology_sLocalDiagonal_range :
    DiscreteTopology (sLocalDiagonal K S).range := by
  obtain ⟨U, hU, hU1, hsep⟩ := exists_sLocalDiagonal_identity_neighborhood K S
  have hpre : (Subtype.val : (sLocalDiagonal K S).range →
      sLocalMultiplicativeGroup K S) ⁻¹' U = {1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp x.property
      have huU : sLocalDiagonal K S u ∈ U := by
        rw [hu]
        exact hx
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      calc
        (x : sLocalMultiplicativeGroup K S) = sLocalDiagonal K S u := hu.symm
        _ = 1 := by rw [hsep u huU, map_one]
    · intro hx
      have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
      change (x : sLocalMultiplicativeGroup K S) ∈ U
      rw [hx1]
      exact hU1
  have hopen := hU.preimage (continuous_subtype_val :
    Continuous (Subtype.val : (sLocalDiagonal K S).range → sLocalMultiplicativeGroup K S))
  rw [hpre] at hopen
  exact discreteTopology_of_isOpen_singleton_one hopen

theorem isDiscrete_sLocalDiagonal_range :
    IsDiscrete ((sLocalDiagonal K S).range : Set (sLocalMultiplicativeGroup K S)) :=
  SetLike.isDiscrete_iff_discreteTopology.mpr (discreteTopology_sLocalDiagonal_range K S)

/-- The actual ambient local group is Hausdorff, so its discrete subgroup is closed. -/
theorem isClosed_sLocalDiagonal_range :
    IsClosed ((sLocalDiagonal K S).range : Set (sLocalMultiplicativeGroup K S)) :=
  (sLocalDiagonal K S).range.isClosed_of_isDiscrete (isDiscrete_sLocalDiagonal_range K S)

/-- No index condition is needed for a subgroup of the discrete diagonal image. -/
theorem isDiscrete_sLocalDiagonal_map (Γ : Subgroup (S.unit K)) :
    IsDiscrete (Γ.map (sLocalDiagonal K S) : Set (sLocalMultiplicativeGroup K S)) := by
  apply (isDiscrete_sLocalDiagonal_range K S).mono
  intro x hx
  obtain ⟨u, _, hu⟩ := Subgroup.mem_map.mp hx
  exact MonoidHom.mem_range.mpr ⟨u, hu⟩

theorem discreteTopology_sLocalDiagonal_map (Γ : Subgroup (S.unit K)) :
    DiscreteTopology (Γ.map (sLocalDiagonal K S)) :=
  SetLike.isDiscrete_iff_discreteTopology.mp (isDiscrete_sLocalDiagonal_map K S Γ)

theorem isClosed_sLocalDiagonal_map (Γ : Subgroup (S.unit K)) :
    IsClosed (Γ.map (sLocalDiagonal K S) : Set (sLocalMultiplicativeGroup K S)) :=
  (Γ.map (sLocalDiagonal K S)).isClosed_of_isDiscrete (isDiscrete_sLocalDiagonal_map K S Γ)

end HeckeGeneral.Arithmetic
