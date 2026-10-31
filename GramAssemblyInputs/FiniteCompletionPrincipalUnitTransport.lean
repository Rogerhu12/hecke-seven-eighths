import ActualFinitePlaceCompletionComparison
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import ValuedFieldTheory.Valuation.LocalRingEquiv

/-! SOURCE ONLY, UNRUN. A principal-unit bridge between the TWO completion
models. This uses the actual public semilinear valuation certificate and
transports maximal-ideal powers; it does not identify Hilbert symbols. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain
open scoped ValuativeRel
variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
local notation "C" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv K v)
local notation "D" => v.adicCompletion K
local instance principalUnitTransport_absoluteValuativeRel : ValuativeRel C :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
local instance principalUnitTransport_adicValuativeRel : ValuativeRel D :=
  ActualFiniteCompletionDraft.adicCompletionValuativeRel K v
local notation "e" => AlgEquiv.toRingEquiv (relativeFinitePlaceCompletionAlgEquiv v)

/-- The chosen completion equivalence preserves the integer predicate. -/
theorem finiteCompletionComparison_integer_iff (x : C) :
    e x ∈ (ValuativeRel.valuation D).integer ↔
      x ∈ (ValuativeRel.valuation C).integer := by
  have h := ActualFiniteCompletionDraft.completion_semilinearValuationCompatible K v
  letI : Algebra C D := (e).toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation D) at h
  have hh := h.val_isEquiv_comap x 1
  have h2 := hh.symm
  simp only [Valuation.comap_apply, map_one] at h2
  simp only [Valuation.mem_integer_iff]
  exact h2

/-- Identity through the actual completion comparison identifies integer rings. -/
def finiteCompletionComparisonIntegerEquiv : 𝒪[C] ≃+* 𝒪[D] where
  toFun x := ⟨e x.val, (finiteCompletionComparison_integer_iff K v x.val).mpr x.property⟩
  invFun x := ⟨(e).symm x.val, (finiteCompletionComparison_integer_iff K v ((e).symm x.val)).mp
    (by simpa using x.property)⟩
  left_inv x := Subtype.ext ((e).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((e).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((e).map_add x.val y.val)
  map_mul' x y := Subtype.ext ((e).map_mul x.val y.val)

theorem finiteCompletionComparison_principalUnits_iff (d : ℕ) (u : 𝒪[C]ˣ) :
    Units.mapEquiv (finiteCompletionComparisonIntegerEquiv K v).toMulEquiv u ∈
        LocalFieldTheory.principalUnits D d ↔
      u ∈ LocalFieldTheory.principalUnits C d := by
  rw [LocalFieldTheory.mem_principalUnits_iff, LocalFieldTheory.mem_principalUnits_iff]
  have hmap : (((Units.mapEquiv (finiteCompletionComparisonIntegerEquiv K v).toMulEquiv u :
      𝒪[D]ˣ) : 𝒪[D]) - 1) = finiteCompletionComparisonIntegerEquiv K v (u.val - 1) := by
    rw [map_sub, map_one] <;> rfl
  rw [hmap]
  exact ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff _ d _

/-- In particular an actual D principal unit pulls back to the SAME depth
in C, where upstream finitePlaceHilbertSymbol actually evaluates. -/
theorem finiteCompletionComparison_fieldPrincipalUnits_pullback
    (d : ℕ) (r : Dˣ) (hr : r ∈ LocalFieldTheory.fieldPrincipalUnits D d) :
    (Units.mapEquiv (e).toMulEquiv).symm r ∈
      LocalFieldTheory.fieldPrincipalUnits C d := by
  obtain ⟨u, hu, rfl⟩ := hr
  let E := Units.mapEquiv (finiteCompletionComparisonIntegerEquiv K v).toMulEquiv
  refine ⟨E.symm u, ?_, ?_⟩
  · apply (finiteCompletionComparison_principalUnits_iff K v d (E.symm u)).mp
    change E (E.symm u) ∈ _
    rw [E.apply_symm_apply]
    exact hu
  · apply Units.ext
    rfl
end HeckeGeneral.Arithmetic

