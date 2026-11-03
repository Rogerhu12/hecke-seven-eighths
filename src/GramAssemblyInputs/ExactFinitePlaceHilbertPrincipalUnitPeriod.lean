import KummerHilbertPrincipalUnitPeriod
import FiniteCompletionPrincipalUnitTransport
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity

/-! SOURCE ONLY, UNRUN. Uniform kernel period for the EXACT upstream global
finite-place symbol. Depth is selected on its actual absolute-value completion
C; principal units are pulled from the adic completion D via the established
valuation-compatible equivalence. No Hilbert-symbol naturality is assumed.
The earlier actual S-integer congruence theorem supplies the principal-unit
premises; they are concrete subgroup membership, not periodicity assumptions. -/
noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.Reciprocity
variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
local notation "C" => AbsoluteValue.Completion (HeightOneSpectrum.adicAbv K v)
local notation "D" => v.adicCompletion K
local instance exactFiniteHilbert_absoluteValuativeRel : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
local instance exactFiniteHilbert_adicValuativeRel : ValuativeRel D := ActualFiniteCompletionDraft.adicCompletionValuativeRel K v
local instance exactFiniteHilbert_absoluteLocalField : IsNonarchimedeanLocalField C :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
local notation "e" => AlgEquiv.toRingEquiv (relativeFinitePlaceCompletionAlgEquiv v)

theorem exists_exact_finitePlaceHilbert_principalUnit_period
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ a' a b' b : Kˣ,
      Units.map (algebraMap K D).toMonoidHom (a' / a) ∈
        LocalFieldTheory.fieldPrincipalUnits D N →
      Units.map (algebraMap K D).toMonoidHom (b' / b) ∈
        LocalFieldTheory.fieldPrincipalUnits D N →
      finitePlaceHilbertSymbol K n hnK hmu v a' b' =
        finitePlaceHilbertSymbol K n hnK hmu v a b := by
  obtain ⟨N, hN, hk⟩ := exists_kummerHilbert_principalUnit_paired_invariance
    C n (finitePlaceHilbert_natCast_ne_zero K n hnK v)
      (finitePlaceHilbert_primitiveRoots_nonempty K n hmu v)
  refine ⟨N, hN, ?_⟩
  intro a' a b' b ha hb
  have hunit (x : Kˣ) :
      (Units.mapEquiv (e).toMulEquiv).symm
          (Units.map (algebraMap K D).toMonoidHom x) =
        finitePlaceHilbert_completionUnit K v x := by
    apply Units.ext
    apply (e).injective
    change e ((e).symm (algebraMap K D (x : K))) =
      e (algebraMap K C (x : K))
    rw [(e).apply_symm_apply]
    exact (relativeFinitePlaceCompletionAlgEquiv v).commutes (x : K) |>.symm
  have hr := finiteCompletionComparison_fieldPrincipalUnits_pullback K v N _ ha
  have hs := finiteCompletionComparison_fieldPrincipalUnits_pullback K v N _ hb
  rw [hunit] at hr hs
  have he := hk (finitePlaceHilbert_completionUnit K v (a' / a))
    (finitePlaceHilbert_completionUnit K v (b' / b)) hr hs
    (finitePlaceHilbert_completionUnit K v a) (finitePlaceHilbert_completionUnit K v b)
  have hmul (x' x : Kˣ) :
      finitePlaceHilbert_completionUnit K v x *
        finitePlaceHilbert_completionUnit K v (x' / x) =
          finitePlaceHilbert_completionUnit K v x' := by
    apply Units.ext
    change algebraMap K C (x : K) * algebraMap K C ((x' / x : Kˣ) : K) = _
    simp [Units.val_div_eq_div_val, map_div₀, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] <;> rfl
  rw [hmul, hmul] at he
  apply nthRootsSubgroupMap_injective K C (n : ℕ)
  rw [finitePlaceHilbertSymbol_map_eq_localHilbertSymbol,
    finitePlaceHilbertSymbol_map_eq_localHilbertSymbol]
  exact he
end HeckeGeneral.Arithmetic

