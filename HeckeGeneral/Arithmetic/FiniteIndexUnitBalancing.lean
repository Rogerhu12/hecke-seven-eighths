import HeckeGeneral.Arithmetic.PrincipalGeneratorBalancing
import HeckeGeneral.Arithmetic.PrincipalUnitOrbits

/-!
# Compact representatives for finite-index ordinary-unit subgroups

A finite union of actual translates of the Dirichlet norm-one slice supplies
the representatives. The compact set and its bounds may depend on the unit
subgroup. No uniformity over varying subgroups is asserted.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def unitCosetRepresentative (Γ : Subgroup (𝓞 K)ˣ) (q : (𝓞 K)ˣ ⧸ Γ) : (𝓞 K)ˣ :=
  Quotient.out q

omit [NumberField K] in
@[simp] theorem quotient_unitCosetRepresentative (Γ : Subgroup (𝓞 K)ˣ)
    (q : (𝓞 K)ˣ ⧸ Γ) :
    (QuotientGroup.mk' Γ) (unitCosetRepresentative K Γ q) = q :=
  Quotient.out_eq q

def finiteIndexBalancedShape (Γ : Subgroup (𝓞 K)ˣ) : Set (mixedSpace K) :=
  ⋃ q : (𝓞 K)ˣ ⧸ Γ,
    (fun x : mixedSpace K => (unitCosetRepresentative K Γ q)⁻¹ • x) ''
      balancedNormOneShape K

theorem isCompact_finiteIndexBalancedShape (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] :
    IsCompact (finiteIndexBalancedShape K Γ) := by
  apply isCompact_iUnion
  intro q
  apply (isCompact_balancedNormOneShape K).image
  change Continuous (fun x : mixedSpace K =>
    mixedEmbedding K ((unitCosetRepresentative K Γ q)⁻¹ : (𝓞 K)ˣ) * x)
  exact continuous_const.mul continuous_id

theorem norm_eq_one_of_mem_finiteIndexBalancedShape (Γ : Subgroup (𝓞 K)ˣ)
    {x : mixedSpace K} (hx : x ∈ finiteIndexBalancedShape K Γ) :
    mixedEmbedding.norm x = 1 := by
  rcases Set.mem_iUnion.mp hx with ⟨q, y, hy, rfl⟩
  rw [norm_unit_smul]
  exact norm_eq_one_of_mem_balancedNormOneShape K hy

theorem exists_subgroup_unit_normalize_mem (Γ : Subgroup (𝓞 K)ˣ)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : Γ, (arithmeticNormRoot K x)⁻¹ • ((u : (𝓞 K)ˣ) • x) ∈
      finiteIndexBalancedShape K Γ := by
  obtain ⟨u, hu⟩ := exists_unit_normalize_mem_balancedNormOneShape K hx
  let q : (𝓞 K)ˣ ⧸ Γ := (QuotientGroup.mk' Γ) u
  let r := unitCosetRepresentative K Γ q
  have hmem : u / r ∈ Γ := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact (quotient_unitCosetRepresentative K Γ q).symm
  refine ⟨⟨u / r, hmem⟩, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
  refine ⟨(arithmeticNormRoot K x)⁻¹ • (u • x), hu, ?_⟩
  change r⁻¹ • ((arithmeticNormRoot K x)⁻¹ • (u • x)) =
    (arithmeticNormRoot K x)⁻¹ • ((u / r) • x)
  have hc : r⁻¹ • ((arithmeticNormRoot K x)⁻¹ • (u • x)) =
      (arithmeticNormRoot K x)⁻¹ • (r⁻¹ • (u • x)) := by
    simp only [unitSMul_smul, mul_smul_comm]
  rw [hc, smul_smul]
  congr 2
  exact (div_eq_inv_mul u r).symm

theorem exists_subgroup_unit_norm_le (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] :
    ∃ C : ℝ, 0 < C ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 →
      ∃ u : Γ, ‖(u : (𝓞 K)ˣ) • x‖ ≤ C * arithmeticNormRoot K x := by
  obtain ⟨C, hC, hbound⟩ :=
    (isCompact_finiteIndexBalancedShape K Γ).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := exists_subgroup_unit_normalize_mem K Γ hx
  refine ⟨u, ?_⟩
  have h := hbound _ hu
  rw [_root_.norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (arithmeticNormRoot_pos K hx))] at h
  exact (div_le_iff₀ (arithmeticNormRoot_pos K hx)).mp
    (by simpa [div_eq_mul_inv, mul_comm] using h)

end HeckeGeneral.Arithmetic
