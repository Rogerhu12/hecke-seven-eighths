import HeckeGeneral.Analysis.LatticeSchwartzTail

/-!
Inverse-power mass under an actual continuous linear equivalence. The moving
lattice is the image of the fixed lattice, represented as the pullback by the
inverse equivalence. The bound retains the inverse operator norm explicitly.
Uniformity for a family requires a genuine uniform bound on that norm; this
module does not identify arbitrary moving ideal lattices with such a family.
-/

noncomputable section

open Classical Module

namespace HeckeGeneral.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual image lattice `e(L)`, written as the inverse pullback. -/
abbrev imageLattice (L : Submodule ℤ E) (e : E ≃L[ℝ] E) : Submodule ℤ E :=
  ZLattice.comap ℝ L e.symm.toLinearMap

/-- The equivalence on nonzero lattice points retains the actual linear map. -/
def nonzeroImageLatticeEquiv (L : Submodule ℤ E) (e : E ≃L[ℝ] E) :
    NonzeroLattice L ≃ NonzeroLattice (imageLattice L e) := by
  let h := ZLattice.comap_equiv ℝ L e.symm.toLinearEquiv
  exact h.toEquiv.subtypeEquiv (fun l => by
    change l ≠ 0 ↔ h l ≠ 0
    constructor
    · intro hn hz
      apply hn
      exact h.injective (by simpa only [map_zero] using hz)
    · intro hn hz
      apply hn
      rw [hz, map_zero])

@[simp] theorem nonzeroImageLatticeEquiv_apply (L : Submodule ℤ E)
    (e : E ≃L[ℝ] E) (l : NonzeroLattice L) :
    (((nonzeroImageLatticeEquiv L e l : NonzeroLattice (imageLattice L e)) :
      imageLattice L e) : E) = e ((l : L) : E) := rfl

/-- A bounded inverse operator norm gives the precise inverse-length comparison. -/
theorem inv_norm_equiv_le (e : E ≃L[ℝ] E) {B : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) {x : E} (hx : x ≠ 0) :
    ‖e x‖⁻¹ ≤ B * ‖x‖⁻¹ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hexpos : 0 < ‖e x‖ := norm_pos_iff.mpr (by
    intro h
    apply hx
    exact e.injective (by simpa only [map_zero] using h))
  have hlen : ‖x‖ ≤ B * ‖e x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_of_opNorm_le hB (e x)
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hxpos).mpr
  calc
    ‖e x‖⁻¹ * ‖x‖ ≤ ‖e x‖⁻¹ * (B * ‖e x‖) :=
      mul_le_mul_of_nonneg_left hlen (inv_nonneg.mpr hexpos.le)
    _ = B := by field_simp [hexpos.ne']

variable [FiniteDimensional ℝ E]

/-- Reindexing the actual moving lattice gives a summable series whenever the
fixed inverse-power series converges. The comparison does not assume a moving
series summability field or an independent lattice-shape parameter. -/
theorem summable_inverse_power_imageLattice (L : Submodule ℤ E)
    [DiscreteTopology L] (e : E ≃L[ℝ] E) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {B : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) :
    Summable fun l : NonzeroLattice (imageLattice L e) =>
      ‖((l : imageLattice L e) : E)‖⁻¹ ^ M := by
  apply (nonzeroImageLatticeEquiv L e).summable_iff.mp
  change Summable (fun l : NonzeroLattice L => ‖e ((l : L) : E)‖⁻¹ ^ M)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
    ((summable_lattice_inverse_power L M hM).mul_left (B ^ M))
  calc
    ‖e ((l : L) : E)‖⁻¹ ^ M ≤ (B * ‖((l : L) : E)‖⁻¹) ^ M :=
      pow_le_pow_left₀ (by positivity) (inv_norm_equiv_le e hB (by
        intro h; exact l.property (Subtype.ext h))) M
    _ = _ := mul_pow _ _ _

/-- Exact quantitative transport of the nonzero inverse-power mass. In a family
with a common inverse operator norm bound `B`, this is the actual uniform
constant `B^M` multiplying the single fixed-lattice mass. -/
theorem latticeInversePowerMass_image_le (L : Submodule ℤ E)
    [DiscreteTopology L] (e : E ≃L[ℝ] E) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {B : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) :
    latticeInversePowerMass (imageLattice L e) M ≤ B ^ M * latticeInversePowerMass L M := by
  calc
    _ = ∑' l : NonzeroLattice L, ‖e ((l : L) : E)‖⁻¹ ^ M := by
      rw [latticeInversePowerMass]
      simpa only [nonzeroImageLatticeEquiv_apply] using
        ((nonzeroImageLatticeEquiv L e).tsum_eq
          (fun l => ‖((l : imageLattice L e) : E)‖⁻¹ ^ M)).symm
    _ ≤ ∑' l : NonzeroLattice L, B ^ M * ‖((l : L) : E)‖⁻¹ ^ M := by
      apply Summable.tsum_le_tsum (fun l => ?_)
        ((nonzeroImageLatticeEquiv L e).summable_iff.mpr
          (summable_inverse_power_imageLattice L e M hM hB))
        ((summable_lattice_inverse_power L M hM).mul_left (B ^ M))
      calc
        ‖e ((l : L) : E)‖⁻¹ ^ M ≤ (B * ‖((l : L) : E)‖⁻¹) ^ M :=
          pow_le_pow_left₀ (by positivity) (inv_norm_equiv_le e hB (by
            intro h; exact l.property (Subtype.ext h))) M
        _ = _ := mul_pow _ _ _
    _ = _ := tsum_mul_left

/-- Compact shape control supplies the common inverse-norm constant rather
than postulating it for a moving ideal family. The continuity obligation is
on the actual inverse linear maps in the operator-norm topology. -/
theorem exists_uniform_latticeInversePowerMass_image_bound
    {T : Type*} [TopologicalSpace T] {S : Set T} (hS : IsCompact S)
    (e : T → E ≃L[ℝ] E)
    (he : ContinuousOn (fun t => (e t).symm.toContinuousLinearMap) S)
    (L : Submodule ℤ E) [DiscreteTopology L] (M : ℕ)
    (hM : Module.finrank ℤ L < M) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ S,
      ‖(e t).symm.toContinuousLinearMap‖ ≤ B ∧
      latticeInversePowerMass (imageLattice L (e t)) M ≤
        B ^ M * latticeInversePowerMass L M := by
  obtain ⟨B, hBpos, hbound⟩ :=
    (hS.image_of_continuousOn he).isBounded.exists_pos_norm_le
  refine ⟨B, hBpos, fun t ht => ?_⟩
  have hB : ‖(e t).symm.toContinuousLinearMap‖ ≤ B :=
    hbound _ (Set.mem_image_of_mem _ ht)
  exact ⟨hB, latticeInversePowerMass_image_le L (e t) M hM hB⟩

end HeckeGeneral.Analysis
