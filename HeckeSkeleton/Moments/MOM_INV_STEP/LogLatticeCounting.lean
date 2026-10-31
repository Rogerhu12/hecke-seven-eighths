import HeckeGeneral.Analysis.LatticeSchwartzTail
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Actual logarithmic lattice counting

A finite set of lattice points in a radius-T ball is controlled by the
existing convergent inverse-power mass. Applying this to the actual
ordinary-unit log lattice, and counting the finite torsion fibers, gives
a polynomial bound in logarithmic height. No count or free constant is
an assumption; every constant is an explicit lattice mass or torsion size.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.LogLatticeCounting

open NumberField HeckeGeneral.Analysis
open scoped Classical BigOperators

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L]

theorem nonzero_lattice_card_le (M : ℕ) (hM : Module.finrank ℤ L < M)
    (T : ℝ) (hT : 0 ≤ T) (s : Finset (NonzeroLattice L))
    (hs : ∀ z ∈ s, ‖((z.val : L) : E)‖ ≤ T) :
    (s.card : ℝ) ≤ T ^ M * latticeInversePowerMass L M := by
  have hpoint (z : NonzeroLattice L) (hz : z ∈ s) :
      (1 : ℝ) ≤ T ^ M * ‖((z.val : L) : E)‖⁻¹ ^ M := by
    have hn : ‖((z.val : L) : E)‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      exact z.property (Subtype.ext hzero)
    calc
      _ = ‖((z.val : L) : E)‖ ^ M * ‖((z.val : L) : E)‖⁻¹ ^ M := by
        rw [← mul_pow, mul_inv_cancel₀ hn, one_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hs z hz) M) (by positivity)
  calc
    _ = ∑ z ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ s, T ^ M * ‖((z.val : L) : E)‖⁻¹ ^ M :=
      Finset.sum_le_sum hpoint
    _ = T ^ M * ∑ z ∈ s, ‖((z.val : L) : E)‖⁻¹ ^ M := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_lattice_inverse_power L M hM).sum_le_tsum s (fun _ _ => by positivity))
      (pow_nonneg hT M)

/-- The zero lattice point contributes at most one. This is also valid
for a rank-zero lattice and for T=0. -/
theorem lattice_card_le (M : ℕ) (hM : Module.finrank ℤ L < M)
    (T : ℝ) (hT : 0 ≤ T) (s : Finset L)
    (hs : ∀ z ∈ s, ‖(z : E)‖ ≤ T) :
    (s.card : ℝ) ≤ 1 + T ^ M * latticeInversePowerMass L M := by
  let t : Finset (NonzeroLattice L) := s.subtype (fun z => z ≠ 0)
  have hcard : t.card = (s.erase 0).card := by
    rw [show t = s.subtype (fun z => z ≠ 0) from rfl, Finset.card_subtype]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase, and_comm]
  have hle : s.card ≤ t.card + 1 := by
    rw [hcard]
    by_cases hzero : (0 : L) ∈ s
    · exact (Finset.card_erase_add_one hzero).ge
    · rw [Finset.erase_eq_of_notMem hzero]
      omega
  have hbound := nonzero_lattice_card_le L M hM T hT t
    (fun z hz => hs z.val (Finset.mem_subtype.mp hz))
  have hleR : (s.card : ℝ) ≤ (t.card : ℝ) + 1 := by exact_mod_cast hle
  calc
    _ ≤ (t.card : ℝ) + 1 := hleR
    _ ≤ T ^ M * latticeInversePowerMass L M + 1 := by linarith
    _ = _ := add_comm _ _

end Lattice

variable (K : Type*) [Field K] [NumberField K]

/-- The actual log lattice point of an ordinary integral unit. -/
def unitLogPoint (u : (𝓞 K)ˣ) : NumberField.Units.unitLattice K :=
  NumberField.Units.logEmbeddingEquiv K
    (Additive.ofMul (QuotientGroup.mk u))

@[simp] theorem unitLogPoint_val (u : (𝓞 K)ˣ) :
    (unitLogPoint K u : NumberField.Units.dirichletUnitTheorem.logSpace K) =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := rfl

/-- A logarithmic fiber injects into the actual finite torsion subgroup
by dividing by one of its original units. -/
theorem unit_log_fiber_card_le (s : Finset (𝓞 K)ˣ)
    (z : NumberField.Units.unitLattice K) :
    (s.filter (fun u => unitLogPoint K u = z)).card ≤
      Nat.card (NumberField.Units.torsion K) := by
  let t := s.filter (fun u => unitLogPoint K u = z)
  change t.card ≤ _
  by_cases ht : t.Nonempty
  · obtain ⟨u₀, hu₀⟩ := ht
    have h₀ : unitLogPoint K u₀ = z := (Finset.mem_filter.mp hu₀).2
    let f : t → NumberField.Units.torsion K := fun u =>
      ⟨u.val / u₀, by
        apply QuotientGroup.eq_iff_div_mem.mp
        have hlog : unitLogPoint K u.val = unitLogPoint K u₀ :=
          (Finset.mem_filter.mp u.property).2.trans h₀.symm
        exact (NumberField.Units.logEmbeddingEquiv K).injective hlog⟩
    have hf : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      exact div_left_injective (congrArg Subtype.val huv)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
      Nat.card_le_card_of_injective f hf
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht, Finset.card_empty]
    exact Nat.zero_le _

theorem unit_card_le_log_image (s : Finset (𝓞 K)ˣ) :
    s.card ≤ (s.image (unitLogPoint K)).card * Nat.card (NumberField.Units.torsion K) := by
  calc
    _ = ∑ z ∈ s.image (unitLogPoint K), (s.filter (fun u => unitLogPoint K u = z)).card :=
      Finset.card_eq_sum_card_image (unitLogPoint K) s
    _ ≤ ∑ _z ∈ s.image (unitLogPoint K), Nat.card (NumberField.Units.torsion K) :=
      Finset.sum_le_sum (fun z _ => unit_log_fiber_card_le K s z)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-- A concrete polynomial bound for any actual finite set of ordinary
units whose logarithmic embeddings lie in the displayed ball. -/
theorem ordinary_unit_log_count (M : ℕ)
    (hM : NumberField.Units.rank K < M) (T : ℝ) (hT : 0 ≤ T)
    (s : Finset (𝓞 K)ˣ)
    (hs : ∀ u ∈ s, ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ ≤ T) :
    (s.card : ℝ) ≤ (Nat.card (NumberField.Units.torsion K) : ℝ) *
      (1 + T ^ M * latticeInversePowerMass (NumberField.Units.unitLattice K) M) := by
  have hL : Module.finrank ℤ (NumberField.Units.unitLattice K) < M := by
    rwa [NumberField.Units.unitLattice_rank]
  have hb := lattice_card_le (NumberField.Units.unitLattice K) M hL T hT
    (s.image (unitLogPoint K)) (by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hs u hu)
  have hc : (s.card : ℝ) ≤ ((s.image (unitLogPoint K)).card : ℝ) *
      (Nat.card (NumberField.Units.torsion K) : ℝ) := by
    exact_mod_cast unit_card_le_log_image K s
  exact hc.trans ((mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)).trans_eq (mul_comm _ _))

end HeckeSkeleton.Moments.MOM_INV_STEP.LogLatticeCounting

end
