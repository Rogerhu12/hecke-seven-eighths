import HeckeGeneral.Arithmetic.SUnitCompactDenominators
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal

/-!
# Uniform denominators for all S-integers selected by finite support

Compactness supplies a common denominator for all actual S-integers in
the finite local support. Outside S their valuations are at most one;
equality, which would restrict the result to global S-units, is not needed.
The support is additive and can include zero.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- A single denominator clears every S-integer in an additive compact set. -/
theorem exists_nonzero_integer_mul_sIntegers_mem_range_of_compact
    (hS : S.Finite)
    (C : Set ((v : S) → v.val.adicCompletion K)) (hC : IsCompact C) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ z : S.integer K,
      (fun v : S => algebraMap K (v.val.adicCompletion K) (z : K)) ∈ C →
      algebraMap (𝓞 K) K a * (z : K) ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_compact_finiteAdeles_mem_integral K
      (finiteLocalZeroExtension K S hS '' C)
      (hC.image (continuous_finiteLocalZeroExtension K S hS))
  refine ⟨a, ha, fun z hz => ?_⟩
  have hlocal := hclear (finiteLocalZeroExtension K S hS
    (fun v : S => algebraMap K (v.val.adicCompletion K) (z : K)))
    (Set.mem_image_of_mem _ hz)
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one K
  intro v
  by_cases hv : v ∈ S
  · have hle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hlocal v)
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) *
      finiteLocalZeroExtension K S hS
        (fun w : S => algebraMap K (w.val.adicCompletion K) (z : K)) v) ≤ 1 at hle
    rw [finiteLocalZeroExtension_apply_mem K S hS _ v hv, ← map_mul] at hle
    change Valued.v ((algebraMap (𝓞 K) K a * (z : K) : K) :
      v.adicCompletion K) ≤ 1 at hle
    rwa [adicCompletion.valued_coe] at hle
  · rw [map_mul]
    exact (mul_le_mul' (v.valuation_le_one a) (z.property v hv)).trans (by simp)

/-- Compact finite support and compact unit multipliers clear every active
S-integer, uniformly in the multiplier. -/
theorem exists_nonzero_integer_mul_sInteger_mem_range_of_finite_support
    (hS : S.Finite)
    (B : Set (SFiniteLocalGroup K S)) (hB : IsCompact B)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (hψ : HasCompactSupport ψ) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ y ∈ B, ∀ z : S.integer K,
      ψ (fun v : S => (y v).val * algebraMap K (v.val.adicCompletion K) (z : K)) ≠ 0 →
        algebraMap (𝓞 K) K a * (z : K) ∈ (algebraMap (𝓞 K) K).range := by
  let q : ((v : S) → v.val.adicCompletion K) × SFiniteLocalGroup K S →
      ((v : S) → v.val.adicCompletion K) := fun p v => p.1 v * ((p.2 v)⁻¹).val
  have hq : Continuous q := by
    apply continuous_pi
    intro v
    exact ((continuous_apply v).comp continuous_fst).mul
      (Units.continuous_val.comp (((continuous_apply v).comp continuous_snd).inv))
  obtain ⟨a, ha, hclear⟩ := exists_nonzero_integer_mul_sIntegers_mem_range_of_compact
    K S hS (q '' (tsupport ψ ×ˢ B)) ((hψ.isCompact.prod hB).image hq)
  refine ⟨a, ha, fun y hy z hz => hclear z ?_⟩
  let w : (v : S) → v.val.adicCompletion K :=
    fun v => (y v).val * algebraMap K (v.val.adicCompletion K) (z : K)
  have hw : w ∈ tsupport ψ := subset_closure hz
  refine ⟨(w, y), ⟨hw, hy⟩, ?_⟩
  funext v
  change (y v).val * algebraMap K (v.val.adicCompletion K) (z : K) * ((y v)⁻¹).val = _
  calc
    _ = algebraMap K (v.val.adicCompletion K) (z : K) *
        ((y v).val * ((y v)⁻¹).val) := by ac_rfl
    _ = _ := by rw [Units.mul_inv, mul_one]

end HeckeGeneral.Arithmetic
