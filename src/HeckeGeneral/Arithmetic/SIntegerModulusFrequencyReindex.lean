import HeckeGeneral.Arithmetic.SIntegerModulusFrequencySupport
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! Actual division by a nonzero S-integer modulus reindexes its frequency
lattice, including zero. Supported total sums require no summability input. -/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Division by the actual modulus identifies OS with its inverse-modulus lattice. -/
def sIntegerModulusFrequencyEquiv (c : S.integer K) (hc : c ≠ 0) :
    S.integer K ≃ {ξ : K // (c : K) * ξ ∈ S.integer K} := by
  have hcK : (c : K) ≠ 0 := fun hz => hc (Subtype.ext hz)
  exact
    { toFun := fun a => ⟨(a : K) / (c : K), by
        have heq : (c : K) * ((a : K) / (c : K)) = (a : K) := by
          field_simp [hcK] <;> ring
        rw [heq]
        exact a.property⟩
      invFun := fun ξ => ⟨(c : K) * ξ.val, ξ.property⟩
      left_inv := fun a => by
        apply Subtype.ext
        change (c : K) * ((a : K) / (c : K)) = (a : K)
        field_simp [hcK] <;> ring
      right_inv := fun ξ => by
        apply Subtype.ext
        change ((c : K) * ξ.val) / (c : K) = ξ.val
        field_simp [hcK] <;> ring }

@[simp] theorem sIntegerModulusFrequencyEquiv_apply_val
    (c : S.integer K) (hc : c ≠ 0) (a : S.integer K) :
    (sIntegerModulusFrequencyEquiv K S c hc a).val = (a : K) / (c : K) := rfl

/-- The full field sum reindexes to OS when its actual support lies in c⁻¹OS. -/
theorem tsum_sIntegerModulusFrequency_eq
    (c : S.integer K) (hc : c ≠ 0) (F : K → ℂ)
    (hF : ∀ ξ : K, (c : K) * ξ ∉ S.integer K → F ξ = 0) :
    (∑' ξ : K, F ξ) = ∑' a : S.integer K, F ((a : K) / (c : K)) := by
  calc
    _ = ∑' ξ : {ξ : K // (c : K) * ξ ∈ S.integer K}, F ξ.val := by
      exact (tsum_subtype_eq_of_support_subset
        (f := F) (s := {ξ : K | (c : K) * ξ ∈ S.integer K}) (by
          intro ξ hξ
          by_contra hnot
          exact hξ (hF ξ hnot))).symm
    _ = _ := (Equiv.tsum_eq (sIntegerModulusFrequencyEquiv K S c hc)
      (fun ξ => F ξ.val)).symm

/-- Summability of the actual full Fourier sum passes to division frequencies. -/
theorem summable_sIntegerModulusFrequency
    (c : S.integer K) (hc : c ≠ 0) {F : K → ℂ} (hF : Summable F) :
    Summable (fun a : S.integer K => F ((a : K) / (c : K))) := by
  apply hF.comp_injective
  intro a b hab
  apply (sIntegerModulusFrequencyEquiv K S c hc).injective
  exact Subtype.ext hab

end HeckeGeneral.Arithmetic
