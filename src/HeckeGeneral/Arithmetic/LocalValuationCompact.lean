import HeckeGeneral.Characters.LocalUnitDecomposition
import FLTReuse.Mc4dd375116d61c53

/-!
Compact boxes of actual finite local units. The integer exponent is the
valuation exponent, so a nonnegative exponent e corresponds to the uniformizer
power pi^(-e). Compactness uses the imported local integer-ring compactness and
the already constructed continuous integral-unit embedding.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def localValuationBox (v : HeightOneSpectrum (𝓞 K)) (H : ℕ) :
    Set (v.adicCompletion K)ˣ :=
  ⋃ e : Fin H, Set.range (fun u : (LocalIntegerRing K v)ˣ =>
    localIntegerUnitsEmbedding K v u * localUniformizerUnit K v ^ (-(e.val : ℤ)))

theorem isCompact_localValuationBox (v : HeightOneSpectrum (𝓞 K)) (H : ℕ) :
    IsCompact (localValuationBox K v H) := by
  apply isCompact_iUnion
  intro e
  exact isCompact_range ((localIntegerUnitsEmbedding K v).continuous.mul_const _)

/-- Every actual local point in the integer valuation interval belongs to the
displayed compact set, with its actual integral-unit part as witness. -/
theorem mem_localValuationBox_of_bounds (v : HeightOneSpectrum (𝓞 K)) (H : ℕ)
    (x : (v.adicCompletion K)ˣ)
    (hlo : 0 ≤ -(localOrderHom K v x).toAdd)
    (hhi : -(localOrderHom K v x).toAdd < (H : ℤ)) :
    x ∈ localValuationBox K v H := by
  let e : Fin H := ⟨(-(localOrderHom K v x).toAdd).toNat, by omega⟩
  refine Set.mem_iUnion.mpr ⟨e, localUnitPart K v x, ?_⟩
  have he : -(e.val : ℤ) = (localOrderHom K v x).toAdd := by
    dsimp [e]
    omega
  rw [he]
  exact (localUnit_decomposition K v x).symm

def finiteLocalValuationBox (S : Set (HeightOneSpectrum (𝓞 K))) (H : ℕ) :
    Set ((v : S) → (v.val.adicCompletion K)ˣ) :=
  {x | ∀ v, x v ∈ localValuationBox K v.val H}

theorem isCompact_finiteLocalValuationBox
    (S : Set (HeightOneSpectrum (𝓞 K))) (H : ℕ) :
    IsCompact (finiteLocalValuationBox K S H) :=
  isCompact_pi_infinite (fun v => isCompact_localValuationBox K v.val H)

end HeckeGeneral.Arithmetic
