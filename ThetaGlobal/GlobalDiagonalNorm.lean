module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

@[expose] public section

/-!
# The literal archimedean diagonal norm

For a totally complex number field the product of squared completion
norms is exactly the mixed embedding norm.  This small dictionary lemma
has only Mathlib dependencies.
-/

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GlobalDiagonalNorm

open NumberField
open scoped BigOperators Classical

variable (F : Type*) [Field F] [NumberField F]

theorem archimedean_product (hcomplex : ∀ w : InfinitePlace F, w.IsComplex) (a : F) :
    (∏ w : InfinitePlace F, ‖algebraMap F w.Completion a‖ ^ 2) =
      mixedEmbedding.norm (mixedEmbedding F a) := by
  rw [mixedEmbedding.norm_apply]
  apply Finset.prod_congr rfl
  intro w _
  rw [mixedEmbedding.normAtPlace_apply, InfinitePlace.mult_isComplex ⟨w, hcomplex w⟩]
  change ‖((WithAbs.equiv w.1).symm a : w.Completion)‖ ^ 2 = _
  rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply]

end ThetaGlobal.GlobalDiagonalNorm

#print axioms ThetaGlobal.GlobalDiagonalNorm.archimedean_product
