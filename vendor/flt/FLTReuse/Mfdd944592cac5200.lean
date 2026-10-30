import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Complex
import FLTReuse.M1868db956c866c8d
import FLTReuse.M09acf99a2e80b735

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.trace_mixedSpace_apply
    (K : Type) [Field K] [NumberField K] (z : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_trace_mixedSpace_apply.solution
