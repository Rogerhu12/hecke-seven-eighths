module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.Mfb32afbc5436addd

@[expose] public section

open NumberField NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors
theorem NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice.solution
