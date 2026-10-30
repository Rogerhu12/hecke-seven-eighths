import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import FLTReuse.M1868db956c866c8d
import FLTReuse.Mec2d1a8675896606

open NumberField NumberField.mixedEmbedding
open scoped Classical
theorem NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.solution
