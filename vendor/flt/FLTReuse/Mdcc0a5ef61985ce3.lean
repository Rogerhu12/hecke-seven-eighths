module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Basic
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M56acd511dcd309e0

@[expose] public section

open scoped FourierTransform
theorem AddChar.exists_continuousLinearMap_fourierChar_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = 𝐞 (l x) := by p2m_exact_reverting @_root_.P2MW.S_AddChar_exists_continuousLinearMap_fourierChar_eq.solution
