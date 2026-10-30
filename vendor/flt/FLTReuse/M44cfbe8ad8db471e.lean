import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FLTReuse.M1868db956c866c8d
import FLTReuse.M396e2ffde8dbe95f

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt.solution
