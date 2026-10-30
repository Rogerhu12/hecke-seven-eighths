import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1868db956c866c8d
import FLTReuse.M9862099cb94033d5

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψk : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) (hψ : ψ ≠ 1) :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel.solution
