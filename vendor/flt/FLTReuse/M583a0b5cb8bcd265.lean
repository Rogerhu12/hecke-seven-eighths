import FLTReuse.M44ba7812b62b73d2
import FLTReuse.M157b087506702f5d
import FLTReuse.M1868db956c866c8d
import FLTReuse.Me934ccc2fb442bbe
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    NumberField.TateGlobal.ideleNorm K a = ∏ w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one.solution
