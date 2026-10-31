import Mathlib
import FLTReuse.M1868db956c866c8d
import FLTReuse.M2aad6443a6d88bc3

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
    (K : Type) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta.solution
