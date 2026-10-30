import FLTReuse.M157b087506702f5d
import FLTReuse.M3c68c1555d4fc687
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal

open NumberField.TateGlobal LanglandsTunnell.TateLocal in

theorem solution
    (K : Type) [Field K]
    [NumberField K] (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : IsUnramifiedCharAt μ v) : HasConductorExponentAt K v (localChar μ v) 0 := by
  rw [hasConductorExponentAt_zero_iff]
  intro u hu
  refine h u ?_ ?_
  · change Valued.v (u : v.adicCompletion K) ≤ 1
    exact hu.le
  · change Valued.v ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
