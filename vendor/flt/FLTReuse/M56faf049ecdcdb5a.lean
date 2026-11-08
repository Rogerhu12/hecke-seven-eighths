module

public import FLTReuse.Mb34f70d821d13751
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M7675cad47f16755c

@[expose] public section

set_option autoImplicit false

theorem LanglandsTunnell.Converse.isNicePinned_of_entire_pair
    {ι : Type*} (D : LDatum ι) (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ)
    (hwf : D.WellFormed) (hconv : D.Converges) (hN : 0 < N)
    (hΛS : ∃ s : ℂ, D.abscissa < s.re ∧ ΛS s ≠ 0)
    (Λ₀ Λ₀d : ℂ → ℂ)
    (hΛ₀ : Differentiable ℂ Λ₀) (hbv : LDatum.BoundedOnStrips Λ₀)
    (hfe : ∀ s : ℂ, Λ₀ s = Λ₀d (2 * (D.center : ℂ) - s))
    (hmain : ∀ s : ℂ, D.abscissa < s.re → Λ₀ s = ΛS s * D.archFactor s * D.LFun s)
    (hmainDual : ∀ s : ℂ, D.abscissa < s.re →
      Λ₀d s = ε * (N : ℂ) ^ (s - (D.center : ℂ)) * ΛSd s * D.archFactorDual s * D.LFunDual s) :
    IsNicePinned D ΛS ΛSd ε N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_isNicePinned_of_entire_pair.solution
