module

public import FLTReuse.Mb8f476785919d863
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.Me5ea551fa3e45226

@[expose] public section

set_option autoImplicit false
open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped NNReal

theorem LanglandsTunnell.TateLocal.complexZeta_eq_localZeta
    (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta.solution
