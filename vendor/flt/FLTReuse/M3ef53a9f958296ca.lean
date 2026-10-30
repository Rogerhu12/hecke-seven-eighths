import FLTReuse.M81477154c83a610e
import FLTReuse.Mb8f476785919d863
import FLTReuse.M1868db956c866c8d
import FLTReuse.Md699b19e5ddb3a74
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq

set_option autoImplicit false

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

theorem LanglandsTunnell.ArchPlace.tateFourier_psiReal_realTestFun (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun.solution
