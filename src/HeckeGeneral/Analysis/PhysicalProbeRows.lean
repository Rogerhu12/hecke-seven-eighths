module

public import HeckeGeneral.Analysis.PhysicalProbePrincipal
public import HeckeGeneral.Analysis.PhysicalProbeRowData
public import HeckeGeneral.Analysis.FiniteEulerRational

@[expose] public section

/-!
Compatibility entry point for the original physical-probe row API.
The row definitions are unchanged and are re-exported from
`PhysicalProbeRowData`; the original principal/Fourier entry point remains
available to existing callers of this module.
-/
