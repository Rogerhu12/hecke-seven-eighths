module

public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.Mc8c6887fbe144bce

@[expose] public section

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical nonZeroDivisors
theorem NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
    (F : Type) [Field F] [NumberField F] :
    integralFiniteAdeles (𝓞 F) F
      ⊆ closure (Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers.solution
