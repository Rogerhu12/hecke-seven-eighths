module

public import Mathlib
public import FLTReuse.M55164c2a16500130
public import FLTReuse.Md2cadaa4525e04a6
public import FLTReuse.Mb875502fbb65df3e
public import FLTReuse.M1868db956c866c8d
public import FLTReuse.M42b654a46b7e80fd

@[expose] public section

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.comp_mul_algebraMap_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F] {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.solution
