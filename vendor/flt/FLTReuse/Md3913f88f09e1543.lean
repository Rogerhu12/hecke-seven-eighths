import FLTReuse.Mc4dd375116d61c53
import FLTReuse.M1868db956c866c8d
import FLTReuse.M20bb09e32372f4f8
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.

open NumberField
theorem NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.solution
