import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M1868db956c866c8d
import FLTReuse.M5bb7284c992035ad

open NumberField
theorem NumberField.AdeleRing.measurePreserving_mul_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.solution
