import FLTReuse.Mc4dd375116d61c53
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import FLTReuse.M1868db956c866c8d
import FLTReuse.M7d583a600b2721d1

open NumberField
theorem NumberField.AdeleRing.distribHaarChar_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_algebraMap.solution
