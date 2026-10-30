import FLTReuse.Mc4dd375116d61c53
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import FLTReuse.M1868db956c866c8d
import FLTReuse.M20a4b4a0de18ada8
-- The removed upstream instance instCountableOfNumberField_definitions is absent in this Mathlib.

theorem NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
    (F : Type) [Field F] [NumberField F]
    (a : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (ha : (a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).2 = 1) :
    (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) a : ℝ)
      = ∏ w : NumberField.InfinitePlace F,
          ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F).1 w‖ ^ w.mult := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one.solution
