import FLTReuse.Md2cadaa4525e04a6
import FLTReuse.M1868db956c866c8d
import FLTReuse.M0d10c8b6e7b3321f

open NumberField
theorem NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) (a : F) (ha : a ≠ 0) :
    MeasureTheory.IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) ⁻¹' AdelicBox.adelicBox F) μ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.solution
