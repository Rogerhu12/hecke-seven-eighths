import AllowedGeneratorFieldClass
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
GR-12 phase 2: the abstract interface replacing the old
`ActualAdjustedGeneratorWitness` (30-module closure, not ported).

A `GeneratorMaskWitness K` retains exactly the fields that the generator-mask
consumers (`ActualAllowedGeneratorOrbitMask` and everything after it) use:

* the finite place set `S` and the arithmetic datum `D` over it,
* a subgroup `C6` of the same-S sextic local power quotients (the old
  `sameSSexticComplement K S C2 C3`), containing the class of every generator,
* disjointness of `C6` from the image of the S-unit power localization
  (the old `compl6.disjoint`), and injectivity of that localization,
* the allowed-generator compatibilities (`AllowedGeneratorInput`),
* total complexity of `K`.  The old witness carried a primitive twelfth root of
  unity `zeta`, and its only use by the consumers
  (`ActualFixedBoxTotalNormSeminormBound`) was to derive `IsTotallyComplex K`
  from it (`nrRealPlaces_eq_zero_of_two_lt`); that consequence is the field here.

It adds no Weil phase, Hecke character or calibration assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.AllowedGeneratorConstruction

/-- Abstract generator-mask witness: the exact data the Gram assembly consumers
use from the old `ActualAdjustedGeneratorWitness`. -/
structure GeneratorMaskWitness (K : Type) [Field K] [NumberField K] where
  S : Finset (HeightOneSpectrum (𝓞 K))
  D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K)))
  C6 : Subgroup (sameSLocalPowerQuotients K S 6)
  generator_class_mem : ∀ I : ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))),
    generatorSameSClass K S D I ∈ C6
  disjoint6 : Disjoint (sUnitPowerLocalization K S 6).range C6
  localization_injective : Function.Injective (sUnitPowerLocalization K S 6)
  allowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D
  totallyComplex : IsTotallyComplex K

end HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
