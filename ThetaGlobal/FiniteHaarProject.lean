import HeckeGeneral.Characters.LocalUnitDecomposition
import HeckeGeneral.Characters.LocalResidueCosetFourier
import ThetaGlobal.FiniteLocalShellProject
import ThetaGlobal.FiniteHaarShells
import ThetaGlobal.FiniteMellinIntegration
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual completion Haar and actual integral-unit shells

The abstract Haar-shell geometry is instantiated with the project's
uniformizer, valuation homomorphism, and integral-unit embedding.  All
measures are pulled back from the given actual multiplicative Haar.  The
local Mellin series therefore represents an integral for that same Haar,
with no unrecorded normalization scalar.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.ProjectFiniteHaar

open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure
open HeckeGeneral.Characters
open ThetaGlobal.FiniteShell ThetaGlobal.FiniteHaarShells
open ThetaGlobal.FiniteMellinIntegration ThetaGlobal.ProjectLocalShell

variable (K : Type) [Field K] [NumberField K]
variable (p : HeightOneSpectrum (𝓞 K))
variable [MeasurableSpace (p.adicCompletion K)ˣ] [BorelSpace (p.adicCompletion K)ˣ]
variable [MeasurableSpace (LocalIntegerRing K p)ˣ] [BorelSpace (LocalIntegerRing K p)ˣ]

theorem integralUnits_measurableEmbedding :
    MeasurableEmbedding (localIntegerUnitsEmbedding K p) := by
  letI : CompactSpace (LocalIntegerRing K p) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K p
  apply ((localIntegerUnitsEmbedding K p).continuous.isClosedEmbedding ?_).measurableEmbedding
  intro u v huv
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun z : (p.adicCompletion K)ˣ => z.val) huv

theorem integralUnits_range :
    Set.range (localIntegerUnitsEmbedding K p) = valuationFiber (localOrderHom K p) 0 := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact localOrder_integralUnit K p u
  · intro hz
    refine ⟨localUnitPart K p z, ?_⟩
    have ho : localOrder K p z = 1 := hz
    simpa only [ho, toAdd_one, zpow_zero, mul_one] using
      (localUnit_decomposition K p z).symm

theorem measurable_valuationFiber (k : ℤ) :
    MeasurableSet (valuationFiber (localOrderHom K p) k) := by
  change MeasurableSet ((localOrder K p) ⁻¹' {Multiplicative.ofAdd k})
  exact ((isOpen_discrete ({Multiplicative.ofAdd k} : Set (Multiplicative ℤ))).preimage
    (localOrder K p).continuous).measurableSet

theorem integralUnits_compact_range : IsCompact (Set.range (localIntegerUnitsEmbedding K p)) := by
  letI : CompactSpace (LocalIntegerRing K p) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K p
  exact isCompact_range (localIntegerUnitsEmbedding K p).continuous

/-- The literal measure on integral units inherited from the chosen Haar. -/
def localUnitMeasure (ν : Measure (p.adicCompletion K)ˣ) :
    Measure (LocalIntegerRing K p)ˣ :=
  unitMeasure ν (localIntegerUnitsEmbedding K p)

instance localUnitMeasure_finite (ν : Measure (p.adicCompletion K)ˣ)
    [IsFiniteMeasureOnCompacts ν] : IsFiniteMeasure (localUnitMeasure K p ν) :=
  unitMeasure_finite ν _ (integralUnits_measurableEmbedding K p)
    (integralUnits_compact_range K p).measure_lt_top

/-- Haar restricted to the `k`th shell is exactly translated unit Haar. -/
theorem local_shell_measure (ν : Measure (p.adicCompletion K)ˣ)
    [IsMulLeftInvariant ν] (k : ℤ) :
    Measure.map (shellPoint K p k) (localUnitMeasure K p ν) =
      ν.restrict (valuationFiber (localOrderHom K p) k) :=
  map_unitMeasure_shell ν (localOrderHom K p) (localUniformizerUnit K p)
    (localOrder_uniformizer K p) (localIntegerUnitsEmbedding K p)
    (integralUnits_measurableEmbedding K p) (integralUnits_range K p) k

/-- Exact decomposition of the original local multiplicative Haar. -/
theorem local_haar_eq_shellMeasure (ν : Measure (p.adicCompletion K)ˣ)
    [IsMulLeftInvariant ν]
    (W : (p.adicCompletion K)ˣ → ℂ) (L : (p.adicCompletion K)ˣ → Circle) :
    ν = shellMeasure (shellData K p W L) (localUnitMeasure K p ν) :=
  haar_eq_sum_shells ν (localOrderHom K p) (localUniformizerUnit K p)
    (localOrder_uniformizer K p) (localIntegerUnitsEmbedding K p)
    (integralUnits_measurableEmbedding K p) (integralUnits_range K p)
    (measurable_valuationFiber K p)

theorem shellPoint_continuous (k : ℤ) : Continuous (shellPoint K p k) :=
  continuous_const.mul (localIntegerUnitsEmbedding K p).continuous

/-- Shell integrability follows from ordinary local continuity on compact
integral units.  This is independent of Mellin convergence. -/
theorem shellData_integrable (ν : Measure (p.adicCompletion K)ˣ)
    [IsFiniteMeasureOnCompacts ν]
    (W : (p.adicCompletion K)ˣ → ℂ) (L : (p.adicCompletion K)ˣ → Circle)
    (hW : Continuous W) (hL : Continuous (fun z => (L z : ℂ))) :
    ShellIntegrable (shellData K p W L) (localUnitMeasure K p ν) := by
  letI : CompactSpace (LocalIntegerRing K p) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K p
  intro b k
  exact ((hL.comp (shellPoint_continuous K p k)).mul
    (hW.comp (shellPoint_continuous K p k))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The real normalized norm on a shell produces exactly the complex Mellin
weight used in the coefficient series, for every complex `s`. -/
theorem shellPoint_norm_cpow (k : ℤ) (u : (LocalIntegerRing K p)ˣ) (s : ℂ) :
    (‖(shellPoint K p k u).val‖ : ℂ) ^ s =
      (p.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s) := by
  rw [shellPoint_norm, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _) (-(k : ℝ)) s]
  simp only [Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_natCast]

end ThetaGlobal.ProjectFiniteHaar

#print axioms ThetaGlobal.ProjectFiniteHaar.local_haar_eq_shellMeasure
#print axioms ThetaGlobal.ProjectFiniteHaar.shellData_integrable
