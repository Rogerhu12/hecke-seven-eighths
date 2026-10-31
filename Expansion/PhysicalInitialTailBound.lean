import Expansion.ActualOuterTailSums
import Expansion.ActualPrincipalExpansion
import Expansion.PowerHeightTailAlgebra

/-!
# The complete actual initial-height tail

Absolute convergence identifies the original sum of cube-complement
integrals with its unique principal row plus every nonprincipal row.
The latter have the fixed summable row envelope N(u)^(-2).  The principal
complement is controlled by the actual principal sweep.  Combining the
two proved bounds fixes the height degree and scale power before either
the analysis-height exponent or the requested external decay order.

The tail is the original `actualInitialTailSum`; this file introduces no
new error value and assumes no tail bound or sum identity.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open Expansion.PhysicalInitialMellin
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

include nu in
/-- Literal partition of the full actual initial tail.  It holds for
every positive original scale and every real cutoff, before any eventual
bound is invoked. -/
theorem actualInitialTailSum_eq_principal_add_nonprincipal
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {Z : ℝ} (hZ : 0 < Z) (H : ℝ) :
    actualInitialTailSum K S mu P psi g ∅ Z H =
      actualInitialRowTailIntegral K S mu P psi g ∅ Z H (physicalPrincipalRow K Sset) +
        actualNonprincipalInitialTailSum K S mu P psi g Z H := by
  letI : IsTotallyComplex K := ⟨hcomplex⟩
  have hs := summable_actualInitialRowTailIntegral K S mu nu P hAllowed psi hcal hunram g ∅ hZ H
  unfold actualInitialTailSum actualNonprincipalInitialTailSum
  rw [tsum_subtype]
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, principalFrequencyRow_iff_eq_physicalPrincipalRow,
    ite_not] using hs.tsum_eq_add_tsum_ite (physicalPrincipalRow K Sset)

include nu in
/-- Conversion of the proved nonprincipal initial tail estimate to the
external power-height contract.  Its scale power is the fixed absolute
tube value `outerBoundaryScalePower 5 5 4`, independent of every order. -/
theorem actualNonprincipal_initial_tail
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) :
    PowerHeightTailBound (actualNonprincipalInitialTailSum K S mu P psi g) := by
  apply PowerHeightTailBound.of_uniform_decay
    (A := 0) (R := outerBoundaryScalePower 5 5 4) le_rfl
  intro n
  obtain ⟨C, Z0, hC, hZ0, hb⟩ := exists_actual_nonprincipal_initial_tail_bound
    K S mu nu hcomplex P psi hcal hunram g n
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hH0 : 0 ≤ H := hHpos.le
  have hinv : ((1 + H) ^ n)⁻¹ ≤ H ^ (-(n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith : 0 ≤ 1 + H)]
    exact Real.rpow_le_rpow_of_nonpos hHpos (by linarith)
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    _ ≤ C * Z ^ (outerBoundaryScalePower 5 5 4) / (1 + H) ^ n :=
      (hb Z H hZ hH0).2
    _ ≤ C * Z ^ (outerBoundaryScalePower 5 5 4) * H ^ (-(n : ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (mul_nonneg hC.le (Real.rpow_nonneg hZpos.le _))
    _ = _ := by rw [Real.rpow_zero, mul_one]

include nu in
/-- The entire initial-height tail, including the principal frequency,
has one external power-height bound.  The algebra first chooses the two
fixed scale powers and height degrees, and only then quantifies over tau
and the external decay order. -/
theorem actualInitialTailSum_powerHeightTailBound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    PowerHeightTailBound (actualInitialTailSum K S mu P psi g ∅) := by
  have hp := actualPrincipal_initial_truncation_tail K S mu nu hcomplex
    P omega psi hpsi hAllowed hunram g hB hB1 he he1 hboundary
  have hn := actualNonprincipal_initial_tail K S mu nu hcomplex P psi hcal hunram g
  apply (hp.add hn).of_eventuallyEq 1
  intro Z H hZ _hH
  exact (actualInitialTailSum_eq_principal_add_nonprincipal K S mu nu hcomplex
    P psi hAllowed hcal hunram g (zero_lt_one.trans_le hZ) H).symm

end Expansion.Project

#print axioms Expansion.Project.actualInitialTailSum_eq_principal_add_nonprincipal
#print axioms Expansion.Project.actualNonprincipal_initial_tail
#print axioms Expansion.Project.actualInitialTailSum_powerHeightTailBound
