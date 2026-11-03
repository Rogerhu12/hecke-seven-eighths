import HeckeSkeleton.Theta
import HeckeSkeleton.Gram
import HeckeSkeleton.ActualProbeIntegralComplete
import HeckeSkeleton.ActualPrincipalWindowError
import HeckeSkeleton.LowCauchy.General

/-!
# LOW-CAUCHY-COMPENSATION (revised Proposition 6.2, pp.40–41)

The target-context form of `HeckeSkeleton.LowCauchy.lc_normalizedProbe_isBigO`.
`completedMarkedRow` and `CompletedMarkedEnergy` are verbatim copies of the
definitions in `HeckeSkeleton/Principal.lean` (which will import this file);
they unfold (by `rfl`) to the general-data `markedRow` and `MarkedEnergy`.
No hypothesis beyond Principal's statement is used: the residue normalizer is
a constant factor, so its nonvanishing is not needed for an upper bound.
-/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace HeckeSkeleton.LowCauchy
open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators Topology ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)
local notation "S" => places K c
local notation "P" => probeData K c
local notation "ψ" => targetCharacter K c
local notation "g" => c.geometry
local notation "T" => rayFilter K c
local instance : MeasurableSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneSpace
local instance : BorelSpace (sLocalNormOneGroup K S) := (probeMeasures K c).normOneBorel
local instance (p : S) : MeasurableSpace (p.val.adicCompletion K) := (probeMeasures K c).localSpace p
local instance (p : S) : BorelSpace (p.val.adicCompletion K) := (probeMeasures K c).localBorel p
local notation "μ" => (probeMeasures K c).haar
local instance (p : S) : (μ p).IsAddHaarMeasure := (probeMeasures K c).haar_isAddHaar p

/-- Surviving marked slots are summed BEFORE taking the actual row norm.
Selected slots remain fixed, as in revised (6.22). -/
def completedMarkedRow (Z : ℝ) (p : Fin c.geometry.slots → ExteriorPrime K S)
    (J : Finset (Fin c.geometry.slots)) (m : NonzeroRingElements ((places K c).integer K)) : ℂ :=
  ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    if ∀ i ∈ J, p' i = p i then
      (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p' i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p' (Finset.univ \ J)).val) *
      completedThetaSum K S (probeData K c).arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') logGaussianProfile
        (Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J)))
    else 0

/-- Precise rescaled row budget, with all original sixth-unit sectors. -/
def CompletedMarkedEnergy : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
  ∀ Z : ℝ, Z₀ ≤ Z → ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
  ∀ J : Finset (Fin c.geometry.slots),
    let q := exteriorNorm K S (subsetPrimeIdeal K S p J)
    (∑' u : Gram.Orbit K S,
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ B * Z ^ (5 / 6 : ℝ) / q ^ 2
      then ‖completedMarkedRow K c Z p J u.out‖ ^ 2 else 0) ≤
      C * Z ^ (5 / 6 + ε) / q ^ 2

/-- The copied row is literally the general-data marked row. -/
theorem completedMarkedRow_eq_markedRow (Z : ℝ) (p : Fin c.geometry.slots → ExteriorPrime K S)
    (J : Finset (Fin c.geometry.slots)) (m : NonzeroRingElements ((places K c).integer K)) :
    completedMarkedRow K c Z p J m = markedRow K S P ψ g T Z p J m := rfl

/-- The copied energy budget is literally the general-data marked energy. -/
theorem completedMarkedEnergy_iff :
    CompletedMarkedEnergy K c ↔ MarkedEnergy K S P ψ g T := Iff.rfl

-- OBLIGATION LOW-CAUCHY-COMPENSATION | revised Proposition 6.2, pp.40–41.
-- Same row box; rapid Fourier separation; subset weights; reciprocal normalizer.
theorem low_of_gram_and_completedEnergy
    (hgram : Gram.GramBound K S P)
    (henergy : CompletedMarkedEnergy K c)
    (hnorm : ∀ ε : ℝ, 0 < ε →
      (fun Z => (primeNormalizer K S g T Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε)) :
    ∀ ε : ℝ, 0 < ε →
      normalizedProbe K S μ P ψ g T =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)) :=
  lc_normalizedProbe_isBigO K S P ψ g T μ hgram
    ((completedMarkedEnergy_iff K c).mp henergy) hnorm

end HeckeSkeleton.LowCauchy
