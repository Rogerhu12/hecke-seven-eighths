import HeckeSkeleton.LowEnergy.ActualRows
import HeckeSkeleton.LowCauchy

/-!
# Exact target-context dictionary for LOW-REFLECTED-ENERGY

`LowCauchy.CompletedMarkedEnergy` has the identical body to the target in
Principal.lean.  We import LowCauchy rather than importing Principal's open
energy declaration.  The results below are identities and an equivalence of
indexings; no instance of CompletedMarkedEnergy is assumed or claimed.

This adapter requires the complete project's transitive dependencies.  It is
kept separate from the independently compiled Mathlib-only core.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.TargetDictionary

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeSkeleton.LowEnergy.ActualRows
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (c : HeckeSkeleton.TargetContext K)

local notation "S" => HeckeSkeleton.places K c
local notation "P" => HeckeSkeleton.probeData K c
local notation "ψ" => HeckeSkeleton.targetCharacter K c
local notation "g" => c.geometry
local notation "T" => HeckeSkeleton.rayFilter K c

/-- The generalized-test row specializes definitionally to the exact target row. -/
theorem completedMarkedRow_eq (Z : ℝ)
    (p : Fin c.geometry.slots → ExteriorPrime K S)
    (J : Finset (Fin c.geometry.slots)) (m : NonzeroRingElements (S.integer K)) :
    HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J m =
      markedRowWithTest K S P ψ g T Z p J logGaussianProfile m.val := rfl

/-- The exact target energy, with its original cutoff and no lost sectors. -/
theorem completedMarkedRow_energy_eq (Z R : ℝ)
    (p : Fin c.geometry.slots → ExteriorPrime K S)
    (J : Finset (Fin c.geometry.slots)) :
    (∑' u : HeckeSkeleton.Gram.Orbit K S,
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ R then
        ‖HeckeSkeleton.LowCauchy.completedMarkedRow K c Z p J u.out‖ ^ 2 else 0) =
      ∑' x : ExteriorIdeal K S × SixthUnitClasses K S,
        if exteriorNorm K S x.1 ≤ R then
          ‖markedRowWithTest K S P ψ g T Z p J logGaussianProfile
            (idealSectorElement K S P.arithmetic x).val‖ ^ 2 else 0 :=
  marked_energy_eq_ideal_sector_energy K S P ψ g T Z p J logGaussianProfile R

/-- Exact equivalence with the complete-ideal/sector form.  It is a dictionary,
not an analytic proof of either side.  In particular, the factor q^(-2) is exact. -/
theorem completedMarkedEnergy_iff_ideal_sector :
    HeckeSkeleton.LowCauchy.CompletedMarkedEnergy K c ↔
      (∀ B ε : ℝ, 0 < B → 0 < ε → ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
        ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ∀ J : Finset (Fin c.geometry.slots),
          let q := exteriorNorm K S (subsetPrimeIdeal K S p J)
          (∑' x : ExteriorIdeal K S × SixthUnitClasses K S,
            if exteriorNorm K S x.1 ≤ B * Z ^ (5 / 6 : ℝ) / q ^ 2 then
              ‖markedRowWithTest K S P ψ g T Z p J logGaussianProfile
                (idealSectorElement K S P.arithmetic x).val‖ ^ 2 else 0) ≤
            C * Z ^ (5 / 6 + ε) / q ^ 2) := by
  unfold HeckeSkeleton.LowCauchy.CompletedMarkedEnergy
  simp_rw [completedMarkedRow_energy_eq K c]

end HeckeSkeleton.LowEnergy.TargetDictionary
