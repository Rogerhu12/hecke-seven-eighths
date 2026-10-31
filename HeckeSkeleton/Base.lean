import HeckeSkeleton.BaseContext

/-!
The retained expansion and target-data assembly for the common primitive
data reexported from `BaseContext`. The original expansion and support
construction obligations remain here; no admitted proof is replaced by
the dependency split.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]

-- OBLIGATION D-EXPANSION | revised Proposition 6.3, §7.1–7.2 (pp.41–44).
-- Buffered blocks, true slot values and actual detector witness subdivisions.
-- Values are data only; exact identity and all bounds occur downstream.
def highExpansion (c : TargetContext K) : ℝ → ℝ →
    HighExpansion (FrequencyRow K (places K c)) c.geometry.slots := by
  sorry

-- OBLIGATION D-SUPPORT | revised §7.1 (pp.42–43).
theorem rows_in_norm_envelope (c : TargetContext K) :
    ∀ Z T₁ : ℝ, 1 ≤ Z → 1 ≤ T₁ →
    ∀ b : Fin (highExpansion K c Z T₁).blockCount,
    ∀ ℓ : ((highExpansion K c Z T₁).block b).Label,
      (((highExpansion K c Z T₁).block b).amplitudeSet ℓ).rows ⊆
        frequencyRows K (places K c) (2 * Z ^ ((highExpansion K c Z T₁).block b).shell) := by
  sorry

def targetData (c : TargetContext K) : TargetData K c.geometry where
  S := excludedPlaces K c
  probe := probeData K c
  measures := probeMeasures K c
  rayFilter := rayFilter K c
  expansion := highExpansion K c
  rows_in_norm_envelope := rows_in_norm_envelope K c

end HeckeSkeleton
