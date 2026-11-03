import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
UNCOMPILED candidate. The two declarations below are adapted from Naganori
Yamaguchi's Apache-2.0 source (assisted by OpenAI Codex):
.cache/upstream/cft-2eb22d64/Lean4/ClassFieldTheory/GlobalClassFieldTheory/
Reciprocity/FinitePlaceAdicLocalField.lean, lines 35-43 and 72-107.
Exact upstream SHA256:
f189bee54a5740a056b900399f00fd2cb060899946f0b7f9640e87cc917ee2b3.
Only the actual adic valuation relation and its completion comparison are
retained. Both imported CFT modules belong to the sealed 843 source parent.
No Hilbert-pairing-family construction or extra hypothesis is introduced.
-/

noncomputable section
namespace HeckeGeneral.Arithmetic.ActualFiniteCompletionDraft

open NumberField IsDedekindDomain LocalClassFieldTheory

/-- The actual integer-valued valuation relation on the adic completion. -/
@[reducible]
def adicCompletionValuativeRel (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

local instance comparisonSourceValuativeRel :
    ValuativeRel (HeightOneSpectrum.adicAbv K v).Completion :=
  GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v

local instance comparisonTargetValuativeRel : ValuativeRel (v.adicCompletion K) :=
  adicCompletionValuativeRel K v

/-- The actual canonical completion equivalence preserves both valuation orders. -/
theorem completion_semilinearValuationCompatible :
    SemilinearValuationCompatible
      (HeightOneSpectrum.adicAbv K v).Completion
      (v.adicCompletion K)
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv := by
  let C := (HeightOneSpectrum.adicAbv K v).Completion
  let C' := v.adicCompletion K
  let e := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let _ : Algebra C C' := e.toRingHom.toAlgebra
  change (ValuativeRel.valuation C).HasExtension (ValuativeRel.valuation C')
  constructor
  intro x y
  change ValuativeRel.valuation C x ≤ ValuativeRel.valuation C y ↔
    ValuativeRel.valuation C' (e x) ≤ ValuativeRel.valuation C' (e y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  change ‖x‖₊ ≤ ‖y‖₊ ↔
    (Valued.v : Valuation C' (WithZero (Multiplicative ℤ))) (e x) ≤ Valued.v (e y)
  rw [← Valued.toNormedField.norm_le_iff]
  change ‖x‖ ≤ ‖y‖ ↔ ‖relativeFinitePlaceCompletionRingEquiv v x‖ ≤
    ‖relativeFinitePlaceCompletionRingEquiv v y‖
  rw [relativeFinitePlaceCompletionRingEquiv_norm,
    relativeFinitePlaceCompletionRingEquiv_norm]

end HeckeGeneral.Arithmetic.ActualFiniteCompletionDraft
