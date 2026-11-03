import HeckeGeneral.Analysis.SUnitFiniteSupportDenominators
import HeckeGeneral.Analysis.SUnitOrbitalIntegrability
import HeckeGeneral.Analysis.CompactSchwartzLatticeBound
import HeckeGeneral.Arithmetic.ClearedUnitLattice

/-!
# Actual tensor Schwartz slices and their global S-unit action index

The infinite test function lives in the same trace Euclidean space as the
integer lattice. The finite test function is evaluated in the additive
product of the actual completions. Norm-one slices use the actual positive
section and the actual norm-one group, with no zero radial argument.

The action index is identified with the given subgroup of global S-units;
it is not replaced by one representative for each ideal. This construction
and its continuity precede the uniform orbital bound and integrability.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- An actual tensor test function, using the trace model at infinity. -/
def sLocalTensorTestFunction (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (x : G) : ℂ :=
  φ ((traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)) *
    ψ (fun v => (x.2 v).val)

theorem continuous_sLocalTensorTestFunction (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (hψ : Continuous ψ) :
    Continuous (sLocalTensorTestFunction K S φ ψ) := by
  have hinf : Continuous (fun x : G =>
      (traceToMixed K).symm (x.1 : mixedEmbedding.mixedSpace K)) :=
    (traceToMixed K).symm.continuous.comp (Units.continuous_val.comp continuous_fst)
  have hfin : Continuous (fun x : G => fun v : S => (x.2 v).val) := by
    apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
  exact (φ.continuous.comp hinf).mul (hψ.comp hfin)

def sLocalSchwartzSlice (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (r : {r : ℝ // 0 < r}) (x : T) : ℂ :=
  sLocalTensorTestFunction K S φ ψ (sLocalNormSection K S r * (x : G))

theorem continuous_sLocalSchwartzSlice (φ : SchwartzMap V ℂ)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ) (hψ : Continuous ψ)
    (r : {r : ℝ // 0 < r}) : Continuous (sLocalSchwartzSlice K S φ ψ r) :=
  (continuous_sLocalTensorTestFunction K S φ ψ hψ).comp
    (continuous_const.mul continuous_subtype_val)

variable (Γ : Subgroup (S.unit K))

/-- The counting action in the Haar theorem is exactly the given global subgroup. -/
def sLocalGammaActionEquiv : Γ ≃ (sLocalNormOneGamma K S Γ).op :=
  (Γ.equivMapOfInjective (sLocalNormOneDiagonal K S)
    (sLocalNormOneDiagonal_injective K S)).toEquiv.trans
      (sLocalNormOneGamma K S Γ).equivOp

@[simp] theorem sLocalGammaActionEquiv_smul (u : Γ) (x : T) :
    sLocalGammaActionEquiv K S Γ u • x =
      sLocalNormOneDiagonal K S (u : S.unit K) * x := by
  apply Subtype.ext
  change (x : G) * sLocalDiagonal K S (u : S.unit K) =
    sLocalDiagonal K S (u : S.unit K) * (x : G)
  exact mul_comm _ _

/-- This exact reindexing retains every unit sector, even before convergence is proved. -/
theorem tsum_sLocalGamma_action (f : T → ℂ) (x : T) :
    (∑' g : (sLocalNormOneGamma K S Γ).op, f (g • x)) =
      ∑' u : Γ, f (sLocalNormOneDiagonal K S (u : S.unit K) * x) := by
  simpa only [sLocalGammaActionEquiv_smul] using
    ((sLocalGammaActionEquiv K S Γ).tsum_eq (fun g => f (g • x))).symm

end HeckeGeneral.Analysis
