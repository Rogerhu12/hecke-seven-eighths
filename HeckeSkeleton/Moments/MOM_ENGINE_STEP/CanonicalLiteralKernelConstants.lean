import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActiveProfileKernelMass

/-!
# Fourier mass constants fixed before the literal source

These are the choices in the proved nested Fourier mass theorem. They
depend only on the field, original characters, slot cap and finite
profile order. In particular no scale, covered label, normalization,
actual source, Fourier parameter or activity set enters their choice.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralKernelConstants

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)
variable (cap order : ℕ)

def firstOrders : Finset (ℕ × ℕ) :=
  (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap order order order order).choose

def secondOrders : Finset (ℕ × ℕ) :=
  (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap order order order order).choose_spec.choose

def constant : ℝ :=
  (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap order order order order).choose_spec.choose_spec.choose

theorem constant_pos : 0 < constant K A σ ω ψ cap order :=
  (actual_finite_normalized_kernel_mass_active
    (F := K) (A := A) (σ := σ) (ω := ω) (ψ := ψ) (U := ℝ) (E := ℝ)
    cap order order order order).choose_spec.choose_spec.choose_spec.1

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralKernelConstants

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralKernelConstants.constant_pos
