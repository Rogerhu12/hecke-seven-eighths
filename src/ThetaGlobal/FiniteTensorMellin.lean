import ThetaGlobal.FiniteTensorCoefficients
import ThetaGlobal.FiniteMellinIntegration

/-!
# The finite tensor Mellin factor is its actual S-local Haar integral

Local shell reassembly is performed with absolute-integral convergence.
Finite-product Fubini and the proved class-mask tensor expansion then give
the exact finite S-local Mellin integral, with all valuations integrated.
-/

set_option autoImplicit false
noncomputable section
namespace ThetaGlobal.FiniteTensorMellin

open MeasureTheory
open ThetaGlobal.FiniteShell ThetaGlobal.FiniteClass ThetaGlobal.FiniteTensor
open ThetaGlobal.FiniteMellinIntegration
open scoped Classical BigOperators

variable {P : Type*} [Fintype P]
variable {C : P → Type*} [∀ p, Fintype (C p)]
variable {V : Type*} [Group V]
variable {X U : P → Type*} [∀ p, MeasurableSpace (X p)] [∀ p, MeasurableSpace (U p)]

theorem radius_cpow_on_shell {Branch Y Z : Type*}
    (d : LocalShellData Branch Y Z) (k : ℤ) (z : Z) (s : ℂ) :
    (d.radius (d.shell k z) : ℂ) ^ s = (d.q : ℂ) ^ (-(k : ℂ) * s) := by
  rw [d.shell_radius, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _) (-(k : ℝ)) s]
  simp only [Complex.ofReal_neg, Complex.ofReal_intCast, Complex.ofReal_natCast]

variable (B : Set V) (H : V → V → ℂ) (hH : ∀ x y, ‖H x y‖ ≤ 1)
  (assemble : (∀ p, C p) → V) (pivot : P) (classOf : ∀ p, X p → C p)
  (d : ∀ p, LocalShellData PUnit (X p) (U p))
  (μ : ∀ p, Measure (U p)) [∀ p, IsFiniteMeasure (μ p)]
  (ν : ∀ p, Measure (X p)) [∀ p, SigmaFinite (ν p)]
  (L : ∀ p, X p → ℂ)

/-- A separated local factor of the *full* finite Mellin integrand. -/
def localIntegrand (κ : V) (σ : ∀ p, C p) (p : P) (s : ℂ) (x : X p) : ℂ :=
  localMaskFactor pivot (fun c => powerClassMask B H κ (assemble c)) σ p (classOf p x) *
    (L p x * ((d p).value x * ((d p).radius x : ℂ) ^ s))

/-- Fubini is justified by the absolute local shell-integral bounds.
The measure input is the geometric Haar-shell identity and the only
regularity inputs are local measurability and unit-shell integrability. -/
theorem finite_tensor_mellin_integral
    (hd : ∀ p, LocalWhittakerBounds (d p))
    (hν : ∀ p, ν p = shellMeasure (d p) (μ p))
    (hm : ∀ p k, AEMeasurable ((d p).shell k) (μ p))
    (hL : ∀ p k u, (d p).multiplier PUnit.unit k u = L p ((d p).shell k u))
    (hi : ∀ p, ShellIntegrable (withClassMask B H hH assemble pivot classOf p (d p)) (μ p))
    (κ : V) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re)
    (hf : ∀ σ p k, AEStronglyMeasurable
      (localIntegrand B H assemble pivot classOf d L κ σ p s)
      (Measure.map ((d p).shell k) (μ p))) :
    Integrable (fun x : ∀ p, X p =>
      powerClassMask B H κ (assemble (fun p => classOf p (x p))) *
        ∏ p, L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s))
      (Measure.pi ν) ∧
    (∑ σ : ∀ p, C p, ∏ p, ∑' k : ℤ,
      FiniteShell.coefficient (withClassMask B H hH assemble pivot classOf p (d p))
        (μ p) (κ, σ) k * ((d p).q : ℂ) ^ (-(k : ℂ) * s)) =
      ∫ x : ∀ p, X p,
        powerClassMask B H κ (assemble (fun p => classOf p (x p))) *
          ∏ p, L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s)
        ∂Measure.pi ν := by
  have hlocal (σ : ∀ p, C p) (p : P) :
      Integrable (localIntegrand B H assemble pivot classOf d L κ σ p s) (ν p) ∧
      (∫ x, localIntegrand B H assemble pivot classOf d L κ σ p s x ∂ν p) =
        ∑' k : ℤ, FiniteShell.coefficient
          (withClassMask B H hH assemble pivot classOf p (d p)) (μ p) (κ, σ) k *
            ((d p).q : ℂ) ^ (-(k : ℂ) * s) := by
    apply integrable_and_integral_of_haar_shells
      (withClassMask B H hH assemble pivot classOf p (d p)) (μ p) (ν p) (hν p)
      (withClassMask_bounds B H hH assemble pivot classOf p (d p) (hd p))
      (hi p) (hm p) (κ, σ) s hs _ (hf σ p)
    intro k u
    simp only [localIntegrand, withClassMask, radius_cpow_on_shell, hL, mul_assoc]
  have hlocal' (σ : ∀ p, C p) (p : P) : Integrable
      (fun x => localMaskFactor pivot (fun c => powerClassMask B H κ (assemble c)) σ p
        (classOf p x) * (L p x * ((d p).value x * ((d p).radius x : ℂ) ^ s))) (ν p) :=
    (hlocal σ p).1
  constructor
  · have hint := integrable_finsetSum (Finset.univ : Finset (∀ p, C p))
      (fun σ _ => Integrable.fintype_prod_dep (hlocal' σ))
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    exact tensor_expansion pivot (fun c => powerClassMask B H κ (assemble c))
      (fun p => classOf p (x p))
      (fun p => L p (x p) * ((d p).value (x p) * ((d p).radius (x p) : ℂ) ^ s))
  · calc
      _ = ∑ σ : ∀ p, C p, ∏ p,
          localCoefficient ν pivot (fun c => powerClassMask B H κ (assemble c))
            classOf L (fun p x => (d p).value x * ((d p).radius x : ℂ) ^ s) σ p := by
        apply Finset.sum_congr rfl
        intro σ _
        apply Finset.prod_congr rfl
        intro p _
        exact (hlocal σ p).2.symm
      _ = _ := tensor_shell_integral ν pivot
        (fun c => powerClassMask B H κ (assemble c)) classOf L
        (fun p x => (d p).value x * ((d p).radius x : ℂ) ^ s) hlocal'

end ThetaGlobal.FiniteTensorMellin

#print axioms ThetaGlobal.FiniteTensorMellin.finite_tensor_mellin_integral
