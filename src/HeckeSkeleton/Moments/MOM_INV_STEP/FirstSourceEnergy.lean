import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceReindexing
import HeckeSkeleton.Moments.MOM_INV_STEP.FullMobiusOrbital

/-!
# Positive first energies on the original squarefree source

The left side still sums over the two original column ranges and
uses their computed residual ideals.  The exact reconstruction
bijection supplies the independent residual ranges.  Full Moebius
inversion and the actual common Fourier profile then give the two
positive energies on the right, without a separated-source or an
energy hypothesis.  The normalized variables are literal ideal norms.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceEnergy

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge MeasureTheory
open IdealMobiusMask FirstSourceDecomposition FirstSourceReindexing CommonKernel
open HeckeSkeleton.Moments.MOMInvStep.FullMobius
open scoped Classical BigOperators FourierTransform ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "NI" => (Ideal (𝓞 K))⁰

def normScale (X : {x : ℝ // 0 < x}) (I : NI) : {r : ℝ // 0 < r} :=
  ⟨(I.val.absNorm : ℝ) / X.val, div_pos (by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I) X.property⟩

def originalResidual (B : Finset (HeightOneSpectrum (𝓞 K))) (n m : NI) : NI :=
  nonzeroProduct (Supports.residual B (primeSupport n) (primeSupport m))

theorem originalResidual_cube_val (n m b₁ b₂ : NI) :
    (originalResidual K (primeSupport (b₁ * b₂)) n m).val = u n m b₁ b₂ := rfl

/-- Two genuine positive columns follow from the original fixed
extraction slice. The full mutual-divisor pool is retained. -/
theorem actual_first_orbital_source_energy
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (χ : LogPlane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχsupport : HasCompactSupport χ)
    (N₁ N₂ : Finset NI)
    (hN₁ : ∀ n ∈ N₁, Squarefree n.val) (hN₂ : ∀ n ∈ N₂, Squarefree n.val)
    (B A₁ A₂ C : Finset (HeightOneSpectrum (𝓞 K)))
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (φ : SchwartzMap V ℂ) (R X Y : {r : ℝ // 0 < r}) (a b : NI → ℂ)
    (hcut : ∀ U ∈ columnDomain N₁ B A₁ C, ∀ W ∈ columnDomain N₂ B A₂ C,
      χ (logPoint (Real.log (normScale K X (nonzeroProduct U)).val)
        (Real.log (normScale K Y (nonzeroProduct W)).val)) = 1) :
    ‖∑ n ∈ N₁, ∑ m ∈ N₂,
      if Supports.Slice B A₁ A₂ C (primeSupport n) (primeSupport m) then
        a (originalResidual K B n m) * b (originalResidual K B m n) *
          sUnitOrbitalProfile K S
            (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
            ⟨R.val / ((normScale K X (originalResidual K B n m)).val *
              (normScale K Y (originalResidual K B m n)).val),
              div_pos R.property (mul_pos
                (normScale K X (originalResidual K B n m)).property
                (normScale K Y (originalResidual K B m n)).property)⟩ else 0‖ ≤
      Real.sqrt (∑ D ∈ divisorPool (columnDomain N₁ B A₁ C) primeProduct,
        ‖(moebius D : ℂ)‖ *
          ∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ *
            ‖∑ U ∈ columnDomain N₁ B A₁ C with D ∣ primeProduct U,
              a (nonzeroProduct U) * columnPhase ξ.fst
                (Real.log (normScale K X (nonzeroProduct U)).val)‖ ^ 2) *
      Real.sqrt (∑ D ∈ divisorPool (columnDomain N₁ B A₁ C) primeProduct,
        ‖(moebius D : ℂ)‖ *
          ∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ *
            ‖∑ W ∈ columnDomain N₂ B A₂ C with D ∣ primeProduct W,
              b (nonzeroProduct W) * columnPhase ξ.snd
                (Real.log (normScale K Y (nonzeroProduct W)).val)‖ ^ 2) := by
  have hreindex := actual_residual_slice_sum N₁ N₂ hN₁ hN₂ B A₁ A₂ C hA₁ hA₂ hCB
    (fun _ _ U W => a U * b W *
      sUnitOrbitalProfile K S
        (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
        ⟨R.val / ((normScale K X U).val * (normScale K Y W).val),
          div_pos R.property (mul_pos (normScale K X U).property
            (normScale K Y W).property)⟩)
  change ‖_‖ ≤ _
  rw [show (∑ n ∈ N₁, ∑ m ∈ N₂,
      if Supports.Slice B A₁ A₂ C (primeSupport n) (primeSupport m) then
        a (originalResidual K B n m) * b (originalResidual K B m n) *
          sUnitOrbitalProfile K S
            (sLocalTensorTestFunction K S (traceSchwartzFourier K φ) ψ)
            ⟨R.val / ((normScale K X (originalResidual K B n m)).val *
              (normScale K Y (originalResidual K B m n)).val),
              div_pos R.property (mul_pos
                (normScale K X (originalResidual K B n m)).property
                (normScale K Y (originalResidual K B m n)).property)⟩ else 0) = _ from hreindex]
  exact genuine_orbital_source_energy K S Γ ψ hψ hψsupport χ hχ hχsupport
    (columnDomain N₁ B A₁ C) (columnDomain N₂ B A₂ C) primeProduct primeProduct
    (fun U _ => primeProduct_ne_bot U) φ R
    (fun U => normScale K X (nonzeroProduct U))
    (fun W => normScale K Y (nonzeroProduct W))
    (fun U => a (nonzeroProduct U)) (fun W => b (nonzeroProduct W)) hcut

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceEnergy

end
