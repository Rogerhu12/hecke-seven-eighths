import HeckeSkeleton.LowEnergy.RawIdealHybrid
import HeckeSkeleton.LowEnergy.HybridScaling
import HeckeSkeleton.LowEnergy.ActualSieveDictionary

/-!
# The two task sieves imply the actual sextic-symbol hybrid bound

The long arithmetic and analytic argument is kernel-checked in the pure
`RawIdealHybrid` closure.  This short dictionary instantiates the kernel
laws with the actual ideal symbol and the actual allowed generators, and
uses the proved finite-set transport of precisely the two task sieves.
-/

noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualRawHybrid

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open scoped NumberField Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- The actual raw row and the independently verified row are definitionally equal. -/
theorem rawRow_eq_project
    (ps ns bs : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K)) :
    IdealCanonicalColumns.hybridRow (cubicKernel K S D) (quadraticKernel K S D)
      ps ns bs a beta k =
      HeckePort.Moments.hybridRow (cubicKernel K S D) (quadraticKernel K S D)
        ps ns bs a beta k := rfl

/-- The actual kernel laws satisfy the pure theorem's local interface. -/
theorem actual_cubic_axioms (hD : AllowedGeneratorInput K S D) :
    IdealCanonicalColumns.CubicKernelAxioms (IsExterior K S) (cubicKernel K S D) := by
  have h := cubicKernel_axioms K S D hD
  exact ⟨h.mul_left, h.mul_right, h.norm_le_one, h.eq_zero_of_not_coprime⟩

def ActualHybridBound : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
    1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
    ∀ rows nset bset ps : Finset (Ideal (𝓞 K)),
    (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
    (∀ n ∈ nset, IsExterior K S n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
    (∀ b ∈ bset, IsExterior K S b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
    (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
    ∀ a : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
    (∀ P ∈ ps, ‖a P‖ ≤ 1) →
    (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
    (∑ k ∈ rows, ‖HeckePort.Moments.hybridRow
      (cubicKernel K S D) (quadraticKernel K S D) ps nset bset a beta k‖ ^ 2) ≤
      C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
        (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))

/-- Only the two permitted sieve bounds remain as analytic assumptions. -/
theorem actual_hybrid_energy_from_two_sieves
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D)
    (hcubic : ExteriorCubicBound K S D) : ActualHybridBound K S D := by
  intro eps heps
  have hextdvd : ∀ I J : Ideal (𝓞 K), IsExterior K S I → J ∣ I → IsExterior K S J := by
    intro I J hI hJI
    exact ⟨ne_zero_of_dvd_ne_zero hI.1 hJI, fun p hp => hI.2 p (dvd_trans hp hJI)⟩
  have h := RawIdealHybrid.raw_ideal_hybrid_energy
    (IsExterior K S) (fun I hI => hI.1)
    (fun I J hI hJ => (isExterior_mul_iff K S).mpr ⟨hI, hJ⟩)
    hextdvd (cubicKernel K S D) (quadraticKernel K S D)
    (actual_cubic_axioms K S D hD)
    (fun k c m h t hk hc ht => original_quadratic_square_mask K S D hD k c m h t hk hc ht)
    (ordinaryQuadratic_of_exterior K S D hD hquadratic)
    (ordinaryCubic_of_exterior K S D hcubic) eps heps
  simpa only [rawRow_eq_project K S D] using h

/-- Exact actual-row interface for a frozen full-cube coefficient. -/
def ActualFrozenHybridBound : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
    1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
    ∀ rows ns bs ps : Finset (Ideal (𝓞 K)),
    (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
    (∀ n ∈ ns, IsExterior K S n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
    (∀ b ∈ bs, IsExterior K S b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
    (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
    ∀ a rho : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
    ∀ frozen nLower bLower : ℝ, 0 ≤ frozen → 0 < nLower → 0 < bLower →
    (∀ n ∈ ns, nLower ≤ (Ideal.absNorm n : ℝ)) →
    (∀ b ∈ bs, bLower ≤ (Ideal.absNorm b : ℝ)) →
    (∀ P ∈ ps, ‖a P‖ ≤ 1) →
    (∀ n ∈ ns, ∀ b ∈ bs, ‖beta n b‖ ≤
      frozen / (Real.sqrt (Ideal.absNorm n : ℝ) * (Ideal.absNorm b : ℝ))) →
    (∀ k ∈ rows, ‖rho k‖ ≤ 1) →
    (∑ k ∈ rows, ‖rho k * HeckePort.Moments.hybridRow
      (cubicKernel K S D) (quadraticKernel K S D) ps ns bs a beta k‖ ^ 2) ≤
      (frozen ^ 2 / (nLower * bLower ^ 2)) * C * (K0 * N0 * B0 * L0) ^ eps *
        (K0 + N0 * B0) * B0 * (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ))

theorem actual_frozen_hybrid_energy_from_two_sieves
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D)
    (hcubic : ExteriorCubicBound K S D) : ActualFrozenHybridBound K S D := by
  intro eps heps
  have hextdvd : ∀ I J : Ideal (𝓞 K), IsExterior K S I → J ∣ I → IsExterior K S J := by
    intro I J hI hJI
    exact ⟨ne_zero_of_dvd_ne_zero hI.1 hJI, fun p hp => hI.2 p (dvd_trans hp hJI)⟩
  have h := HybridScaling.raw_hybrid_energy_frozen_cube
    (IsExterior K S) (fun I hI => hI.1)
    (fun I J hI hJ => (isExterior_mul_iff K S).mpr ⟨hI, hJ⟩)
    hextdvd (cubicKernel K S D) (quadraticKernel K S D)
    (actual_cubic_axioms K S D hD)
    (fun k c m h t hk hc ht => original_quadratic_square_mask K S D hD k c m h t hk hc ht)
    (ordinaryQuadratic_of_exterior K S D hD hquadratic)
    (ordinaryCubic_of_exterior K S D hcubic) eps heps
  simpa only [rawRow_eq_project K S D] using h

#print axioms actual_hybrid_energy_from_two_sieves
#print axioms actual_frozen_hybrid_energy_from_two_sieves

end HeckeSkeleton.LowEnergy.ActualRawHybrid
end
