import HeckeGeneral.Analysis.SUnitMellinPhase
import HeckeGeneral.Analysis.TraceMovingFourierBounds

/-!
# Uniform Fourier bounds for the genuine total Mellin phase

The actual fixed-fibre total phase differs from the existing archimedean
phase by a constant of norm one. The literal kernel identity is proved on
regular columns by logarithmic factorization and off them by the actual
cutoff's vanishing. Thus no logarithmic product identity at zero is used.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical ContDiff BigOperators nonZeroDivisors

private theorem seminorm_unimodular_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℂ) (hc : ‖c‖ = 1) (F : SchwartzMap E ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (c • F) = SchwartzMap.seminorm ℝ k n F := by
  change SchwartzMap.seminorm ℂ k n (c • F) = SchwartzMap.seminorm ℂ k n F
  rw [map_smul_eq_mul, hc, one_mul]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S
local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- A genuine Schwartz map representing the total-phase annular orbital
kernel. The following apply theorem identifies its literal values globally. -/
def sUnitMellinAnnularPartitionJointSchwartz
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (V × V) ℂ :=
  sUnitMellinFiniteFactor K S ν ζ ξ •
    traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ)
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.2
      ν φ R

/-- Actual total Mellin phase times actual cutoff times actual joint orbital
kernel, including points outside the regular locus where the cutoff is zero. -/
theorem sUnitMellinAnnularPartitionJointSchwartz_apply
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (p : V × V) :
    sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R p =
      sUnitMellinPhase K S ν ζ ξ p *
        (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ p *
          traceJointOrbitalKernel K S φ ψ R p) := by
  change sUnitMellinFiniteFactor K S ν ζ ξ *
    traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ) _ _ _ ν φ R p = _
  rw [traceMovingCutoffOrbitalSchwartz_apply]
  by_cases hp : p ∈ traceArchRegular K ×ˢ traceArchRegular K
  · rw [sUnitMellinPhase_eq_finiteFactor_mul_traceMovingPhase K S ν ζ ξ p hp.1 hp.2]
    ring
  · have hzero : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ p = 0 := by
      by_contra hn
      exact hp ((sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ
        a0 b0 ha0 haSupport).2.2 (subset_closure hn))
    simp only [hzero, zero_mul, mul_zero]

theorem seminorm_sUnitMellinAnnularPartitionJointSchwartz
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R) =
      SchwartzMap.seminorm ℝ k n
        (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
          (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ)
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.2
          ν φ R) :=
  seminorm_unimodular_smul _ (norm_sUnitMellinFiniteFactor K S ν ζ ξ) _ k n

/-- The actual two-column mixed Fourier operator applied to the total kernel. -/
def sUnitMellinAnnularPartitionJointFourier
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (TraceJointEuclideanSpace K) ℂ :=
  traceJointProductFourierCLM K
    (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport ν ζ ξ φ R)

theorem sUnitMellinAnnularPartitionJointFourier_eq_smul
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R =
      sUnitMellinFiniteFactor K S ν ζ ξ •
        sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ R := by
  unfold sUnitMellinAnnularPartitionJointFourier sUnitMellinAnnularPartitionJointSchwartz
    sUnitMovingAnnularPartitionJointFourier traceMovingCutoffOrbitalFourier
  exact (traceJointProductFourierCLM K).map_smul _ _

theorem seminorm_sUnitMellinAnnularPartitionJointFourier
    (ν : ℝ) (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
      (sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν ζ ξ φ R) =
      SchwartzMap.seminorm ℝ k n
        (sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ R) := by
  rw [sUnitMellinAnnularPartitionJointFourier_eq_smul]
  exact seminorm_unimodular_smul _ (norm_sUnitMellinFiniteFactor K S ν ζ ξ) _ k n

/-- Exactly the existing uniform bound: the finite original-input seminorms,
constant, threshold and polynomial exponent are selected before ν, ζ, ξ, φ, R. -/
theorem exists_sUnitMellinAnnularPartitionJointFourier_seminorm_power_bound
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  obtain ⟨s, C, R0, J, hC, hR0, hb⟩ :=
    exists_sUnitMovingAnnularPartitionJointFourier_seminorm_power_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport B M hM hOrder k n
  refine ⟨s, C, R0, J, hC, hR0, fun ν ζ ξ φ R hR => ?_⟩
  rw [seminorm_sUnitMellinAnnularPartitionJointFourier]
  exact hb ν ζ ξ φ R hR

end HeckeGeneral.Analysis
