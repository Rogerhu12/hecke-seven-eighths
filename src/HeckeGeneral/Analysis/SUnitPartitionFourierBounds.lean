import HeckeGeneral.Analysis.SUnitPartitionFiniteFibres
import HeckeGeneral.Analysis.TraceJointSchwartzFourierBounds

/-!
# Uniform Fourier bounds for all actual finite partition fibres

The complete finite-coordinate range of the annular partition cutoff is
finite, including its zero function off the original valuation box. The
two-column family is consequently finite as well. Applying the actual joint
trace Fourier estimate to that finite family gives constants chosen before
both finite coordinates and the original Schwartz test function.

The subgroup is the original Γ throughout, including its torsion. This closes
finite-fibre uniformity only; it does not identify a fixed fibre with a whole
orbit or assemble the eventual Gram or sector Fourier formula.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical ContDiff BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Z" => SFiniteLocalGroup K S

/-- Finiteness concerns the complete actual function family, rather than
representatives from only one orbit or only one finite-coordinate fibre. -/
theorem finite_range_sUnitAnnularPartitionJointCutoff (a : ℝ → ℝ) :
    Set.Finite (Set.range (fun p : Z × Z =>
      sUnitAnnularPartitionJointCutoff K S Γ a p.1 p.2)) := by
  have hfinite := finite_range_sUnitAnnularPartitionCutoff K S Γ a
  apply ((hfinite.prod hfinite).image (fun q : (V → ℝ) × (V → ℝ) =>
    fun p : V × V => ((q.1 p.1 * q.2 p.2 : ℝ) : ℂ))).subset
  rintro F ⟨⟨ζ, ξ⟩, rfl⟩
  exact ⟨(sUnitAnnularPartitionCutoff K S Γ a ζ,
    sUnitAnnularPartitionCutoff K S Γ a ξ), ⟨⟨ζ, rfl⟩, ⟨ξ, rfl⟩⟩, rfl⟩

variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]

/-- The actual Fourier transform of the actual annular partition cutoff
times the joint orbital kernel, with both trace columns and the mixed Haar
Jacobian supplied by `traceJointProductFourierCLM`. -/
def sUnitAnnularPartitionJointFourier
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ζ ξ : Z) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    SchwartzMap (TraceJointEuclideanSpace K) ℂ :=
  traceJointProductFourierCLM K
    (traceCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ)
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.2
      φ R)

/-- Equality of the actual cutoff functions gives equality of their actual
Schwartz Fourier transforms; smoothness witnesses do not alter the function. -/
theorem sUnitAnnularPartitionJointFourier_congr
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (ζ ξ ζ' ξ' : Z)
    (h : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a ζ' ξ')
    (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) :
    sUnitAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ζ ξ φ R =
      sUnitAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ζ' ξ' φ R := by
  unfold sUnitAnnularPartitionJointFourier
  apply congrArg (traceJointProductFourierCLM K)
  ext p
  simp only [traceCutoffOrbitalSchwartz_apply, h]

local notation "Lattice" => traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- Shared Fourier seminorm constants for every actual finite-coordinate
pair. The finite original φ seminorms, C, and the support-dependent threshold
R0 are selected before ζ, ξ, φ, and R. No whole-orbit or Gram identity is an
assumption or a conclusion of this finite-family estimate. -/
theorem exists_sUnitAnnularPartitionJointFourier_seminorm_power_bound
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
    (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)
    (B : ℝ) (M : ℕ) (hM : Module.finrank ℤ Lattice < M)
    (hOrder : (Module.finrank ℚ K : ℝ) * B ≤ M) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        SchwartzMap.seminorm ℝ k n
          (sUnitAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
  let I := Set.range (fun p : Z × Z =>
    sUnitAnnularPartitionJointCutoff K S Γ a p.1 p.2)
  letI : Fintype I := (finite_range_sUnitAnnularPartitionJointCutoff K S Γ a).fintype
  let pick : I → Z × Z := fun i => Classical.choose i.property
  have hpick (i : I) :
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 = i.val :=
    Classical.choose_spec i.property
  have hex (i : I) :
      ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, 0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          SchwartzMap.seminorm ℝ k n
            (sUnitAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
              ψ hψ hψsupport (pick i).1 (pick i).2 φ R) ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) := by
    exact exists_traceCutoffOrbitalFourier_seminorm_power_bound
      K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2
      B M hM hOrder k n
  choose s C R0 hC _hR0 hbound using hex
  let sall : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let Call : ℝ := ∑ i : I, C i
  let Rall : ℝ := 1 + ∑ i : I, max (R0 i) 0
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun i _ => hC i)
  have hRall : 1 ≤ Rall :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => le_max_right (R0 i) 0))
  have hCi (i : I) : C i ≤ Call :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hRi (i : I) : R0 i ≤ Rall := by
    calc
      R0 i ≤ max (R0 i) 0 := le_max_left _ _
      _ ≤ ∑ j : I, max (R0 j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right (R0 j) 0) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j : I, max (R0 j) 0 := le_add_of_nonneg_left (by norm_num)
  have hsi (i : I) (φ : SchwartzMap V ℂ) :
      (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        sall.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩)
  refine ⟨sall, Call, Rall, hCall, hRall, fun ζ ξ φ R hR => ?_⟩
  let i : I := ⟨sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ, ⟨(ζ, ξ), rfl⟩⟩
  have heq : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 := (hpick i).symm
  rw [sUnitAnnularPartitionJointFourier_congr K S Γ a ha a0 b0 ha0 haSupport
    ψ hψ hψsupport ζ ξ (pick i).1 (pick i).2 heq φ R]
  calc
    _ ≤ C i * (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
      hbound i φ R ((hRi i).trans hR)
    _ ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hCi i) (hsi i φ) (apply_nonneg _ _) hCall)
        (Real.rpow_nonneg R.property.le _)

end HeckeGeneral.Analysis
