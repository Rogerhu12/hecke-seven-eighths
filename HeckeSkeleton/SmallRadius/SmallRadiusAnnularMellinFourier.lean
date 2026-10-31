import HeckeSkeleton.SmallRadius.SmallRadiusMovingFourierSeminorm
import HeckeGeneral.Analysis.SUnitMellinFourierBounds

/-!
UNCOMPILED candidate. The actual annular cutoff family is finite, although
the finite coordinates range over all local units. Aggregate the proved
all-positive-radius moving Fourier bounds over that family, then insert
the actual finite Mellin factor using its norm-one identity. All constants,
original-input seminorms and the height exponent precede the finite
coordinates, Mellin height, original Schwartz input and positive radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusAnnularMellinDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open SmallRadiusMovingFourierSeminormDraft
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

private theorem finite_uniform_allRadius_bounds {ι : Type*} [Fintype ι]
    (P : ι → ℝ → SchwartzMap V ℂ → {r : ℝ // 0 < r} → ℝ) (σ : ℝ)
    (hP : ∀ i, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        P i ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, ∀ i,
        P i ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  choose s C J hC hbound using hP
  let sall : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let Call : ℝ := ∑ i : ι, C i
  let Jall : ℕ := Finset.univ.sup J
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun i _ => hC i)
  have hCi (i : ι) : C i ≤ Call :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hJi (i : ι) : J i ≤ Jall := Finset.le_sup (Finset.mem_univ i)
  have hsi (i : ι) (φ : SchwartzMap V ℂ) :
      (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        sall.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩)
  refine ⟨sall, Call, Jall, hCall, fun ν φ R i => ?_⟩
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hfactor : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    mul_nonneg hCall (apply_nonneg _ _)
  calc
    _ ≤ C i * (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J i * R.val ^ (-σ) := hbound i ν φ R
    _ ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ Jall * R.val ^ (-σ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (hCi i) (hsi i φ) (apply_nonneg _ _) hCall)
          (pow_le_pow_right₀ hν (hJi i)) (pow_nonneg (zero_le_one.trans hν) _) hfactor)
        (Real.rpow_nonneg R.property.le _)

variable [IsTotallyComplex K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : S, MeasurableSpace (v.val.adicCompletion K)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (sLocalNormOneGroup K S)]
  [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "Z" => SFiniteLocalGroup K S

variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Uniformity over the actual finite family, with no lower radius threshold. -/
theorem exists_sUnitMovingAnnularPartitionJointFourier_seminorm_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℝ k n
          (sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  let I := Set.range (fun p : Z × Z => sUnitAnnularPartitionJointCutoff K S Γ a p.1 p.2)
  letI : Fintype I := (finite_range_sUnitAnnularPartitionJointCutoff K S Γ a).fintype
  let pick : I → Z × Z := fun i => Classical.choose i.property
  have hpick (i : I) :
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 = i.val :=
    Classical.choose_spec i.property
  let P (i : I) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ k n
      (sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (pick i).1 (pick i).2 φ R)
  have hP (i : I) :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
          P i ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
    exact exists_traceMovingCutoffOrbitalFourier_seminorm_allRadius_bound
      K S Γ ψ hψ hψsupport
      (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
      (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
        (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2
      σ hσ hσ1 k n
  obtain ⟨s, C, J, hC, hb⟩ := finite_uniform_allRadius_bounds K P σ hP
  refine ⟨s, C, J, hC, fun ν ζ ξ φ R => ?_⟩
  let i : I := ⟨sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ, ⟨(ζ, ξ), rfl⟩⟩
  have heq : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 := (hpick i).symm
  have hFourier :
      sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ R =
        sUnitMovingAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν (pick i).1 (pick i).2 φ R := by
    unfold sUnitMovingAnnularPartitionJointFourier traceMovingCutoffOrbitalFourier
    apply congrArg (traceJointProductFourierCLM K)
    ext p
    simp only [traceMovingCutoffOrbitalSchwartz_apply, heq]
  rw [hFourier]
  exact hb ν φ R i

/-- Insert the genuine finite-place Mellin phase, uniformly in all finite fibres. -/
theorem exists_sUnitMellinAnnularPartitionJointFourier_seminorm_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℝ k n
          (sUnitMellinAnnularPartitionJointFourier K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  obtain ⟨s, C, J, hC, hb⟩ :=
    exists_sUnitMovingAnnularPartitionJointFourier_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 k n
  refine ⟨s, C, J, hC, fun ν ζ ξ φ R => ?_⟩
  rw [seminorm_sUnitMellinAnnularPartitionJointFourier]
  exact hb ν ζ ξ φ R

end HeckeGeneral.Analysis.SmallRadiusAnnularMellinDraft
