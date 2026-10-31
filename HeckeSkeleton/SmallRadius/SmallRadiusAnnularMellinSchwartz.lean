import HeckeSkeleton.SmallRadius.SmallRadiusMovingSeminorm
import HeckeGeneral.Analysis.SUnitTotalNormFourierBounds

/-!
UNCOMPILED / native 0. Pre-Fourier all-positive-radius estimates for the
actual annular Mellin joint Schwartz map. The actual finite cutoff family
is aggregated before the finite Mellin phase is inserted using its proved
norm-one identity. Finite target seminorm sets are allowed directly, as
required by the balanced all-scale Poisson bound. The total-norm version
retains the product of both finite column norms and proves its uniform
control on the original valuation box; outside that box the map is zero.
The original Schwartz input and the continuous compactly supported finite
test are arbitrary. No inverse Fourier estimate or Gram estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.SmallRadiusAnnularMellinSchwartzDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Bridge
open SmallRadiusMovingSeminormDraft
open scoped Classical ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/- This finite aggregation is the all-radius version of the verified
finite-family argument in TraceMovingFourierBounds. It also permits an
arbitrary extra parameter, over which each input bound is already uniform. -/
private theorem finite_uniform_allRadius_bounds {ι ρ : Type*} [Fintype ι]
    (P : ι → ρ → ℝ → SchwartzMap V ℂ → {r : ℝ // 0 < r} → ℝ) (σ : ℝ)
    (hP : ∀ i, ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ w : ρ, ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        P i w ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ w : ρ, ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, ∀ i,
        P i w ν φ R ≤
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
  refine ⟨sall, Call, Jall, hCall, fun w ν φ R i => ?_⟩
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hfactor : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    mul_nonneg hCall (apply_nonneg _ _)
  calc
    _ ≤ C i * (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J i * R.val ^ (-σ) := hbound i w ν φ R
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

/-- Actual pre-Fourier annular Mellin kernel, uniformly over every finite fibre
and every positive radius. In particular no condition R ≥ 1 is introduced. -/
theorem exists_sUnitMellinAnnularPartitionJointSchwartz_seminorm_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        SchwartzMap.seminorm ℝ k n
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  let I := Set.range (fun p : Z × Z => sUnitAnnularPartitionJointCutoff K S Γ a p.1 p.2)
  letI : Fintype I := (finite_range_sUnitAnnularPartitionJointCutoff K S Γ a).fintype
  let pick : I → Z × Z := fun i => Classical.choose i.property
  have hpick (i : I) :
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 = i.val :=
    Classical.choose_spec i.property
  let P (i : I) (_w : Unit) (ν : ℝ) (φ : SchwartzMap V ℂ)
      (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ k n
      (traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
        (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2 ν φ R)
  have hP (i : I) :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
        ∀ w : Unit, ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
          P i w ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
    obtain ⟨s, C, hC, hb⟩ :=
      exists_traceMovingCutoffOrbitalSchwartz_seminorm_allRadius_bound
        K S Γ ψ hψ hψsupport
        (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2
        σ hσ hσ1 k n
    exact ⟨s, C, n, hC, fun _ ν φ R => hb ν φ R n le_rfl⟩
  obtain ⟨s, C, J, hC, hb⟩ := finite_uniform_allRadius_bounds K P σ hP
  refine ⟨s, C, J, hC, fun ν ζ ξ φ R => ?_⟩
  let i : I := ⟨sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ, ⟨(ζ, ξ), rfl⟩⟩
  have heq : sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ =
      sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2 := (hpick i).symm
  rw [seminorm_sUnitMellinAnnularPartitionJointSchwartz]
  have hSchwartz :
      traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
          (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ)
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha ζ ξ a0 b0 ha0 haSupport).2.2
          ν φ R =
        traceMovingCutoffOrbitalSchwartz K S Γ ψ hψ hψsupport
          (sUnitAnnularPartitionJointCutoff K S Γ a (pick i).1 (pick i).2)
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
            (pick i).1 (pick i).2 a0 b0 ha0 haSupport).1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
            (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.1
          (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
            (pick i).1 (pick i).2 a0 b0 ha0 haSupport).2.2 ν φ R := by
    ext p
    simp only [traceMovingCutoffOrbitalSchwartz_apply, heq]
  rw [hSchwartz]
  exact hb () ν φ R i

/-- Directly controls the finite input seminorm supremum exported by the
actual balanced all-scale Poisson theorem, before Fourier transformation. -/
theorem exists_sUnitMellinAnnularPartitionJointSchwartz_finite_seminorm_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  let P (i : t) (w : Z × Z) (ν : ℝ) (φ : SchwartzMap V ℂ)
      (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ i.val.1 i.val.2
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν w.1 w.2 φ R)
  have hP (i : t) :
      ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
        ∀ w : Z × Z, ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
          P i w ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
    obtain ⟨s, C, J, hC, hb⟩ :=
      exists_sUnitMellinAnnularPartitionJointSchwartz_seminorm_allRadius_bound
        K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 i.val.1 i.val.2
    exact ⟨s, C, J, hC, fun w ν φ R => hb ν w.1 w.2 φ R⟩
  obtain ⟨s, C, J, hC, hb⟩ := finite_uniform_allRadius_bounds K P σ hP
  refine ⟨s, C, J, hC, fun ν ζ ξ φ R => ?_⟩
  have hfinal : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  apply Seminorm.finset_sup_apply_le hfinal
  intro i hi
  exact hb (ζ, ξ) ν φ R ⟨i, hi⟩

private theorem exists_finiteNormFactor_power_bound (σ : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ζ ξ : Z,
      ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) →
      sUnitTotalNormFibreFactor K S ζ ξ ^ σ ≤ T := by
  let Q : Set (Z × Z) :=
    finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) ×ˢ
      finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  have hQ : IsCompact Q :=
    (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)).prod
      (isCompact_finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
  let F : Z × Z → ℝ := fun p => sUnitTotalNormFibreFactor K S p.1 p.2
  have hF : Continuous F :=
    ((continuous_sFiniteProductNorm K S).comp continuous_fst).mul
      ((continuous_sFiniteProductNorm K S).comp continuous_snd)
  have hFσ : ContinuousOn (fun p => F p ^ σ) Q :=
    hF.continuousOn.rpow_const (fun p _ => Or.inl
      (sUnitTotalNormFibreFactor_pos K S p.1 p.2).ne')
  obtain ⟨T, hT⟩ := hQ.bddAbove_image hFσ
  refine ⟨max 1 T, le_max_left _ _, fun ζ ξ hζ hξ => ?_⟩
  have hmem : (ζ, ξ) ∈ Q := ⟨hζ, hξ⟩
  have h1 : F (ζ, ξ) ^ σ ≤ T := hT ⟨(ζ, ξ), hmem, rfl⟩
  exact h1.trans (le_max_right _ _)

/-- Both finite column norms are retained. The compact valuation box supplies
their actual uniform power bound, and every off-box fibre is genuinely zero. -/
theorem exists_sUnitTotalNormAnnularPartitionJointSchwartz_finite_seminorm_allRadius_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ ζ ξ : Z, ∀ φ : SchwartzMap V ℂ,
      ∀ R : {r : ℝ // 0 < r},
        t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
          (sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
            ψ hψ hψsupport ν ζ ξ φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-σ) := by
  obtain ⟨s, C, J, hC, hb⟩ :=
    exists_sUnitMellinAnnularPartitionJointSchwartz_finite_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 t
  obtain ⟨T, hT, hbox⟩ := exists_finiteNormFactor_power_bound K S Γ σ
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  refine ⟨s, C * T, J, mul_nonneg hC hT0, fun ν ζ ξ φ R => ?_⟩
  have hfinal : 0 ≤ (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-σ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC hT0) (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  by_cases hζ : ζ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  · by_cases hξ : ξ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
    · have hFT := hbox ζ ξ hζ hξ
      have hFpos := sUnitTotalNormFibreFactor_pos K S ζ ξ
      have hpow : (sUnitTotalNormRadius K S ζ ξ R).val ^ (-σ) =
          sUnitTotalNormFibreFactor K S ζ ξ ^ σ * R.val ^ (-σ) := by
        change (R.val / sUnitTotalNormFibreFactor K S ζ ξ) ^ (-σ) = _
        rw [Real.div_rpow R.property.le hFpos.le, Real.rpow_neg hFpos.le,
          div_inv_eq_mul]
        exact mul_comm _ _
      let P : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ J * R.val ^ (-σ)
      have hP : 0 ≤ P :=
        mul_nonneg (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
          (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
      change t.sup (schwartzSeminormFamily ℝ (V × V) ℂ)
        (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)) ≤ _
      calc
        _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * (sUnitTotalNormRadius K S ζ ξ R).val ^ (-σ) :=
          hb ν ζ ξ φ (sUnitTotalNormRadius K S ζ ξ R)
        _ = P * sUnitTotalNormFibreFactor K S ζ ξ ^ σ := by rw [hpow]; dsimp [P]; ring
        _ ≤ P * T := mul_le_mul_of_nonneg_left hFT hP
        _ = (C * T) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * R.val ^ (-σ) := by dsimp [P]; ring
    · rw [sUnitTotalNormAnnularPartitionJointSchwartz_eq_zero_of_not_mem_box K S Γ
        a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inr hξ), map_zero]
      exact hfinal
  · rw [sUnitTotalNormAnnularPartitionJointSchwartz_eq_zero_of_not_mem_box K S Γ
      a ha a0 b0 ha0 haSupport ψ hψ hψsupport ν ζ ξ φ R (Or.inl hζ), map_zero]
    exact hfinal

end HeckeGeneral.Analysis.SmallRadiusAnnularMellinSchwartzDraft
