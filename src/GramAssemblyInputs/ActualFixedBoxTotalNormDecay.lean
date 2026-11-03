import ActualFixedBoxTotalNormSeminormBound
import HeckeGeneral.Analysis.TraceMovingPhaseBounds

/-!
UNCOMPILED / native 0. Original joint Schwartz seminorms at the actual
fixed finite fibres have arbitrary power decay at large total radius.
The finite norm compensation is retained before aggregation. Together
with the proved small-radius estimate this gives a two-ended min envelope.
No Fourier seminorm or external decay estimate is substituted.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualFixedBoxTotalNormDecayDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open ActualChoiceMaskedTotalNormDraft ActualFixedBoxTotalNormSeminormDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

private theorem finite_uniform_original_power_bounds
    {ι : Type*} [Fintype ι]
    (P : ι → ℝ → SchwartzMap V ℂ → {r : ℝ // 0 < r} → ℝ) (B : ℝ)
    (hP : ∀ i, ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ,
      0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          P i ν φ R ≤
            C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        ∀ i, P i ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  choose s C R0 J hC _hR0 hbound using hP
  let sall : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let Call : ℝ := ∑ i : ι, C i
  let Rall : ℝ := 1 + ∑ i : ι, max (R0 i) 0
  let Jall : ℕ := Finset.univ.sup J
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun i _ => hC i)
  have hRall : 1 ≤ Rall :=
    le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => le_max_right (R0 i) 0))
  have hCi (i : ι) : C i ≤ Call :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hRi (i : ι) : R0 i ≤ Rall := by
    calc
      R0 i ≤ max (R0 i) 0 := le_max_left _ _
      _ ≤ ∑ j : ι, max (R0 j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right (R0 j) 0) (Finset.mem_univ i)
      _ ≤ 1 + ∑ j : ι, max (R0 j) 0 := le_add_of_nonneg_left (by norm_num)
  have hJi (i : ι) : J i ≤ Jall := Finset.le_sup (Finset.mem_univ i)
  have hsi (i : ι) (φ : SchwartzMap V ℂ) :
      (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        sall.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    exact Seminorm.le_finset_sup_apply
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩)
  refine ⟨sall, Call, Rall, Jall, hCall, hRall, fun ν φ R hR i => ?_⟩
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hfactor : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    mul_nonneg hCall (apply_nonneg _ _)
  calc
    _ ≤ C i * (s i).sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ (J i) * R.val ^ (-B) := hbound i ν φ R ((hRi i).trans hR)
    _ ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        (1 + |ν|) ^ Jall * R.val ^ (-B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (hCi i) (hsi i φ) (apply_nonneg _ _) hCall)
          (pow_le_pow_right₀ hν (hJi i)) (pow_nonneg (zero_le_one.trans hν) _) hfactor)
        (Real.rpow_nonneg R.property.le _)


variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K S
local instance : Subgroup.FiniteIndex Γ := sUnit_power_range_finiteIndex K S 6 (by decide)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ
local notation "Z" => SFiniteLocalGroup K S

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : (w.S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Arbitrary large-radius decay of the exact fixedBox sum of ORIGINAL
Schwartz seminorms. The threshold includes every actual finite norm factor. -/
theorem exists_fixedBoxTotalNormJointSeminormSum_largeRadius_bound
    (B : ℝ) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
        fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport t ν φ R ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
  let F := S → Fin H
  let I := (F × F) × t
  let z : F → Z := sUnitPartitionFiniteFibreRepresentative K S H
  let P (i : I) (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) : ℝ :=
    SchwartzMap.seminorm ℝ i.2.val.1 i.2.val.2
      (sUnitTotalNormAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (z i.1.1) (z i.1.2) φ R)
  let Lattice := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  obtain ⟨M, hM⟩ := exists_nat_gt
    (max (Module.finrank ℤ Lattice : ℝ) ((Module.finrank ℚ K : ℝ) * B))
  have hMrank : Module.finrank ℤ Lattice < M := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hM)
  have hMorder : (Module.finrank ℚ K : ℝ) * B ≤ M :=
    (le_max_right _ _).trans hM.le
  have hP (i : I) :
      ∃ s : Finset (ℕ × ℕ), ∃ C R0 : ℝ, ∃ J : ℕ, 0 ≤ C ∧ 1 ≤ R0 ∧
        ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r}, R0 ≤ R.val →
          P i ν φ R ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
    obtain ⟨s, C, R0, hC, hR0, hb⟩ :=
      exists_traceMovingCutoffOrbitalSchwartz_seminorm_power_bound
        K S Γ ψ hψ hψsupport
        (sUnitAnnularPartitionJointCutoff K S Γ a (z i.1.1) (z i.1.2))
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (z i.1.1) (z i.1.2) a0 b0 ha0 haSupport).1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (z i.1.1) (z i.1.2) a0 b0 ha0 haSupport).2.1
        (sUnitAnnularPartitionJointCutoff_spec K S Γ a ha
          (z i.1.1) (z i.1.2) a0 b0 ha0 haSupport).2.2
        B M hMrank hMorder i.2.val.1 i.2.val.2
    let f := sUnitTotalNormFibreFactor K S (z i.1.1) (z i.1.2)
    have hf : 0 < f := sUnitTotalNormFibreFactor_pos K S _ _
    refine ⟨s, C * f ^ B, max 1 (R0 * f), i.2.val.2,
      mul_nonneg hC (Real.rpow_nonneg hf.le _), le_max_left _ _, ?_⟩
    intro ν φ R hR
    have hR' : R0 ≤ (sUnitTotalNormRadius K S (z i.1.1) (z i.1.2) R).val := by
      change R0 ≤ R.val / f
      exact (le_div_iff₀ hf).mpr ((le_max_right _ _).trans hR)
    have hpow : (sUnitTotalNormRadius K S (z i.1.1) (z i.1.2) R).val ^ (-B) =
        f ^ B * R.val ^ (-B) := by
      change (R.val / f) ^ (-B) = _
      rw [Real.div_rpow R.property.le hf.le, Real.rpow_neg hf.le, div_inv_eq_mul]
      exact mul_comm _ _
    change SchwartzMap.seminorm ℝ i.2.val.1 i.2.val.2
      (sUnitMellinAnnularPartitionJointSchwartz K S Γ a ha a0 b0 ha0 haSupport
        ψ hψ hψsupport ν (z i.1.1) (z i.1.2) φ
        (sUnitTotalNormRadius K S (z i.1.1) (z i.1.2) R)) ≤ _
    rw [seminorm_sUnitMellinAnnularPartitionJointSchwartz]
    calc
      _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ i.2.val.2 *
          (sUnitTotalNormRadius K S (z i.1.1) (z i.1.2) R).val ^ (-B) :=
        hb ν φ _ hR' i.2.val.2 le_rfl
      _ = _ := by rw [hpow]; ring
  obtain ⟨s, C, R0, J, hC, hR0, hb⟩ := finite_uniform_original_power_bounds K P B hP
  let n : ℝ := Fintype.card F
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨s, n * n * C, R0, J, mul_nonneg (mul_nonneg hn hn) hC, hR0, ?_⟩
  intro ν φ R hR
  have hfinal : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
      (1 + |ν|) ^ J * R.val ^ (-B) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)) (Real.rpow_nonneg R.property.le _)
  unfold fixedBoxTotalNormJointSeminormSum
  calc
    _ ≤ ∑ _e₁ : F, ∑ _e₂ : F,
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-B) := by
      apply Finset.sum_le_sum
      intro e₁ _
      apply Finset.sum_le_sum
      intro e₂ _
      apply Seminorm.finset_sup_apply_le hfinal
      intro i hi
      exact hb ν φ R hR ((e₁, e₂), ⟨i, hi⟩)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [n]
      ring

/-- The actual fixed-fibre sum has simultaneous small- and large-radius
control. No radius threshold or additional decay assumption is an input. -/
theorem exists_fixedBoxTotalNormJointSeminormSum_min_decay_bound
    (σ B : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσB : σ ≤ B)
    (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 ≤ C ∧
      ∀ ν : ℝ, ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport t ν φ R ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J *
          min (R.val ^ (-σ)) (R.val ^ (-B)) := by
  obtain ⟨s₀, C₀, J₀, hC₀, hb₀⟩ :=
    exists_fixedBoxTotalNormJointSeminormSum_allRadius_bound
      K w a ha a0 b0 ha0 haSupport ψ hψ hψsupport σ hσ hσ1 t
  obtain ⟨s₁, C₁, R₀, J₁, hC₁, hR₀, hb₁⟩ :=
    exists_fixedBoxTotalNormJointSeminormSum_largeRadius_bound
      K w a ha a0 b0 ha0 haSupport ψ hψ hψsupport B t
  let s := s₀ ∪ s₁
  let J := max J₀ J₁
  let T := R₀ ^ (B - σ)
  have hT : 0 ≤ T := Real.rpow_nonneg (zero_le_one.trans hR₀) _
  let C := C₀ * (1 + T) + C₁
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hC₀ (by linarith)) hC₁
  have hC₀C : C₀ ≤ C := by dsimp only [C]; nlinarith
  have hC₁C : C₁ ≤ C := by dsimp only [C]; nlinarith
  have hC₀TC : C₀ * T ≤ C := by dsimp only [C]; nlinarith
  have hp₀ (φ : SchwartzMap V ℂ) :
      s₀.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_left s₁ hi)
  have hp₁ (φ : SchwartzMap V ℂ) :
      s₁.sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
        s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    exact Seminorm.le_finset_sup_apply (Finset.mem_union_right s₀ hi)
  refine ⟨s, C, J, hC, ?_⟩
  intro ν φ R
  let F := s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J
  have hF : 0 ≤ F := mul_nonneg (apply_nonneg _ _) (pow_nonneg (by positivity) _)
  have hν : 1 ≤ 1 + |ν| := by linarith [abs_nonneg ν]
  have hsmall : fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport t ν φ R ≤ C₀ * F * R.val ^ (-σ) := by
    calc
      _ ≤ C₀ * s₀.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J₀ * R.val ^ (-σ) := hb₀ ν φ R
      _ ≤ C₀ * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J * R.val ^ (-σ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left (hp₀ φ) hC₀)
            (pow_le_pow_right₀ hν (le_max_left _ _))
            (pow_nonneg (by positivity) _) (mul_nonneg hC₀ (apply_nonneg _ _)))
          (Real.rpow_nonneg R.property.le _)
      _ = _ := by dsimp only [F]; ring
  have hs : fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport t ν φ R ≤ C * F * R.val ^ (-σ) :=
    hsmall.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C hF) (Real.rpow_nonneg R.property.le _))
  have hl : fixedBoxTotalNormJointSeminormSum K w a ha a0 b0 ha0 haSupport
      ψ hψ hψsupport t ν φ R ≤ C * F * R.val ^ (-B) := by
    by_cases hR : R₀ ≤ R.val
    · calc
        _ ≤ C₁ * s₁.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J₁ * R.val ^ (-B) := hb₁ ν φ R hR
        _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (1 + |ν|) ^ J * R.val ^ (-B) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul hC₁C (hp₁ φ) (apply_nonneg _ _) hC)
              (pow_le_pow_right₀ hν (le_max_right _ _))
              (pow_nonneg (by positivity) _) (mul_nonneg hC (apply_nonneg _ _)))
            (Real.rpow_nonneg R.property.le _)
        _ = _ := by dsimp only [F]; ring
    · have hbridge : R.val ^ (-σ) ≤ T * R.val ^ (-B) := by
        calc
          _ = R.val ^ (B - σ) * R.val ^ (-B) := by
            rw [← Real.rpow_add R.property]
            congr 1
            ring
          _ ≤ T * R.val ^ (-B) := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow R.property.le (le_of_not_ge hR) (sub_nonneg.mpr hσB))
            (Real.rpow_nonneg R.property.le _)
      calc
        _ ≤ C₀ * F * R.val ^ (-σ) := hsmall
        _ ≤ C₀ * F * (T * R.val ^ (-B)) :=
          mul_le_mul_of_nonneg_left hbridge (mul_nonneg hC₀ hF)
        _ = (C₀ * T) * F * R.val ^ (-B) := by ring
        _ ≤ C * F * R.val ^ (-B) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀TC hF) (Real.rpow_nonneg R.property.le _)
  change _ ≤ C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * _
  by_cases hmin : R.val ^ (-σ) ≤ R.val ^ (-B)
  · rw [min_eq_left hmin]
    simpa only [F, mul_assoc] using hs
  · rw [min_eq_right (le_of_not_ge hmin)]
    simpa only [F, mul_assoc] using hl

end HeckeGeneral.ThetaSkeleton.Physical.ActualFixedBoxTotalNormDecayDraft
