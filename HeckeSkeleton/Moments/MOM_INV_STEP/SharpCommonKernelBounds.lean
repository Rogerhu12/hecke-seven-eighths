import HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernelBounds
import HeckeSkeleton.Moments.MOM_INV_STEP.SUnitSmallRadius

/-!
# A common Fourier envelope with arbitrarily small outer-radius loss

The actual S-unit small-power bound replaces the coarse additive-lattice
degree-root loss. The common compact cutoff, every Euler derivative, and
the actual Fourier transform are retained. Constants and finite families
of original-test seminorms precede every original test and outer radius.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.Bridge MeasureTheory SUnitSmallRadius
open scoped Classical ContDiff BigOperators nonZeroDivisors FourierTransform NNReal

variable (K : Type) [Field K] [NumberField K]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- A finite family of target seminorms and all Euler orders up to J
are controlled by one finite family of original-test seminorms. -/
theorem traceFourierEulerIter_finite_seminorm_bound (t : Finset (ℕ × ℕ)) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ φ : SchwartzMap V ℂ, ∀ j : ℕ, j ≤ J →
        t.sup (schwartzSeminormFamily ℝ V ℂ) (traceFourierEulerIterCLM K j φ) ≤
          (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
  let p : ℕ → Seminorm ℝ (SchwartzMap V ℂ) := fun j =>
    (t.sup (schwartzSeminormFamily ℝ V ℂ)).comp (traceFourierEulerIterCLM K j).toLinearMap
  let q : Seminorm ℝ (SchwartzMap V ℂ) := (Finset.range (J + 1)).sup p
  have hp := schwartz_withSeminorms ℝ V ℂ
  have ht : Continuous (fun φ : SchwartzMap V ℂ =>
      t.sup (schwartzSeminormFamily ℝ V ℂ) φ) :=
    Seminorm.continuous_finsetSup (fun m _ => hp.continuous_seminorm m)
  have hq : Continuous q := Seminorm.continuous_finsetSup
    (fun j _ => ht.comp (traceFourierEulerIterCLM K j).continuous)
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous hp q hq
  refine ⟨s, C, hC, fun φ j hj => ?_⟩
  have hle : p j ≤ q := Finset.le_sup (f := p) (Finset.mem_range.mpr (by omega))
  exact (Seminorm.le_def.mp hle φ).trans (Seminorm.le_def.mp hb φ)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
variable (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

private def smallPowerRawProfile (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) : LogPlane → ℂ :=
  fun p => sUnitJointRadialProfile K S φ ψ R 0 (logCoordinates p)

include Γ hψ hψsupport in
private theorem smallPowerRawProfile_contDiff (φ : SchwartzMap V ℂ)
    (R : {r : ℝ // 0 < r}) : ContDiff ℝ ∞ (smallPowerRawProfile K S ψ φ R) :=
  (contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0).comp
    logCoordinates.contDiff

include Γ hψ hψsupport in
private theorem exists_smallPowerRawProfile_compact_bound
    (A : Set LogPlane) (hA : IsCompact A) (ε : ℝ) (hε : 0 < ε) (J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ p ∈ A, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (smallPowerRawProfile K S ψ φ R) p‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-ε) := by
  let q : LogPlane → ℝ := fun p => Real.exp p.fst * Real.exp p.snd
  have hq : Continuous q :=
    (Real.continuous_exp.comp logCoordinates.continuous.fst).mul
      (Real.continuous_exp.comp logCoordinates.continuous.snd)
  have hqpos (p : LogPlane) : 0 < q p := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hqε : ContinuousOn (fun p => q p ^ ε) A :=
    hq.continuousOn.rpow_const (fun p _ => Or.inl (hqpos p).ne')
  obtain ⟨Z, hZ⟩ := hA.bddAbove_image hqε
  let T : ℝ := max Z 0
  have hT : 0 ≤ T := le_max_right _ _
  have hqT (p : LogPlane) (hp : p ∈ A) : q p ^ ε ≤ T :=
    (hZ (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)
  let E := logCoordinates.toContinuousLinearMap
  let D0 : ℝ := max 1 ‖E‖
  let D1 : ℝ := max 1 ‖sUnitJointLogRadiusCLM‖
  have hD0 : 1 ≤ D0 := le_max_left _ _
  have hD1 : 1 ≤ D1 := le_max_left _ _
  obtain ⟨t, D, hD, hradial⟩ := exists_sLocalSchwartzProfile_smallPower_global_bound
    K S Γ ψ hψ hψsupport ε hε
  obtain ⟨s, C, _hC, hfourier⟩ := traceFourierEulerIter_finite_seminorm_bound K t J
  refine ⟨s, D * (C : ℝ) * T * D1 ^ J * D0 ^ J,
    by positivity, fun φ R p hp n hn => ?_⟩
  have hρeq : Real.exp (Real.log R.val - p.fst - p.snd) = R.val / q p :=
    sUnitJoint_exp_radius R p.fst p.snd
  have hradialScale : (Real.exp (Real.log R.val - p.fst - p.snd)) ^ (-ε) ≤
      R.val ^ (-ε) * T := by
    rw [hρeq, Real.div_rpow R.property.le (hqpos p).le,
      Real.rpow_neg (hqpos p).le, div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_left (hqT p hp) (Real.rpow_nonneg R.property.le _)
  have heuler : ‖sUnitJointRadialProfile K S φ ψ R n (logCoordinates p)‖ ≤
      (D * (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-ε)) * T := by
    have hraw := hradial (traceFourierEulerIterCLM K n φ)
      (sUnitExpRadius (Real.log R.val - p.fst - p.snd))
    change ‖sUnitJointRadialProfile K S φ ψ R n (logCoordinates p)‖ ≤
      D * t.sup (schwartzSeminormFamily ℝ V ℂ) (traceFourierEulerIterCLM K n φ) *
        (Real.exp (Real.log R.val - p.fst - p.snd)) ^ (-ε) at hraw
    calc
      _ ≤ _ := hraw
      _ ≤ D * ((C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) *
          (R.val ^ (-ε) * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hfourier φ n hn) hD)
          hradialScale (by positivity) (by positivity)
      _ = _ := by ring
  have hbase : 0 ≤ D * (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-ε) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD C.coe_nonneg) (apply_nonneg _ _))
      (Real.rpow_nonneg R.property.le _)
  have hscale1 : ‖sUnitJointLogRadiusCLM‖ ^ n ≤ D1 ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hD1 hn)
  have hout : ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0)
      (logCoordinates p)‖ ≤
      ((D * (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-ε)) * T) *
        D1 ^ J :=
    (norm_iteratedFDeriv_sUnitJointRadialProfile_le K S Γ φ ψ hψ hψsupport R n
      (logCoordinates p)).trans
      (mul_le_mul heuler hscale1 (pow_nonneg (norm_nonneg _) _) (mul_nonneg hbase hT))
  have hscale : ‖E‖ ^ n ≤ D0 ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hD0 hn)
  have hG := contDiff_sUnitJointRadialProfile K S Γ φ ψ hψ hψsupport R 0
  change ‖iteratedFDeriv ℝ n ((sUnitJointRadialProfile K S φ ψ R 0) ∘ E) p‖ ≤ _
  rw [E.iteratedFDeriv_comp_right hG p (by simp)]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) (E p))
    (fun _ : Fin n => E)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (sUnitJointRadialProfile K S φ ψ R 0) (E p)‖ * ‖E‖ ^ n := hcomp
    _ ≤ (((D * (C : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * R.val ^ (-ε)) * T) *
        D1 ^ J) * D0 ^ J :=
      mul_le_mul hout hscale (pow_nonneg (norm_nonneg _) _)
        (mul_nonneg (mul_nonneg hbase hT) (pow_nonneg (zero_le_one.trans hD1) _))
    _ = _ := by ring

variable (χ : LogPlane → ℂ) (hχ : ContDiff ℝ ∞ χ)
  (hχsupport : HasCompactSupport χ)

/-- One uniform seminorm bound for the genuine cutoff orbital kernel.
The arbitrary positive exponent is valid at every positive outer radius. -/
theorem exists_orbitalKernel_seminorm_smallPower_bound
    (ε : ℝ) (hε : 0 < ε) (k J : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ n : ℕ, n ≤ J →
        SchwartzMap.seminorm ℝ k n
          (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) := by
  obtain ⟨s, C, hC, hb⟩ := exists_smallPowerRawProfile_compact_bound
    K S Γ ψ hψ hψsupport (tsupport χ) hχsupport ε hε J
  have hbi (i : ℕ) : ∃ b : ℝ, ∀ p, ‖iteratedFDeriv ℝ i χ p‖ ≤ b :=
    (hχsupport.iteratedFDeriv i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by simp))
  choose b hbound using hbi
  let L : ℝ := ∑ i ∈ Finset.range (J + 1), max (b i) 0
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hcut (i : ℕ) (hi : i ≤ J) (p : LogPlane) : ‖iteratedFDeriv ℝ i χ p‖ ≤ L :=
    (hbound i p).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right _ _)
        (Finset.mem_range.mpr (by omega))))
  obtain ⟨H, hH⟩ := hχsupport.bddAbove_image (continuous_norm.continuousOn)
  let W : ℝ := max H 0
  have hW : 0 ≤ W := le_max_right _ _
  have hweight (p : LogPlane) (hp : p ∈ tsupport χ) : ‖p‖ ^ k ≤ W ^ k :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((hH (Set.mem_image_of_mem _ hp)).trans (le_max_left _ _)) k
  have hfactor : 0 ≤ W ^ k * (2 : ℝ) ^ J * L * C := by positivity
  refine ⟨s, W ^ k * (2 : ℝ) ^ J * L * C, hfactor,
    fun φ R n hn => ?_⟩
  let Q : ℝ := C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε))
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg hC (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le (-ε))
  have hnorm (p : LogPlane) (hp : p ∈ tsupport χ) :
      ‖iteratedFDeriv ℝ n (fun p => χ p * smallPowerRawProfile K S ψ φ R p) p‖ ≤
        (2 : ℝ) ^ J * L * Q := by
    have hleib := norm_iteratedFDeriv_mul_le hχ
      (smallPowerRawProfile_contDiff K S Γ ψ hψ hψsupport φ R) p
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ p‖ * ‖iteratedFDeriv ℝ (n - i) (smallPowerRawProfile K S ψ φ R) p‖ := hleib
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * L * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hcut i (hin.trans hn) p)
          (Nat.cast_nonneg _))
          (hb φ R p hp (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hL)
      _ = (2 : ℝ) ^ n * L * Q := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hL) hQ
  have hfinal : 0 ≤ (W ^ k * (2 : ℝ) ^ J * L * C) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) :=
    mul_nonneg (mul_nonneg hfactor (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le (-ε))
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hfinal
  intro p
  change ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => χ p * smallPowerRawProfile K S ψ φ R p) p‖ ≤ _
  by_cases hp : p ∈ tsupport χ
  · calc
      _ ≤ W ^ k * ((2 : ℝ) ^ J * L * Q) :=
        mul_le_mul (hweight p hp) (hnorm p hp) (norm_nonneg _) (pow_nonneg hW _)
      _ = _ := by dsimp only [Q]; ring
  · have hz : iteratedFDeriv ℝ n (fun p => χ p * smallPowerRawProfile K S ψ φ R p) p = 0 := by
      by_contra hne
      exact hp (tsupport_mul_subset_left (support_iteratedFDeriv_subset n hne))
    rw [hz, norm_zero, mul_zero]
    exact hfinal

/-- Finite aggregation retains one family of original-test seminorms and
one constant for all requested target seminorms. -/
theorem exists_orbitalKernel_finite_seminorm_smallPower_bound
    (ε : ℝ) (hε : 0 < ε) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        t.sup (schwartzSeminormFamily ℝ LogPlane ℂ)
          (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) := by
  have hex (j : ℕ × ℕ) := exists_orbitalKernel_seminorm_smallPower_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport ε hε j.1 j.2
  choose s C hC hb using hex
  let sall := t.biUnion s
  let Call : ℝ := ∑ j ∈ t, C j
  have hCall : 0 ≤ Call := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨sall, Call, hCall, fun φ R => ?_⟩
  have hfinal : 0 ≤ Call * sall.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) :=
    mul_nonneg (mul_nonneg hCall (apply_nonneg _ _)) (Real.rpow_nonneg R.property.le (-ε))
  apply Seminorm.finset_sup_apply_le hfinal
  intro j hj
  have hCj : C j ≤ Call := Finset.single_le_sum (fun i _ => hC i) hj
  have hsj : (s j).sup (schwartzSeminormFamily ℝ V ℂ) φ ≤
      sall.sup (schwartzSeminormFamily ℝ V ℂ) φ :=
    Seminorm.finset_sup_apply_le (apply_nonneg _ _)
      (fun i hi => Seminorm.le_finset_sup_apply (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩))
  exact (hb j φ R j.2 le_rfl).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hCj hsj (apply_nonneg _ _) hCall) (Real.rpow_nonneg R.property.le (-ε)))

/-- A common L¹ density bound, uniform in the actual outer radius and
the original test function. -/
theorem exists_orbitalDensity_mass_smallPower_bound
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
        (∫ ξ : LogPlane, ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖) ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) := by
  obtain ⟨t, D0, _hD0, hfourier⟩ := exists_spectralMass_seminorm_bound
  obtain ⟨s, C, hC, hb⟩ := exists_orbitalKernel_finite_seminorm_smallPower_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport ε hε t
  refine ⟨s, (D0 : ℝ) * C, mul_nonneg D0.coe_nonneg hC,
    fun φ R => ?_⟩
  exact (hfourier (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R)).trans
    ((mul_le_mul_of_nonneg_left (hb φ R) D0.coe_nonneg).trans_eq (by ring))

/-- One Fourier-frequency envelope for every outer radius.  In
particular the residual radius cannot select its own frequency cutoff. -/
theorem exists_orbitalDensity_weighted_smallPower_bound
    (ε : ℝ) (hε : 0 < ε) (q : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ ξ : LogPlane,
        (1 + ‖ξ‖) ^ q *
          ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε)) := by
  obtain ⟨t, D0, hD0, hfourier⟩ := exists_weighted_fourier_bound q
  obtain ⟨s, C, hC, hb⟩ := exists_orbitalKernel_finite_seminorm_smallPower_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport ε hε t
  refine ⟨s, D0 * C, mul_nonneg hD0 hC, fun φ R ξ => ?_⟩
  exact (hfourier (orbitalKernel K S Γ ψ hψ hψsupport χ hχ hχsupport φ R) ξ).trans
    ((mul_le_mul_of_nonneg_left (hb φ R) hD0).trans_eq (by ring))

/-- The actual densities share the same fixed integrable Fourier
envelope.  Only the scalar original-test seminorm and arbitrary small radial power vary. -/
theorem exists_orbitalDensity_smallPower_common_envelope
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ R : {r : ℝ // 0 < r},
      ∀ ξ : LogPlane,
        ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε))) *
            fourierEnvelope ξ := by
  let q := (volume : Measure LogPlane).integrablePower
  obtain ⟨s, C, hC, hb⟩ := exists_orbitalDensity_weighted_smallPower_bound
    K S Γ ψ hψ hψsupport χ hχ hχsupport ε hε q
  refine ⟨s, C, hC, fun φ R ξ => ?_⟩
  have hpow : 0 < (1 + ‖ξ‖) ^ q := pow_pos (by positivity) _
  have hd : ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖ ≤
      (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (R.val ^ (-ε))) /
        (1 + ‖ξ‖) ^ q := by
    apply (le_div_iff₀ hpow).mpr
    rw [mul_comm ‖orbitalDensity K S Γ ψ hψ hψsupport χ hχ hχsupport φ R ξ‖]
    exact hb φ R ξ
  simpa only [fourierEnvelope, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖),
    Real.rpow_natCast, div_eq_mul_inv, q] using hd

end HeckeSkeleton.Moments.MOM_INV_STEP.CommonKernel
