import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceCompleteRows
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOriginal
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

/-!
# The complete physical rows with the actual residual mark

The whole-column multiplier is retained through the original complete-row
calibration.  Conjugation acts on the entire marked polynomial, including
each residual prime coefficient and the radial profile.  The complete
row ball is enlarged to actual sixth-unit orbits before any restriction
to sixth-free rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedPhysical

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
  HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
  HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open SourceCompleteRows CanonicalNormPools
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def polynomial (d : MomentData K ω ψ) (mark : Ideal (𝓞 K) → ℂ)
    (u : NonzeroIdeal K) (X : ℝ) (W : SchwartzMap ℝ ℂ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∑ I ∈ dyadicIdealSupport K X,
    inverseRowCoefficient d u I * mark I.val * W (idealNorm K I / X)

theorem conjugate_polynomial (d : MomentData K ω ψ) (mark : Ideal (𝓞 K) → ℂ)
    (u : NonzeroIdeal K) (X : ℝ) (W : SchwartzMap ℝ ℂ) :
    polynomial K (conjugateInverseModel d) (fun I => conj (mark I)) u X
      (conjugateTest W) = conj (polynomial K d mark u X W) := by
  simp only [polynomial, SourceCompleteRows.conjugate_coefficient,
    conjugateTest_apply, map_mul, map_sum, map_inv₀, Complex.conj_ofReal]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable (P : ProbeData K Sset) (R : RowCharacterInput K Sset P)

theorem inverse_coefficient_calibration (d : MomentData K ω ψ)
    (sector : SixthUnitClasses K Sset) (hdir : d.direction = -1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (I : Ext) (n : NonzeroIdeal K) :
    inverseRowCoefficient d I.val n =
      (moebius n.val : ℂ) * heckeIdealCoefficient K d.inverseBackground n *
        zeroExtendedSexticIdealEvaluation K Sset P.arithmetic.root6
          P.arithmetic.primitive6 P.arithmetic.embedding n
          (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val ^ (-1 : ℤ) := by
  rw [actualOrbitSexticEvaluation_out,
    actualOrbitSexticEvaluation_decomposed_inverse K Sset P R]
  simp only [inverseRowCoefficient, hdir, hchar,
    completeIdealRowCharacter_exterior K Sset P R, maskValue, hmask,
    completeIdealCommonMask, decomposedIdealRowMask, sexticIdealOutsideS]
  split_ifs <;> ring

/-- Exact physical equality for any fixed whole-column multiplier.
The multiplier is neither estimated nor moved across a row-dependent
ramification zero. -/
theorem negative_polynomial_eq_source (d : MomentData K ω ψ)
    (mark : Ideal (𝓞 K) → ℂ) (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = -1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (I : Ext) (X : ℝ) (hX : 0 < X) (W : SchwartzMap ℝ ℂ) :
    polynomial K d mark I.val X W =
      SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground
        (fun n => mark n.val.val) W X
        (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val := by
  let a := (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val
  let f : NonzeroIdeal K → ℂ := fun n =>
    (moebius n.val : ℂ) * heckeIdealCoefficient K d.inverseBackground n *
      zeroExtendedSexticIdealEvaluation K Sset P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding n a ^ (-1 : ℤ) *
      mark n.val * W (idealNorm K n / X)
  have hs : (∑ n ∈ dyadicIdealSupport K X, f n) =
      ∑ n ∈ (dyadicIdealSupport K X).filter (fun n => Squarefree n.val ∧
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → p ∉ Sset), f n := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnot
    by_cases hsf : Squarefree n.val
    · have hbad : ¬sexticIdealOutsideS K Sset n := by
        intro he
        exact hnot (Finset.mem_filter.mpr ⟨hn, hsf, fun p hp => (he p hp).1⟩)
      simp only [f, zeroExtendedSexticIdealEvaluation_eq_zero K Sset
        P.arithmetic.root6 P.arithmetic.primitive6 P.arithmetic.embedding n a hbad,
        zpow_neg_one, inv_zero, mul_zero, zero_mul]
    · simp only [f, moebius_of_not_squarefree hsf, Int.cast_zero, zero_mul]
  rw [← SourceReductionPoisson.squarefreePool_image K S X hX.le,
    Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hs
  unfold polynomial
  simp_rw [inverse_coefficient_calibration K S P R d sector hdir hchar hmask I]
  change (Real.sqrt X : ℂ)⁻¹ * (∑ n ∈ dyadicIdealSupport K X, f n) = _
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [f, SourceReductionPoisson.coefficient]
  rw [SourceReductionPoisson.zeroExtended_exterior,
    SourceReductionPoisson.idealSymbol_inverse]
  change _ = (Real.sqrt X : ℂ)⁻¹ *
    ((moebius n.val.val : ℂ) * heckeIdealCoefficient K d.inverseBackground n.val *
      mark n.val.val * W (idealNorm K n.val / X)) * star (idealSymbol K Sset P.arithmetic n a)
  ring

/-- Positive orientation requires conjugating the residual prime
coefficients as well as the background and profile. -/
theorem positive_polynomial_norm (d : MomentData K ω ψ)
    (mark : Ideal (𝓞 K) → ℂ) (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = 1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (I : Ext) (X : ℝ) (hX : 0 < X) (W : SchwartzMap ℝ ℂ) :
    ‖polynomial K d mark I.val X W‖ =
      ‖SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground⁻¹
        (fun n => conj (mark n.val.val)) (conjugateTest W) X
        (decomposedIdealSectorOrbit K Sset P (I, sector)).out.val‖ := by
  have h := negative_polynomial_eq_source K S P R (conjugateInverseModel d)
    (fun I => conj (mark I)) sector (by change -d.direction = -1; rw [hdir])
    hchar hmask I X hX (conjugateTest W)
  rw [conjugate_polynomial] at h
  simpa only [Complex.norm_conj] using congrArg norm h

variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
  [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "Γ" => sixthPowerSUnitSubgroup K Sset
local notation "Orbit" => ActualSIntegerOrbit K Sset

theorem complete_positive_rows_le_orbital (d : MomentData K ω ψ)
    (mark : Ideal (𝓞 K) → ℂ) (sector : SixthUnitClasses K Sset)
    (hdir : d.direction = 1)
    (hchar : d.rowCharacter = completeIdealRowCharacter K Sset P R sector)
    (hmask : d.commonMask = completeIdealCommonMask K Sset)
    (hrows : d.allowedRow = completeIdealIsExterior K Sset)
    (H X : ℝ) (hH : 0 < H) (hX : 0 < X) (W : SchwartzMap ℝ ℂ) :
    (∑ u ∈ d.rows H, ‖polynomial K d mark u X W‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖SourceReductionPoisson.orbitalEnergy K S P.arithmetic Γ d.inverseBackground⁻¹
          (fun n => conj (mark n.val.val)) (conjugateTest W) X ⟨H, hH⟩‖ := by
  let exterior (u : {u // u ∈ d.rows H}) : Ext :=
    ⟨u.val, by
      have he := ((d.rows_spec H u.val).mp u.property).1
      simpa only [hrows] using he⟩
  let row (u : {u // u ∈ d.rows H}) : Orbit :=
    decomposedIdealSectorOrbit K Sset P (exterior u, sector)
  have hinj : Function.Injective row := by
    intro u v huv
    apply Subtype.ext
    exact congrArg Subtype.val
      (congrArg Prod.fst (decomposedIdealSectorOrbit_injective K Sset P huv))
  let T : Finset Orbit := (d.rows H).attach.image row
  have hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    change actualSIntegerOrbitNorm K Sset (decomposedIdealSectorOrbit K Sset P
      (exterior u, sector)) ≤ H
    rw [decomposedIdealSectorOrbit_norm]
    exact ((d.rows_spec H u.val).mp u.property).2
  have heq : (∑ u ∈ d.rows H, ‖polynomial K d mark u X W‖ ^ 2) =
      ∑ q ∈ T, ‖SourceReductionPoisson.sourceColumn K S P.arithmetic d.inverseBackground⁻¹
        (fun n => conj (mark n.val.val)) (conjugateTest W) X q.out.val‖ ^ 2 := by
    dsimp only [T]
    rw [Finset.sum_image (fun u hu v hv h => hinj h)]
    rw [← Finset.sum_attach (d.rows H) (fun u => ‖polynomial K d mark u X W‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [positive_polynomial_norm K S P R d mark sector hdir hchar hmask (exterior u) X hX W]
  rw [heq]
  exact SourceReductionPoisson.finite_rows_le_orbital_norm K S P.arithmetic Γ
    d.inverseBackground⁻¹ (fun n => conj (mark n.val.val)) (conjugateTest W) X ⟨H, hH⟩ T hT

section Marks

variable {K}
variable {σ : Type*} (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
  (a : σ → Ideal (𝓞 K) → ℂ) (j : Ideal (𝓞 K))

def mark (I : Ideal (𝓞 K)) : ℂ :=
  (if IsCoprime I j then 1 else 0) * divisorMark slots lists a I

theorem conjugate_divisorMark (I : Ideal (𝓞 K)) :
    conj (divisorMark slots lists a I) = divisorMark slots lists (fun i p => conj (a i p)) I := by
  simp only [divisorMark, map_prod, map_sum]

theorem conjugate_mark (I : Ideal (𝓞 K)) :
    conj (mark slots lists a j I) = mark slots lists (fun i p => conj (a i p)) j I := by
  rw [mark, map_mul, conjugate_divisorMark]
  by_cases h : IsCoprime I j <;> simp only [mark, h, if_true, if_false, map_one, map_zero]

end Marks

variable (K)

theorem exists_small_scale_row_bound (slotCap : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      {σ : Type*} (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
      (a : σ → Ideal (𝓞 K) → ℂ) (j : Ideal (𝓞 K)),
      slots.card ≤ slotCap → (∀ i ∈ slots, ∀ p ∈ lists i, ‖a i p‖ ≤ 1) →
      ∀ (H X : ℝ) (W : SchwartzMap ℝ ℂ),
      1 ≤ H → 0 < X → X ≤ 1 →
      (∑ u ∈ d.rows H, ‖polynomial K d (mark slots lists a j) u X W‖ ^ 2) ≤
        C * H * (SchwartzMap.seminorm ℝ 0 0 W) ^ 2 := by
  obtain ⟨A, hA, hcount⟩ := HeckeSkeleton.Moments.UniformAmplify.exists_nonzero_ideal_count_bound
    (K := K)
  obtain ⟨B, hB, hdivisor⟩ := CoefficientBounds.exists_divisorMark_bound K slotCap 1 (by norm_num)
  refine ⟨64 * A ^ 3 * B ^ 2, by positivity, ?_⟩
  intro ω ψ d σ slots lists a j hslots ha H X W hH hX hX1
  by_cases hsmall : X < 1 / 2
  · have he : dyadicIdealSupport K X = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hn := (mem_dyadicIdealSupport_iff K hX.le I).mp hI
      linarith [one_le_idealNorm K I]
    simp only [polynomial, he, Finset.sum_empty, mul_zero, norm_zero, zero_pow,
      Finset.sum_const_zero]
    positivity
  · have hXlower : 1 / 2 ≤ X := le_of_not_gt hsmall
    have hinv : (Real.sqrt X)⁻¹ ≤ 2 := by
      have hroot : 1 / 2 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by nlinarith)
      have hi := (inv_le_inv₀ (Real.sqrt_pos.2 hX)
        (by norm_num : (0 : ℝ) < 1 / 2)).mpr hroot
      norm_num at hi
      exact hi
    let Q := SchwartzMap.seminorm ℝ 0 0 W
    have hQ : 0 ≤ Q := apply_nonneg _ _
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have hcols : ((dyadicIdealSupport K X).card : ℝ) ≤ A * 2 := by
      apply hcount _ 2 (by norm_num)
      intro I hI
      have hn := (mem_dyadicIdealSupport_iff K hX.le I).mp hI
      linarith
    have hmark (I : NonzeroIdeal K) (hI : I ∈ dyadicIdealSupport K X) :
        ‖mark slots lists a j I.val‖ ≤ 2 * B := by
      have hn : idealNorm K I ≤ 2 := by
        have h := (mem_dyadicIdealSupport_iff K hX.le I).mp hI
        linarith
      have hm := hdivisor slots lists a I.val (nonZeroDivisors.coe_ne_zero I) hslots ha
      rw [Real.rpow_one] at hm
      have hc : ‖(if IsCoprime I.val j then 1 else 0 : ℂ)‖ ≤ 1 := by
        split_ifs <;> norm_num
      rw [mark, norm_mul]
      calc
        _ ≤ 1 * ‖divisorMark slots lists a I.val‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ B * idealNorm K I := by simpa only [one_mul] using hm
        _ ≤ 2 * B := by nlinarith
    have hpoly (u : NonzeroIdeal K) :
        ‖polynomial K d (mark slots lists a j) u X W‖ ≤ 8 * A * B * Q := by
      have hs : ‖∑ I ∈ dyadicIdealSupport K X,
          inverseRowCoefficient d u I * mark slots lists a j I.val * W (idealNorm K I / X)‖ ≤
            A * 2 * (2 * B * Q) := by
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _I ∈ dyadicIdealSupport K X, 2 * B * Q := by
            apply Finset.sum_le_sum
            intro I hI
            rw [norm_mul, norm_mul]
            calc
              _ ≤ 1 * (2 * B) * Q := by
                gcongr
                · exact norm_inverseRowCoefficient_le_one d u I
                · exact hmark I hI
                · exact SchwartzMap.norm_le_seminorm ℝ W _
              _ = _ := by ring
          _ = ((dyadicIdealSupport K X).card : ℝ) * (2 * B * Q) := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hcols (by positivity)
      rw [polynomial, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_mul hinv hs (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hrows : ((d.rows H).card : ℝ) ≤ A * H :=
      hcount _ H hH (fun u hu => ((d.rows_spec H u).mp hu).2)
    calc
      _ ≤ ∑ _u ∈ d.rows H, (8 * A * B * Q) ^ 2 :=
        Finset.sum_le_sum (fun u hu => pow_le_pow_left₀ (norm_nonneg _) (hpoly u) 2)
      _ = ((d.rows H).card : ℝ) * (8 * A * B * Q) ^ 2 := by simp
      _ ≤ A * H * (8 * A * B * Q) ^ 2 := mul_le_mul_of_nonneg_right hrows (sq_nonneg _)
      _ = _ := by dsimp only [Q]; ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedPhysical

end
