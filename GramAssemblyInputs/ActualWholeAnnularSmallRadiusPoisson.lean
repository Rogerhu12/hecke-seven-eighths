import ActualWholeAnnularAllScalePoisson
import ActualAnnularDivisorUnitReindex
import SmallRadiusAnnularMellinSchwartz
import SmallRadiusPolynomialLoss

/-!
UNCOMPILED / native 0. The actual fixed-box joint seminorm sum is bounded
using the PRE-Fourier all-radius estimate. Its finite box cardinal is fixed
before all moving data. Substitution into the genuine whole-annular bound
returns to the original divisor, keeping both arithmetic nonexceptional
conditions and the balanced lattice scale N/q_d. The orbital radius is the
ordinary ARCH radius of originalJointFactor, not the total-norm radius.
An additional endpoint absorbs the small radius loss on a polynomial range
using the proved small-exponent choice and real-power monotonicity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeGeneral.Analysis.ActualWholeAnnularSmallRadiusDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open AlgebraicNumberTheory.PowerResidueSymbols
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramFixedDenominatorDraft ActualWholeAnnularAllScaleDraft
open ActualAnnularDivisorUnitReindexDraft
open SmallRadiusAnnularMellinSchwartzDraft SmallRadiusPolynomialLossDraft
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
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
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ

variable (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
  (a0 b0 : ℝ) (ha0 : 0 < a0) (haSupport : tsupport a ⊆ Set.Icc a0 b0)
  (ψ : ((v : S) → v.val.adicCompletion K) → ℂ)
  (hψ : Continuous ψ) (hψsupport : HasCompactSupport ψ)

/-- Every genuine finite representative uses the same pre-Fourier bound.
The fixed box cardinal squared is absorbed into a positive constant. -/
theorem exists_fixedBoxJointSeminormSum_allRadius_bound
    (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (t : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}),
        fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport t ν φ R ≤
        C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-β) := by
  obtain ⟨s, C₀, J, hC₀, hb⟩ :=
    exists_sUnitMellinAnnularPartitionJointSchwartz_finite_seminorm_allRadius_bound
      K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport β hβ hβ1 t
  let n : ℝ := Fintype.card (S → Fin H)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC : 0 < 1 + n * n * C₀ :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (mul_nonneg hn hn) hC₀)
  refine ⟨s, 1 + n * n * C₀, J, hC, fun ν φ R => ?_⟩
  let B : ℝ := s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (1 + |ν|) ^ J * R.val ^ (-β)
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (apply_nonneg _ _) (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg R.property.le _)
  calc
    _ ≤ ∑ _e₁ : S → Fin H, ∑ _e₂ : S → Fin H,
        C₀ * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J * R.val ^ (-β) := by
      unfold fixedBoxJointSeminormSum
      exact Finset.sum_le_sum (fun e₁ _ => Finset.sum_le_sum (fun e₂ _ =>
        hb ν (sUnitPartitionFiniteFibreRepresentative K S H e₁)
          (sUnitPartitionFiniteFibreRepresentative K S H e₂) φ R))
    _ = (n * n * C₀) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [n, B]
      ring
    _ ≤ (1 + n * n * C₀) * B :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hB
    _ = _ := by dsimp only [B]; ring

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (ρ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
/-- The whole literal annular sum now has a bound in finitely many
seminorms of the original one-column input. Constants precede the divisor,
and all frequency/profile/scale data; the divisor is the original d. -/
theorem exists_whole_annular_fixedDepth_allRadius_min_bound
    (A : ℕ) (hA : 2 < A) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧ ∀ (d c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}) (N : ℝ), 0 < N →
      ‖∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ ρ hS6 c k d ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * R.val ^ (-β) *
          (N / (sIntegerElementNorm K S d).val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d).val)) ^ A) := by
  obtain ⟨t, C₀, hC₀, hwhole⟩ := exists_original_whole_annular_fixedDepth_allScale_min_bound
    (K := K) (S := S) (Γ := Γ) (ζ := ζ) (hζ := hζ) (σ := ρ) (hS6 := hS6)
    (a := a) (ψ := ψ) (ha := ha) (a0 := a0) (b0 := b0) (ha0 := ha0)
    (haSupport := haSupport) (hψ := hψ) (hψsupport := hψsupport) A hA
  obtain ⟨s, C₁, J, hC₁, hbox⟩ := exists_fixedBoxJointSeminormSum_allRadius_bound
    K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport β hβ hβ1 t
  refine ⟨s, C₀ * C₁, J, mul_pos hC₀ hC₁, ?_⟩
  intro d c k p hpC hpJ ν φ R N hN
  have hq : 0 < N / (sIntegerElementNorm K S d).val :=
    div_pos hN (sIntegerElementNorm K S d).property
  have hmin : 0 ≤ min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
        (N / (sIntegerElementNorm K S d).val)) ^ A) := by positivity
  have hs := hbox ν φ R
  calc
    _ ≤ C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        fixedBoxJointSeminormSum K S Γ a ha a0 b0 ha0 haSupport
          ψ hψ hψsupport t ν φ R *
        (N / (sIntegerElementNorm K S d).val) ^ 2 *
        min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
            (N / (sIntegerElementNorm K S d).val)) ^ A) :=
      hwhole d c k p hpC hpJ ν φ R N hN
    _ ≤ C₀ * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
        (C₁ * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (1 + |ν|) ^ J * R.val ^ (-β)) *
        (N / (sIntegerElementNorm K S d).val) ^ 2 *
        min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
            (N / (sIntegerElementNorm K S d).val)) ^ A) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (mul_nonneg hC₀.le (Nat.cast_nonneg _)))
            (sq_nonneg _)) hmin
    _ = _ := by ring

/-- Choose the small positive exponent before the moving height. On the
literal polynomial lower radius range this gives an arbitrary Z^epsilon
loss, with the original divisor and the same ordinary arch R. -/
theorem exists_whole_annular_fixedDepth_polynomialRadius_min_bound
    (A : ℕ) (hA : 2 < A) (L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, ∃ J : ℕ, 0 < C ∧ ∀ (d c k : NZ)
      (p : jointPlaces K (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)),
      (¬ p.val.asIdeal ∣ actualFrequencyIdeal K S c) →
      (¬ 6 ∣ idealPrimeMultiplicity K p.val (actualFrequencyIdeal K S k)) →
      ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (ν : ℝ) (φ : SchwartzMap V ℂ) (R : {r : ℝ // 0 < r}), Z ^ (-L) ≤ R.val →
      ∀ N : ℝ, 0 < N →
      ‖∑' m, actualAnnularJointSummand K S Γ a ψ ζ hζ ρ hS6 c k d ν φ R N m‖ ≤
        C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
          s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J * Z ^ ε *
          (N / (sIntegerElementNorm K S d).val) ^ 2 *
          min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
            (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
              (N / (sIntegerElementNorm K S d).val)) ^ A) := by
  obtain ⟨β, hβ, hβ1, hβε⟩ := exists_small_radius_exponent L ε hL hε
  obtain ⟨s, C, J, hC, hwhole⟩ := exists_whole_annular_fixedDepth_allRadius_min_bound
    K S Γ a ha a0 b0 ha0 haSupport ψ hψ hψsupport ζ hζ ρ hS6 A hA β hβ hβ1
  refine ⟨s, C, J, hC, ?_⟩
  intro d c k p hpC hpJ Z hZ ν φ R hR N hN
  have hq : 0 < N / (sIntegerElementNorm K S d).val :=
    div_pos hN (sIntegerElementNorm K S d).property
  have hmin : 0 ≤ min 1 ((((Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      (Ideal.absNorm (actualFrequencyIdeal K S k) : ℝ)) /
        (N / (sIntegerElementNorm K S d).val)) ^ A) := by positivity
  have hpref : 0 ≤ C * (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) *
      s.sup (schwartzSeminormFamily ℝ V ℂ) φ * (1 + |ν|) ^ J :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _)) (apply_nonneg _ _))
      (pow_nonneg (by positivity) _)
  exact (hwhole d c k p hpC hpJ ν φ R N hN).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (radius_neg_rpow_le_small_power Z R.val L ε β hZ hR hβ.le hβε) hpref)
          (sq_nonneg _)) hmin)

end HeckeGeneral.Analysis.ActualWholeAnnularSmallRadiusDraft
