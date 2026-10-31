import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedLogMellin
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedPhysical

/-! The fixed supported tests and exact complete-pool physical bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTests

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderMarkedMellin ProviderMarkedMaskedMellin ProviderMarkedReindex CommonKernel
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

def piece (t : ℝ) (i : SchwartzTestPartition.Index) : SchwartzMap ℝ ℂ :=
  SchwartzTestPartition.piece (test t) (SchwartzTestPartition.exponent i)

theorem test_wide_support (t : ℝ) : tsupport (test t) ⊆ Set.Icc (1 / 512 : ℝ) 4 := by
  intro x hx
  obtain ⟨hl, hu⟩ := test_support t hx
  exact ⟨by linarith, by linarith⟩

theorem piece_support (t : ℝ) (i : SchwartzTestPartition.Index) :
    tsupport (piece t i) ⊆ Set.Icc (1 : ℝ) 2 :=
  SchwartzTestPartition.piece_support (test t) (test_wide_support t) _

theorem piece_polynomial_seminorm (q : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ i : SchwartzTestPartition.Index,
      q.sup (schwartzSeminormFamily ℝ ℝ ℂ) (piece t i) ≤ C * (1 + |t|) ^ J := by
  obtain ⟨s, A, hA, hs⟩ := SchwartzTestPartition.exists_finite_seminorm_bound q
  obtain ⟨J, B, hB, hb⟩ := test_polynomial_seminorm s
  refine ⟨J, A * B, mul_nonneg hA hB, ?_⟩
  intro t i
  exact (hs (test t) i).trans
    ((mul_le_mul_of_nonneg_left (hb t) hA).trans_eq (by ring))

theorem finite_test_eq_pieces {ι : Type*} (T : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) (U t : ℝ) :
    (∑ i ∈ T, a i * test t (N i / U)) =
      ∑ k : SchwartzTestPartition.Index, ∑ i ∈ T, a i *
        piece t k (N i / (SchwartzTestPartition.scale (SchwartzTestPartition.exponent k) * U)) :=
  SchwartzTestPartition.finite_source_reconstruct T a N U (test t) (test_wide_support t)

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem live_coefficient (d : MomentData K ω ψ) (u n : NonzeroIdeal K)
    (hdir : d.direction = 1)
    (hν : d.commonMask u n.val = true →
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p) :
    inverseRowCoefficient d u n = (moebius n.val : ℂ) *
      heckeIdealCoefficient K (d.inverseBackground * d.rowCharacter u) n * maskValue d u n.val := by
  cases hm : d.commonMask u n.val with
  | false => simp only [inverseRowCoefficient, maskValue, hm, Bool.false_eq_true, if_false, mul_zero]
  | true =>
    rw [inverseRowCoefficient, hdir, zpow_one,
      source_idealCoefficient_mul_unramified d.inverseBackground (d.rowCharacter u) n (hν hm)]
    ring

/-- The enlarged complete norm pool is justified separately for each
supported test, including all columns inserted before Fourier inversion. -/
theorem complete_pool_sum (U Y : ℝ) (hU : 0 < U) (hUY : U ≤ Y)
    (a : Ideal (𝓞 K) → ℂ) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    (∑ n ∈ ProviderMarkedPools.pool U, a n * W (ProviderMarkedPools.norm n / U)) =
      ∑ n ∈ ProviderMarkedPools.pool Y, a n * W (ProviderMarkedPools.norm n / U) := by
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn0, hnorm⟩ := (ProviderMarkedPools.mem_pool hU.le n).mp hn
    exact (ProviderMarkedPools.mem_pool (hU.le.trans hUY) n).mpr ⟨hn0, by linarith⟩
  · intro n hn hnU
    have hn0 := ((ProviderMarkedPools.mem_pool (hU.le.trans hUY) n).mp hn).1
    have hz : W (ProviderMarkedPools.norm n / U) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hw
      have hnorm := (div_le_iff₀ hU).mp (hW hw).2
      exact hnU ((ProviderMarkedPools.mem_pool hU.le n).mpr ⟨hn0, hnorm⟩)
    rw [hz, mul_zero]

/-- The output of fixed-overlap Mellin separation is precisely the
normalized original complete-row polynomial, with the actual extra
puncture and literal residual divisor mark. -/
theorem polynomial_eq_complete_column {σ : Type*}
    (d : MomentData K ω ψ) (u : NonzeroIdeal K) (hdir : d.direction = 1)
    (good : HeightOneSpectrum (𝓞 K) → Prop)
    (hmask : ∀ n, maskValue d u n = ProviderMarkedMask.value good u.val n)
    (hν : ∀ n : NonzeroIdeal K, d.commonMask u n.val = true →
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (j : Ideal (𝓞 K))
    (U Y : ℝ) (hU : 0 < U) (hUY : U ≤ Y) (W : SchwartzMap ℝ ℂ)
    (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2) :
    SourceMarkedPhysical.polynomial K d (SourceMarkedPhysical.mark slots lists a j) u U W =
      (Real.sqrt U : ℂ)⁻¹ * ∑ n ∈ columns Y j,
        (moebius n : ℂ) * idealCoefficient (primeCoefficient K
          (d.inverseBackground * d.rowCharacter u)) n * ProviderMarkedMask.value good u.val n *
          divisorMark slots lists a n * W (ProviderMarkedPools.norm n / U) := by
  let f : Ideal (𝓞 K) → ℂ := fun n => (moebius n : ℂ) *
    idealCoefficient (primeCoefficient K (d.inverseBackground * d.rowCharacter u)) n *
      ProviderMarkedMask.value good u.val n * SourceMarkedPhysical.mark slots lists a j n
  have hfirst : SourceMarkedPhysical.polynomial K d (SourceMarkedPhysical.mark slots lists a j)
      u U W = (Real.sqrt U : ℂ)⁻¹ *
        ∑ n ∈ ProviderMarkedPools.pool U, f n * W (ProviderMarkedPools.norm n / U) := by
    rw [ProviderMarkedPools.pool,
      Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    unfold SourceMarkedPhysical.polynomial
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [live_coefficient d u n hdir (hν n), hmask]
    rfl
  rw [hfirst, complete_pool_sum U Y hU hUY f W hW]
  congr 1
  rw [columns, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsf : Squarefree n
  · by_cases hcop : IsCoprime n j
    · simp only [hsf, hcop, and_self, if_true, f, SourceMarkedPhysical.mark, one_mul]
    · simp only [hsf, hcop, and_false, if_false, f, SourceMarkedPhysical.mark, zero_mul, mul_zero]
  · simp only [hsf, false_and, if_false, f, moebius_of_not_squarefree hsf,
      Int.cast_zero, zero_mul]

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTests

end
