import ExpansionDetector.IdealZeroSource
import HeckeGeneral.Analysis.IdealMobiusDeletion

/-!
# The actual deleted Hecke series used by the expansion detector

The finite prime deletion is performed on the prime coefficients before
the detector weight is constructed. In particular this accommodates every
prime in the original fixed exceptional set and every prime dividing the
complete row, whether or not it ramifies in the inducing character.

The ordinary deleted initial series follows from the already constructed
Moebius reciprocal identities by injectivity of inversion. Thus the input
to `actualIdeal_terminal_lower_of_zero` is calibrated with a concrete
existing Hecke continuation, not supplied as a new identity assumption.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ExpansionDetectorInitial
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.IdealMobiusReciprocal
open ExpansionDetector.IdealCutoff
open scoped NumberField Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem deleted_idealDirichletSeries_eq
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    idealDirichletSeries K (nonzeroIdealCoefficient (deletePrimes K S a)) s =
      (∏ p ∈ S, (1 - primeIdealRatio K a s p)) *
        idealDirichletSeries K (nonzeroIdealCoefficient a) s := by
  apply inv_injective
  rw [← moebius_series_eq_inverse K (deletePrimes K S a)
    (norm_deletePrimes_le_one K S a ha) hs]
  simp_rw [term_deletePrimes]
  exact excluded_series_eq_inverse K S a ha hs

theorem heckeDeletedContinuation_eq_deleted_series
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ S s =
      idealDirichletSeries K
        (nonzeroIdealCoefficient (deletePrimes K S (primeCoefficient K χ))) s := by
  rw [deleted_idealDirichletSeries_eq K S (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) hs]
  unfold heckeDeletedContinuation
  rw [heckeContinuation_eq_series K χ hs]
  congr 1
  simp only [heckeEulerDeletionPolynomial, finiteEulerPolynomial,
    eulerPolynomial, primeIdealRatio, residueCard, Complex.ofReal_natCast]

def deletedCoefficientHom (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Ideal (𝓞 K) →*₀ ℂ :=
  idealCoefficientHom (deletePrimes K S (primeCoefficient K χ))

theorem deletedCoefficientHom_norm_le (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) :
    ‖deletedCoefficientHom K χ S I‖ ≤ 1 :=
  norm_idealCoefficient_le_one _
    (norm_deletePrimes_le_one K S (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ)) I

theorem tsum_nonzeroIdeal_eq_tsum {f : Ideal (𝓞 K) → ℂ} (h0 : f 0 = 0) :
    (∑' I : NonzeroIdeal K, f I.val) = ∑' I : Ideal (𝓞 K), f I := by
  have hsup := support_subset_nonzero_of_zero h0
  let e : NonzeroIdeal K ≃
      {I : Ideal (𝓞 K) // I ∈ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K)))} :=
    { toFun := fun I => ⟨I.val, I.property⟩
      invFun := fun I => ⟨I.val, I.property⟩
      left_inv := fun I => Subtype.ext rfl
      right_inv := fun I => Subtype.ext rfl }
  calc
    _ = ∑' I : {I : Ideal (𝓞 K) // I ∈ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K)))}, f I.val :=
      e.tsum_eq _
    _ = _ := tsum_subtype_eq_of_support_subset hsup

/-- The exact all-integral-ideal convention required by the verified
detector. The zero ideal contributes zero by the same multiplicative map. -/
theorem heckeDeletedContinuation_eq_allIdeal_series
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 1 < s.re) :
    heckeDeletedContinuation K χ S s =
      ∑' I : Ideal (𝓞 K), idealDirichletWeight (deletedCoefficientHom K χ S) s I := by
  rw [heckeDeletedContinuation_eq_deleted_series K χ S hs]
  have ht := tsum_nonzeroIdeal_eq_tsum K
    (f := fun I => idealDirichletWeight (deletedCoefficientHom K χ S) s I) (by simp)
  rw [← ht]
  apply tsum_congr
  intro I
  simp only [idealDirichletSeries, dirichletSeries, dirichletTerm,
    idealDirichletWeight_apply, deletedCoefficientHom, idealCoefficientHom,
    nonzeroIdealCoefficient, idealNorm, Complex.ofReal_natCast]

/-- Ordinary absolute convergence is inherited from the existing actual
ideal series for bounded deleted prime coefficients. -/
theorem deletedCoefficient_initial_absolutelySummable
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) =>
      ‖idealDirichletWeight (deletedCoefficientHom K χ S) s I‖) := by
  let f : Ideal (𝓞 K) → ℝ := fun I =>
    ‖idealDirichletWeight (deletedCoefficientHom K χ S) s I‖
  have hsup : Function.support f ⊆ ((Ideal (𝓞 K))⁰ : Set (Ideal (𝓞 K))) := by
    intro I hI
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro heq
    subst I
    exact hI (by simp [f])
  have h := absolutelySummable_idealEulerWeight K (deletePrimes K S (primeCoefficient K χ))
    (norm_deletePrimes_le_one K S (primeCoefficient K χ) (norm_primeCoefficient_le_one K χ)) hs
  have hNZ : Summable (fun I : NonzeroIdeal K => f I.val) := by
    simpa only [f, idealDirichletWeight_apply, deletedCoefficientHom,
      idealCoefficientHom, idealEulerWeight] using h
  exact ((hasSum_subtype_iff_of_support_subset hsup).mp hNZ.hasSum).summable

theorem heckeDeletedContinuation_entire
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (heckeDeletedContinuation K χ S) := by
  apply Differentiable.mul
  · intro s
    exact (heckeEulerDeletionPolynomial_analyticAt K χ S s).differentiableAt
  · exact differentiable_heckeContinuation_of_nonNorm K χ hχ

theorem heckeDeletedContinuation_zero
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {ρ : ℂ} (hρ : heckeContinuation K χ ρ = 0) :
    heckeDeletedContinuation K χ S ρ = 0 := by
  simp only [heckeDeletedContinuation, hρ, mul_zero]

theorem heckeEulerDeletionPolynomial_norm_le_card
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖heckeEulerDeletionPolynomial K χ S s‖ ≤ (2 : ℝ) ^ S.card := by
  unfold heckeEulerDeletionPolynomial finiteEulerPolynomial
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ S, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      intro p hp
      unfold eulerPolynomial
      have hq : 1 ≤ (residueCard K p : ℝ) := by
        exact_mod_cast (one_lt_residueCard K p).le
      have hqpos : 0 < (residueCard K p : ℝ) := zero_lt_one.trans_le hq
      have ht : ‖primeCoefficient K χ p * ((residueCard K p : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hqpos, Complex.neg_re]
        exact (mul_le_mul (norm_primeCoefficient_le_one K χ p)
          (Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr hs))
          (by positivity) zero_le_one).trans_eq (one_mul _)
      have h := norm_sub_le (1 : ℂ)
        (primeCoefficient K χ p * ((residueCard K p : ℝ) : ℂ) ^ (-s))
      rw [norm_one] at h
      linarith
    _ = _ := Finset.prod_const _

end HeckeGeneral.Analysis.ExpansionDetectorInitial
