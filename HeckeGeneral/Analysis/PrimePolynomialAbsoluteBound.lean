import HeckeGeneral.Analysis.MomentPrimeWindows
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.IdealEulerProduct

/-!
Absolute counting for the actual normalized prime polynomials. Constants
come from the proved linear count of nonzero integral ideals. Supports are
the exact PrimeWindow supports and lie in the annulus (1,2); all original
mask and ramified coefficient zeros are retained. The slot-square estimate
has exponent totalLength (the kappa=1 absolute slot exponent). It is not
the paired plain fourth moment.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The count constant depends only on K, before characters, rows, windows,
height and scale. Profile bounds are explicit, not encoded as admissibility. -/
theorem exists_norm_primePolynomial_absolute_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t B : ℝ),
      1 ≤ Z → 0 ≤ B →
      Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2 →
      (∀ y, ‖(d.geometry.slots i).profile t y‖ ≤ B) →
      ‖primePolynomial d i u Z t‖ ≤ C * B * Real.sqrt (Z ^ (d.geometry.slots i).length) := by
  obtain ⟨c, hc, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨2 * c, by positivity, ?_⟩
  intro ω ψ d i u Z t B hZ hB hann hprof
  let X := Z ^ (d.geometry.slots i).length
  have hX : 1 ≤ X := Real.one_le_rpow hZ (d.geometry.slots i).length_pos.le
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  let F := (d.geometry.slots i).support t X
  have hsub : F.image (primeNonzeroIdeal K) ⊆ dyadicIdealSupport K X := by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hw := ((d.geometry.slots i).support_spec t X p).mp hp
    have hn := (div_lt_iff₀ hX0).mp (hann hw).2
    exact (mem_dyadicIdealSupport_iff K hX0.le (primeNonzeroIdeal K p)).mpr hn.le
  have hcard : (F.card : ℝ) ≤ (2 * c) * X := by
    have hf : F.card ≤ (dyadicIdealSupport K X).card := by
      calc
        F.card = (F.image (primeNonzeroIdeal K)).card :=
          (Finset.card_image_of_injective F (primeNonzeroIdeal_injective K)).symm
        _ ≤ _ := Finset.card_le_card hsub
    have hn := hcount (2 * X) (by linarith)
    have hx : 2 * X / 2 = X := by ring
    calc
      _ ≤ ((dyadicIdealSupport K X).card : ℝ) := Nat.cast_le.mpr hf
      _ ≤ c * (2 * X) := by simpa only [hx] using hn
      _ = (2 * c) * X := by ring
  have hmask (p : HeightOneSpectrum (𝓞 K)) : ‖maskValue d u p.asIdeal‖ ≤ 1 := by
    unfold maskValue
    split_ifs <;> simp
  have hterm (p : HeightOneSpectrum (𝓞 K)) :
      ‖primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
        (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
        maskValue d u p.asIdeal‖ ≤ B := by
    simp only [norm_mul]
    calc
      _ ≤ 1 * B * 1 := by
        exact mul_le_mul
          (mul_le_mul (norm_primeCoefficient_le_one K _ p) (hprof _)
            (norm_nonneg _) zero_le_one)
          (hmask p) (norm_nonneg _) (by positivity)
      _ = B := by ring
  have hsum : ‖∑ p ∈ F,
      primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
        (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
        maskValue d u p.asIdeal‖ ≤ (2 * c) * B * X := by
    calc
      _ ≤ ∑ p ∈ F, ‖primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
          (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
          maskValue d u p.asIdeal‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ F, B := Finset.sum_le_sum (fun p _ => hterm p)
      _ = (F.card : ℝ) * B := by simp
      _ ≤ ((2 * c) * X) * B := mul_le_mul_of_nonneg_right hcard hB
      _ = (2 * c) * B * X := by ring
  change ‖(Real.sqrt X : ℂ)⁻¹ * ∑ p ∈ F,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((p.asIdeal.absNorm : ℝ) / X) *
      maskValue d u p.asIdeal‖ ≤ (2 * c) * B * Real.sqrt X
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg X), inv_mul_eq_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hX0)).mpr
  calc
    _ ≤ (2 * c) * B * X := hsum
    _ = ((2 * c) * B) * (Real.sqrt X * Real.sqrt X) := by
      rw [Real.mul_self_sqrt hX0.le]
    _ = _ := by ring

/-- For fixed windows and uniform profile bounds, actual slot products have
the absolute exponent sum(lengths), with no row or target-dependent count. -/
theorem slotProduct_sq_absolute_bound {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (B : Fin d.geometry.slotCount → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hann : ∀ i t, Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2)
    (hprof : ∀ i t y, ‖(d.geometry.slots i).profile t y‖ ≤ B i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : NonzeroIdeal K) (Z t : ℝ), 1 ≤ Z →
      ‖slotProduct d u Z t‖ ^ 2 ≤ A * Z ^ d.geometry.totalLength := by
  obtain ⟨C, hC, hp⟩ := exists_norm_primePolynomial_absolute_bound K
  refine ⟨∏ i, (C * B i) ^ 2, Finset.prod_nonneg (fun i _ => sq_nonneg _), ?_⟩
  intro u Z t hZ
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hi (i : Fin d.geometry.slotCount) :
      ‖primePolynomial d i u Z t‖ ^ 2 ≤ (C * B i) ^ 2 * Z ^ (d.geometry.slots i).length := by
    have hBi := hB i
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ C * B i * Real.sqrt (Z ^ (d.geometry.slots i).length))).mpr
        (hp d i u Z t (B i) hZ (hB i) (hann i t) (hprof i t))
    simpa only [mul_pow, Real.sq_sqrt (Real.rpow_nonneg hZ0.le _)] using h
  calc
    _ = ∏ i, ‖primePolynomial d i u Z t‖ ^ 2 := by
      rw [slotProduct, norm_prod, Finset.prod_pow]
    _ ≤ ∏ i, (C * B i) ^ 2 * Z ^ (d.geometry.slots i).length :=
      Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hi i)
    _ = (∏ i, (C * B i) ^ 2) * Z ^ d.geometry.totalLength := by
      change (∏ i, (C * B i) ^ 2 * Z ^ (d.geometry.slots i).length) =
        (∏ i, (C * B i) ^ 2) * Z ^ (∑ i, (d.geometry.slots i).length)
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hZ0]

end HeckeGeneral.ThetaSkeleton.Physical
