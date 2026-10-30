import HeckeSkeleton.LowHybrid.CompletedQuadratic

/-!
# The original completed quadratic row satisfies Lemma 4.6

The coefficients depend only on the original squarefree n and arbitrary b.
The product fiber is bounded by the actual squarefree divisors of n*b. All
constants precede the scales, supports and coefficients. Only the quadratic
sieve, prime coordinates, and linear norm counting enter the public theorem.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace CompletedQuadratic

variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def products (columns cubes : Finset A) : Finset A :=
  (columns ×ˢ cubes).image (fun u => u.1 * u.2)

def productCoefficient (columns cubes : Finset A) (beta : A → A → ℂ) (y : A) : ℂ :=
  ∑ u ∈ columns ×ˢ cubes with u.1 * u.2 = y, beta u.1 u.2

theorem product_row (symbol : A → A → ℂ)
    (columns cubes : Finset A) (beta : A → A → ℂ) (k : A) :
    (∑ n ∈ columns, ∑ b ∈ cubes, beta n b * symbol k (n * b) ^ 3) =
      ∑ y ∈ products columns cubes, productCoefficient columns cubes beta y * symbol k y ^ 3 := by
  have hm : ∀ u ∈ columns ×ˢ cubes, u.1 * u.2 ∈ products columns cubes := by
    intro u hu
    exact Finset.mem_image_of_mem _ hu
  calc
    _ = ∑ u ∈ columns ×ˢ cubes, beta u.1 u.2 * symbol k (u.1 * u.2) ^ 3 := by
      rw [Finset.sum_product]
    _ = ∑ y ∈ products columns cubes,
        ∑ u ∈ columns ×ˢ cubes with u.1 * u.2 = y,
          beta u.1 u.2 * symbol k (u.1 * u.2) ^ 3 :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [productCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]

theorem product_fiber_card (columns cubes : Finset A)
    (hcolumns : ∀ n ∈ columns, PrimeArithmetic.Squarefree coords n) (y : A) :
    (((columns ×ˢ cubes).filter fun u => u.1 * u.2 = y).card : ℝ) ≤
      ((PrimeArithmetic.divisors coords y).card : ℝ) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun u : A × A => u.1)
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    have hd : u.1 ∣ y := ⟨u.2, hu'.2.symm⟩
    exact PrimeArithmetic.mem_divisors_of_squarefree_dvd coords
      (hcolumns u.1 (Finset.mem_product.mp hu'.1).1) hd
  · intro u hu v hv huv
    change u.1 = v.1 at huv
    apply Prod.ext huv
    have heq := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    rw [huv] at heq
    apply valuation_injective coords
    ext p
    have hp := congrArg (fun a => valuation coords a p) heq
    simp only [valuation_mul_apply] at hp
    omega

theorem productCoefficient_norm (columns cubes : Finset A)
    (hcolumns : ∀ n ∈ columns, PrimeArithmetic.Squarefree coords n)
    (beta : A → A → ℂ) (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1)
    (y : A) :
    ‖productCoefficient columns cubes beta y‖ ≤
      ((PrimeArithmetic.divisors coords y).card : ℝ) := by
  calc
    _ ≤ ∑ u ∈ columns ×ˢ cubes with u.1 * u.2 = y, ‖beta u.1 u.2‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ columns ×ˢ cubes with _u.1 * _u.2 = y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      have hp := Finset.mem_product.mp (Finset.mem_filter.mp hu).1
      exact hbeta u.1 hp.1 u.2 hp.2
    _ = (((columns ×ˢ cubes).filter fun u => u.1 * u.2 = y).card : ℝ) := by simp
    _ ≤ _ := product_fiber_card coords columns cubes hcolumns y

end CompletedQuadratic

/-- The standalone completed quadratic bound, with precisely the paper's
(K+NB)NB growth and no cubic sieve assumption. The cube b is unrestricted. -/
theorem completed_quadratic_energy_bounded
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      ∀ (rows columns cubes : Finset A) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        (∑ k ∈ rows, ‖∑ n ∈ columns, ∑ b ∈ cubes,
          beta n b * symbol k (n * b) ^ 3‖ ^ 2) ≤
          C0 * (K * N * B) ^ eps * (K + N * B) * (N * B) := by
  let eta := eps / 5
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨Cq, hCq, hquadratic⟩ := CompletedQuadratic.completed_energy_le coords normI q
    hnatural hqpos Ccount hCcount hcount symbol hright h6 hq eta heta
  obtain ⟨CD, hCD, hdivisor⟩ := divisorEnvelopeOfCounting_subpower coords normI q
    hnatural Ccount hcount hqpos eta heta
  obtain ⟨CH, hCH, hharmonic⟩ := harmonicEnvelope_subpower Ccount hCcount eta heta
  refine ⟨Cq * CD ^ 2 * Ccount * CH ^ 2, by positivity, ?_⟩
  intro K N B hK hN hB rows columns cubes beta hrows hcolumns hcubes hbeta
  let X := N * B
  let M := K * X
  let ys := CompletedQuadratic.products columns cubes
  let gamma := CompletedQuadratic.productCoefficient columns cubes beta
  let D := divisorEnvelopeOfCounting coords normI q hnatural Ccount hcount X
  have hn := one_le_real_norm_of_natural q normI hnatural hqpos
  have hX : 1 ≤ X := by
    simpa only [X, one_mul] using
      (mul_le_mul hN hB zero_le_one (le_trans zero_le_one hN))
  have hM : 1 ≤ M := by
    simpa only [M, one_mul] using
      (mul_le_mul hK hX zero_le_one (le_trans zero_le_one hK))
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hXM : X ≤ M := le_mul_of_one_le_left hX0 hK
  have hys : ∀ y ∈ ys, normI y ≤ X := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have hp := Finset.mem_product.mp hu
    rw [map_mul]
    exact mul_le_mul (hcolumns u.1 hp.1).2 (hcubes u.2 hp.2)
      (le_trans zero_le_one (hn u.2)) (le_trans zero_le_one hN)
  have hgamma : ∀ y ∈ ys, ‖gamma y‖ ≤ D := by
    intro y hy
    exact (CompletedQuadratic.productCoefficient_norm coords columns cubes
      (fun n hn => (hcolumns n hn).1) beta hbeta y).trans
      (divisor_count_le_envelopeOfCounting coords normI q hnatural Ccount hcount X y (hys y hy))
  have hD0 : 0 ≤ D := divisorEnvelopeOfCounting_nonneg coords normI q hnatural Ccount hcount X
  have hH0 : 0 ≤ harmonicEnvelope Ccount X := harmonicEnvelope_nonneg Ccount (le_of_lt hCcount) X hX
  have hpowmono : X ^ eta ≤ M ^ eta := Real.rpow_le_rpow hX0 hXM (le_of_lt heta)
  have hD : D ≤ CD * M ^ eta :=
    (hdivisor X hX).trans (mul_le_mul_of_nonneg_left hpowmono (le_of_lt hCD))
  have hH : harmonicEnvelope Ccount X ≤ CH * M ^ eta :=
    (hharmonic X hX).trans (mul_le_mul_of_nonneg_left hpowmono (le_of_lt hCH))
  have hQ : 0 ≤ Cq * (K * X) ^ eta * (K + X) := by positivity
  have hpower : (M ^ eta) ^ 5 = M ^ eps := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hMpos)]
    congr 1
    dsimp only [eta]
    ring
  have hb := hquadratic K X hK hX rows ys gamma D hD0 hrows hys hgamma
  have hmain :
      (∑ k ∈ rows, ‖∑ n ∈ columns, ∑ b ∈ cubes,
        beta n b * symbol k (n * b) ^ 3‖ ^ 2) ≤
        (Cq * CD ^ 2 * Ccount * CH ^ 2) * M ^ eps * (K + X) * X := by
    calc
      _ = ∑ k ∈ rows, ‖∑ y ∈ ys, gamma y * symbol k y ^ 3‖ ^ 2 := by
        simp_rw [CompletedQuadratic.product_row symbol columns cubes beta]
        rfl
      _ ≤ (Cq * (K * X) ^ eta * (K + X)) * D ^ 2 * Ccount * X *
          harmonicEnvelope Ccount X ^ 2 := hb
      _ ≤ (Cq * (K * X) ^ eta * (K + X)) * (CD * M ^ eta) ^ 2 * Ccount * X *
          (CH * M ^ eta) ^ 2 := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ hX0
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hCcount)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2) hQ
        · exact pow_le_pow_left₀ hH0 hH 2
        · exact sq_nonneg _
        · positivity
      _ = (Cq * CD ^ 2 * Ccount * CH ^ 2) * (M ^ eta) ^ 5 * (K + X) * X := by
        dsimp only [M]
        ring
      _ = _ := by rw [hpower]
  simpa only [M, X, mul_assoc] using hmain

#print axioms completed_quadratic_energy_bounded
#print axioms CompletedQuadratic.completed_quadratic_positive

end
end HeckeSkeleton.LowHybrid
