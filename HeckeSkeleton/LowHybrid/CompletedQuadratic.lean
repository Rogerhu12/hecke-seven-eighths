import HeckeSkeleton.LowHybrid.ArithmeticLosses
import HeckeSkeleton.LowHybrid.CanonicalSupport
import HeckeSkeleton.LowHybrid.Transpose
import HeckeSkeleton.LowHybrid.Weighted

/-!
# The completed quadratic estimate using only the quadratic sieve

The product y = n*b is grouped before any norm inequality. Its canonical
square extraction y = s*t^2 retains the exact row--t collision zero. Weighted
Cauchy acts on t, and the quadratic sieve acts on the squarefree s variable.
There is no Cauchy step at a fixed original cube b.
-/

namespace HeckeSkeleton.LowHybrid.CompletedQuadratic

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

def squarefreePart (y : A) : A := mapExponents coords (fun e => e % 2) rfl y

def squarePart (y : A) : A := PrimeArithmetic.squarePart coords y

theorem square_decomposition (y : A) :
    squarefreePart coords y * squarePart coords y ^ 2 = y := by
  apply valuation_injective coords
  ext p
  simp only [valuation_mul_apply, valuation_pow_apply]
  simp only [squarefreePart, squarePart, PrimeArithmetic.squarePart,
    valuation_mapExponents]
  omega

theorem squarefreePart_squarefree (y : A) :
    PrimeArithmetic.Squarefree coords (squarefreePart coords y) := by
  intro p
  simp only [squarefreePart, valuation_mapExponents]
  omega

def squareRoots (ys : Finset A) : Finset A := ys.image (squarePart coords)

def squarefreeColumns (ys : Finset A) (t : A) : Finset A :=
  (ys.filter fun y => squarePart coords y = t).image (squarefreePart coords)

theorem squarefreeColumns_mem {ys : Finset A} {t s : A}
    (hs : s ∈ squarefreeColumns coords ys t) :
    s * t ^ 2 ∈ ys ∧ PrimeArithmetic.Squarefree coords s := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hs
  have ht := (Finset.mem_filter.mp hy).2
  constructor
  · rw [← ht, square_decomposition]
    exact (Finset.mem_filter.mp hy).1
  · exact squarefreePart_squarefree coords y

theorem squarefreeColumn_injective (ys : Finset A) (t : A) :
    Set.InjOn (squarefreePart coords) (ys.filter fun y => squarePart coords y = t) := by
  intro y hy z hz heq
  calc
    y = squarefreePart coords y * t ^ 2 := by
      rw [← (Finset.mem_filter.mp hy).2, square_decomposition]
    _ = squarefreePart coords z * t ^ 2 := by rw [heq]
    _ = z := by rw [← (Finset.mem_filter.mp hz).2, square_decomposition]

theorem sum_square_parts {R : Type*} [AddCommMonoid R]
    (ys : Finset A) (F : A → R) :
    (∑ y ∈ ys, F y) =
      ∑ t ∈ squareRoots coords ys, ∑ s ∈ squarefreeColumns coords ys t, F (s * t ^ 2) := by
  have hm : ∀ y ∈ ys, squarePart coords y ∈ squareRoots coords ys := by
    intro y hy
    exact Finset.mem_image_of_mem _ hy
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [squarefreeColumns, Finset.sum_image (squarefreeColumn_injective coords ys t)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← (Finset.mem_filter.mp hy).2, square_decomposition]

theorem square_symbol (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (k s t : A) :
    symbol k (s * t ^ 2) ^ 3 =
      (if Coprime coords k t then (1 : ℂ) else 0) * symbol k s ^ 3 := by
  rw [hright, pow_two, hright, mul_pow, mul_pow]
  have hp : symbol k t ^ 3 * symbol k t ^ 3 = symbol k t ^ 6 := by ring
  rw [hp, h6]
  ring

theorem sum_square_symbols (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (ys : Finset A) (gamma : A → ℂ) (k : A) :
    (∑ y ∈ ys, gamma y * symbol k y ^ 3) =
      ∑ t ∈ squareRoots coords ys,
        (if Coprime coords k t then (1 : ℂ) else 0) *
          ∑ s ∈ squarefreeColumns coords ys t, gamma (s * t ^ 2) * symbol k s ^ 3 := by
  rw [sum_square_parts coords ys]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [square_symbol coords symbol hright h6]
  ring

/-- The arbitrary-coefficient positive completed reduction. The original
row--square-part zeros are retained until each t is frozen. -/
theorem completed_quadratic_positive
    (normI : A → ℝ) (hn : ∀ a, 0 < normI a)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (rows ys : Finset A) (gamma : A → ℂ) (Q : ℝ)
    (hquadratic : ∀ t ∈ squareRoots coords ys, ∀ f : A → ℂ,
      (∑ k ∈ rows, ‖∑ s ∈ squarefreeColumns coords ys t, f s * symbol k s ^ 3‖ ^ 2) ≤
        Q * ∑ s ∈ squarefreeColumns coords ys t, ‖f s‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ y ∈ ys, gamma y * symbol k y ^ 3‖ ^ 2) ≤
      (∑ t ∈ squareRoots coords ys, 1 / normI t) *
        ∑ t ∈ squareRoots coords ys,
          normI t * (Q * ∑ s ∈ squarefreeColumns coords ys t, ‖gamma (s * t ^ 2)‖ ^ 2) := by
  simp_rw [sum_square_symbols coords symbol hright h6 ys gamma]
  apply weighted_mixture_energy rows (squareRoots coords ys) normI
  · intro t ht
    exact hn t
  · intro t ht
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (hn t))
    apply le_trans _ (hquadratic t ht (fun s => gamma (s * t ^ 2)))
    apply Finset.sum_le_sum
    intro k hk
    by_cases hc : Coprime coords k t
    · simp only [if_pos hc, one_mul, le_refl]
    · simp only [if_neg hc, zero_mul, norm_zero, zero_pow two_ne_zero]
      exact sq_nonneg _

theorem card_le_real_scale
    (normI : A → ℝ) (q : A → ℕ) (hnatural : ∀ a, normI a = (q a : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 0 ≤ X) (s : Finset A) (hs : ∀ a ∈ s, normI a ≤ X) :
    (s.card : ℝ) ≤ C * X := by
  have hnat : ∀ a ∈ s, q a ≤ Nat.floor X := by
    intro a ha
    apply Nat.le_floor
    simpa only [hnatural] using hs a ha
  exact (hcount (Nat.floor X) s hnat).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le hX) hC)

/-- A finite bound with the actual harmonic sum, before epsilon absorption.
Only the quadratic sieve is used. -/
theorem completed_energy_le
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
      ∀ (rows ys : Finset A) (gamma : A → ℂ) (G : ℝ), 0 ≤ G →
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ y ∈ ys, normI y ≤ X) → (∀ y ∈ ys, ‖gamma y‖ ≤ G) →
        (∑ k ∈ rows, ‖∑ y ∈ ys, gamma y * symbol k y ^ 3‖ ^ 2) ≤
          (Cq * (K * X) ^ eta * (K + X)) * G ^ 2 * Ccount * X *
            harmonicEnvelope Ccount X ^ 2 := by
  obtain ⟨Cq, hCq, hsieve⟩ := quadratic_sieve_input_transpose normI
    (PrimeArithmetic.Squarefree coords) symbol hq eta heta
  refine ⟨Cq, hCq, ?_⟩
  intro K X hK hX rows ys gamma G hG hrows hys hgamma
  have hn := one_le_real_norm_of_natural q normI hnatural hqpos
  have hpos (a : A) : 0 < normI a := lt_of_lt_of_le zero_lt_one (hn a)
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  let Q := Cq * (K * X) ^ eta * (K + X)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hcolumns (t s : A) (hs : s ∈ squarefreeColumns coords ys t) :
      PrimeArithmetic.Squarefree coords s ∧ normI s * normI t ^ 2 ≤ X := by
    have hh := squarefreeColumns_mem coords hs
    exact ⟨hh.2, by simpa only [map_mul, map_pow] using hys _ hh.1⟩
  have hnormcol (t s : A) (hs : s ∈ squarefreeColumns coords ys t) : normI s ≤ X := by
    exact (le_mul_of_one_le_right (le_of_lt (hpos s))
      (one_le_pow₀ (hn t))).trans (hcolumns t s hs).2
  have hquadratic : ∀ t ∈ squareRoots coords ys, ∀ f : A → ℂ,
      (∑ k ∈ rows, ‖∑ s ∈ squarefreeColumns coords ys t, f s * symbol k s ^ 3‖ ^ 2) ≤
        Q * ∑ s ∈ squarefreeColumns coords ys t, ‖f s‖ ^ 2 := by
    intro t ht f
    exact hsieve K X hK hX rows (squarefreeColumns coords ys t) hrows
      (fun s hs => ⟨(hcolumns t s hs).1, hnormcol t s hs⟩) f
  have hcard (t : A) : ((squarefreeColumns coords ys t).card : ℝ) ≤
      Ccount * (X / normI t ^ 2) := by
    apply card_le_real_scale normI q hnatural Ccount (le_of_lt hCcount) hcount
      (X / normI t ^ 2) (div_nonneg hX0 (sq_nonneg _))
    intro s hs
    exact (le_div_iff₀ (sq_pos_of_pos (hpos t))).mpr (hcolumns t s hs).2
  have hmass (t : A) :
      (∑ s ∈ squarefreeColumns coords ys t, ‖gamma (s * t ^ 2)‖ ^ 2) ≤
        G ^ 2 * (Ccount * (X / normI t ^ 2)) := by
    calc
      _ ≤ ∑ _s ∈ squarefreeColumns coords ys t, G ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        exact pow_le_pow_left₀ (norm_nonneg _)
          (hgamma _ (squarefreeColumns_mem coords hs).1) 2
      _ = G ^ 2 * ((squarefreeColumns coords ys t).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcard t) (sq_nonneg G)
  have htbound : ∀ t ∈ squareRoots coords ys, normI t ≤ X := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    have hd : squarePart coords y ∣ y := by
      refine ⟨squarefreePart coords y * squarePart coords y, ?_⟩
      calc
        y = squarefreePart coords y * squarePart coords y ^ 2 :=
          (square_decomposition coords y).symm
        _ = _ := by rw [pow_two]; ac_rfl
    exact (PrimeArithmetic.norm_le_of_dvd normI hn hd).trans (hys y hy)
  let H := ∑ t ∈ squareRoots coords ys, 1 / normI t
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun t ht => le_of_lt (one_div_pos.mpr (hpos t)))
  have hH : H ≤ harmonicEnvelope Ccount X :=
    reciprocal_sum_le_harmonicEnvelope q normI hnatural Ccount (le_of_lt hCcount)
      hqpos hcount X hX (squareRoots coords ys) htbound
  have hb := completed_quadratic_positive coords normI hpos symbol hright h6
    rows ys gamma Q hquadratic
  calc
    _ ≤ H * ∑ t ∈ squareRoots coords ys,
        normI t * (Q * ∑ s ∈ squarefreeColumns coords ys t, ‖gamma (s * t ^ 2)‖ ^ 2) := hb
    _ ≤ H * ∑ t ∈ squareRoots coords ys,
        normI t * (Q * (G ^ 2 * (Ccount * (X / normI t ^ 2)))) := by
      apply mul_le_mul_of_nonneg_left _ hH0
      exact Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmass t) hQ) (le_of_lt (hpos t))
    _ = (Q * G ^ 2 * Ccount * X) * H ^ 2 := by
      have he (t : A) : normI t * (Q * (G ^ 2 * (Ccount * (X / normI t ^ 2)))) =
          (Q * G ^ 2 * Ccount * X) * (1 / normI t) := by
        field_simp [ne_of_gt (hpos t)] <;> ring
      simp_rw [he]
      rw [← Finset.mul_sum]
      dsimp only [H]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hH 2)
      (by dsimp only [Q]; positivity)

end
end HeckeSkeleton.LowHybrid.CompletedQuadratic
