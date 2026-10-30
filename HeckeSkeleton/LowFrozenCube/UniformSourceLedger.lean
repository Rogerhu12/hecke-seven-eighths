import HeckeSkeleton.LowFrozenCube.UniformWeightedHybridBound
import HeckeSkeleton.LowFrozenCube.SourceLedger

/-!
# A source-ledger constant uniform in every frozen local datum

The global prime coordinates, symbol, norm counting, and two sieve inputs
are fixed before the constant is chosen. Every frozen support, ordinary
subset, digit vector, minimum ideal, and finite source block is quantified
after that constant. The intermediate helper consumes the proved hybrid
constant; the main theorem derives it from the two sieve inputs.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- The conclusion of the actual source ledger at a specified constant. -/
def SourceLedgerBound (D : Data ι A) (normI : A →* ℝ) (eps C : ℝ) : Prop :=
  ∀ Z O H v ell S B z T : ℝ,
    1 ≤ Z → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
    ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
      PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
      Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
        C * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z))

namespace Data

variable (D : Data ι A)

/-- Transport a single proved hybrid constant through the full raw local
calculation. No new constant depending on the frozen data is selected. -/
theorem source_ledger_bound_from_weighted (normI : A →* ℝ)
    (hpos : ∀ a, 0 < normI a) (eps C0 : ℝ) (hC0 : 0 < C0)
    (hbound : WeightedRawHybridBound D normI eps C0) :
    SourceLedgerBound D normI eps (48 * C0) := by
  intro Z O H v ell S B z T hZ hH hv hell hz b hs hlocal hcharge
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hNpos : 0 < Z ^ v := Real.rpow_pos_of_pos hZpos v
  have hBpos : 0 < Z ^ ell := Real.rpow_pos_of_pos hZpos ell
  by_cases hactive : (D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs).Nonempty
  · obtain ⟨u, hu⟩ := hactive
    have hCtable := D.tableMajorant_sq_le_charge normI hpos b.first b.prefactor b.atZero
      (fun p hp => D.minimum_cases_of_activeInput normI b.first b.prefactor b.atZero b.inputs u hu p)
      hlocal.first_sq hlocal.prefactor_sq hlocal.zero_sq
    have hCscale : D.tableMajorant normI b.first b.prefactor b.atZero ^ 2 ≤
        (Z ^ (S + B))⁻¹ := by
      apply hCtable.trans
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hZpos (S + B)) hcharge
    have hcoeff : (D.tableMajorant normI b.first b.prefactor b.atZero / (Z ^ ell / 2)) ^ 2 /
        (Z ^ v / 2) ≤ 8 * Z ^ (squaredCoefficientExponent v ell S B) := by
      rw [dyadic_coefficient_scale _ _ _ hNpos hBpos]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact normalizedCoefficient_le_ledger _ _ _ _ Z v ell S B
        hNpos hZpos hCscale rfl rfl rfl
    have hE := hbound hs.rowBall (Z ^ H) (Z ^ v) (Z ^ ell) (Z ^ z)
      (Z ^ v / 2) (Z ^ ell / 2)
      (Real.one_le_rpow hZ hH) (Real.one_le_rpow hZ hv)
      (Real.one_le_rpow hZ hell) (Real.one_le_rpow hZ hz)
      (div_pos hNpos (by norm_num)) (div_pos hBpos (by norm_num))
      b.first b.prefactor b.atZero b.phase b.a₀ b.ρ₀ b.lam b.pow b.sup
      b.rows b.marks b.columns b.inputs hs.rows_norm hs.residual_norm hs.rho_norm
      hs.marks_away hs.marks_sf_norm hs.marks_coeff hs.columns_away hs.columns_sf_norm
      hs.columns_coeff hs.columns_lower hs.input_supported hs.input_away hs.input_phase
      hs.cube_lower hs.cube_upper
    have hE' : b.energy D normI ≤
        (D.tableMajorant normI b.first b.prefactor b.atZero / (Z ^ ell / 2)) ^ 2 / (Z ^ v / 2) *
          ((C0 * Z ^ (eps * (H + v + ell + z))) * hybridScale Z H v ell z) := by
      rw [four_scale_power Z H v ell z eps hZpos] at hE
      simpa only [SourceBlock.energy, hybridScale, quadraticScale, cubicScale,
        mul_assoc] using hE
    have hlead : 0 ≤ C0 * Z ^ (eps * (H + v + ell + z)) :=
      mul_nonneg (le_of_lt hC0) (Real.rpow_nonneg hZ0 _)
    have hhybrid : 0 ≤ hybridScale Z H v ell z := by
      unfold hybridScale quadraticScale cubicScale
      positivity
    have hEsimple : b.energy D normI ≤
        (48 * C0) * Z ^ (eps * (H + v + ell + z)) *
          Z ^ (squaredCoefficientExponent v ell S B + hybridGrowthExponent H v ell z) := by
      calc
        _ ≤ (8 * Z ^ (squaredCoefficientExponent v ell S B)) *
            ((C0 * Z ^ (eps * (H + v + ell + z))) *
              (6 * Z ^ (hybridGrowthExponent H v ell z))) := by
          apply hE'.trans
          exact mul_le_mul hcoeff
            (mul_le_mul_of_nonneg_left (hybridScale_le Z H v ell z hZ) hlead)
            (mul_nonneg hlead hhybrid)
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hZ0 _))
        _ = _ := by
          rw [Real.rpow_add hZpos]
          ring
    calc
      Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          Z ^ (O / 2) *
            ((48 * C0) * Z ^ (eps * (H + v + ell + z)) *
              Z ^ (squaredCoefficientExponent v ell S B + hybridGrowthExponent H v ell z)) *
                Z ^ (squaredKernelExponent T v ell) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEsimple (Real.rpow_nonneg hZ0 _))
          (Real.rpow_nonneg hZ0 _)
      _ = _ := by
        rw [← reflected_exponent_identity O H v ell S B z T]
        simp only [Real.rpow_add hZpos]
        ring
  · have hempty : D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [b.energy_zero_of_empty_active D normI hs.input_supported hempty]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC0)) (Real.rpow_nonneg hZ0 _)


end Data

/-- Uniformity in the frozen support, digit vector, and minimum ideal, as
well as in every scale and source block. The only analytic hypotheses are
the two large-sieve inputs and linear ideal counting. -/
theorem uniform_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol → SourceLedgerBound D normI eps C := by
  have hnorm := HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural q normI hnatural hqpos
  have hpos (a : A) : 0 < normI a := lt_of_lt_of_le zero_lt_one (hnorm a)
  obtain ⟨C0, hC0, hweighted⟩ := Data.uniform_weighted_raw_hybrid_bound
    coords symbol hleft h6 normI q hnatural hqpos Ccount hCcount hcount hq hc eps heps
  refine ⟨48 * C0, mul_pos (by norm_num) hC0, ?_⟩
  intro D hcoords hsymbol
  exact D.source_ledger_bound_from_weighted normI hpos eps C0 hC0
    (hweighted D hcoords hsymbol)

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
