import HeckeSkeleton.LowFrozenCube.SourceLedger

/-!
# Terminal margins for the proved raw source-energy bound

The inequalities here apply the existing three-branch terminal ledger to
the source estimate proved in `SourceLedger`. They do not assume an energy
bound. The conductor, retained-range, and margin premises are the scalar
geometric data appearing in the paper's terminal comparison.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

theorem source_energy_terminal
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (terminalBound F M c delta tau + eps * (H + v + ell + z)) := by
  obtain ⟨C, hC, hledger⟩ := D.source_energy_ledger normI q hnatural hqpos
    Ccount hCcount hcount hq hc eps heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau
    hZ hH0 hO hS hB hell hv hz hQ hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained b hs hlocal hcharge
  have hsource := hledger Z O H v ell S B z T hZ hH0 hv hell hz b hs hlocal hcharge
  have hterminal := terminal_ledger F M N Nstar V bh delta O H v ell S B z T Q z0 c tau
    hF hNstar hO hS hB hell hv hz hQ hV hbh hz0 hH hmargin1 hmargin2 hconductor hretained
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (add_le_add hterminal le_rfl)) (le_of_lt hC))

/-- With the explicit step, retained-range, and small-power margins, the
actual source energy has a fixed quarter-margin power saving. -/
theorem source_energy_power_saving
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hcubic : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps * (H + v + ell + z) ≤ c / 4 →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (F - c / 4) := by
  obtain ⟨C, hC, hterminal⟩ := D.source_energy_terminal normI q hnatural hqpos
    Ccount hCcount hcount hq hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau
    hZ hH0 hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained hdelta htau hloss b hs hlocal hcharge
  have hsource := hterminal Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau
    hZ hH0 hO hS hB hell hv hz hQ hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained b hs hlocal hcharge
  have hhalf := terminalBound_le_half_margin F M c delta tau hM hc hdelta htau
  have hexponent : terminalBound F M c delta tau + eps * (H + v + ell + z) ≤ F - c / 4 := by
    linarith
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexponent) (le_of_lt hC))

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
