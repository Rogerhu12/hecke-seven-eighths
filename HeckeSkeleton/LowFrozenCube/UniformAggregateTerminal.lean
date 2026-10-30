import HeckeSkeleton.LowFrozenCube.UniformAggregateSource
import HeckeSkeleton.LowHybrid.CountingPositivity

/-!
# Arbitrary small-power and terminal bounds for the complete original row family

A fixed logarithmic length budget is chosen before the analytic constant.
Both the hybrid loss and the actual frozen-pair count are then absorbed into
one arbitrary prescribed exponent. The final bounds keep every scale, local
datum, finite row support and coefficient family after that constant.

Natural norm positivity and positivity of the counting constant are derived
from linear counting. The public hypotheses contain two sieve inputs and the
linear counting estimate, together with explicit support and scalar budgets.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical
open HeckeSkeleton.LowHybrid
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- Every prescribed positive loss exponent is available uniformly over
all original row families whose logarithmic length budget is at most W. -/
theorem uniform_family_source_energy_subpower
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T + eps) := by
  have hqpos := linear_norm_counting_norm_one_le q Ccount hcount
  have hCcount := linear_norm_counting_constant_pos_of_element q Ccount hcount (1 : A)
  let eta : ℝ := eps / W
  have heta : 0 < eta := div_pos heps hW
  obtain ⟨C, hC, hledger⟩ := uniform_family_source_energy_ledger coords symbol hleft h6
    normI q hnatural hqpos Ccount hCcount hcount hq hc eta eta heta heta
  refine ⟨C, hC, ?_⟩
  intro Z O H v ell S B z T Rrad hZ hO hH hv hell hz hbudget base rows hpow hrad
    data family hf hsymbol hs hlocal hcharge
  have hsource := hledger Z O H v ell S B z T Rrad hZ hO hH hv hell hz
    base rows hpow hrad data family hf hsymbol hs hlocal hcharge
  have hloss : eta * (H + v + ell + z) + eta * (O + Rrad) ≤ eps := by
    calc
      _ = eta * ((H + v + ell + z) + (O + Rrad)) := by ring
      _ ≤ eta * W := mul_le_mul_of_nonneg_left hbudget (le_of_lt heta)
      _ = eps := div_mul_cancel₀ eps (ne_of_gt hW)
  have hexponent : reflectedExponent O H v ell S B z T +
      eta * (H + v + ell + z) + eta * (O + Rrad) ≤
        reflectedExponent O H v ell S B z T + eps := by linarith
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexponent) (le_of_lt hC))

/-- The original full row energy satisfies the paper's terminal maximum,
with an arbitrary prescribed total small-power loss. All conductor and
invariant comparisons in this statement are scalar hypotheses. -/
theorem uniform_family_source_energy_terminal
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (terminalBound F M c delta tau + eps) := by
  obtain ⟨C, hC, hledger⟩ := uniform_family_source_energy_subpower coords symbol hleft h6
    normI q hnatural Ccount hcount hq hc W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad
    hZ hH0 hO hS hB hell hv hz hQ hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained hbudget base rows hpow hrad data family hf hsymbol hs hlocal hcharge
  have hsource := hledger Z O H v ell S B z T Rrad hZ hO hH0 hv hell hz hbudget
    base rows hpow hrad data family hf hsymbol hs hlocal hcharge
  have hterminal := terminal_ledger F M N Nstar V bh delta O H v ell S B z T Q z0 c tau
    hF hNstar hO hS hB hell hv hz hQ hV hbh hz0 hH hmargin1 hmargin2 hconductor hretained
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (add_le_add hterminal le_rfl)) (le_of_lt hC))

/-- A genuine quarter-margin saving for the complete original source row
family. The same constant works for every frozen datum and every node
margin c for which the prescribed eps is at most c/4. -/
theorem uniform_family_source_energy_power_saving
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hcubic : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps ≤ c / 4 →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤ C * Z ^ (F - c / 4) := by
  obtain ⟨C, hC, hterminal⟩ := uniform_family_source_energy_terminal coords symbol hleft h6
    normI q hnatural Ccount hcount hq hcubic W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad
    hZ hH0 hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained hdelta htau hloss hbudget base rows hpow hrad
    data family hf hsymbol hs hlocal hcharge
  have hsource := hterminal Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad
    hZ hH0 hO hS hB hell hv hz hQ hF hNstar hV hbh hz0 hH hmargin1 hmargin2
    hconductor hretained hbudget base rows hpow hrad data family hf hsymbol hs hlocal hcharge
  have hhalf := terminalBound_le_half_margin F M c delta tau hM hc hdelta htau
  have hexponent : terminalBound F M c delta tau + eps ≤ F - c / 4 := by linarith
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ hexponent) (le_of_lt hC))

#print axioms uniform_family_source_energy_subpower
#print axioms uniform_family_source_energy_terminal
#print axioms uniform_family_source_energy_power_saving

end
end HeckeSkeleton.LowFrozenCube.FrozenReduction
