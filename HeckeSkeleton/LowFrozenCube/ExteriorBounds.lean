import HeckeSkeleton.LowFrozenCube.ExteriorLocalTable
import HeckeSkeleton.LowFrozenCube.ExteriorPhases
import HeckeSkeleton.LowHybrid.ExteriorSieve
import HeckeSkeleton.LowFrozenCube.UniformAggregateTerminal

/-!
# The frozen-cube bounds for the project's actual arithmetic

The two sieve inputs, natural norm, prime factorization and linear counting
are discharged by the actual exterior-ideal dictionary.  Every constant
below is chosen before all finite frozen supports, digits, minima, row
sets, annuli and coefficients.  The final family bound is therefore
available for the varying frozen supports in the reflected-energy proof.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowHybrid
open FrozenReduction PrimeCoordinates
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {S₀ : Finset (HeightOneSpectrum (𝓞 K))} {root12 : K} {σ : K →+* ℂ}
variable (X : HeckeAxiom.ArithmeticChoice K S₀ root12 σ)
local notation "S" => (X.places : Set (HeightOneSpectrum (𝓞 K)))
local notation "D" => X.thetaData
local notation "coords" => ExteriorArithmetic.coords K S
local notation "normI" => ExteriorArithmetic.normHom K S

local notation "hD" => ExteriorSieve.allowedInput X

/-- A uniform weighted raw frozen-cube bound for the actual allowed
generator symbol.  Its left side is the original finite raw source energy
in `WeightedRawHybridBound`, including both square-root column weights. -/
theorem uniform_weighted_raw_hybrid_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Data K S,
      FrozenReduction.Data.WeightedRawHybridBound (f.toFrozen K S D hD) normI eps C := by
  obtain ⟨C, hC, h⟩ := FrozenReduction.Data.uniform_weighted_raw_hybrid_bound
    coords (ExteriorSymbol.symbolHom K S D hD)
    (ExteriorSymbol.symbol_mul_left K S D hD)
    (ExteriorSymbol.symbolHom_sixth K S D hD)
    normI (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
    (ExteriorArithmetic.one_le_natNorm K S)
    (ExteriorArithmetic.countConstant K) (ExteriorArithmetic.countConstant_pos K)
    (ExteriorArithmetic.linearNormCounting K S)
    (ExteriorSieve.quadraticSieveInput X) (ExteriorSieve.cubicSieveInput X.A D hD)
    eps heps
  exact ⟨C, hC, fun f => h (f.toFrozen K S D hD) rfl rfl⟩

/-- The source ledger uses the same actual arithmetic and remains uniform
over the frozen local data.  Primitive local bounds enter only after the
constant is fixed; they do not include any global energy assertion. -/
theorem uniform_source_energy_ledger (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Data K S,
      SourceLedgerBound (f.toFrozen K S D hD) normI eps C := by
  obtain ⟨C, hC, h⟩ := FrozenReduction.uniform_source_energy_ledger
    coords (ExteriorSymbol.symbolHom K S D hD)
    (ExteriorSymbol.symbol_mul_left K S D hD)
    (ExteriorSymbol.symbolHom_sixth K S D hD)
    normI (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
    (ExteriorArithmetic.one_le_natNorm K S)
    (ExteriorArithmetic.countConstant K) (ExteriorArithmetic.countConstant_pos K)
    (ExteriorArithmetic.linearNormCounting K S)
    (ExteriorSieve.quadraticSieveInput X) (ExteriorSieve.cubicSieveInput X.A D hD)
    eps heps
  exact ⟨C, hC, fun f => h (f.toFrozen K S D hD) rfl rfl⟩

/-- The same uniform source ledger with every local Gauss bound discharged
for the original finite Weyl coefficients. -/
theorem uniform_actual_source_energy_ledger (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Data K S,
      ∀ Z O H v ell Sexp B z T : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ b : SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S),
        AnnularSupport (f.toFrozen K S D hD) normI Z H v ell z
          (withActualLocalTables K S D b) →
        Z ^ (Sexp + B) ≤ normI (f.toFrozen K S D hD).chargeIdeal →
        Z ^ (O / 2) * (withActualLocalTables K S D b).energy
            (f.toFrozen K S D hD) normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell Sexp B z T + eps * (H + v + ell + z)) := by
  obtain ⟨C, hC, h⟩ := uniform_source_energy_ledger X eps heps
  refine ⟨C, hC, ?_⟩
  intro f Z O H v ell Sexp B z T hZ hH hv hell hz b hs hcharge
  exact h f Z O H v ell Sexp B z T hZ hH hv hell hz
    (withActualLocalTables K S D b) hs (primitiveLocalBounds K S D hD f b) hcharge

/-- The complete original ideal-row family, with a single prescribed
small-power loss.  Each frozen pair may use its own ordinary set, actual
digit vector and minimum ideal. -/
theorem uniform_family_source_energy_subpower
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell Sexp B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset (ExteriorPrime K S)) (rows : Finset (ExteriorIdeal K S)),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : ExteriorIdeal K S × ExteriorIdeal K S → Data K S)
        (family : ExteriorIdeal K S × ExteriorIdeal K S →
          SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)),
        FrozenFamilyAlignment coords base rows
          (fun pair => (data pair).toFrozen K S D hD) family →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport ((data pair).toFrozen K S D hD) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds ((data pair).toFrozen K S D hD) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (Sexp + B) ≤ normI ((data pair).toFrozen K S D hD).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI
          (fun pair => (data pair).toFrozen K S D hD) family rows *
            Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell Sexp B z T + eps) := by
  obtain ⟨C, hC, h⟩ := FrozenReduction.uniform_family_source_energy_subpower
    coords (ExteriorSymbol.symbolHom K S D hD)
    (ExteriorSymbol.symbol_mul_left K S D hD)
    (ExteriorSymbol.symbolHom_sixth K S D hD)
    normI (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
    (ExteriorArithmetic.countConstant K) (ExteriorArithmetic.linearNormCounting K S)
    (ExteriorSieve.quadraticSieveInput X) (ExteriorSieve.cubicSieveInput X.A D hD)
    W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z O H v ell Sexp B z T Rrad hZ hO hH hv hell hz hbudget
    base rows hpow hrad data family halign hs hlocal hcharge
  exact h Z O H v ell Sexp B z T Rrad hZ hO hH hv hell hz hbudget
    base rows hpow hrad (fun pair => (data pair).toFrozen K S D hD) family halign
    (fun _ _ => rfl) hs hlocal hcharge

/-- All local tables in the varying family are the actual residue Gauss
and Weyl tables; no primitive local estimate is an input to this endpoint. -/
theorem uniform_actual_family_source_energy_subpower
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell Sexp B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset (ExteriorPrime K S)) (rows : Finset (ExteriorIdeal K S)),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : ExteriorIdeal K S × ExteriorIdeal K S → Data K S)
        (family : ExteriorIdeal K S × ExteriorIdeal K S →
          SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)),
        FrozenFamilyAlignment coords base rows
          (fun pair => (data pair).toFrozen K S D hD)
          (fun pair => withActualLocalTables K S D (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport ((data pair).toFrozen K S D hD) normI Z H v ell z
            (withActualLocalTables K S D (family pair))) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (Sexp + B) ≤ normI ((data pair).toFrozen K S D hD).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI
          (fun pair => (data pair).toFrozen K S D hD)
          (fun pair => withActualLocalTables K S D (family pair)) rows *
            Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell Sexp B z T + eps) := by
  obtain ⟨C, hC, h⟩ := uniform_family_source_energy_subpower X W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z O H v ell Sexp B z T Rrad hZ hO hH hv hell hz hbudget
    base rows hpow hrad data family halign hs hcharge
  exact h Z O H v ell Sexp B z T Rrad hZ hO hH hv hell hz hbudget
    base rows hpow hrad data (fun pair => withActualLocalTables K S D (family pair))
    halign hs (fun pair _ => primitiveLocalBounds K S D hD (data pair) (family pair)) hcharge

/-- The terminal quarter-margin saving for the actual exterior-ideal
family.  All conductor, annular and common-kernel scale comparisons are
explicit in the statement and are quantified after the uniform constant. -/
theorem uniform_family_source_energy_power_saving
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ Sexp → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - Sexp - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps ≤ c / 4 →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset (ExteriorPrime K S)) (rows : Finset (ExteriorIdeal K S)),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : ExteriorIdeal K S × ExteriorIdeal K S → Data K S)
        (family : ExteriorIdeal K S × ExteriorIdeal K S →
          SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)),
        FrozenFamilyAlignment coords base rows
          (fun pair => (data pair).toFrozen K S D hD) family →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport ((data pair).toFrozen K S D hD) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds ((data pair).toFrozen K S D hD) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (Sexp + B) ≤ normI ((data pair).toFrozen K S D hD).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI
          (fun pair => (data pair).toFrozen K S D hD) family rows *
            Z ^ (squaredKernelExponent T v ell) ≤ C * Z ^ (F - c / 4) := by
  obtain ⟨C, hC, h⟩ := FrozenReduction.uniform_family_source_energy_power_saving
    coords (ExteriorSymbol.symbolHom K S D hD)
    (ExteriorSymbol.symbol_mul_left K S D hD)
    (ExteriorSymbol.symbolHom_sixth K S D hD)
    normI (ExteriorArithmetic.natNorm K S) (ExteriorArithmetic.normHom_natNorm K S)
    (ExteriorArithmetic.countConstant K) (ExteriorArithmetic.linearNormCounting K S)
    (ExteriorSieve.quadraticSieveInput X) (ExteriorSieve.cubicSieveInput X.A D hD)
    W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad
    hZ hH hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hHbound
    hmargin1 hmargin2 hconductor hretained hdelta htau hloss hbudget
    base rows hpow hrad data family halign hs hlocal hcharge
  exact h Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad
    hZ hH hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hHbound
    hmargin1 hmargin2 hconductor hretained hdelta htau hloss hbudget
    base rows hpow hrad (fun pair => (data pair).toFrozen K S D hD) family halign
    (fun _ _ => rfl) hs hlocal hcharge

/-- The final whole-family saving with actual local tables at every
frozen pair.  Arithmetic, counting, both sieves and primitive local scalar
bounds are supplied by the repository's proved providers. -/
theorem uniform_actual_family_source_energy_power_saving
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ Sexp → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - Sexp - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps ≤ c / 4 →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset (ExteriorPrime K S)) (rows : Finset (ExteriorIdeal K S)),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : ExteriorIdeal K S × ExteriorIdeal K S → Data K S)
        (family : ExteriorIdeal K S × ExteriorIdeal K S →
          SourceBlock (ExteriorPrime K S) (ExteriorIdeal K S)),
        FrozenFamilyAlignment coords base rows
          (fun pair => (data pair).toFrozen K S D hD)
          (fun pair => withActualLocalTables K S D (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport ((data pair).toFrozen K S D hD) normI Z H v ell z
            (withActualLocalTables K S D (family pair))) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (Sexp + B) ≤ normI ((data pair).toFrozen K S D hD).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI
          (fun pair => (data pair).toFrozen K S D hD)
          (fun pair => withActualLocalTables K S D (family pair)) rows *
            Z ^ (squaredKernelExponent T v ell) ≤ C * Z ^ (F - c / 4) := by
  obtain ⟨C, hC, h⟩ := uniform_family_source_energy_power_saving X W eps hW heps
  refine ⟨C, hC, ?_⟩
  intro Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad
    hZ hH hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hHbound
    hmargin1 hmargin2 hconductor hretained hdelta htau hloss hbudget
    base rows hpow hrad data family halign hs hcharge
  exact h Z F M N Nstar V bh delta O H v ell Sexp B z T Q z0 c tau Rrad
    hZ hH hO hS hB hell hv hz hQ hM hc hF hNstar hV hbh hz0 hHbound
    hmargin1 hmargin2 hconductor hretained hdelta htau hloss hbudget
    base rows hpow hrad data (fun pair => withActualLocalTables K S D (family pair))
    halign hs (fun pair _ => primitiveLocalBounds K S D hD (data pair) (family pair)) hcharge

#print axioms uniform_weighted_raw_hybrid_bound
#print axioms uniform_source_energy_ledger
#print axioms uniform_actual_source_energy_ledger
#print axioms uniform_family_source_energy_subpower
#print axioms uniform_actual_family_source_energy_subpower
#print axioms uniform_family_source_energy_power_saving
#print axioms uniform_actual_family_source_energy_power_saving

end HeckeSkeleton.LowFrozenCube.Exterior
