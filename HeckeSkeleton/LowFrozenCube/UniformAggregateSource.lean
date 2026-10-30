import HeckeSkeleton.LowFrozenCube.UniformSourceLedger
import HeckeSkeleton.LowFrozenCube.FrozenSupportExtension

/-!
# Original-row aggregation with a constant uniform in all frozen data

Every actual frozen pair may carry its own local digit vector, ordinary
subset, minimum ideal, and source coefficients. Only the prime coordinates
and symbol are fixed before the analytic constant. The exclusion support
may grow by the prime support of that pair's powerful factor; this does not
change its original row block or residual row.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical
open HeckeSkeleton.LowHybrid
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- Metadata identifying each varying local datum with its actual original
row block. These are equalities of data, not energy estimates. -/
structure FrozenFamilyAlignment
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (base : Finset ι) (rows : Finset A)
    (data : A × A → Data ι A) (family : A × A → SourceBlock ι A) : Prop where
  coordinates : ∀ pair ∈ frozenRowPairs coords base rows, (data pair).coords = coords
  support : ∀ pair ∈ frozenRowPairs coords base rows,
    (data pair).support = extendedFrozenSupport coords base pair.1
  original_rows : ∀ pair ∈ frozenRowPairs coords base rows, (family pair).rows = rows
  powerful : ∀ pair ∈ frozenRowPairs coords base rows, (family pair).pow = pair.1
  supported : ∀ pair ∈ frozenRowPairs coords base rows, (family pair).sup = pair.2

def varyingFamilySourceRow
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (base : Finset ι) (normI : A → ℝ)
    (data : A × A → Data ι A) (family : A × A → SourceBlock ι A) (k : A) : ℂ :=
  let pair := (powerfulRowFactor coords k, supportedRowFactor coords base k)
  let D := data pair
  let b := family pair
  D.rawSourceRow normI b.first b.prefactor b.atZero b.phase b.a₀ b.ρ₀
    (annularColumn normI b.lam) b.marks b.columns b.inputs
    (residualRowFactor coords base k)

def varyingFamilySourceEnergy
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (base : Finset ι) (normI : A → ℝ)
    (data : A × A → Data ι A) (family : A × A → SourceBlock ι A) (rows : Finset A) : ℝ :=
  ∑ k ∈ rows, ‖varyingFamilySourceRow coords base normI data family k‖ ^ 2

/-- The exact positive partition remains valid while the local exclusion
support varies with the powerful factor of each block. -/
theorem varyingFamilySourceEnergy_eq_blocks
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (base : Finset ι) (normI : A → ℝ)
    (data : A × A → Data ι A) (family : A × A → SourceBlock ι A) (rows : Finset A)
    (hf : FrozenFamilyAlignment coords base rows data family) :
    varyingFamilySourceEnergy coords base normI data family rows =
      ∑ pair ∈ frozenRowPairs coords base rows, (family pair).energy (data pair) normI := by
  unfold varyingFamilySourceEnergy
  rw [sum_rows_eq_frozen_blocks coords base rows]
  apply Finset.sum_congr rfl
  intro pair hpair
  simp only [SourceBlock.energy, Data.rawBlockSourceEnergy,
    hf.original_rows pair hpair, hf.powerful pair hpair, hf.supported pair hpair,
    hf.coordinates pair hpair, hf.support pair hpair, rowBlock_extended]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  have hpair' : (powerfulRowFactor coords k, supportedRowFactor coords base k) = pair :=
    Prod.ext hk'.1 hk'.2
  simp only [varyingFamilySourceRow, hpair']
  rw [residualRowFactor_extended coords base k pair.1 hk'.1]

/-- A single constant controls every finite family of frozen source
blocks. Each datum is quantified after the constant; no uniform energy
bound for those data is an input. -/
theorem uniform_aggregate_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).coords = coords) →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        (∑ pair ∈ frozenRowPairs coords base rows, (family pair).energy (data pair) normI) *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
  obtain ⟨Cs, hCs, hsource⟩ := uniform_source_energy_ledger coords symbol hleft h6
    normI q hnatural hqpos Ccount hCcount hcount hq hc eps heps
  obtain ⟨Cr, hCr, hrowcount⟩ := frozen_row_pair_count_small_power coords normI q
    hnatural Ccount hCcount hqpos hcount eta heta
  have hnorm := one_le_real_norm_of_natural q normI hnatural hqpos
  refine ⟨Cs * Cr, mul_pos hCs hCr, ?_⟩
  intro Z O H v ell S B z T Rrad hZ hO hH hv hell hz base rows hpow hrad
    data family hcoords hsymbol hs hlocal hcharge
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hOp : 0 < Z ^ (O / 2) := Real.rpow_pos_of_pos hZpos _
  have hOn : 0 ≤ Z ^ O := Real.rpow_nonneg hZ0 _
  have hroot : Real.sqrt (Z ^ O) = Z ^ (O / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ0]
    congr 1
    ring
  have hradpow : (Z ^ O * normI (PrimeArithmetic.fromSupport coords base)) ^ eta ≤
      Z ^ (eta * (O + Rrad)) := by
    calc
      _ ≤ (Z ^ O * Z ^ Rrad) ^ eta := Real.rpow_le_rpow
        (mul_nonneg hOn (le_trans zero_le_one (hnorm _)))
        (mul_le_mul_of_nonneg_left hrad hOn) (le_of_lt heta)
      _ = _ := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_mul hZ0]
        congr 1
        ring
  have hcard : ((frozenRowPairs coords base rows).card : ℝ) ≤
      Cr * Z ^ (O / 2) * Z ^ (eta * (O + Rrad)) := by
    have h := hrowcount (Z ^ O) (Real.one_le_rpow hZ hO) base rows hpow
    rw [hroot] at h
    exact h.trans (mul_le_mul_of_nonneg_left hradpow
      (mul_nonneg (le_of_lt hCr) (le_of_lt hOp)))
  apply (mul_le_mul_iff_of_pos_left hOp).mp
  calc
    Z ^ (O / 2) *
        ((∑ pair ∈ frozenRowPairs coords base rows, (family pair).energy (data pair) normI) *
          Z ^ (squaredKernelExponent T v ell)) =
        ∑ pair ∈ frozenRowPairs coords base rows,
          Z ^ (O / 2) * (family pair).energy (data pair) normI *
            Z ^ (squaredKernelExponent T v ell) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ _pair ∈ frozenRowPairs coords base rows,
        Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z)) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact hsource (data pair) (hcoords pair hpair) (hsymbol pair hpair)
        Z O H v ell S B z T hZ hH hv hell hz (family pair)
        (hs pair hpair) (hlocal pair hpair) (hcharge pair hpair)
    _ = ((frozenRowPairs coords base rows).card : ℝ) *
        (Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z))) := by simp
    _ ≤ (Cr * Z ^ (O / 2) * Z ^ (eta * (O + Rrad))) *
        (Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z))) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (le_of_lt hCs) (Real.rpow_nonneg hZ0 _))
    _ = Z ^ (O / 2) *
        ((Cs * Cr) * Z ^ (reflectedExponent O H v ell S B z T +
          eps * (H + v + ell + z) + eta * (O + Rrad))) := by
      simp only [Real.rpow_add hZpos]
      ring

/-- The uniform bound applies to the literal original row energy with a
different valid local datum at each actual frozen pair. Powerful-prime
exclusions are reconciled by the proved row-block identity. -/
theorem uniform_family_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
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
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
  obtain ⟨C, hC, hb⟩ := uniform_aggregate_source_energy_ledger coords symbol hleft h6
    normI q hnatural hqpos Ccount hCcount hcount hq hc eps eta heps heta
  refine ⟨C, hC, ?_⟩
  intro Z O H v ell S B z T Rrad hZ hO hH hv hell hz base rows hpow hrad
    data family hf hsymbol hs hlocal hcharge
  rw [varyingFamilySourceEnergy_eq_blocks coords base normI data family rows hf]
  exact hb Z O H v ell S B z T Rrad hZ hO hH hv hell hz base rows hpow hrad
    data family hf.coordinates hsymbol hs hlocal hcharge

#print axioms varyingFamilySourceEnergy_eq_blocks
#print axioms uniform_aggregate_source_energy_ledger
#print axioms uniform_family_source_energy_ledger

end
end HeckeSkeleton.LowFrozenCube.FrozenReduction
