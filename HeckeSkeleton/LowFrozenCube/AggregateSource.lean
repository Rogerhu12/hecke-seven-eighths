import HeckeSkeleton.LowFrozenCube.TerminalSource
import HeckeSkeleton.LowFrozenCube.FrozenPartition

/-!
# Actual frozen row blocks are summed with the powerful cost paid once

The index set is the finite image of the original rows under their actual
powerful and supported factors. The counting theorem is proved from prime
coordinates and ideal counting. Its square-root factor cancels the factor
already present in the single-block source ledger. A separate exact identity
identifies the resulting block sum with the original row energy.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

def familySourceRow (normI : A → ℝ) (family : A × A → SourceBlock ι A) (k : A) : ℂ :=
  let b := family (PrimeCoordinates.powerfulRowFactor D.coords k,
    PrimeCoordinates.supportedRowFactor D.coords D.support k)
  D.rawSourceRow normI b.first b.prefactor b.atZero b.phase b.a₀ b.ρ₀
    (annularColumn normI b.lam) b.marks b.columns b.inputs
    (PrimeCoordinates.residualRowFactor D.coords D.support k)

def familySourceEnergy (normI : A → ℝ) (family : A × A → SourceBlock ι A)
    (rows : Finset A) : ℝ :=
  ∑ k ∈ rows, ‖D.familySourceRow normI family k‖ ^ 2

/-- Exact positive partition of the original energy. Coefficients and local
input sets may depend on the frozen pair, while each family member uses the
same original row set and its actual prescribed pair. -/
theorem familySourceEnergy_eq_blocks (normI : A → ℝ)
    (family : A × A → SourceBlock ι A) (rows : Finset A)
    (hfamily : ∀ pair ∈ frozenRowPairs D.coords D.support rows,
      (family pair).rows = rows ∧ (family pair).pow = pair.1 ∧ (family pair).sup = pair.2) :
    D.familySourceEnergy normI family rows =
      ∑ pair ∈ frozenRowPairs D.coords D.support rows, (family pair).energy D normI := by
  unfold familySourceEnergy
  rw [sum_rows_eq_frozen_blocks D.coords D.support rows]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hf := hfamily pair hpair
  unfold SourceBlock.energy rawBlockSourceEnergy
  rw [hf.1, hf.2.1, hf.2.2]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  have hpair' : (PrimeCoordinates.powerfulRowFactor D.coords k,
      PrimeCoordinates.supportedRowFactor D.coords D.support k) = pair :=
    Prod.ext hk'.1 hk'.2
  simp only [familySourceRow, hpair']

/-- The actual finite sum of source blocks obeys the reflected ledger. The
powerful exponent `O / 2` occurs once: the proved frozen-pair count cancels
the scalar already on the left of `source_energy_ledger`.
-/
theorem aggregate_source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (PrimeCoordinates.powerfulRowFactor D.coords k) ≤ Z ^ O) →
        normI (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport D.coords D.support) ≤ Z ^ Rrad →
      ∀ family : A × A → SourceBlock ι A,
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          AnnularSupport D normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          PrimitiveLocalBounds D normI (family pair)) →
        Z ^ (S + B) ≤ normI D.chargeIdeal →
        (∑ pair ∈ frozenRowPairs D.coords D.support rows,
          (family pair).energy D normI) * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
  obtain ⟨Cs, hCs, hsource⟩ := D.source_energy_ledger normI q hnatural hqpos
    Ccount hCcount hcount hq hc eps heps
  obtain ⟨Cr, hCr, hrowcount⟩ := frozen_row_pair_count_small_power D.coords normI q
    hnatural Ccount hCcount hqpos hcount eta heta
  have hnorm := HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural q normI hnatural hqpos
  refine ⟨Cs * Cr, mul_pos hCs hCr, ?_⟩
  intro Z O H v ell S B z T Rrad hZ hO hH hv hell hz rows hpow hrad family hs hlocal hcharge
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hOp : 0 < Z ^ (O / 2) := Real.rpow_pos_of_pos hZpos _
  have hOn : 0 ≤ Z ^ O := Real.rpow_nonneg hZ0 _
  have hroot : Real.sqrt (Z ^ O) = Z ^ (O / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ0]
    congr 1
    ring
  have hradpow : (Z ^ O * normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport D.coords D.support)) ^ eta ≤
      Z ^ (eta * (O + Rrad)) := by
    calc
      _ ≤ (Z ^ O * Z ^ Rrad) ^ eta :=
        Real.rpow_le_rpow
          (mul_nonneg hOn (le_trans zero_le_one (hnorm _)))
          (mul_le_mul_of_nonneg_left hrad hOn) (le_of_lt heta)
      _ = _ := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_mul hZ0]
        congr 1
        ring
  have hcard : ((frozenRowPairs D.coords D.support rows).card : ℝ) ≤
      Cr * Z ^ (O / 2) * Z ^ (eta * (O + Rrad)) := by
    have h := hrowcount (Z ^ O) (Real.one_le_rpow hZ hO) D.support rows hpow
    rw [hroot] at h
    exact h.trans (mul_le_mul_of_nonneg_left hradpow
      (mul_nonneg (le_of_lt hCr) (le_of_lt hOp)))
  apply (mul_le_mul_iff_right₀ hOp).mp
  calc
    Z ^ (O / 2) *
        ((∑ pair ∈ frozenRowPairs D.coords D.support rows,
          (family pair).energy D normI) * Z ^ (squaredKernelExponent T v ell)) =
        ∑ pair ∈ frozenRowPairs D.coords D.support rows,
          Z ^ (O / 2) * (family pair).energy D normI *
            Z ^ (squaredKernelExponent T v ell) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ _pair ∈ frozenRowPairs D.coords D.support rows,
        Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z)) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact hsource Z O H v ell S B z T hZ hH hv hell hz
        (family pair) (hs pair hpair) (hlocal pair hpair) hcharge
    _ = ((frozenRowPairs D.coords D.support rows).card : ℝ) *
        (Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z))) := by
      simp
    _ ≤ (Cr * Z ^ (O / 2) * Z ^ (eta * (O + Rrad))) *
        (Cs * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z))) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (le_of_lt hCs) (Real.rpow_nonneg hZ0 _))
    _ = Z ^ (O / 2) *
        ((Cs * Cr) * Z ^ (reflectedExponent O H v ell S B z T +
          eps * (H + v + ell + z) + eta * (O + Rrad))) := by
      simp only [Real.rpow_add hZpos]
      ring

/-- The same uniform ledger for the original row energy itself. This uses
the exact partition rather than introducing another Cauchy--Schwarz cost. -/
theorem family_source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (PrimeCoordinates.powerfulRowFactor D.coords k) ≤ Z ^ O) →
        normI (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport D.coords D.support) ≤ Z ^ Rrad →
      ∀ family : A × A → SourceBlock ι A,
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          (family pair).rows = rows ∧ (family pair).pow = pair.1 ∧ (family pair).sup = pair.2) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          AnnularSupport D normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          PrimitiveLocalBounds D normI (family pair)) →
        Z ^ (S + B) ≤ normI D.chargeIdeal →
        D.familySourceEnergy normI family rows * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
  obtain ⟨C, hC, hb⟩ := D.aggregate_source_energy_ledger normI q hnatural hqpos
    Ccount hCcount hcount hq hc eps eta heps heta
  refine ⟨C, hC, ?_⟩
  intro Z O H v ell S B z T Rrad hZ hO hH hv hell hz rows hpow hrad family
    hfamily hs hlocal hcharge
  rw [D.familySourceEnergy_eq_blocks normI family rows hfamily]
  exact hb Z O H v ell S B z T Rrad hZ hO hH hv hell hz rows hpow hrad family hs hlocal hcharge

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
