import HeckeSkeleton.Moments.MOM_INV_INDUCTION.CanonicalEnergy
import HeckeSkeleton.LowCauchy.General

/-!
# Transport from the permitted physical completed-energy input

This adapter consumes exactly `LowCauchy.MarkedEnergy`, the general-data
form of the skeleton's `CompletedMarkedEnergy`.  It proves a finite-row
bound from an exact row-polynomial realization in the original marked physical
row family.  Its extra hypotheses are an exact polynomial identity,
injectivity of the original orbit map, a norm cutoff, and scalar bounds;
no canonical moment estimate is an input.

The realization is deliberately explicit.  The fixed physical Gaussian
statement does not construct realizations for arbitrary canonical
backgrounds, labels, punctures, or annular profiles.  Establishing those
identities, or supplying a broader reflected-energy theorem, remains the
source terminal obligation described in `STATEMENT_AUDIT.md`.

This file is separate from the numerical induction and its ordinary
audit, so importing that induction does not load the physical probe
closure.  `CompletedEnergyTransportAudit.lean` audits this adapter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (ψ : HeckeCharacter K)
variable (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))

/-- Algebraic realization of one canonical label's row polynomial in
the actual physical completed rows.  The selected tuple belongs to the
original prime windows, and the map retains the original sixth-unit
orbit space. -/
structure CompletedLabelRealization (B X Z A : ℝ)
    (d : CanonicalDatum K) (f : NonzeroIdeal K) where
  tuple : Fin g.slots → ExteriorPrime K S
  tuple_mem : tuple ∈ Fintype.piFinset (fun i => primeWindow K S g T X i)
  selected : Finset (Fin g.slots)
  rowMap : NonzeroIdeal K → HeckeSkeleton.Gram.Orbit K S
  rowMap_injective : Set.InjOn rowMap (d.rows : Set (NonzeroIdeal K))
  scalar : NonzeroIdeal K → ℂ
  scalar_bound : ∀ k ∈ d.rows, ‖scalar k‖ ≤ A
  row_bound : ∀ k ∈ d.rows,
    (sIntegerOrbitNorm K S (sixthPowerUnits K S) (rowMap k)).val ≤
      B * X ^ (5 / 6 : ℝ) /
        (exteriorNorm K S (subsetPrimeIdeal K S tuple selected)) ^ 2
  identity : ∀ k ∈ d.rows,
    d.columnValue Z k f = scalar k *
      HeckeSkeleton.LowCauchy.markedRow K S P ψ g T X tuple selected (rowMap k).out

namespace CompletedLabelRealization

variable {K S P ψ g T}
variable {B X Z A : ℝ} {d : CanonicalDatum K} {f : NonzeroIdeal K}

def selectedNorm (r : CompletedLabelRealization K S P ψ g T B X Z A d f) : ℝ :=
  exteriorNorm K S (subsetPrimeIdeal K S r.tuple r.selected)

/-- The actual bounded-orbit energy from the physical hypothesis. -/
def physicalEnergy (r : CompletedLabelRealization K S P ψ g T B X Z A d f) : ℝ :=
  ∑' u : HeckeSkeleton.Gram.Orbit K S,
    if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤
        B * X ^ (5 / 6 : ℝ) / r.selectedNorm ^ 2
    then ‖HeckeSkeleton.LowCauchy.markedRow K S P ψ g T X r.tuple r.selected u.out‖ ^ 2
    else 0

/-- Exact row reindexing and the scalar estimate reduce the literal
canonical label energy to the permitted physical energy.  The orbit-box
series is summable because its support is finite, as proved by
`lc_sum_le_tsum_orbit_box`; no convention for divergent real sums is used. -/
theorem labelEnergy_le_physicalEnergy
    (r : CompletedLabelRealization K S P ψ g T B X Z A d f) (hA : 0 ≤ A) :
    d.labelEnergy Z f ≤ A ^ 2 * r.physicalEnergy := by
  let rowValue : HeckeSkeleton.Gram.Orbit K S → ℂ := fun u =>
    HeckeSkeleton.LowCauchy.markedRow K S P ψ g T X r.tuple r.selected u.out
  have hrow (k : NonzeroIdeal K) (hk : k ∈ d.rows) :
      ‖d.columnValue Z k f‖ ^ 2 ≤ A ^ 2 * ‖rowValue (r.rowMap k)‖ ^ 2 := by
    rw [r.identity k hk, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) hA).mpr (r.scalar_bound k hk)) (sq_nonneg _)
  have hbox := HeckeSkeleton.LowCauchy.lc_sum_le_tsum_orbit_box K S
    (d.rows.image r.rowMap) (B * X ^ (5 / 6 : ℝ) / r.selectedNorm ^ 2)
    (fun u => ‖rowValue u‖ ^ 2) (fun _ => sq_nonneg _) (by
      intro u hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      exact r.row_bound k hk)
  calc
    d.labelEnergy Z f ≤ ∑ k ∈ d.rows, A ^ 2 * ‖rowValue (r.rowMap k)‖ ^ 2 :=
      Finset.sum_le_sum hrow
    _ = A ^ 2 * ∑ k ∈ d.rows, ‖rowValue (r.rowMap k)‖ ^ 2 :=
      (Finset.mul_sum ..).symm
    _ = A ^ 2 * ∑ u ∈ d.rows.image r.rowMap, ‖rowValue u‖ ^ 2 := by
      rw [Finset.sum_image r.rowMap_injective]
    _ ≤ A ^ 2 * r.physicalEnergy :=
      mul_le_mul_of_nonneg_left hbox (sq_nonneg _)

end CompletedLabelRealization

/-- One pair of physical constants works for every realized canonical
label, with independently chosen source scale and selected tuple. -/
theorem completedEnergy_label_transport
    (henergy : HeckeSkeleton.LowCauchy.MarkedEnergy K S P ψ g T)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (X Z A : ℝ), X₀ ≤ X → 0 ≤ A →
      ∀ (d : CanonicalDatum K) (f : NonzeroIdeal K)
        (r : CompletedLabelRealization K S P ψ g T B X Z A d f),
        d.labelEnergy Z f ≤ A ^ 2 * C * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2 := by
  obtain ⟨C, X₀, hC, hX₀, hb⟩ := henergy B ε hB hε
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X Z A hX hA d f r
  have hphysical : r.physicalEnergy ≤ C * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2 :=
    hb X hX r.tuple r.tuple_mem r.selected
  calc
    d.labelEnergy Z f ≤ A ^ 2 * r.physicalEnergy := r.labelEnergy_le_physicalEnergy hA
    _ ≤ A ^ 2 * (C * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2) :=
      mul_le_mul_of_nonneg_left hphysical (sq_nonneg _)
    _ = _ := by ring

/-- Combine the completed-energy input with exact row realizations and
purely numerical scale bounds, then cancel the actual label mass once.
The scale hypothesis contains no canonical energy and no row norm sum. -/
theorem completedEnergy_normalized_transport
    (henergy : HeckeSkeleton.LowCauchy.MarkedEnergy K S P ψ g T)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ 1 ≤ X₀ ∧
      ∀ (d : CanonicalDatum K) (Z δ R L p : ℝ), 1 ≤ Z → 0 ≤ R →
      (∑ f ∈ d.labels, d.labelWeight f ≤ L * Z ^ (d.labelLength + δ)) →
      (∀ f ∈ d.labels, ∃ X A : ℝ, X₀ ≤ X ∧ 0 ≤ A ∧
        ∃ r : CompletedLabelRealization K S P ψ g T B X Z A d f,
          A ^ 2 * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2 ≤ R * Z ^ p) →
      d.energy Z ≤ (C * R * L) * Z ^ (p + δ) := by
  obtain ⟨C, X₀, hC, hX₀, hlabel⟩ :=
    completedEnergy_label_transport K S P ψ g T henergy B ε hB hε
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro d Z δ R L p hZ hR hmass hreal
  apply normalized_label_energy_le d.labels d.labelWeight (d.labelEnergy Z)
    hZ (mul_nonneg hC.le hR) d.labelWeight_nonneg hmass
  intro f hf
  obtain ⟨X, A, hX, hA, r, hscale⟩ := hreal f hf
  calc
    d.labelEnergy Z f ≤ A ^ 2 * C * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2 :=
      hlabel X Z A hX hA d f r
    _ = C * (A ^ 2 * X ^ (5 / 6 + ε) / r.selectedNorm ^ 2) := by ring
    _ ≤ C * (R * Z ^ p) := mul_le_mul_of_nonneg_left hscale hC.le
    _ = (C * R) * Z ^ p := by ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
