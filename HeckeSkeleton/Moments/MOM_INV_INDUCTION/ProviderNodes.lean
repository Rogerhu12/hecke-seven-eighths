import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildren
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectors
import HeckeSkeleton.Moments.MOM_INV_STEP.SourceLengths
import HeckePort.Moments.Descent.Basic

/-!
# The actual induction class

A node contains the literal canonical family, frozen puncture triple,
finite ideal-sector rows, and finite squarefree labels. Its energy is
defined by the provider's `normalizedChildEnergy`; it is not a supplied
real number. The admissibility predicate records the full column pool,
the actual test support, arithmetic source conditions, and the two
descent margins.

The individual mark lengths and prime windows remain attached to the
original slots. Restricting the surviving slots preserves these data and
their total budget. In particular, a child is not allowed to replace
the original prime coefficients by arbitrary divisor-bounded weights.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable {σ : Type*}

/-- The fixed annular original prime windows and their individual
coefficients. `lo` and `hi` are fixed support constants, not node data. -/
structure MarkConditions (slotCap : ℕ) (Z z lo hi : ℝ)
    (slots : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
    (weights : σ → Ideal (𝓞 K) → ℂ) (lengths : σ → ℝ) : Prop where
  card_le : slots.card ≤ slotCap
  length_nonneg : ∀ i ∈ slots, 0 ≤ lengths i
  total_length : (∑ i ∈ slots, lengths i) ≤ z
  prime : ∀ i ∈ slots, ∀ p ∈ lists i, Prime p
  exterior : ∀ i ∈ slots, ∀ p ∈ lists i, IsExterior K Sset p
  norm_window : ∀ i ∈ slots, ∀ p ∈ lists i,
    lo * Z ^ lengths i ≤ (p.absNorm : ℝ) ∧ (p.absNorm : ℝ) ≤ hi * Z ^ lengths i
  weights_le : ∀ i ∈ slots, ∀ p ∈ lists i, ‖weights i p‖ ≤ 1
  disjoint : ∀ i ∈ slots, ∀ j ∈ slots, i ≠ j → Disjoint (lists i) (lists j)

namespace MarkConditions

variable {K S}

/-- Slot restriction uses the same prime windows, exponents, and
individual coefficients, with no new source hypothesis. -/
theorem restrict {slotCap : ℕ} {Z z lo hi : ℝ}
    {A B : Finset σ} {lists : σ → Finset (Ideal (𝓞 K))}
    {weights : σ → Ideal (𝓞 K) → ℂ} {lengths : σ → ℝ}
    (h : MarkConditions K S slotCap Z z lo hi A lists weights lengths)
    (hBA : B ⊆ A) :
    MarkConditions K S slotCap Z z lo hi B lists weights lengths where
  card_le := (Finset.card_le_card hBA).trans h.card_le
  length_nonneg := fun i hi => h.length_nonneg i (hBA hi)
  total_length := (Finset.sum_le_sum_of_subset_of_nonneg hBA
    (fun i hi _ => h.length_nonneg i hi)).trans h.total_length
  prime := fun i hi => h.prime i (hBA hi)
  exterior := fun i hi => h.exterior i (hBA hi)
  norm_window := fun i hi => h.norm_window i (hBA hi)
  weights_le := fun i hi => h.weights_le i (hBA hi)
  disjoint := fun i hi j hj => h.disjoint i (hBA hi) j (hBA hj)

end MarkConditions

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)

/-- Only actual canonical data are stored. There is no energy field,
terminal estimate, or one-step estimate in a node. -/
structure Node (σ : Type*) where
  family : ColumnFamily K Sset σ Θ ψ
  triple : OuterTriple K
  labels : Finset (Ideal (𝓞 K))
  rows : Finset (Ideal (𝓞 K) × Sector)
  rowLength : ℝ
  labelLength : ℝ
  markLengths : σ → ℝ

variable {K S Γ Θ ψ}

namespace Node

def columnLength (x : Node K S Γ Θ ψ σ) : ℝ := x.family.columnLength x.triple
def totalLength (x : Node K S Γ Θ ψ σ) : ℝ := x.columnLength + x.labelLength
def puncture (x : Node K S Γ Θ ψ σ) : Ideal (𝓞 K) :=
  childPuncture x.family.originalPuncture x.triple
def punctureLength (Z : ℝ) (x : Node K S Γ Θ ψ σ) : ℝ :=
  Real.logb Z (Ideal.absNorm x.puncture.radical : ℝ)
def test (x : Node K S Γ Θ ψ σ) : SchwartzMap ℝ ℂ := x.family.cutoff x.triple

variable (D : ThetaArithmeticData K Sset)

def energy (slotCap : ℕ) (x : Node K S Γ Θ ψ σ) : ℝ :=
  normalizedChildEnergy x.family.base x.columnLength x.labelLength slotCap x.labels x.rows
    (childValue K Sset D x.family (CanonicalSectors.sectorUnit K Sset Γ)) x.triple

theorem energy_nonneg (slotCap : ℕ) (x : Node K S Γ Θ ψ σ)
    (hbase : 0 ≤ x.family.base) :
    0 ≤ x.energy D slotCap := by
  unfold energy normalizedChildEnergy
  apply mul_nonneg (Real.rpow_nonneg hbase _)
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (labelDivisorWeight_nonneg slotCap f)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

variable (Λ G : HeckeCharacter K) (slotCap : ℕ) (Z A c z lo hi : ℝ)

/-- The universal induction class for the complete actual canonical
energy. The puncture exponent is computed from its genuine radical. -/
structure Admissible (x : Node K S Γ Θ ψ σ) : Prop where
  base_eq : x.family.base = Z
  row_nonneg : 0 ≤ x.rowLength
  column_nonneg : 0 ≤ x.columnLength
  label_nonneg : 0 ≤ x.labelLength
  total_le : x.totalLength ≤ A
  complete_pool : x.family.columns x.triple =
    squarefreePool K Sset (2 * Z ^ x.columnLength)
  test_support : tsupport x.test ⊆ Set.Icc (1 : ℝ) 2
  label_squarefree : ∀ f ∈ x.labels, Squarefree f
  label_bound : ∀ f ∈ x.labels, (f.absNorm : ℝ) ≤ Z ^ x.labelLength
  row_bound : ∀ r ∈ x.rows, (r.1.absNorm : ℝ) ≤ Z ^ x.rowLength
  puncture_nonzero : x.puncture ≠ 0
  lambda_eq : x.family.lambda = Λ
  calibration : ThetaCalibrationInput K Sset D x.family.lambda G
  background_unramified : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset →
    UnramifiedAt K (x.family.background x.triple) p
  marks : MarkConditions K S slotCap Z z lo hi (x.family.survivors x.triple)
    x.family.primeLists x.family.primeWeights x.markLengths
  margins : HeckePort.Moments.CanonicalMargins x.totalLength x.rowLength
    (x.punctureLength Z) z c

variable {D Λ G slotCap Z A c z lo hi}

theorem Admissible.puncture_norm (x : Node K S Γ Θ ψ σ)
    (hx : x.Admissible D Λ G slotCap Z A c z lo hi) (hZ : 1 < Z) :
    (Ideal.absNorm x.puncture.radical : ℝ) = Z ^ x.punctureLength Z := by
  have hn : 0 < Ideal.absNorm x.puncture.radical := Nat.pos_of_ne_zero
    (fun he => SourceLengths.radical_ne_zero _ hx.puncture_nonzero
      (Ideal.absNorm_eq_zero_iff.mp he))
  exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (by exact_mod_cast hn)).symm

theorem Admissible.puncture_nonneg (x : Node K S Γ Θ ψ σ)
    (hx : x.Admissible D Λ G slotCap Z A c z lo hi) (hZ : 1 < Z) :
    0 ≤ x.punctureLength Z := by
  apply Real.logb_nonneg hZ
  have hn : 0 < Ideal.absNorm x.puncture.radical := Nat.pos_of_ne_zero
    (fun he => SourceLengths.radical_ne_zero _ hx.puncture_nonzero
      (Ideal.absNorm_eq_zero_iff.mp he))
  exact_mod_cast hn

/-- All individual scalar lengths required by the one-step theorem
are bounded by the same fixed capacity. -/
theorem Admissible.lengths_le (x : Node K S Γ Θ ψ σ)
    (hx : x.Admissible D Λ G slotCap Z A c z lo hi) (hZ : 1 < Z)
    (hc : 0 ≤ c) (hz : 0 ≤ z) :
    x.rowLength ≤ A ∧ x.columnLength ≤ A ∧ x.labelLength ≤ A := by
  have hQ := Admissible.puncture_nonneg x hx hZ
  have hm := hx.margins.1
  have ht := hx.total_le
  have hn := hx.column_nonneg
  have hv := hx.label_nonneg
  change x.columnLength + x.labelLength ≤ A at ht
  change c ≤ x.columnLength + x.labelLength - x.rowLength - x.punctureLength Z - z at hm
  constructor
  · linarith
  constructor <;> linarith

end Node

/-- A stage bound quantifies over actual nodes. The finite seminorm
and the constant are selected before the family, scale, slots, frozen
triple, row set, label set, or profile vary. -/
def UniformBound (D : ThetaArithmeticData K Sset) (Λ G : HeckeCharacter K)
    (slotCap : ℕ) (Z A c z lo hi eps R C : ℝ) (t : Finset (ℕ × ℕ)) : Prop :=
  ∀ {σ : Type*} (x : Node K S Γ Θ ψ σ),
    x.Admissible D Λ G slotCap Z A c z lo hi → x.rowLength ≤ R →
    x.energy D slotCap ≤ C * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) x.test) ^ 2 *
      Z ^ (x.totalLength + eps)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes

end
