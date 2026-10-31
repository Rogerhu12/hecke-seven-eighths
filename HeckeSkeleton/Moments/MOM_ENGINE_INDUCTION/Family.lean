import HeckeGeneral.Analysis.MomentInputs

/-!
# Actual source families for the fourth-moment induction

The expansion index and the finite sector type are parameters.  This keeps
the induction independent of the unfinished construction `highExpansion` in
the exploratory skeleton.  Every energy below is the original finite
`pairedEnergy` from `MomentInputs`; no energy estimate is a field.

The shell, selected slots, plain lengths, capacity and quantifier order are
the ones used by `HeckeSkeleton.Moments`.  The only data specialization is
that the model's external heights have already been evaluated.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped BigOperators Classical

universe u v

variable (K : Type) [Field K] [NumberField K]

/-- Source data for the actual selected-slot polynomials.  `Index` may be
the index of any one fixed expansion; it is not chosen after an estimate.
`Sector` is one fixed finite type for the whole scale family. -/
structure SourceFamily (ω ψ : HeckeCharacter K)
    (Index : ℝ → ℝ → Type u) (Sector : Type v) where
  slots : ℕ
  kappa : ℝ
  mesh : ℝ
  loss : ℝ
  shell : ∀ Z T, Index Z T → ℝ
  bin : ∀ Z T, Index Z T → ℝ
  plainLength : ∀ Z T, Index Z T → ℝ
  selected : ∀ Z T, Index Z T → Finset (Fin slots)
  noSlots : ∀ Z T, Index Z T → Index Z T
  noSlots_shell : ∀ Z T i, shell Z T (noSlots Z T i) = shell Z T i
  noSlots_bin : ∀ Z T i, bin Z T (noSlots Z T i) = bin Z T i
  noSlots_plainLength : ∀ Z T i,
    plainLength Z T (noSlots Z T i) = plainLength Z T i
  noSlots_selected : ∀ Z T i, selected Z T (noSlots Z T i) = ∅
  model : ∀ Z T, Index Z T → Sector → MomentData K ω ψ

namespace SourceFamily

variable {K} {ω ψ : HeckeCharacter K}
variable {Index : ℝ → ℝ → Type u} {Sector : Type v}
variable (F : SourceFamily K ω ψ Index Sector)

def base {Z T : ℝ} (i : Index Z T) : ℝ := Z ^ F.shell Z T i

/-- The source slot length `(1/6)/(J₀ d)`, at base `Z^d`. -/
def slotWidth {Z T : ℝ} (i : Index Z T) : ℝ :=
  (1 / 6) / (F.slots * F.shell Z T i)

def selectedLength {Z T : ℝ} (i : Index Z T) : ℝ :=
  ∑ _j ∈ F.selected Z T i, F.slotWidth i

/-- The exact seven source parameters, including the full dynamic kappa. -/
def parameters {Z T : ℝ} (i : Index Z T) : RealParameters :=
  ⟨1, 0, F.selectedLength i, 0,
    F.plainLength Z T i, F.plainLength Z T i, F.kappa⟩

/-- Source capacity, without imposing a restriction on the zero-slot
projection.  Its two conjuncts match `pairedCapacity` exactly. -/
def capacity {Z T : ℝ} (i : Index Z T) : Prop :=
  (∀ j ∈ F.selected Z T i, F.slotWidth i ≤ F.mesh) ∧
    2 * F.plainLength Z T i + 6 * F.kappa * F.selectedLength i ≤ 1

def positiveEligible {Z T : ℝ} (i : Index Z T) : Prop :=
  F.capacity i ∧ (F.selected Z T i).Nonempty

@[simp] theorem base_noSlots {Z T : ℝ} (i : Index Z T) :
    F.base (F.noSlots Z T i) = F.base i := by
  simp only [base, F.noSlots_shell]

@[simp] theorem selectedLength_noSlots {Z T : ℝ} (i : Index Z T) :
    F.selectedLength (F.noSlots Z T i) = 0 := by
  simp only [selectedLength, F.noSlots_selected, Finset.sum_empty]

@[simp] theorem parameters_noSlots_z {Z T : ℝ} (i : Index Z T) :
    (F.parameters (F.noSlots Z T i)).z = 0 := by
  exact F.selectedLength_noSlots i

@[simp] theorem parameters_noSlots_n₁ {Z T : ℝ} (i : Index Z T) :
    (F.parameters (F.noSlots Z T i)).n₁ = F.plainLength Z T i := by
  exact F.noSlots_plainLength Z T i

@[simp] theorem parameters_noSlots_n₂ {Z T : ℝ} (i : Index Z T) :
    (F.parameters (F.noSlots Z T i)).n₂ = F.plainLength Z T i := by
  exact F.noSlots_plainLength Z T i

variable [Fintype Sector]

/-- The original paired finite polynomial energy, summed over every sector. -/
def energy {Z T : ℝ} (i : Index Z T) : ℝ :=
  ∑ s : Sector, pairedEnergy (F.model Z T i s) (F.parameters i) (F.base i) 0

theorem energy_nonneg {Z T : ℝ} (i : Index Z T) : 0 ≤ F.energy i := by
  unfold energy pairedEnergy
  exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun u _ => sq_nonneg _

/-- Prime products for the same models, masks, row sets and selected slots. -/
def primeEnergy {Z T : ℝ} (i : Index Z T) : ℝ :=
  ∑ s : Sector,
    ∑ u ∈ pairedRows (F.model Z T i s) (F.parameters i) (F.base i),
      ‖slotProduct (F.model Z T i s) u (F.base i) 0‖ ^ 2

theorem primeEnergy_nonneg {Z T : ℝ} (i : Index Z T) : 0 ≤ F.primeEnergy i := by
  unfold primeEnergy
  exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun u _ => sq_nonneg _

/-- The height degree and ceiling precede tau; the threshold and scalar may
depend on fixed tau.  This is the source's `UniformMomentBound` order. -/
def UniformBound
    (E power : ∀ Z T, Index Z T → ℝ)
    (eligible : ∀ Z T, Index Z T → Prop) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
        51 / 100 < F.bin Z (Z ^ τ) i → eligible Z (Z ^ τ) i →
          E Z (Z ^ τ) i ≤
            C * F.base i ^ (power Z (Z ^ τ) i + F.loss) * (1 + Z ^ τ) ^ A

def ZeroSlotBound : Prop :=
  F.UniformBound (fun Z T i => F.energy (F.noSlots Z T i))
    (fun _ _ _ => 1) (fun _ _ _ => True)

def PositiveSlotBound : Prop :=
  F.UniformBound (fun _ _ i => F.energy i)
    (fun _ _ _ => 1) (fun _ _ i => F.positiveEligible i)

def PrimeProductBound (κ : ℝ) : Prop :=
  F.UniformBound (fun _ _ i => F.primeEnergy i)
    (fun _ _ i => 1 + κ * F.selectedLength i) (fun _ _ i => F.capacity i)

/-- Pointwise sector estimates with one set of constants for the entire
scale/index family and for all sectors.  `at` is either identity or the
source's zero-slot projection. -/
def SectorBound (at : ∀ Z T, Index Z T → Index Z T)
    (eligible : ∀ Z T, Index Z T → Prop) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ C : ℝ, 1 ≤ Z₀ ∧ 0 ≤ C ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
        51 / 100 < F.bin Z (Z ^ τ) i → eligible Z (Z ^ τ) i → ∀ s : Sector,
          pairedEnergy (F.model Z (Z ^ τ) (at Z (Z ^ τ) i) s)
            (F.parameters (at Z (Z ^ τ) i)) (F.base (at Z (Z ^ τ) i)) 0 ≤
            C * F.base i ^ (1 + F.loss) * (1 + Z ^ τ) ^ A

/-- Summing a common per-sector estimate introduces exactly the fixed
sector cardinality.  No index, height or tau dependence enters that factor. -/
theorem uniformBound_of_sectorBound
    (at : ∀ Z T, Index Z T → Index Z T)
    (eligible : ∀ Z T, Index Z T → Prop)
    (h : F.SectorBound at eligible) :
    F.UniformBound (fun Z T i => F.energy (at Z T i))
      (fun _ _ _ => 1) eligible := by
  obtain ⟨A, ceiling, hA, hc, hb⟩ := h
  refine ⟨A, ceiling, hA, hc, ?_⟩
  intro τ hτ hτc
  obtain ⟨Z₀, C, hZ₀, hC, hh⟩ := hb τ hτ hτc
  refine ⟨Z₀, (Fintype.card Sector : ℝ) * C, hZ₀, mul_nonneg (by positivity) hC, ?_⟩
  intro Z hZ i hbin helig
  calc
    F.energy (at Z (Z ^ τ) i) ≤
        ∑ _s : Sector, C * F.base i ^ (1 + F.loss) * (1 + Z ^ τ) ^ A :=
      Finset.sum_le_sum fun s _ => hh Z hZ i hbin helig s
    _ = (Fintype.card Sector : ℝ) * C * F.base i ^ (1 + F.loss) *
        (1 + Z ^ τ) ^ A := by simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]; ring

theorem zeroSlotBound_of_sectorBound
    (h : F.SectorBound F.noSlots (fun _ _ _ => True)) : F.ZeroSlotBound :=
  F.uniformBound_of_sectorBound F.noSlots (fun _ _ _ => True) h

theorem positiveSlotBound_of_sectorBound
    (h : F.SectorBound (fun _ _ i => i) (fun _ _ i => F.positiveEligible i)) :
    F.PositiveSlotBound :=
  F.uniformBound_of_sectorBound (fun _ _ i => i) (fun _ _ i => F.positiveEligible i) h

end SourceFamily

end HeckeSkeleton.Moments.EngineInduction
