import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAllocationFingerprint
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FiniteBranchIndex

/-!
# The two-divisor arithmetic carrier computed from original finite labels

The input here consists only of projections from the actual retained
source labels. Every arithmetic support is an image of those labels,
with its preceding coordinates fixed. The engine therefore constructs
the harmonic carrier and its map; no preassembled branch, admissible
carrier, or total mass estimate is supplied as source data.

Both padded occurrence allocations are kept literally. The image carrier
may contain compatible recombinations, but the actual map never changes
an original coordinate. Such extra positive terms are harmless for the
harmonic estimate, and actual fibres are counted separately.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField UniqueFactorizationMonoid CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {I : Type*} [Fintype I] {cap : ℕ}

/-- Coordinate projections of the same original finite source carrier.
There are no analytical estimates in this dictionary. -/
structure OriginalArithmeticLabels (K : Type) [Field K] [NumberField K]
    (I : Type*) (cap : ℕ) where
  first : I → Label K
  firstDivisor : I → Ideal (𝓞 K)
  second : I → Label K
  allocation : I → OriginalAllocationFingerprint K cap

namespace OriginalArithmeticLabels

variable (L : OriginalArithmeticLabels K I cap)

def firstLabels : Finset (Label K) := Finset.univ.image L.first

def firstDivisors (v : Label K) : Finset (Ideal (𝓞 K)) :=
  (Finset.univ.filter (fun i => L.first i = v)).image L.firstDivisor

def secondLabels (v : Label K) (S : Ideal (𝓞 K)) : Finset (Label K) :=
  (Finset.univ.filter (fun i => L.first i = v ∧ L.firstDivisor i = S)).image L.second

def secondDivisors (v : Label K) (S : Ideal (𝓞 K)) (w : Label K) :
    Finset (Ideal (𝓞 K)) :=
  (Finset.univ.filter (fun i =>
    L.first i = v ∧ L.firstDivisor i = S ∧ L.second i = w)).image
      (fun i => (L.allocation i).1)

/-- All four finite supports are computed from the original projections.
The two occurrence counts include the two distinct plain occurrences. -/
def carrier : TwoDivisorCommonBranch (K := K) where
  first := L.firstLabels
  firstDivisors := L.firstDivisors
  second := L.secondLabels
  secondDivisors := L.secondDivisors
  leftOccurrences := fun _ _ _ _ => cap + 2
  rightOccurrences := fun _ _ _ _ => cap + 2

theorem first_mem (i : I) : L.first i ∈ L.carrier.first :=
  Finset.mem_image_of_mem L.first (Finset.mem_univ i)

theorem firstDivisor_mem (i : I) :
    L.firstDivisor i ∈ L.carrier.firstDivisors (L.first i) :=
  Finset.mem_image_of_mem L.firstDivisor
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)

theorem second_mem (i : I) :
    L.second i ∈ L.carrier.second (L.first i) (L.firstDivisor i) :=
  Finset.mem_image_of_mem L.second
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl, rfl⟩)

theorem secondDivisor_mem (i : I) :
    (L.allocation i).1 ∈ L.carrier.secondDivisors
      (L.first i) (L.firstDivisor i) (L.second i) :=
  Finset.mem_image_of_mem (fun j => (L.allocation j).1)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl, rfl, rfl⟩)

/-- The actual source map retains all four arithmetic labels and both
complete original padded allocation functions. -/
def index (i : I) : L.carrier.Index :=
  ⟨⟨L.first i, L.first_mem i⟩,
    ⟨L.firstDivisor i, L.firstDivisor_mem i⟩,
    ⟨L.second i, L.second_mem i⟩,
    ⟨(L.allocation i).1, L.secondDivisor_mem i⟩,
    (L.allocation i).2⟩

def indexAllocation (j : L.carrier.Index) : OriginalAllocationFingerprint K cap :=
  ⟨j.2.2.2.1.val, j.2.2.2.2⟩

@[simp] theorem index_first (i : I) : (L.index i).1.val = L.first i := rfl

@[simp] theorem index_firstDivisor (i : I) :
    (L.index i).2.1.val = L.firstDivisor i := rfl

@[simp] theorem index_second (i : I) : (L.index i).2.2.1.val = L.second i := rfl

@[simp] theorem index_allocation (i : I) :
    L.indexAllocation (L.index i) = L.allocation i := rfl

/-- Equality in the computed arithmetic carrier preserves the actual
common pair and the actual full allocation. These are the identities
used by the physical-source fibre estimate. -/
theorem index_eq_coordinates {i j : I} (h : L.index i = L.index j) :
    L.first i = L.first j ∧ L.firstDivisor i = L.firstDivisor j ∧
      L.second i = L.second j ∧ L.allocation i = L.allocation j := by
  refine ⟨congrArg (fun z : L.carrier.Index => z.1.val) h,
    congrArg (fun z : L.carrier.Index => z.2.1.val) h,
    congrArg (fun z : L.carrier.Index => z.2.2.1.val) h, ?_⟩
  exact congrArg L.indexAllocation h

/-- The literal harmonic weight, with the two independent divisors in
their original positions. Padding does not change either weight. -/
theorem indexWeight_eq (i : I) :
    L.carrier.indexWeight (L.index i) =
      (1 / (Ideal.absNorm (commonRadical (L.first i).1.1 (L.first i).1.2) : ℝ)) *
        ‖(moebius (L.firstDivisor i) : ℂ)‖ *
        (1 / (Ideal.absNorm (commonRadical (L.second i).1.1 (L.second i).1.2) : ℝ)) *
        ‖(moebius (L.allocation i).1 : ℂ)‖ / (Ideal.absNorm (L.allocation i).1 : ℝ) := rfl

/-- Individual original support and norm windows imply admissibility
of the internally computed carrier. These premises contain no sums,
label counts, parent estimate, or chosen-child estimate. -/
theorem carrier_admissible (B Z : ℝ) (oldMask : Ideal (𝓞 K))
    (hfirst : ∀ i, Valid oldMask (L.first i))
    (hfirstN : ∀ i, (Ideal.absNorm (L.first i).1.1 : ℝ) ≤ Z ^ B ∧
      (Ideal.absNorm (L.first i).1.2 : ℝ) ≤ Z ^ B)
    (hS : ∀ i, Squarefree (L.firstDivisor i) ∧ L.firstDivisor i ≠ 0)
    (hSN : ∀ i, (Ideal.absNorm (L.firstDivisor i) : ℝ) ≤ Z ^ B)
    (hsecond : ∀ i, Valid (L.firstDivisor i) (L.second i))
    (hsecondN : ∀ i, (Ideal.absNorm (L.second i).1.1 : ℝ) ≤ Z ^ B ∧
      (Ideal.absNorm (L.second i).1.2 : ℝ) ≤ Z ^ B)
    (hL : ∀ i, (L.allocation i).1 ≠ 0)
    (hLN : ∀ i, (Ideal.absNorm (L.allocation i).1 : ℝ) ≤ Z ^ B) :
    L.carrier.Admissible (cap + 2) B Z oldMask := by
  constructor
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hfirst i
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hfirstN i
  · intro v _ S hS'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS'
    exact hS i
  · intro v _ S hS'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hS'
    exact hSN i
  · intro v _ S _ w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hSi : L.firstDivisor i = S := (Finset.mem_filter.mp hi).2.2
    simpa only [hSi] using hsecond i
  · intro v _ S _ w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hsecondN i
  · intro v _ S _ w _ D hD
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
    exact hL i
  · intro v _ S _ w _ D hD
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
    exact hLN i
  · intro v _ S _ w _ D _
    exact ⟨le_rfl, le_rfl⟩

/-- The actual image carrier has a uniform mass from its individual
original windows. The constant is chosen before all moving labels,
including the type and cardinality of the original finite carrier. -/
theorem image_mass_subpower (cap : ℕ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      ∀ {I : Type*} [Fintype I] (L : OriginalArithmeticLabels K I cap),
      (∀ i, Valid oldMask (L.first i)) →
      (∀ i, (Ideal.absNorm (L.first i).1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm (L.first i).1.2 : ℝ) ≤ Z ^ B) →
      (∀ i, Squarefree (L.firstDivisor i) ∧ L.firstDivisor i ≠ 0) →
      (∀ i, (Ideal.absNorm (L.firstDivisor i) : ℝ) ≤ Z ^ B) →
      (∀ i, Valid (L.firstDivisor i) (L.second i)) →
      (∀ i, (Ideal.absNorm (L.second i).1.1 : ℝ) ≤ Z ^ B ∧
        (Ideal.absNorm (L.second i).1.2 : ℝ) ≤ Z ^ B) →
      (∀ i, (L.allocation i).1 ≠ 0) →
      (∀ i, (Ideal.absNorm (L.allocation i).1 : ℝ) ≤ Z ^ B) →
      L.carrier.mass ≤ C * Z ^ ε / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨C, hC, hm⟩ := TwoDivisorCommonBranch.uniform_mass (K := K)
    (cap + 2) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ oldMask hs hs0 I inst L hf hfN hS hSN hw hwN hD hDN
  exact hm Z hZ oldMask hs hs0 L.carrier
    (L.carrier_admissible B Z oldMask hf hfN hS hSN hw hwN hD hDN)

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.index_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.carrier_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.image_mass_subpower
