import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalArithmeticCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedFiniteIndex

/-!
# The original tagged source computes its amplified arithmetic carrier

The main and valuation-error carriers are the four coordinate images of
the actual source labels with their original tag fixed.  The genuine
index retains the prime and the valuation 1, 6 or 7.  Neither a prime-pool
cardinality nor a supplied total fibre bound enters this construction.
Each branch is admissible from the same individual original support and
norm windows.  Its arithmetic mass is then the proved one-pool mass.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}
variable {I : Type*} [Fintype I] {cap : ℕ}

namespace OriginalArithmeticLabels

variable (L : OriginalArithmeticLabels K I cap)

/-- Restriction retains every original coordinate literally.  The
subtype is selected before the two continuous Fourier parameters. -/
def restrict (S : I → Prop) : OriginalArithmeticLabels K {i : I // S i} cap where
  first i := L.first i.val
  firstDivisor i := L.firstDivisor i.val
  second i := L.second i.val
  allocation i := L.allocation i.val

@[simp] theorem restrict_first (S : I → Prop) (i : {i : I // S i}) :
    (L.restrict S).first i = L.first i.val := rfl

@[simp] theorem restrict_firstDivisor (S : I → Prop) (i : {i : I // S i}) :
    (L.restrict S).firstDivisor i = L.firstDivisor i.val := rfl

@[simp] theorem restrict_second (S : I → Prop) (i : {i : I // S i}) :
    (L.restrict S).second i = L.second i.val := rfl

@[simp] theorem restrict_allocation (S : I → Prop) (i : {i : I // S i}) :
    (L.restrict S).allocation i = L.allocation i.val := rfl

variable (tag : I → Option (ℕ × ExteriorPrime A))

def mainLabels : OriginalArithmeticLabels K {i : I // tag i = none} cap :=
  L.restrict (fun i => tag i = none)

def errorLabels (n : ℕ) (p : ExteriorPrime A) :
    OriginalArithmeticLabels K {i : I // tag i = some (n, p)} cap :=
  L.restrict (fun i => tag i = some (n, p))

def mainCarrier : TwoDivisorCommonBranch (K := K) := (L.mainLabels tag).carrier

def errorCarrier (n : ℕ) (p : ExteriorPrime A) : TwoDivisorCommonBranch (K := K) :=
  (L.errorLabels tag n p).carrier

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable (P : PowerScaleExteriorPool A bad Z ell eps)
variable (tag_mem : ∀ i n p, tag i = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes)

/-- The actual index chooses the tag fibre containing its original
label.  The error tag contains both the actual prime and valuation. -/
def amplifiedIndex (i : I) :
    AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) :=
  match h : tag i with
  | none => .inl ((L.mainLabels tag).index ⟨i, h⟩)
  | some q => .inr
      ⟨⟨q.1, (tag_mem i q.1 q.2 h).1⟩,
        ⟨q.2, (tag_mem i q.1 q.2 h).2⟩,
          (L.errorLabels tag q.1 q.2).index ⟨i, h⟩⟩

def amplifiedTag : AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) →
    Option (ℕ × ExteriorPrime A)
  | .inl _ => none
  | .inr j => some (j.1.val, j.2.1.val)

def amplifiedFirst : AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) → Label K
  | .inl j => j.1.val
  | .inr j => j.2.2.1.val

def amplifiedFirstDivisor :
    AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) → Ideal (𝓞 K)
  | .inl j => j.2.1.val
  | .inr j => j.2.2.2.1.val

def amplifiedSecond : AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) → Label K
  | .inl j => j.2.2.1.val
  | .inr j => j.2.2.2.2.1.val

def amplifiedAllocation :
    AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag) →
      OriginalAllocationFingerprint K cap
  | .inl j => (L.mainLabels tag).indexAllocation j
  | .inr j => (L.errorLabels tag j.1.val j.2.1.val).indexAllocation j.2.2

@[simp] theorem amplifiedIndex_tag (i : I) :
    L.amplifiedTag tag P (L.amplifiedIndex tag P tag_mem i) = tag i := by
  unfold amplifiedIndex
  split <;> rename_i ht <;> simp only [amplifiedTag, ht]

@[simp] theorem amplifiedIndex_first (i : I) :
    L.amplifiedFirst tag P (L.amplifiedIndex tag P tag_mem i) = L.first i := by
  unfold amplifiedIndex
  split <;> rfl

@[simp] theorem amplifiedIndex_firstDivisor (i : I) :
    L.amplifiedFirstDivisor tag P (L.amplifiedIndex tag P tag_mem i) = L.firstDivisor i := by
  unfold amplifiedIndex
  split <;> rfl

@[simp] theorem amplifiedIndex_second (i : I) :
    L.amplifiedSecond tag P (L.amplifiedIndex tag P tag_mem i) = L.second i := by
  unfold amplifiedIndex
  split <;> rfl

/-- This is exactly the allocation-projection identity used by the
physical `CoveredLeafKey` fibre theorem. No allocation is reselected. -/
@[simp] theorem amplifiedIndex_allocation (i : I) :
    L.amplifiedAllocation tag P (L.amplifiedIndex tag P tag_mem i) = L.allocation i := by
  unfold amplifiedIndex
  split <;> rfl

theorem amplifiedIndex_eq_tag {i j : I}
    (h : L.amplifiedIndex tag P tag_mem i = L.amplifiedIndex tag P tag_mem j) :
    tag i = tag j := by
  have he := congrArg (L.amplifiedTag tag P) h
  simpa only [amplifiedIndex_tag] using he

theorem amplifiedIndex_eq_coordinates {i j : I}
    (h : L.amplifiedIndex tag P tag_mem i = L.amplifiedIndex tag P tag_mem j) :
    L.first i = L.first j ∧ L.firstDivisor i = L.firstDivisor j ∧
      L.second i = L.second j ∧ L.allocation i = L.allocation j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [amplifiedIndex_first] using congrArg (L.amplifiedFirst tag P) h
  · simpa only [amplifiedIndex_firstDivisor] using congrArg (L.amplifiedFirstDivisor tag P) h
  · simpa only [amplifiedIndex_second] using congrArg (L.amplifiedSecond tag P) h
  · simpa only [amplifiedIndex_allocation] using congrArg (L.amplifiedAllocation tag P) h

/-- The tag restriction changes no original support or norm premise. -/
theorem restricted_carrier_admissible (T : I → Prop)
    (B Z : ℝ) (oldMask : Ideal (𝓞 K))
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
    (L.restrict T).carrier.Admissible (cap + 2) B Z oldMask :=
  (L.restrict T).carrier_admissible B Z oldMask
    (fun i => hfirst i.val) (fun i => hfirstN i.val)
    (fun i => hS i.val) (fun i => hSN i.val)
    (fun i => hsecond i.val) (fun i => hsecondN i.val)
    (fun i => hL i.val) (fun i => hLN i.val)

theorem amplified_carriers_admissible (B Z : ℝ) (oldMask : Ideal (𝓞 K))
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
    (L.mainCarrier tag).Admissible (cap + 2) B Z oldMask ∧
      ∀ n p, (L.errorCarrier tag n p).Admissible (cap + 2) B Z oldMask :=
  by
    unfold mainCarrier mainLabels errorCarrier errorLabels
    exact ⟨L.restricted_carrier_admissible (fun i => tag i = none) B Z oldMask
        hfirst hfirstN hS hSN hsecond hsecondN hL hLN,
      fun n p => L.restricted_carrier_admissible (fun i => tag i = some (n, p)) B Z oldMask
        hfirst hfirstN hS hSN hsecond hsecondN hL hLN⟩

/-- The internally computed tagged image has the official one-pool
mass. Constants precede the actual pool, all source labels and their
tags. The source fibre is deliberately left for the physical theorem. -/
theorem amplified_image_mass_subpower
    (cap : ℕ) (normBox δ ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hδ : 0 < δ)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
    ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ P : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
    ∀ {I : Type*} [Fintype I] (L : OriginalArithmeticLabels K I cap)
      (tag : I → Option (ℕ × ExteriorPrime A)),
      (∀ i n p, tag i = some (n, p) → n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes) →
      (∀ i, Valid oldMask (L.first i)) →
      (∀ i, (Ideal.absNorm (L.first i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.first i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, Squarefree (L.firstDivisor i) ∧ L.firstDivisor i ≠ 0) →
      (∀ i, (Ideal.absNorm (L.firstDivisor i) : ℝ) ≤ Z ^ normBox) →
      (∀ i, Valid (L.firstDivisor i) (L.second i)) →
      (∀ i, (Ideal.absNorm (L.second i).1.1 : ℝ) ≤ Z ^ normBox ∧
        (Ideal.absNorm (L.second i).1.2 : ℝ) ≤ Z ^ normBox) →
      (∀ i, (L.allocation i).1 ≠ 0) →
      (∀ i, (Ideal.absNorm (L.allocation i).1 : ℝ) ≤ Z ^ normBox) →
      (∑ j : AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag),
        amplifiedIndexWeight P M B (L.mainCarrier tag) (L.errorCarrier tag) j) ≤
          C * Z ^ (δ + eps) / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨C, Z₀, hC, hZ₀, hm⟩ := amplified_finite_index_mass (A := A)
    (cap + 2) normBox δ ell eps Mmax Bmax hbox hδ hell heps hepsell hMmax hBmax
  refine ⟨C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ bad P M B hM hMM hBB oldMask hs hs0 I inst L tag
    _htag hf hfN hS hSN hw hwN hD hDN
  have ha := L.amplified_carriers_admissible tag normBox Z oldMask
    hf hfN hS hSN hw hwN hD hDN
  exact hm Z hZ bad P M B hM hMM hBB oldMask hs hs0
    (L.mainCarrier tag) ha.1 (L.errorCarrier tag) (fun n _ p _ => ha.2 n p)

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplifiedIndex_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplifiedIndex_tag
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplified_carriers_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplified_image_mass_subpower
