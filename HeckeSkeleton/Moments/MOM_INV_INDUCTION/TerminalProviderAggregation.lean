import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderStates
import HeckeSkeleton.LowEnergy.IdealMass

/-!
# Original tuple coefficients and inactive prime masses

The original disjoint prime lists make the map from a tuple to its
squarefree marked ideal injective. Aggregation consequently preserves
the bound one on the original product coefficient; it is independent
of the moving row and every dual column. The inactive prime sums have
a uniform small-power mass from the existing ideal harmonic estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalAggregation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open TerminalMarks TerminalAtoms
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable {σ : Type*} [DecidableEq σ]

variable (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
variable (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
variable (hexterior : ∀ i ∈ I, ∀ p ∈ L i, MOM_INV_STEP.CanonicalChildren.IsExterior K S p)
variable (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j))

theorem tuplePrime_injective (q : tuplePool K I L) :
    Function.Injective (tuplePrime K S I L hprime hexterior q) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hpi := (Fintype.mem_piFinset.mp q.property) i
  have hpj := (Fintype.mem_piFinset.mp q.property) j
  have hp : q.val i = q.val j := congrArg (fun p : ExteriorPrime K S => p.val.asIdeal) hij
  exact Finset.disjoint_left.mp (hdisjoint i.val i.property j.val j.property hne)
    hpi (hp.symm ▸ hpj)

def tupleIdeal (q : tuplePool K I L) : ExteriorIdeal K S :=
  primeSetIdeal K S (tuplePrimes K S I L hprime hexterior q)

theorem tupleIdeal_squarefree (q : tuplePool K I L) :
    Squarefree (tupleIdeal K S I L hprime hexterior q).val.val :=
  HeckeGeneral.Arithmetic.IdealMobiusMask.squarefree_primeProduct _

/-- The ideal of an active tuple determines each of its original
prime choices, because the individual prime lists are disjoint. -/
theorem tupleIdeal_injective :
    Function.Injective (tupleIdeal K S I L hprime hexterior) := by
  intro q q' h
  have hQ : tuplePrimes K S I L hprime hexterior q =
      tuplePrimes K S I L hprime hexterior q' := by
    have he := congrArg (exteriorSupport K S) h
    simpa only [tupleIdeal, exteriorSupport_primeSetIdeal] using he
  apply Subtype.ext
  funext i
  have hi : tuplePrime K S I L hprime hexterior q i ∈
      tuplePrimes K S I L hprime hexterior q' := by
    rw [← hQ]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
  have hp : q'.val j = q.val i := congrArg (fun p : ExteriorPrime K S => p.val.asIdeal) hji
  have hij : i.val = j.val := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint i.val i.property j.val j.property hne)
      ((Fintype.mem_piFinset.mp q.property) i)
      (hp ▸ ((Fintype.mem_piFinset.mp q'.property) j))
  have hij' : i = j := Subtype.ext hij
  subst j
  exact hp.symm

def idealPool : Finset (ExteriorIdeal K S) :=
  Finset.univ.image (tupleIdeal K S I L hprime hexterior)

/-- Literal finite aggregation of the original individual coefficients.
Its arguments contain neither a moving row nor a dual variable. -/
def coefficient (a : σ → Ideal (𝓞 K) → ℂ) (P : ExteriorIdeal K S) : ℂ :=
  ∑ q : tuplePool K I L,
    if tupleIdeal K S I L hprime hexterior q = P then tupleWeight K I a q.val else 0

theorem coefficient_on_tuple (a : σ → Ideal (𝓞 K) → ℂ) (q : tuplePool K I L) :
    coefficient K S I L hprime hexterior a (tupleIdeal K S I L hprime hexterior q) =
      tupleWeight K I a q.val := by
  unfold coefficient
  rw [Finset.sum_eq_single q]
  · simp only [if_pos rfl]
  · intro q' hq' hne
    exact if_neg (fun he => hne (tupleIdeal_injective K S I L hprime hexterior hdisjoint he))
  · simp

theorem coefficient_norm_le_one (a : σ → Ideal (𝓞 K) → ℂ)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) (P : ExteriorIdeal K S) :
    ‖coefficient K S I L hprime hexterior a P‖ ≤ 1 := by
  by_cases h : ∃ q, tupleIdeal K S I L hprime hexterior q = P
  · obtain ⟨q, rfl⟩ := h
    rw [coefficient_on_tuple K S I L hprime hexterior hdisjoint]
    exact tupleWeight_norm_le_one K I L a ha q
  · have hz : coefficient K S I L hprime hexterior a P = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact if_neg (fun he => h ⟨q, he⟩)
    simp only [hz, norm_zero, zero_le_one]

theorem sum_eq_aggregated (a : σ → Ideal (𝓞 K) → ℂ)
    (F : ExteriorIdeal K S → ℂ) :
    (∑ q : tuplePool K I L, tupleWeight K I a q.val *
      F (tupleIdeal K S I L hprime hexterior q)) =
      ∑ P ∈ idealPool K S I L hprime hexterior,
        coefficient K S I L hprime hexterior a P * F P := by
  rw [idealPool, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro q hq
    rw [coefficient_on_tuple K S I L hprime hexterior hdisjoint]
  · intro q hq q' hq' h
    exact tupleIdeal_injective K S I L hprime hexterior hdisjoint h

def reciprocalWeight (q : tuplePool K I L) : ℝ :=
  ∏ p ∈ tuplePrimes K S I L hprime hexterior q, (p.val.asIdeal.absNorm : ℝ)⁻¹

theorem reciprocalWeight_nonneg (q : tuplePool K I L) :
    0 ≤ reciprocalWeight K S I L hprime hexterior q := by
  apply Finset.prod_nonneg
  intro p hp
  positivity

theorem reciprocalWeight_eq_product (q : tuplePool K I L) :
    reciprocalWeight K S I L hprime hexterior q =
      ∏ i : I, ((q.val i).absNorm : ℝ)⁻¹ := by
  unfold reciprocalWeight tuplePrimes
  rw [Finset.prod_image]
  · rfl
  · intro i hi j hj he
    exact tuplePrime_injective K S I L hprime hexterior hdisjoint q he

theorem reciprocalWeight_sum :
    (∑ q : tuplePool K I L, reciprocalWeight K S I L hprime hexterior q) =
      ∏ i : I, ∑ p ∈ L i.val, (p.absNorm : ℝ)⁻¹ := by
  simp_rw [reciprocalWeight_eq_product K S I L hprime hexterior hdisjoint]
  rw [Finset.sum_coe_sort]
  symm
  exact Finset.prod_univ_sum _ _

/-- Inactive tuple sums cost only the original reciprocal-prime mass.
The constant is uniform over all original lists and individual bounded
coefficients, and is chosen before the norm cap or any tuple. -/
theorem exists_inactive_mass_bound (slotCap : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
      (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
      (hexterior : ∀ i ∈ I, ∀ p ∈ L i, MOM_INV_STEP.CanonicalChildren.IsExterior K S p),
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j)) →
      I.card ≤ slotCap → ∀ (a : σ → Ideal (𝓞 K) → ℂ),
      (∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) → ∀ X : ℝ, 1 ≤ X →
      (∀ i ∈ I, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ X) →
      (∑ q : tuplePool K I L, ‖tupleWeight K I a q.val‖ *
        reciprocalWeight K S I L hprime hexterior q) ≤ C * X ^ eps := by
  obtain ⟨C, hC, hb⟩ := HeckeSkeleton.LowEnergy.ideal_harmonic_products_small_power
    K slotCap eps heps
  refine ⟨C, hC, ?_⟩
  intro σ hσ I L hprime hexterior hdisjoint hI a ha X hX hnorm
  calc
    _ ≤ ∑ q : tuplePool K I L, reciprocalWeight K S I L hprime hexterior q := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_of_le_one_left (reciprocalWeight_nonneg K S I L hprime hexterior q)
        (tupleWeight_norm_le_one K I L a ha q)
    _ = ∏ i : I, ∑ p ∈ L i.val, (p.absNorm : ℝ)⁻¹ :=
      reciprocalWeight_sum K S I L hprime hexterior hdisjoint
    _ ≤ C * X ^ eps := by
      simpa only [one_div] using hb (σ := I) (by simpa using hI) X hX
        (fun i : I => L i.val)
        (fun i p hp => (hprime i.val i.property p hp).ne_zero)
        (fun i p hp => hnorm i.val i.property p hp)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalAggregation

end
