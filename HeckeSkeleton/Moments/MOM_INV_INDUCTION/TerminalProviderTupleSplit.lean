import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderAggregation

/-!
# Exact active and inactive original tuple coordinates

The active subset is a subset of the original slots. The tuple splits
bijectively into its active and inactive restrictions, and the literal
product coefficient factors accordingly. No moving row appears in any
of these maps or coefficients.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalTupleSplit

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open TerminalMarks TerminalAggregation
open scoped Classical BigOperators nonZeroDivisors

instance subsetsFintype {α : Type*} (Q : Finset α) :
    Fintype {A : Finset α // A ⊆ Q} :=
  Fintype.ofFinset Q.powerset (fun A => Finset.mem_powerset)

variable (K : Type) [Field K] [NumberField K]
variable {σ : Type*} [DecidableEq σ]
variable (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))

def restrict (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L) : tuplePool K J L :=
  ⟨fun i => q.val ⟨i.val, hJ i.property⟩,
    Fintype.mem_piFinset.mpr (fun i => (Fintype.mem_piFinset.mp q.property) _)⟩

def join (J : Finset σ) (hJ : J ⊆ I)
    (qa : tuplePool K J L) (qi : tuplePool K (I \ J) L) : tuplePool K I L :=
  ⟨fun i => if h : i.val ∈ J then qa.val ⟨i.val, h⟩
    else qi.val ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, h⟩⟩,
    Fintype.mem_piFinset.mpr (by
      intro i
      split_ifs with h
      · exact (Fintype.mem_piFinset.mp qa.property) _
      · exact (Fintype.mem_piFinset.mp qi.property) _)⟩

@[simp] theorem join_active (J : Finset σ) (hJ : J ⊆ I)
    (qa : tuplePool K J L) (qi : tuplePool K (I \ J) L) (i : J) :
    (join K I L J hJ qa qi).val ⟨i.val, hJ i.property⟩ = qa.val i := by
  simp only [join, dif_pos i.property]

@[simp] theorem join_inactive (J : Finset σ) (hJ : J ⊆ I)
    (qa : tuplePool K J L) (qi : tuplePool K (I \ J) L) (i : ↥(I \ J)) :
    (join K I L J hJ qa qi).val ⟨i.val, (Finset.mem_sdiff.mp i.property).1⟩ = qi.val i := by
  simp only [join, dif_neg (Finset.mem_sdiff.mp i.property).2]

def equiv (J : Finset σ) (hJ : J ⊆ I) :
    tuplePool K I L ≃ tuplePool K J L × tuplePool K (I \ J) L where
  toFun q := (restrict K I L J hJ q,
    restrict K I L (I \ J) Finset.sdiff_subset q)
  invFun q := join K I L J hJ q.1 q.2
  left_inv q := by
    apply Subtype.ext
    funext i
    dsimp only [join]
    split_ifs <;> rfl
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact join_active K I L J hJ q.1 q.2 i
    · apply Subtype.ext
      funext i
      exact join_inactive K I L J hJ q.1 q.2 i

theorem sum_split (J : Finset σ) (hJ : J ⊆ I) (F : tuplePool K I L → ℂ) :
    (∑ q : tuplePool K I L, F q) =
      ∑ qi : tuplePool K (I \ J) L, ∑ qa : tuplePool K J L,
        F (join K I L J hJ qa qi) := by
  rw [← (equiv K I L J hJ).symm.sum_comp F, Fintype.sum_prod_type]
  exact Finset.sum_comm

private def extendedWeight (a : σ → Ideal (𝓞 K) → ℂ) (q : tuplePool K I L)
    (i : σ) : ℂ := if h : i ∈ I then a i (q.val ⟨i, h⟩) else 1

private theorem tupleWeight_eq_extended (a : σ → Ideal (𝓞 K) → ℂ)
    (q : tuplePool K I L) :
    tupleWeight K I a q.val = ∏ i ∈ I, extendedWeight K I L a q i := by
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [extendedWeight, dif_pos i.property, tupleWeight]

theorem weight_split (a : σ → Ideal (𝓞 K) → ℂ)
    (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L) :
    tupleWeight K I a q.val =
      tupleWeight K J a (restrict K I L J hJ q).val *
        tupleWeight K (I \ J) a (restrict K I L (I \ J) Finset.sdiff_subset q).val := by
  rw [tupleWeight_eq_extended K I L a q]
  have hA : (∏ i ∈ J, extendedWeight K I L a q i) =
      tupleWeight K J a (restrict K I L J hJ q).val := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [extendedWeight, dif_pos (hJ i.property), restrict, tupleWeight]
  have hB : (∏ i ∈ I \ J, extendedWeight K I L a q i) =
      tupleWeight K (I \ J) a (restrict K I L (I \ J) Finset.sdiff_subset q).val := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [extendedWeight, dif_pos ((Finset.mem_sdiff.mp i.property).1),
      restrict, tupleWeight]
  rw [← hA, ← hB]
  exact (Finset.prod_sdiff hJ).symm.trans (mul_comm _ _)

theorem weight_join (a : σ → Ideal (𝓞 K) → ℂ)
    (J : Finset σ) (hJ : J ⊆ I)
    (qa : tuplePool K J L) (qi : tuplePool K (I \ J) L) :
    tupleWeight K I a (join K I L J hJ qa qi).val =
      tupleWeight K J a qa.val * tupleWeight K (I \ J) a qi.val := by
  have h := weight_split K I L a J hJ (join K I L J hJ qa qi)
  have ha : restrict K I L J hJ (join K I L J hJ qa qi) = qa :=
    congrArg Prod.fst ((equiv K I L J hJ).apply_symm_apply (qa, qi))
  have hi : restrict K I L (I \ J) Finset.sdiff_subset (join K I L J hJ qa qi) = qi :=
    congrArg Prod.snd ((equiv K I L J hJ).apply_symm_apply (qa, qi))
  simpa only [ha, hi] using h

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
variable (hexterior : ∀ i ∈ I, ∀ p ∈ L i, MOM_INV_STEP.CanonicalChildren.IsExterior K S p)

def activePrimes (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L) :
    Finset (ExteriorPrime K S) :=
  tuplePrimes K S J L (fun i hi => hprime i (hJ hi))
    (fun i hi => hexterior i (hJ hi)) (restrict K I L J hJ q)

theorem activePrimes_mem (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L)
    (p : ExteriorPrime K S) :
    p ∈ activePrimes K I L S hprime hexterior J hJ q ↔
      ∃ i : I, i.val ∈ J ∧ tuplePrime K S I L hprime hexterior q i = p := by
  constructor
  · intro hp
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hp
    exact ⟨⟨i.val, hJ i.property⟩, i.property, he⟩
  · rintro ⟨i, hi, he⟩
    exact Finset.mem_image.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, he⟩

theorem activePrimes_subset (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L) :
    activePrimes K I L S hprime hexterior J hJ q ⊆
      tuplePrimes K S I L hprime hexterior q := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := (activePrimes_mem K I L S hprime hexterior J hJ q p).mp hp
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def slotsForPrimes (q : tuplePool K I L) (A : Finset (ExteriorPrime K S)) : Finset σ :=
  I.filter (fun i => ∃ hi : i ∈ I, tuplePrime K S I L hprime hexterior q ⟨i, hi⟩ ∈ A)

def choicesEquiv
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j))
    (q : tuplePool K I L) :
    {J : Finset σ // J ⊆ I} ≃
      {A : Finset (ExteriorPrime K S) // A ⊆ tuplePrimes K S I L hprime hexterior q} where
  toFun J := ⟨activePrimes K I L S hprime hexterior J.val J.property q,
    activePrimes_subset K I L S hprime hexterior J.val J.property q⟩
  invFun A := ⟨slotsForPrimes K I L S hprime hexterior q A.val, Finset.filter_subset _ _⟩
  left_inv J := by
    apply Subtype.ext
    ext i
    simp only [slotsForPrimes, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hi', hp⟩
      obtain ⟨j, hj, he⟩ :=
        (activePrimes_mem K I L S hprime hexterior J.val J.property q _).mp hp
      have hji := tuplePrime_injective K S I L hprime hexterior hdisjoint q he
      have hval : j.val = i := congrArg Subtype.val hji
      simpa only [hval] using hj
    · intro hi
      have hiI := J.property hi
      exact ⟨hiI, hiI,
        (activePrimes_mem K I L S hprime hexterior J.val J.property q _).mpr
          ⟨⟨i, hiI⟩, hi, rfl⟩⟩
  right_inv A := by
    apply Subtype.ext
    ext p
    rw [activePrimes_mem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hiI, hi', hp⟩ := Finset.mem_filter.mp hi
      exact hp
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (A.property hp)
      exact ⟨i, Finset.mem_filter.mpr ⟨i.property, i.property, hp⟩, rfl⟩

theorem inactivePrimes_eq
    (hdisjoint : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (L i) (L j))
    (J : Finset σ) (hJ : J ⊆ I) (q : tuplePool K I L) :
    tuplePrimes K S I L hprime hexterior q \
        activePrimes K I L S hprime hexterior J hJ q =
      activePrimes K I L S hprime hexterior (I \ J) Finset.sdiff_subset q := by
  ext p
  rw [Finset.mem_sdiff,
    activePrimes_mem K I L S hprime hexterior (I \ J) Finset.sdiff_subset q p]
  constructor
  · rintro ⟨hp, hpa⟩
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hp
    refine ⟨i, Finset.mem_sdiff.mpr ⟨i.property, ?_⟩, he⟩
    intro hiJ
    exact hpa ((activePrimes_mem K I L S hprime hexterior J hJ q p).mpr ⟨i, hiJ, he⟩)
  · rintro ⟨i, hi, he⟩
    refine ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩, ?_⟩
    intro hpa
    obtain ⟨j, hj, hje⟩ := (activePrimes_mem K I L S hprime hexterior J hJ q p).mp hpa
    have hij := tuplePrime_injective K S I L hprime hexterior hdisjoint q (he.trans hje.symm)
    exact (Finset.mem_sdiff.mp hi).2 ((congrArg Subtype.val hij).symm ▸ hj)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalTupleSplit

end
