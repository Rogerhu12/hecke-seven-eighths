import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition

/-!
# Independent residual ranges for the actual first source

The original two squarefree columns determine their cube-supported
parts and their common part outside the cube.  For a fixed value of
these three parts, the residual ranges below are independent: each is
defined using only its original one-column range and the fixed parts.
The only remaining condition involving both columns is coprimality.

Both directions are proved.  In particular, the right side is not an
arbitrary product enlargement of the original signed source.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceReindexing

open IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Arithmetic
open IdealMobiusMask FirstSourceDecomposition
open scoped Classical BigOperators nonZeroDivisors

namespace Supports

variable {α : Type*}

def residual (B P Q : Finset α) : Finset α := (P \ Q) \ B

def restore (A C U : Finset α) : Finset α := A ∪ C ∪ U

def Slice (B A₁ A₂ C P Q : Finset α) : Prop :=
  P ∩ B = A₁ ∧ Q ∩ B = A₂ ∧ (P ∩ Q) \ B = C

/-- This domain uses just one original column range. -/
def columnDomain (F : Finset (Finset α)) (B A C : Finset α) : Finset (Finset α) :=
  (F.biUnion id).powerset.filter fun U =>
    Disjoint U (B ∪ C) ∧ restore A C U ∈ F

theorem slice_swap {B A₁ A₂ C P Q : Finset α}
    (h : Slice B A₁ A₂ C P Q) : Slice B A₂ A₁ C Q P := by
  exact ⟨h.2.1, h.1, by simpa only [Finset.inter_comm] using h.2.2⟩

theorem restore_residual {B A₁ A₂ C P Q : Finset α}
    (h : Slice B A₁ A₂ C P Q) : restore A₁ C (residual B P Q) = P := by
  ext p
  have hA := Finset.ext_iff.mp h.1 p
  have hC := Finset.ext_iff.mp h.2.2 p
  simp only [restore, residual, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff] at *
  tauto

theorem residual_avoid {B A₁ A₂ C P Q : Finset α}
    (h : Slice B A₁ A₂ C P Q) : Disjoint (residual B P Q) (B ∪ C) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hC := Finset.ext_iff.mp h.2.2 p
  simp only [residual, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at *
  tauto

theorem residuals_disjoint (B P Q : Finset α) :
    Disjoint (residual B P Q) (residual B Q P) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  simp only [residual, Finset.mem_sdiff] at hp hq
  tauto

theorem residual_mem_column {F : Finset (Finset α)} {B A₁ A₂ C P Q : Finset α}
    (hP : P ∈ F) (h : Slice B A₁ A₂ C P Q) :
    residual B P Q ∈ columnDomain F B A₁ C := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, residual_avoid h, ?_⟩
  · intro p hp
    exact Finset.mem_biUnion.mpr
      ⟨P, hP, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1⟩
  · simpa only [restore_residual h] using hP

theorem restored_slice {B A₁ A₂ C U V : Finset α}
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (hU : Disjoint U (B ∪ C)) (hV : Disjoint V (B ∪ C)) (hUV : Disjoint U V) :
    Slice B A₁ A₂ C (restore A₁ C U) (restore A₂ C V) := by
  have h (p : α) : (p ∈ A₁ → p ∈ B) ∧ (p ∈ A₂ → p ∈ B) ∧
      ¬ (p ∈ C ∧ p ∈ B) ∧ ¬ (p ∈ U ∧ (p ∈ B ∨ p ∈ C)) ∧
      ¬ (p ∈ V ∧ (p ∈ B ∨ p ∈ C)) ∧ ¬ (p ∈ U ∧ p ∈ V) := by
    exact ⟨fun hp => hA₁ hp, fun hp => hA₂ hp, fun hp => Finset.disjoint_left.mp hCB hp.1 hp.2,
      fun hp => Finset.disjoint_left.mp hU hp.1 (Finset.mem_union.mpr hp.2),
      fun hp => Finset.disjoint_left.mp hV hp.1 (Finset.mem_union.mpr hp.2),
      fun hp => Finset.disjoint_left.mp hUV hp.1 hp.2⟩
  refine ⟨?_, ?_, ?_⟩ <;> ext p <;> have hp := h p <;>
    simp only [restore, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] <;> tauto

theorem residual_restored {B A₁ A₂ C U V : Finset α}
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B)
    (hU : Disjoint U (B ∪ C)) (hV : Disjoint V (B ∪ C)) (hUV : Disjoint U V) :
    residual B (restore A₁ C U) (restore A₂ C V) = U := by
  ext p
  have ha₁ : p ∈ A₁ → p ∈ B := fun hp => hA₁ hp
  have ha₂ : p ∈ A₂ → p ∈ B := fun hp => hA₂ hp
  have hu : ¬ (p ∈ U ∧ (p ∈ B ∨ p ∈ C)) := fun hp =>
    Finset.disjoint_left.mp hU hp.1 (Finset.mem_union.mpr hp.2)
  have hv : ¬ (p ∈ V ∧ (p ∈ B ∨ p ∈ C)) := fun hp =>
    Finset.disjoint_left.mp hV hp.1 (Finset.mem_union.mpr hp.2)
  have huv : ¬ (p ∈ U ∧ p ∈ V) := fun hp => Finset.disjoint_left.mp hUV hp.1 hp.2
  simp only [residual, restore, Finset.mem_sdiff, Finset.mem_union]
  tauto

def sourcePairs (F₁ F₂ : Finset (Finset α)) (B A₁ A₂ C : Finset α) :
    Finset (Finset α × Finset α) :=
  (F₁ ×ˢ F₂).filter fun x => Slice B A₁ A₂ C x.1 x.2

def residualPairs (F₁ F₂ : Finset (Finset α)) (B A₁ A₂ C : Finset α) :
    Finset (Finset α × Finset α) :=
  (columnDomain F₁ B A₁ C ×ˢ columnDomain F₂ B A₂ C).filter fun x => Disjoint x.1 x.2

/-- Exact signed reindexing, with independently defined target ranges. -/
theorem sum_reindex (F₁ F₂ : Finset (Finset α)) (B A₁ A₂ C : Finset α)
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (w : Finset α → Finset α → ℂ) :
    (∑ x ∈ sourcePairs F₁ F₂ B A₁ A₂ C, w x.1 x.2) =
      ∑ x ∈ residualPairs F₁ F₂ B A₁ A₂ C,
        w (restore A₁ C x.1) (restore A₂ C x.2) := by
  let f (x : Finset α × Finset α) := (residual B x.1 x.2, residual B x.2 x.1)
  let g (x : Finset α × Finset α) := (restore A₁ C x.1, restore A₂ C x.2)
  have hf (x : Finset α × Finset α) (hx : x ∈ sourcePairs F₁ F₂ B A₁ A₂ C) :
      f x ∈ residualPairs F₁ F₂ B A₁ A₂ C := by
    obtain ⟨hx, hs⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨residual_mem_column hx₁ hs,
        residual_mem_column hx₂ (slice_swap hs)⟩, residuals_disjoint _ _ _⟩
  have hg (x : Finset α × Finset α) (hx : x ∈ residualPairs F₁ F₂ B A₁ A₂ C) :
      g x ∈ sourcePairs F₁ F₂ B A₁ A₂ C := by
    obtain ⟨hx, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp hx
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₁.2, h₂.2⟩,
      restored_slice hA₁ hA₂ hCB h₁.1 h₂.1 hd⟩
  have hgf (x : Finset α × Finset α) (hx : x ∈ sourcePairs F₁ F₂ B A₁ A₂ C) :
      g (f x) = x := by
    have hs := (Finset.mem_filter.mp hx).2
    exact Prod.ext (restore_residual hs) (restore_residual (slice_swap hs))
  have hfg (x : Finset α × Finset α) (hx : x ∈ residualPairs F₁ F₂ B A₁ A₂ C) :
      f (g x) = x := by
    obtain ⟨hx, hd⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_product.mp hx
    have h₁ := (Finset.mem_filter.mp hx₁).2.1
    have h₂ := (Finset.mem_filter.mp hx₂).2.1
    exact Prod.ext (residual_restored hA₁ hA₂ h₁ h₂ hd)
      (residual_restored hA₂ hA₁ h₂ h₁ hd.symm)
  apply Finset.sum_nbij' f g hf hg hgf hfg
  intro x hx
  exact congrArg (fun z => w z.1 z.2) (hgf x hx).symm

theorem slice_sum (F₁ F₂ : Finset (Finset α)) (B A₁ A₂ C : Finset α)
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (w : Finset α → Finset α → ℂ) :
    (∑ P ∈ F₁, ∑ Q ∈ F₂, if Slice B A₁ A₂ C P Q then w P Q else 0) =
      ∑ U ∈ columnDomain F₁ B A₁ C, ∑ V ∈ columnDomain F₂ B A₂ C,
        if Disjoint U V then w (restore A₁ C U) (restore A₂ C V) else 0 := by
  simpa only [sourcePairs, residualPairs, Finset.sum_filter, Finset.sum_product] using
    sum_reindex F₁ F₂ B A₁ A₂ C hA₁ hA₂ hCB w

end Supports

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def nonzeroProduct (P : Finset (HeightOneSpectrum R)) : (Ideal R)⁰ :=
  ⟨primeProduct P, mem_nonZeroDivisors_of_ne_zero (primeProduct_ne_bot P)⟩

@[simp] theorem primeSupport_nonzeroProduct (P : Finset (HeightOneSpectrum R)) :
    primeSupport (nonzeroProduct P) = P := by
  ext p
  rw [mem_primeSupport]
  constructor
  · intro hp
    obtain ⟨q, hq, hpq⟩ :=
      (p.prime.dvd_finsetProd_iff (fun q : HeightOneSpectrum R => q.asIdeal)).mp hp
    have he : q = p := HeightOneSpectrum.ext
      (q.isMaximal.eq_of_le p.isPrime.ne_top (Ideal.dvd_iff_le.mp hpq))
    simpa only [he] using hq
  · intro hp
    exact Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum R => q.asIdeal) hp

theorem nonzeroProduct_support (n : (Ideal R)⁰) (hn : Squarefree n.val) :
    nonzeroProduct (primeSupport n) = n :=
  Subtype.ext (primeProduct_support n hn)

theorem primeProduct_coprime_iff_disjoint (P Q : Finset (HeightOneSpectrum R)) :
    IsCoprime (primeProduct P) (primeProduct Q) ↔ Disjoint P Q := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact p.prime.not_unit (h.isUnit_of_dvd'
      (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum R => q.asIdeal) hp)
      (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum R => q.asIdeal) hq))
  · exact primeProduct_coprime

def supportFamily (N : Finset ((Ideal R)⁰)) : Finset (Finset (HeightOneSpectrum R)) :=
  N.image primeSupport

theorem sum_supportFamily (N : Finset ((Ideal R)⁰))
    (hN : ∀ n ∈ N, Squarefree n.val) (f : (Ideal R)⁰ → ℂ) :
    (∑ n ∈ N, f n) = ∑ P ∈ supportFamily N, f (nonzeroProduct P) := by
  rw [supportFamily, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [nonzeroProduct_support n (hN n hn)]
  · intro n hn m hm h
    rw [← nonzeroProduct_support n (hN n hn), ← nonzeroProduct_support m (hN m hm), h]

/-- The actual original column ranges are preserved in each independent
residual domain.  No row, label, or opposite residual enters this definition. -/
def columnDomain (N : Finset ((Ideal R)⁰)) (B A C : Finset (HeightOneSpectrum R)) :=
  Supports.columnDomain (supportFamily N) B A C

theorem columnDomain_reconstruct_mem {N : Finset ((Ideal R)⁰)}
    (hN : ∀ n ∈ N, Squarefree n.val) {B A C U : Finset (HeightOneSpectrum R)}
    (hU : U ∈ columnDomain N B A C) : nonzeroProduct (Supports.restore A C U) ∈ N := by
  have hm := (Finset.mem_filter.mp hU).2.2
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  rw [← he, nonzeroProduct_support n (hN n hn)]
  exact hn

theorem columnDomain_reconstruct_factor {N : Finset ((Ideal R)⁰)}
    {B A C U : Finset (HeightOneSpectrum R)} (hA : A ⊆ B) (hCB : Disjoint C B)
    (hU : U ∈ columnDomain N B A C) :
    (nonzeroProduct (Supports.restore A C U)).val =
      primeProduct A * primeProduct C * primeProduct U := by
  have hu := (Finset.mem_filter.mp hU).2.1
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp hCB hq (hA hp)
  have hACU : Disjoint (A ∪ C) U := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    apply Finset.disjoint_left.mp hu hq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union.mpr (Or.inl (hA hp))
    · exact Finset.mem_union.mpr (Or.inr hp)
  change primeProduct (A ∪ C ∪ U) = _
  rw [show primeProduct (A ∪ C ∪ U) = primeProduct (A ∪ C) * primeProduct U from
    Finset.prod_union hACU,
    show primeProduct (A ∪ C) = primeProduct A * primeProduct C from Finset.prod_union hAC]

/-- The complete signed first-source fiber is an exact product of two
independent column ranges with the actual mutual ideal coprimality mask. -/
theorem actual_slice_sum (N₁ N₂ : Finset ((Ideal R)⁰))
    (hN₁ : ∀ n ∈ N₁, Squarefree n.val) (hN₂ : ∀ n ∈ N₂, Squarefree n.val)
    (B A₁ A₂ C : Finset (HeightOneSpectrum R))
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (w : (Ideal R)⁰ → (Ideal R)⁰ → ℂ) :
    (∑ n ∈ N₁, ∑ m ∈ N₂,
      if Supports.Slice B A₁ A₂ C (primeSupport n) (primeSupport m) then w n m else 0) =
      ∑ U ∈ columnDomain N₁ B A₁ C, ∑ V ∈ columnDomain N₂ B A₂ C,
        if IsCoprime (primeProduct U) (primeProduct V) then
          w (nonzeroProduct (Supports.restore A₁ C U))
            (nonzeroProduct (Supports.restore A₂ C V)) else 0 := by
  calc
    _ = ∑ P ∈ supportFamily N₁, ∑ Q ∈ supportFamily N₂,
        if Supports.Slice B A₁ A₂ C P Q then
          w (nonzeroProduct P) (nonzeroProduct Q) else 0 := by
      rw [sum_supportFamily N₁ hN₁]
      apply Finset.sum_congr rfl
      intro P hP
      rw [sum_supportFamily N₂ hN₂]
      simp only [primeSupport_nonzeroProduct]
    _ = ∑ U ∈ columnDomain N₁ B A₁ C, ∑ V ∈ columnDomain N₂ B A₂ C,
        if Disjoint U V then w (nonzeroProduct (Supports.restore A₁ C U))
          (nonzeroProduct (Supports.restore A₂ C V)) else 0 :=
      Supports.slice_sum _ _ B A₁ A₂ C hA₁ hA₂ hCB _
    _ = _ := by simp only [primeProduct_coprime_iff_disjoint]

/-- The same bijection explicitly transports the two residual ideals,
so a coefficient defined from the original gcd decomposition can be
used directly, without a supplied identification of its residuals. -/
theorem actual_residual_slice_sum (N₁ N₂ : Finset ((Ideal R)⁰))
    (hN₁ : ∀ n ∈ N₁, Squarefree n.val) (hN₂ : ∀ n ∈ N₂, Squarefree n.val)
    (B A₁ A₂ C : Finset (HeightOneSpectrum R))
    (hA₁ : A₁ ⊆ B) (hA₂ : A₂ ⊆ B) (hCB : Disjoint C B)
    (w : (Ideal R)⁰ → (Ideal R)⁰ → (Ideal R)⁰ → (Ideal R)⁰ → ℂ) :
    (∑ n ∈ N₁, ∑ m ∈ N₂,
      if Supports.Slice B A₁ A₂ C (primeSupport n) (primeSupport m) then
        w n m (nonzeroProduct (Supports.residual B (primeSupport n) (primeSupport m)))
          (nonzeroProduct (Supports.residual B (primeSupport m) (primeSupport n))) else 0) =
      ∑ U ∈ columnDomain N₁ B A₁ C, ∑ V ∈ columnDomain N₂ B A₂ C,
        if IsCoprime (primeProduct U) (primeProduct V) then
          w (nonzeroProduct (Supports.restore A₁ C U))
            (nonzeroProduct (Supports.restore A₂ C V))
            (nonzeroProduct U) (nonzeroProduct V) else 0 := by
  rw [actual_slice_sum N₁ N₂ hN₁ hN₂ B A₁ A₂ C hA₁ hA₂ hCB]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hUV : IsCoprime (primeProduct U) (primeProduct V)
  · have hUV' := (primeProduct_coprime_iff_disjoint U V).mp hUV
    have hu := (Finset.mem_filter.mp hU).2.1
    have hv := (Finset.mem_filter.mp hV).2.1
    simp only [if_pos hUV, primeSupport_nonzeroProduct,
      Supports.residual_restored hA₁ hA₂ hu hv hUV',
      Supports.residual_restored hA₂ hA₁ hv hu hUV'.symm]
  · simp only [if_neg hUV]

/-- Specialization to the actual cube support identifies the source
predicate with the extraction used throughout the first Poisson pass. -/
theorem actual_slice_iff (n m b₁ b₂ : (Ideal R)⁰)
    (A₁ A₂ C : Finset (HeightOneSpectrum R)) :
    Supports.Slice (primeSupport (b₁ * b₂)) A₁ A₂ C (primeSupport n) (primeSupport m) ↔
      extractedSupport n b₁ b₂ = A₁ ∧ extractedSupport m b₁ b₂ = A₂ ∧
        commonSupport n m b₁ b₂ = C := Iff.rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceReindexing

end
