import HeckeSkeleton.Moments.MOM_INV_STEP.ActualSecondTuple

/-!
# Exact signed reindexing of the actual reconstruction source

The reconstruction tuple intentionally omits the four residual columns.
Those columns must remain in an inner sum. The complete map to the tuple
and these four actual residual ideals is injective: the original source
columns are reconstructed by the two proved gcd decompositions, and the
two divisor subsets and overlap support are recovered from prime products.

The final identities preserve arbitrary signed source coefficients and
all original support restrictions. They do not replace the column fibers
by unrestricted products or discard zero factors.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualSourceReindexing

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic UniqueFactorizationMonoid
open IdealMobiusMask FirstSourceDecomposition ActualSecondTuple
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open scoped Classical BigOperators NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {Jo Jn : ℕ}

theorem primeProduct_injective :
    Function.Injective (primeProduct (R := 𝓞 K)) := by
  intro S T h
  have hm := congrArg normalizedFactors h
  rw [normalizedFactors_primeProduct, normalizedFactors_primeProduct] at hm
  exact Finset.val_injective (Multiset.map_injective HeightOneSpectrum.asIdeal_injective hm)

def columns (B : Source K Sector) : Fin 4 → Ideal (𝓞 K) :=
  ![u B.n₁ B.n₂ B.b₁ B.b₂, u B.n₂ B.n₁ B.b₁ B.b₂,
    pairResidual B.x₁ B.x₂, pairResidual B.x₂ B.x₁]

variable (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
variable (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))

abbrev ExpandedSource := Σ B : Source K Sector, Choices B oldLists newLists

abbrev ReconstructionKey := SecondTuple K Sector Jo Jn × (Fin 4 → Ideal (𝓞 K))

def key (x : ExpandedSource oldLists newLists (Sector := Sector)) : ReconstructionKey (K := K) (Sector := Sector)
    (Jo := Jo) (Jn := Jn) :=
  (x.2.tuple, columns x.1)

theorem source_eq_of_key {B D : Source K Sector}
    (a : Choices B oldLists newLists) (b : Choices D oldLists newLists)
    (ht : a.tuple = b.tuple) (hc : columns B = columns D) : B = D := by
  have hcore (i : Fin 8) : a.tuple.core i = b.tuple.core i :=
    congrArg (fun t : SecondTuple K Sector Jo Jn => t.core i) ht
  have hcol (i : Fin 4) : columns B i = columns D i := congrFun hc i
  have hfirstB := first_decomposition B.n₁ B.n₂ B.b₁ B.b₂ B.n₁_squarefree B.n₂_squarefree
  have hfirstD := first_decomposition D.n₁ D.n₂ D.b₁ D.b₂ D.n₁_squarefree D.n₂_squarefree
  have hsecondB := second_decomposition B.x₁ B.x₂ B.x₁_squarefree B.x₂_squarefree
  have hsecondD := second_decomposition D.x₁ D.x₂ D.x₁_squarefree D.x₂_squarefree
  have hg : a.tuple.extractedCommon = b.tuple.extractedCommon :=
    congrArg SecondTuple.extractedCommon ht
  apply Source.ext
  · apply Subtype.ext
    exact hcore 4
  · apply Subtype.ext
    exact congrArg SecondTuple.secondCube ht
  · apply Subtype.ext
    calc
      B.n₁.val = a.tuple.core 5 * a.tuple.core 1 * columns B 0 := hfirstB.1
      _ = b.tuple.core 5 * b.tuple.core 1 * columns D 0 := by rw [hcore, hcore, hcol]
      _ = D.n₁.val := hfirstD.1.symm
  · apply Subtype.ext
    calc
      B.n₂.val = a.tuple.core 6 * a.tuple.core 1 * columns B 1 := hfirstB.2
      _ = b.tuple.core 6 * b.tuple.core 1 * columns D 1 := by rw [hcore, hcore, hcol]
      _ = D.n₂.val := hfirstD.2.symm
  · apply Subtype.ext
    calc
      B.x₁.val = a.tuple.extractedCommon * columns B 2 := hsecondB.1
      _ = b.tuple.extractedCommon * columns D 2 := by rw [hg, hcol]
      _ = D.x₁.val := hsecondD.1.symm
  · apply Subtype.ext
    calc
      B.x₂.val = a.tuple.extractedCommon * columns B 3 := hsecondB.2.1
      _ = b.tuple.extractedCommon * columns D 3 := by rw [hg, hcol]
      _ = D.x₂.val := hsecondD.2.1.symm
  · apply Subtype.ext
    exact congrArg (fun t : SecondTuple K Sector Jo Jn => t.outer.quotient) ht
  · apply primeProduct_injective
    exact congrArg SecondTuple.commonResidual ht
  · exact congrArg SecondTuple.frequency ht

theorem choices_eq_of_tuple {B : Source K Sector}
    (a b : Choices B oldLists newLists) (ht : a.tuple = b.tuple) : a = b := by
  apply Choices.ext
  · apply Subtype.ext
    apply primeProduct_injective
    exact congrArg (fun t : SecondTuple K Sector Jo Jn => t.core 7) ht
  · apply Subtype.ext
    apply primeProduct_injective
    exact congrArg (fun t : SecondTuple K Sector Jo Jn => t.core 2) ht
  · funext i
    apply Subtype.ext
    exact congrArg (fun t : SecondTuple K Sector Jo Jn => t.oldAssigned i) ht
  · funext i
    apply Subtype.ext
    exact congrArg (fun t : SecondTuple K Sector Jo Jn => t.newAssigned i) ht

/-- The tuple together with the four residual column ideals retains
every actual original source index, including divisor and prime choices. -/
theorem key_injective : Function.Injective (key oldLists newLists (Sector := Sector)) := by
  rintro ⟨B, a⟩ ⟨D, b⟩ h
  have ht : a.tuple = b.tuple := congrArg Prod.fst h
  have hc : columns B = columns D := congrArg Prod.snd h
  have hB := source_eq_of_key oldLists newLists a b ht hc
  cases hB
  have ha := choices_eq_of_tuple oldLists newLists a b ht
  cases ha
  rfl

def keySource (T : Finset (ExpandedSource oldLists newLists (Sector := Sector))) :
    Finset (ReconstructionKey (K := K) (Sector := Sector) (Jo := Jo) (Jn := Jn)) :=
  T.image (key oldLists newLists)

def tupleSource (T : Finset (ExpandedSource oldLists newLists (Sector := Sector))) :
    Finset (SecondTuple K Sector Jo Jn) :=
  (keySource oldLists newLists T).image Prod.fst

def columnSource (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (t : SecondTuple K Sector Jo Jn) : Finset (Fin 4 → Ideal (𝓞 K)) :=
  ((keySource oldLists newLists T).filter (fun y => y.1 = t)).image Prod.snd

def reindexedCoefficient (w : ExpandedSource oldLists newLists (Sector := Sector) → ℂ) :
    ReconstructionKey (K := K) (Sector := Sector) (Jo := Jo) (Jn := Jn) → ℂ :=
  Function.extend (key oldLists newLists) w (fun _ => 0)

theorem reindexedCoefficient_key (w : ExpandedSource oldLists newLists (Sector := Sector) → ℂ)
    (x : ExpandedSource oldLists newLists (Sector := Sector)) :
    reindexedCoefficient oldLists newLists w (key oldLists newLists x) = w x :=
  (key_injective oldLists newLists).extend_apply _ _ _

theorem sum_reindex (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (w : ExpandedSource oldLists newLists (Sector := Sector) → ℂ) :
    (∑ x ∈ T, w x) =
      ∑ y ∈ keySource oldLists newLists T, reindexedCoefficient oldLists newLists w y := by
  rw [keySource, Finset.sum_image (fun _ _ _ _ h => key_injective oldLists newLists h)]
  apply Finset.sum_congr rfl
  intro x hx
  exact (reindexedCoefficient_key oldLists newLists w x).symm

theorem sum_reindex_with_kernel
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (w : ExpandedSource oldLists newLists (Sector := Sector) → ℂ)
    (F : ReconstructionKey (K := K) (Sector := Sector) (Jo := Jo) (Jn := Jn) → ℂ) :
    (∑ x ∈ T, w x * F (key oldLists newLists x)) =
      ∑ y ∈ keySource oldLists newLists T, reindexedCoefficient oldLists newLists w y * F y := by
  rw [keySource, Finset.sum_image (fun _ _ _ _ h => key_injective oldLists newLists h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [reindexedCoefficient_key]

/-- Exact grouping by the actual tuple, retaining the correlated original
column fiber as the inner range. -/
theorem sum_group_keys (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (F : ReconstructionKey (K := K) (Sector := Sector) (Jo := Jo) (Jn := Jn) → ℂ) :
    (∑ y ∈ keySource oldLists newLists T, F y) =
      ∑ t ∈ tupleSource oldLists newLists T,
        ∑ c ∈ columnSource oldLists newLists T t, F (t, c) := by
  calc
    _ = ∑ t ∈ tupleSource oldLists newLists T,
        ∑ y ∈ keySource oldLists newLists T with y.1 = t, F y :=
      (Finset.sum_fiberwise_of_maps_to
        (fun y hy => Finset.mem_image_of_mem Prod.fst hy) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have hi : ∀ y ∈ (keySource oldLists newLists T).filter (fun y => y.1 = t),
          ∀ z ∈ (keySource oldLists newLists T).filter (fun y => y.1 = t),
          y.2 = z.2 → y = z := by
        intro y hy z hz he
        exact Prod.ext ((Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hz).2.symm) he
      rw [columnSource, Finset.sum_image hi]
      apply Finset.sum_congr rfl
      intro y hy
      exact congrArg F (Prod.ext (Finset.mem_filter.mp hy).2 rfl)

/-- The original finite signed source is recovered exactly, with its
coefficients and all original ranges retained inside the column fibers. -/
theorem signed_source_grouped
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (w : ExpandedSource oldLists newLists (Sector := Sector) → ℂ) :
    (∑ x ∈ T, w x) = ∑ t ∈ tupleSource oldLists newLists T,
      ∑ c ∈ columnSource oldLists newLists T t, reindexedCoefficient oldLists newLists w (t, c) :=
  (sum_reindex oldLists newLists T w).trans
    (sum_group_keys oldLists newLists T (reindexedCoefficient oldLists newLists w))

theorem columnSource_witness
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (t : SecondTuple K Sector Jo Jn) (c : Fin 4 → Ideal (𝓞 K))
    (hc : c ∈ columnSource oldLists newLists T t) :
    ∃ x ∈ T, x.2.tuple = t ∧ columns x.1 = c := by
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hc
  obtain ⟨hy, ht⟩ := Finset.mem_filter.mp hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x, hx, ht, he⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualSourceReindexing

end
