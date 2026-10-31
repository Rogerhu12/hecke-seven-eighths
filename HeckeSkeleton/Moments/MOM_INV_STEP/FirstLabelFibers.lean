module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers


/-!
# Removing the old averaged label at the first positive step

For fixed `E` and a fixed new row `y = h f² E`, the old squarefree label
`f` divides the actual row ideal. Once `f` is fixed, cancellation determines
`h`, including its unit sector. The resulting mass bound keeps the original
label weight as a function of `f` alone.

The argument works for all nonzero labels, so restriction to the original
squarefree label range or to any original mask can only reduce the fiber.
-/

@[expose] public section

noncomputable section
namespace HeckeSkeleton.Moments.MOMInvStep.FirstLabelFibers

open NumberField IsDedekindDomain DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators NumberField

variable (K : Type*) [Field K] [NumberField K]

@[ext] structure SourcePair (Sector : Type*) where
  label : Ideal (𝓞 K)
  frequency : Ideal (𝓞 K) × Sector

variable {K} {Sector : Type*}

structure Valid
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (x : SourcePair K Sector) (E : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) : Prop where
  row : x.label ^ 2 * E * x.frequency.1 = y.1
  sector : sectorTransport (x.label ^ 2) E x.frequency.2 = y.2

variable {sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector)}

/-- The actual first-transform row map, retaining its fixed sector. -/
def newRow
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    (E : Ideal (𝓞 K)) (x : SourcePair K Sector) : Ideal (𝓞 K) × Sector :=
  (x.label ^ 2 * E * x.frequency.1,
    sectorTransport (x.label ^ 2) E x.frequency.2)

theorem valid_newRow (E : Ideal (𝓞 K)) (x : SourcePair K Sector) :
    Valid sectorTransport x E (newRow sectorTransport E x) := ⟨rfl, rfl⟩

theorem label_dvd {x : SourcePair K Sector} {E : Ideal (𝓞 K)}
    {y : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x E y) :
    x.label ∣ y.1 := by
  refine ⟨x.label * E * x.frequency.1, ?_⟩
  rw [← hx.row]
  ring

theorem label_ne_zero {x : SourcePair K Sector} {E : Ideal (𝓞 K)}
    {y : Ideal (𝓞 K) × Sector} (hx : Valid sectorTransport x E y)
    (hy : y.1 ≠ 0) : x.label ≠ 0 := by
  intro hz
  have hd := label_dvd hx
  rw [hz, zero_dvd_iff] at hd
  exact hy hd

theorem label_injective {E : Ideal (𝓞 K)} {y : Ideal (𝓞 K) × Sector}
    (hy : y.1 ≠ 0) {x z : SourcePair K Sector}
    (hx : Valid sectorTransport x E y) (hz : Valid sectorTransport z E y)
    (hl : x.label = z.label) : x = z := by
  have hfac : x.label ^ 2 * E ≠ 0 := by
    intro hzero
    apply hy
    rw [← hx.row, hzero, zero_mul]
  have hfreq : x.frequency = z.frequency := by
    apply Prod.ext
    · apply mul_left_cancel₀ hfac
      exact hx.row.trans (by simpa only [hl] using hz.row.symm)
    · apply (sectorTransport (x.label ^ 2) E).injective
      exact hx.sector.trans (by simpa only [hl] using hz.sector.symm)
  exact SourcePair.ext hl hfreq

theorem source_card_le (T : Finset (SourcePair K Sector))
    (E : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) (hy : y.1 ≠ 0)
    (hT : ∀ x ∈ T, Valid sectorTransport x E y) :
    T.card ≤ (idealDivisors y.1).card := by
  let encode (x : T) : idealDivisors y.1 :=
    ⟨x.val.label, (mem_idealDivisors hy).mpr (label_dvd (hT x.val x.property))⟩
  have hi : Function.Injective encode := by
    intro x z hxz
    apply Subtype.ext
    apply label_injective hy (hT x.val x.property) (hT z.val z.property)
    exact congrArg Subtype.val hxz
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode hi

theorem source_weight_le (T : Finset (SourcePair K Sector))
    (E : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) (hy : y.1 ≠ 0)
    (hT : ∀ x ∈ T, Valid sectorTransport x E y)
    (w : Ideal (𝓞 K) → ℝ) (d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ T, w x.label ≤ C * ((idealDivisors x.label).card : ℝ) ^ d) :
    (∑ x ∈ T, w x.label) ≤ C * ((idealDivisors y.1).card : ℝ) ^ (d + 1) := by
  have hlocal (x : SourcePair K Sector) (hx : x ∈ T) :
      w x.label ≤ C * ((idealDivisors y.1).card : ℝ) ^ d := by
    have hsub : idealDivisors x.label ⊆ idealDivisors y.1 := by
      intro J hJ
      exact (mem_idealDivisors hy).mpr
        (((mem_idealDivisors (label_ne_zero (hT x hx) hy)).mp hJ).trans
          (label_dvd (hT x hx)))
    apply (hw x hx).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card hsub
  have hcard : (T.card : ℝ) ≤ ((idealDivisors y.1).card : ℝ) := by
    exact_mod_cast source_card_le T E y hy hT
  calc
    (∑ x ∈ T, w x.label) ≤
        ∑ _x ∈ T, C * ((idealDivisors y.1).card : ℝ) ^ d :=
      Finset.sum_le_sum hlocal
    _ = (T.card : ℝ) * (C * ((idealDivisors y.1).card : ℝ) ^ d) := by simp
    _ ≤ ((idealDivisors y.1).card : ℝ) *
        (C * ((idealDivisors y.1).card : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * ((idealDivisors y.1).card : ℝ) ^ (d + 1) := by rw [pow_succ]; ring

/-- At the first positive step, both the old label and its old frequency
are removed from the energy. The resulting weight depends only on the new
row, and the input label weight is still one common function of the label. -/
theorem source_energy_bound (T : Finset (SourcePair K Sector))
    (E : Ideal (𝓞 K)) (w : Ideal (𝓞 K) → ℝ) (d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ T, w x.label ≤ C * ((idealDivisors x.label).card : ℝ) ^ d)
    (hrow : ∀ x ∈ T, (newRow sectorTransport E x).1 ≠ 0)
    (energy : Ideal (𝓞 K) × Sector → ℝ)
    (henergy : ∀ y ∈ T.image (newRow sectorTransport E), 0 ≤ energy y) :
    (∑ x ∈ T, w x.label * energy (newRow sectorTransport E x)) ≤
      ∑ y ∈ T.image (newRow sectorTransport E),
        (C * ((idealDivisors y.1).card : ℝ) ^ (d + 1)) * energy y := by
  have hmass (y : Ideal (𝓞 K) × Sector)
      (hy : y ∈ T.image (newRow sectorTransport E)) :
      (∑ x ∈ T with newRow sectorTransport E x = y, w x.label) ≤
        C * ((idealDivisors y.1).card : ℝ) ^ (d + 1) := by
    have hy0 : y.1 ≠ 0 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hrow x hx
    apply source_weight_le _ E y hy0 _ w d C hC
    · intro x hx
      simpa only [(Finset.mem_filter.mp hx).2] using
        (valid_newRow (sectorTransport := sectorTransport) E x)
    · intro x hx
      exact hw x (Finset.mem_filter.mp hx).1
  calc
    _ = ∑ y ∈ T.image (newRow sectorTransport E),
        ∑ x ∈ T with newRow sectorTransport E x = y,
          w x.label * energy (newRow sectorTransport E x) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image_of_mem (newRow sectorTransport E) hx) _).symm
    _ = ∑ y ∈ T.image (newRow sectorTransport E),
        (∑ x ∈ T with newRow sectorTransport E x = y, w x.label) * energy y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := Finset.sum_le_sum fun y hy =>
      mul_le_mul_of_nonneg_right (hmass y hy) (henergy y hy)

/-- Every fixed divisor power in the old-label measure costs an arbitrarily
small power of the new row norm, with a constant independent of the fiber. -/
theorem source_weight_small_power (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (T : Finset (SourcePair K Sector)) (E : Ideal (𝓞 K))
        (y : Ideal (𝓞 K) × Sector) (w : Ideal (𝓞 K) → ℝ) (C : ℝ),
        0 ≤ C → y.1 ≠ 0 → (∀ x ∈ T, Valid sectorTransport x E y) →
        (∀ x ∈ T, w x.label ≤ C * ((idealDivisors x.label).card : ℝ) ^ d) →
        (∑ x ∈ T, w x.label) ≤ C * B * (Ideal.absNorm y.1 : ℝ) ^ ε := by
  obtain ⟨B, hB, hpow⟩ := FixedTripleFibers.exists_divisor_power_bound
    (K := K) (d + 1) (by omega) ε hε
  refine ⟨B, lt_of_lt_of_le zero_lt_one hB, ?_⟩
  intro T E y w C hC hy hT hw
  calc
    _ ≤ C * ((idealDivisors y.1).card : ℝ) ^ (d + 1) :=
      source_weight_le T E y hy hT w d C hC hw
    _ ≤ C * (B * (Ideal.absNorm y.1 : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hpow y.1) hC
    _ = C * B * (Ideal.absNorm y.1 : ℝ) ^ ε := by ring

end HeckeSkeleton.Moments.MOMInvStep.FirstLabelFibers

end
