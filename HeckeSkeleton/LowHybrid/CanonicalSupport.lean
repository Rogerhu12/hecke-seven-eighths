import HeckeSkeleton.LowHybrid.PrimeArithmetic
import HeckeSkeleton.LowHybrid.NormalFormSupport
import HeckeSkeleton.LowHybrid.ProductBounds

/-!
# Support conditions of the canonical completed-square decomposition

Every squarefreeness and norm restriction here follows from the original
column and cube support. No block support or product-fiber estimate is an
additional hypothesis.
-/

namespace HeckeSkeleton.LowHybrid.PrimeArithmetic

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates
open HeckeSkeleton.LowHybrid.NormalForm

noncomputable section

variable {ι A : Type*} [CommMonoid A]
variable (coords : A ≃* Multiplicative (ι →₀ ℕ))

theorem fromSupport_support_of_squarefree {a : A} (ha : Squarefree coords a) :
    fromSupport coords (support coords a) = a := by
  apply valuation_injective coords
  ext p
  rw [valuation_fromSupport]
  by_cases hp : p ∈ support coords a
  · have hn := Finsupp.mem_support_iff.mp hp
    have hs := ha p
    simp only [if_pos hp]
    omega
  · have hz : valuation coords a p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp, hz]

theorem support_subset_of_dvd {a b : A} (h : a ∣ b) :
    support coords a ⊆ support coords b := by
  intro p hp
  have ha := Finsupp.mem_support_iff.mp hp
  have hle := (dvd_iff_coordinates_le coords a b).mp h p
  exact Finsupp.mem_support_iff.mpr (by omega)

theorem mem_divisors_of_squarefree_dvd {a d : A}
    (hsf : Squarefree coords d) (hd : d ∣ a) : d ∈ divisors coords a := by
  exact Finset.mem_image.mpr ⟨support coords d,
    Finset.mem_powerset.mpr (support_subset_of_dvd coords hd),
    fromSupport_support_of_squarefree coords hsf⟩

theorem canonical_support_residual_squarefree
    {columns cubes : Finset A} (hcolumns : ∀ n ∈ columns, Squarefree coords n)
    {v : CompletedIndex A} (hv : v ∈ (completion coords columns cubes).support) :
    Squarefree coords (v.2.2.1 * v.2.2.2) := by
  obtain ⟨⟨n, b⟩, hnb, rfl⟩ := Finset.mem_image.mp hv
  exact completed_residual_squarefree coords n b
    (hcolumns n (Finset.mem_product.mp hnb).1)

theorem canonical_block_residual_squarefree (S : Arithmetic A)
    {columns cubes : Finset A} (hcolumns : ∀ n ∈ columns, Squarefree coords n)
    {r : A} {v : CompletedIndex A}
    (hv : v ∈ S.blockSupport (completion coords columns cubes).support r) :
    Squarefree coords (v.2.2.1 * v.2.2.2) := by
  have h := canonical_support_residual_squarefree coords hcolumns
    (S.blockSupport_restore_mem hv)
  exact h

theorem arithmetic_norm_le_of_dvd (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x) {a b : A} (h : a ∣ b) :
    S.normI a ≤ S.normI b := by
  obtain ⟨c, rfl⟩ := h
  rw [S.norm_mul]
  calc
    S.normI a = S.normI a * 1 := (mul_one _).symm
    _ ≤ S.normI a * S.normI c :=
      mul_le_mul_of_nonneg_left (hnorm c) (S.norm_nonneg a)

theorem canonical_block_bounds (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x)
    {columns cubes : Finset A} (N B : ℝ)
    (hcolumns : ∀ n ∈ columns, Squarefree coords n ∧ S.normI n ≤ N)
    (hcubes : ∀ b ∈ cubes, S.normI b ≤ B)
    {r : A} {v : CompletedIndex A}
    (hv : v ∈ S.blockSupport (completion coords columns cubes).support r) :
    S.normI v.1 ≤ B ∧ S.normI v.2.1 ≤ N ∧
      S.normI v.2.2.1 ≤ N ∧ S.normI v.2.2.2 ≤ B ∧
      Squarefree coords (v.2.2.1 * v.2.2.2) ∧
      S.normI (v.2.2.1 * v.2.2.2) ≤ N * B ∧
      Squarefree coords (v.2.1 * v.2.2.1) ∧
      S.normI (v.2.1 * v.2.2.1) ≤ N := by
  rcases v with ⟨t, c, m, h⟩
  obtain ⟨hcolumn, hcube⟩ := S.blockSupport_original_mem (completion coords columns cubes) hv
  have hn := hcolumns _ hcolumn
  have hb := hcubes _ hcube
  have htdvd : t ∣ r * c * h * t ^ 2 := by
    refine ⟨r * c * h * t, ?_⟩
    simp only [pow_two]
    ac_rfl
  have hcdvd : c ∣ r * c * m := ⟨r * m, by ac_rfl⟩
  have hmdvd : m ∣ r * c * m := ⟨r * c, by ac_rfl⟩
  have hhdvd : h ∣ r * c * h * t ^ 2 := ⟨r * c * t ^ 2, by ac_rfl⟩
  have hcmdvd : c * m ∣ r * c * m := ⟨r, by ac_rfl⟩
  have ht := (arithmetic_norm_le_of_dvd S hnorm htdvd).trans hb
  have hc := (arithmetic_norm_le_of_dvd S hnorm hcdvd).trans hn.2
  have hm := (arithmetic_norm_le_of_dvd S hnorm hmdvd).trans hn.2
  have hh := (arithmetic_norm_le_of_dvd S hnorm hhdvd).trans hb
  refine ⟨ht, hc, hm, hh,
    canonical_block_residual_squarefree coords S (fun n hn => (hcolumns n hn).1) hv,
    ?_, squarefree_of_dvd coords hcmdvd hn.1,
    (arithmetic_norm_le_of_dvd S hnorm hcmdvd).trans hn.2⟩
  rw [S.norm_mul]
  exact mul_le_mul hm hh (S.norm_nonneg h) ((S.norm_nonneg m).trans hm)

theorem product_fiber_card_le_squarefree_divisors
    (pairs : Finset (A × A)) (j : A) (hj : Squarefree coords j) :
    ((pairs.filter fun u => u.1 * u.2 = j).card : ℝ) ≤
      ((divisors coords j).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn (fun u => u.1)
  · intro u hu
    have heq := (Finset.mem_filter.mp hu).2
    have hd : u.1 ∣ j := ⟨u.2, heq.symm⟩
    exact mem_divisors_of_squarefree_dvd coords (squarefree_of_dvd coords hd hj) hd
  · intro u hu v hv huv
    change u.1 = v.1 at huv
    apply Prod.ext huv
    have heq := (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    rw [huv] at heq
    apply valuation_injective coords
    ext p
    have hp := congrArg (fun a => valuation coords a p) heq
    simp only [valuation_mul_apply] at hp
    omega

theorem swapped_product_fiber_card_le_squarefree_divisors
    (pairs : Finset (A × A)) (j : A) (hj : Squarefree coords j) :
    ((pairs.filter fun u => u.2 * u.1 = j).card : ℝ) ≤
      ((divisors coords j).card : ℝ) := by
  simpa only [mul_comm] using product_fiber_card_le_squarefree_divisors coords pairs j hj

#print axioms canonical_block_bounds
#print axioms product_fiber_card_le_squarefree_divisors

end
end HeckeSkeleton.LowHybrid.PrimeArithmetic
