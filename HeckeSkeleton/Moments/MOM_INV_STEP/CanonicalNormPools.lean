import HeckeGeneral.Analysis.GlobalThetaData
import DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets

/-!
# Complete finite squarefree norm pools

The pools contain actual exterior ideals. Division is the actual ideal
factorization, with its norm scaling and squarefreeness proved. No
arbitrary original-range indicator is retained as a new coefficient.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Ext" => ExteriorIdeal K S

def height (I : Ext) : ℝ := (I.val.val.absNorm : ℝ)

theorem height_pos (I : Ext) : 0 < height K S I := by
  change (0 : ℝ) < (I.val.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem height_one_le (I : Ext) : 1 ≤ height K S I := by
  change (1 : ℝ) ≤ (I.val.val.absNorm : ℝ)
  have h : 1 ≤ I.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors I.val
  exact_mod_cast h

theorem height_mul (I J : Ext) :
    height K S (exteriorMul K S I J) = height K S I * height K S J := by
  change ((I.val.val * J.val.val).absNorm : ℝ) = _
  rw [map_mul, Nat.cast_mul]
  rfl

theorem ideal_injective : Function.Injective (fun I : Ext => I.val.val) := by
  intro I J h
  exact Subtype.ext (Subtype.ext h)

def boundedPool (X : ℝ) : Finset Ext :=
  (boundedNormIdeals K (2 * X)).preimage (fun I : Ext => I.val.val)
    (ideal_injective K S).injOn

def squarefreePool (X : ℝ) : Finset Ext :=
  (boundedPool K S X).filter (fun I => Squarefree I.val.val)

@[simp] theorem mem_squarefreePool (X : ℝ) (I : Ext) :
    I ∈ squarefreePool K S X ↔ Squarefree I.val.val ∧ height K S I ≤ 2 * X := by
  simp only [squarefreePool, boundedPool, Finset.mem_filter, Finset.mem_preimage,
    mem_boundedNormIdeals, height, and_comm]

def dyadicPool (X : ℝ) : Finset Ext :=
  (squarefreePool K S X).filter (fun I => X ≤ height K S I)

@[simp] theorem mem_dyadicPool (X : ℝ) (I : Ext) :
    I ∈ dyadicPool K S X ↔
      Squarefree I.val.val ∧ X ≤ height K S I ∧ height K S I ≤ 2 * X := by
  simp only [dyadicPool, Finset.mem_filter, mem_squarefreePool]
  tauto

theorem squarefreePool_squarefree {X : ℝ} {I : Ext}
    (hI : I ∈ squarefreePool K S X) : Squarefree I.val.val :=
  ((mem_squarefreePool K S X I).mp hI).1

theorem dyadicPool_squarefree {X : ℝ} {I : Ext}
    (hI : I ∈ dyadicPool K S X) : Squarefree I.val.val :=
  ((mem_dyadicPool K S X I).mp hI).1

theorem dyadicPool_subset_squarefreePool (X : ℝ) :
    dyadicPool K S X ⊆ squarefreePool K S X := Finset.filter_subset _ _

theorem exteriorMul_injective (e : Ext) : Function.Injective (exteriorMul K S e) := by
  intro u v huv
  apply ideal_injective K S
  exact mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero e.val)
    (congrArg (fun I : Ext => I.val.val) huv)

theorem exists_exterior_quotient (n e : Ext) (hdiv : e.val.val ∣ n.val.val) :
    ∃ u : Ext, exteriorMul K S e u = n := by
  obtain ⟨I, hI⟩ := hdiv
  have hI0 : I ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hI
    exact nonZeroDivisors.coe_ne_zero n.val hI
  let u : Ext := ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩, by
    intro p hp
    apply n.property p
    rw [hI]
    exact dvd_mul_of_dvd_right hp _⟩
  refine ⟨u, ?_⟩
  apply ideal_injective K S
  exact hI.symm

/-- Actual exterior quotient; the squarefree properties are separate proved facts. -/
def squarefreeQuotient (n e : Ext) (hdiv : e.val.val ∣ n.val.val) : Ext :=
  Classical.choose (exists_exterior_quotient K S n e hdiv)

theorem squarefreeQuotient_spec (n e : Ext) (hdiv : e.val.val ∣ n.val.val) :
    exteriorMul K S e (squarefreeQuotient K S n e hdiv) = n :=
  Classical.choose_spec (exists_exterior_quotient K S n e hdiv)

theorem squarefreeQuotient_height (n e : Ext) (hdiv : e.val.val ∣ n.val.val) :
    height K S (squarefreeQuotient K S n e hdiv) = height K S n / height K S e := by
  apply (eq_div_iff (height_pos K S e).ne').mpr
  rw [mul_comm, ← height_mul, squarefreeQuotient_spec]

theorem ideal_relPrime_iff_coprime (I J : Ideal (𝓞 K)) :
    IsRelPrime I J ↔ IsCoprime I J := by
  refine ⟨fun h => ?_, IsCoprime.isRelPrime⟩
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact Ideal.isUnit_iff.mp
    (h (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right))

theorem squarefree_quotient (n e : Ext) (hn : Squarefree n.val.val)
    (hdiv : e.val.val ∣ n.val.val) :
    Squarefree (squarefreeQuotient K S n e hdiv).val.val ∧
      IsCoprime e.val.val (squarefreeQuotient K S n e hdiv).val.val := by
  have hm : Squarefree
      (e.val.val * (squarefreeQuotient K S n e hdiv).val.val) := by
    have he := congrArg (fun I : Ext => I.val.val) (squarefreeQuotient_spec K S n e hdiv)
    change e.val.val * (squarefreeQuotient K S n e hdiv).val.val = n.val.val at he
    rwa [he]
  exact ⟨hm.of_mul_right,
    (ideal_relPrime_iff_coprime K _ _).mp (IsRelPrime.of_squarefree_mul hm)⟩

theorem exteriorMul_mem_squarefreePool (X : ℝ) (e u : Ext) (he : Squarefree e.val.val) :
    exteriorMul K S e u ∈ squarefreePool K S X ↔
      u ∈ squarefreePool K S (X / height K S e) ∧ IsCoprime e.val.val u.val.val := by
  rw [mem_squarefreePool, mem_squarefreePool, height_mul]
  have hh : height K S e * height K S u ≤ 2 * X ↔
      height K S u ≤ 2 * (X / height K S e) := by
    rw [show 2 * (X / height K S e) = (2 * X) / height K S e by ring,
      le_div_iff₀ (height_pos K S e), mul_comm]
  change (Squarefree (e.val.val * u.val.val) ∧ _) ↔ _
  rw [squarefree_mul_iff, ideal_relPrime_iff_coprime K, hh]
  tauto

theorem exteriorMul_mem_dyadicPool (X : ℝ) (e u : Ext) (he : Squarefree e.val.val) :
    exteriorMul K S e u ∈ dyadicPool K S X ↔
      u ∈ dyadicPool K S (X / height K S e) ∧ IsCoprime e.val.val u.val.val := by
  simp only [dyadicPool, Finset.mem_filter, exteriorMul_mem_squarefreePool K S X e u he,
    height_mul]
  rw [div_le_iff₀ (height_pos K S e)]
  simp only [mul_comm]
  tauto

def quotientPool (e : Ext) (X : ℝ) : Finset Ext :=
  (squarefreePool K S (X / height K S e)).filter (fun u => IsCoprime e.val.val u.val.val)

theorem quotientPool_eq (e : Ext) (X : ℝ) (he : Squarefree e.val.val) :
    (squarefreePool K S X).filter (fun n => e.val.val ∣ n.val.val) =
      (quotientPool K S e X).image (exteriorMul K S e) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn, hdiv⟩ := Finset.mem_filter.mp hn
    let u := squarefreeQuotient K S n e hdiv
    have hmul : exteriorMul K S e u = n := squarefreeQuotient_spec K S n e hdiv
    have hu := (exteriorMul_mem_squarefreePool K S X e u he).mp (hmul.symm ▸ hn)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr hu, hmul⟩
  · intro hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr
      ⟨(exteriorMul_mem_squarefreePool K S X e u he).mpr (Finset.mem_filter.mp hu),
        dvd_mul_right _ _⟩

theorem sum_multiples (e : Ext) (X : ℝ) (he : Squarefree e.val.val) (F : Ext → ℂ) :
    (∑ n ∈ squarefreePool K S X with e.val.val ∣ n.val.val, F n) =
      ∑ u ∈ quotientPool K S e X, F (exteriorMul K S e u) := by
  rw [quotientPool_eq K S e X he]
  exact Finset.sum_image (fun _ _ _ _ h => exteriorMul_injective K S e h)

theorem sum_dyadicPool_eq (X : ℝ) (F : Ext → ℂ) :
    (∑ n ∈ dyadicPool K S X, F n) =
      ∑ n ∈ squarefreePool K S X, if X ≤ height K S n then F n else 0 := by
  exact Finset.sum_filter _ _

theorem cutoff_mul_scale (W : ℝ → ℂ) (A u : Ext) (X : ℝ) (hX : 0 < X) :
    W (height K S (exteriorMul K S A u) / X) =
      W (height K S u / (X / height K S A)) := by
  congr 1
  rw [height_mul]
  field_simp [(height_pos K S A).ne', hX.ne'] <;> ring

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

end
