import HeckeSkeleton.Moments.MOM_INV_STEP.SecondPhysicalEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.DyadicSourcePartition

/-!
# Actual second overlap divisors and fixed production centers

Every overlap in the complete mutual-divisor sum is converted to its
actual exterior ideal. Squarefreeness, nonvanishing, support and the norm
bound follow from a member of the original complete residual pool.
The product N(g)N(v) then selects a bin in a fixed finite center set.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondMobiusGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve DedekindZetaZeroFree.LargeSieve.Vendor
open HeckeSkeleton.Moments.MOMInvStep
open FullMobius CanonicalNormPools SecondColumnEnergy SecondPhysicalEnergy
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def overlapPool (X : ℝ) (g : Ext) : Finset (Ideal (𝓞 K)) :=
  divisorPool (sourcePool K S g X) (fun z => z.val.val)

theorem overlap_exists_source (X : ℝ) (g : Ext) (v : Ideal (𝓞 K))
    (hv : v ∈ overlapPool K S X g) :
    ∃ z ∈ sourcePool K S g X, v ∣ z.val.val := by
  obtain ⟨z,hz,hv⟩ := Finset.mem_biUnion.mp hv
  exact ⟨z,hz,(mem_idealDivisors (nonZeroDivisors.coe_ne_zero z.val)).mp hv⟩

theorem overlap_nonzero (X : ℝ) (g : Ext) (v : Ideal (𝓞 K))
    (hv : v ∈ overlapPool K S X g) : v ≠ 0 := by
  obtain ⟨z,hz,hvz⟩ := overlap_exists_source K S X g v hv
  exact ne_zero_of_dvd_ne_zero (nonZeroDivisors.coe_ne_zero z.val) hvz

theorem overlap_squarefree (X : ℝ) (g : Ext) (v : Ideal (𝓞 K))
    (hv : v ∈ overlapPool K S X g) : Squarefree v := by
  obtain ⟨z,hz,hvz⟩ := overlap_exists_source K S X g v hv
  exact (squarefreePool_squarefree K Sset hz).of_dvd hvz

theorem overlap_outside (X : ℝ) (g : Ext) (v : Ideal (𝓞 K))
    (hv : v ∈ overlapPool K S X g) :
    ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ v → p ∉ Sset := by
  obtain ⟨z,hz,hvz⟩ := overlap_exists_source K S X g v hv
  intro p hp
  exact z.property p (hp.trans hvz)

def overlapIdeal (X : ℝ) (g : Ext) (v : overlapPool K S X g) : Ext :=
  ⟨⟨v.val, mem_nonZeroDivisors_of_ne_zero (overlap_nonzero K S X g v.val v.property)⟩,
    overlap_outside K S X g v.val v.property⟩

@[simp] theorem overlapIdeal_val (X : ℝ) (g : Ext) (v : overlapPool K S X g) :
    (overlapIdeal K S X g v).val.val = v.val := rfl

theorem overlapIdeal_squarefree (X : ℝ) (g : Ext) (v : overlapPool K S X g) :
    Squarefree (overlapIdeal K S X g v).val.val :=
  overlap_squarefree K S X g v.val v.property

theorem overlap_norm_le (X : ℝ) (g : Ext) (v : overlapPool K S X g) :
    height K Sset (overlapIdeal K S X g v) ≤ 2 * (2 * X / height K Sset g) := by
  obtain ⟨z,hz,hvz⟩ := overlap_exists_source K S X g v.val v.property
  have hn : v.val.absNorm ≤ z.val.val.absNorm :=
    Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors z.val)
      (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hvz))
  have hzr := (mem_squarefreePool K Sset (2 * X / height K Sset g) z).mp hz
  exact (by exact_mod_cast hn).trans hzr.2

theorem product_bounds (X : ℝ) (g : Ext) (v : overlapPool K S X g) :
    1 ≤ productHeight K S g (overlapIdeal K S X g v) ∧
      productHeight K S g (overlapIdeal K S X g v) ≤ 4 * X := by
  refine ⟨?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (height_one_le K Sset g)
      (height_one_le K Sset (overlapIdeal K S X g v))
  · have h := mul_le_mul_of_nonneg_left (overlap_norm_le K S X g v)
      (height_pos K Sset g).le
    have he : height K Sset g * (2 * (2 * X / height K Sset g)) = 4 * X := by
      field_simp [(height_pos K Sset g).ne']
      <;> ring
    exact h.trans_eq he

/-- The number and centers of these bins depend only on the fixed
parent norm scale X, not on its moving row, label, common ideal or v. -/
abbrev Index (X : ℝ) := Fin (dyadicLength (4 * X) + 1)

def centerIndex (X : ℝ) (g : Ext) (v : overlapPool K S X g) : Index X :=
  DyadicSourcePartition.boundedLabel (4 * X) (productHeight K S g (overlapIdeal K S X g v))

def childScale (X : ℝ) (i : Index X) : ℝ := X / DyadicSourcePartition.center i.val

theorem childScale_pos (X : ℝ) (hX : 0 < X) (i : Index X) : 0 < childScale X i :=
  div_pos hX (DyadicSourcePartition.center_pos i.val)

theorem childScale_identity (X : ℝ) (i : Index X) :
    X = DyadicSourcePartition.center i.val * childScale X i := by
  unfold childScale
  field_simp [(DyadicSourcePartition.center_pos i.val).ne']
  <;> ring

theorem centerIndex_bounds (X : ℝ) (g : Ext) (v : overlapPool K S X g) :
    DyadicSourcePartition.center (centerIndex K S X g v).val ≤
        productHeight K S g (overlapIdeal K S X g v) ∧
      productHeight K S g (overlapIdeal K S X g v) ≤
        4 * DyadicSourcePartition.center (centerIndex K S X g v).val := by
  have hb := product_bounds K S X g v
  have hi := (DyadicSourcePartition.exists_dyadic_index (4 * X)
    (productHeight K S g (overlapIdeal K S X g v)) hb.1 hb.2).choose_spec
  have hindex : centerIndex K S X g v =
      (DyadicSourcePartition.exists_dyadic_index (4 * X)
        (productHeight K S g (overlapIdeal K S X g v)) hb.1 hb.2).choose := by
    simp only [centerIndex, DyadicSourcePartition.boundedLabel, dif_pos hb]
  rw [← hindex] at hi
  refine ⟨max_le hb.1 hi.1.le, ?_⟩
  have hm := le_max_right (1 : ℝ) ((2 : ℝ) ^ (centerIndex K S X g v).val / 2)
  change (2 : ℝ) ^ (centerIndex K S X g v).val / 2 ≤
    DyadicSourcePartition.center (centerIndex K S X g v).val at hm
  linarith [DyadicSourcePartition.center_pos (centerIndex K S X g v).val, hi.2]

def bin (X : ℝ) (g : Ext) (i : Index X) : Finset (overlapPool K S X g) :=
  Finset.univ.filter (fun v => centerIndex K S X g v = i)

theorem sum_bins {A : Type*} [AddCommMonoid A] (X : ℝ) (g : Ext)
    (F : overlapPool K S X g → A) :
    (∑ v : overlapPool K S X g, F v) =
      ∑ i : Index X, ∑ v ∈ bin K S X g i, F v := by
  simp only [bin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondMobiusGeometry

end
