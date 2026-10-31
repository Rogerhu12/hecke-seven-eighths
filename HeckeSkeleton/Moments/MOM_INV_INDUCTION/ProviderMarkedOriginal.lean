import HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceRelativeSlots
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedMask
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedTupleSplit

/-!
# The literal original marked moment enters the overlap source

This file starts at the actual `MomentData.inversePolynomial` multiplied
by its original prime slots.  The complete finite norm envelope is
justified by the original test's support specification.  The live
character, individual relative prime coefficients, square-root factors,
and complete common masks are all displayed in the resulting source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOriginal

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.Moments.MOM_BASE.Paired
open ProviderMarkedSlots ProviderMarkedReindex
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

def lists (d : MomentData K ω ψ) (Z t : ℝ) :
    Fin d.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)) :=
  fun i => (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)

def primeWeight (d : MomentData K ω ψ) (Z t : ℝ)
    (i : Fin d.geometry.slotCount) (P : Ideal (𝓞 K)) : ℂ :=
  primeIdealValue (fun p => inverseRelativeSlotCoefficient d i p *
    (d.geometry.slots i).profile t
      ((p.asIdeal.absNorm : ℝ) / Z ^ (d.geometry.slots i).length)) P

theorem primeWeight_asIdeal (d : MomentData K ω ψ) (Z t : ℝ)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    primeWeight d Z t i p.asIdeal = inverseRelativeSlotCoefficient d i p *
      (d.geometry.slots i).profile t
        ((p.asIdeal.absNorm : ℝ) / Z ^ (d.geometry.slots i).length) :=
  primeIdealValue_asIdeal _ _

def normalization (d : MomentData K ω ψ) (X Z : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * ∏ i, (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹

theorem squarefree_pool_image (X : ℝ) :
    ((dyadicIdealSupport K X).filter (fun I => Squarefree I.val)).image (fun I => I.val) =
      (ProviderMarkedPools.pool X).filter Squarefree := by
  ext I
  constructor
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨J, (Finset.mem_filter.mp hJ).1, rfl⟩,
        (Finset.mem_filter.mp hJ).2⟩
  · intro hI
    obtain ⟨hI, hsf⟩ := Finset.mem_filter.mp hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨hJ, hsf⟩, rfl⟩

/-- The original inverse polynomial, with its literal ideal test and
mask, extended only by columns where that original profile is zero. -/
theorem inverse_eq_complete_live_source (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (X t : ℝ) (hX : 0 < X) (hdir : d.direction = 1)
    (hW : Function.support (d.inverseTest.profile u t) ⊆ Set.Iic 2)
    (hν : ∀ n : NonzeroIdeal K, d.commonMask u n.val = true →
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p) :
    inversePolynomial d u X t = (Real.sqrt X : ℂ)⁻¹ *
      ∑ n ∈ (ProviderMarkedPools.pool X).filter Squarefree,
        (moebius n : ℂ) * idealCoefficient (primeCoefficient K
          (d.inverseBackground * d.rowCharacter u)) n *
          d.inverseTest.profile u t (ProviderMarkedPools.norm n / X) * maskValue d u n := by
  let f : Ideal (𝓞 K) → ℂ := fun n =>
    (moebius n : ℂ) * idealCoefficient (primeCoefficient K
      (d.inverseBackground * d.rowCharacter u)) n *
      d.inverseTest.profile u t (ProviderMarkedPools.norm n / X) * maskValue d u n
  have hterm (n : NonzeroIdeal K) :
      sourceInverseTerm d u X t n = (Real.sqrt X : ℂ)⁻¹ * f n.val := by
    rw [sourceInverseTerm_eq_live d u n X t hdir (hν n)]
    rfl
  rw [inversePolynomial_eq_squarefree_sum]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ n ∈ (dyadicIdealSupport K X).filter (fun n => Squarefree n.val), f n.val := by
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨hn, hsf⟩ := Finset.mem_filter.mp hn
        refine Finset.mem_filter.mpr ⟨?_, hsf⟩
        apply (mem_dyadicIdealSupport_iff K hX.le n).mpr
        exact (div_le_iff₀ hX).mp (hW ((d.inverseTest.support_spec u t X n).mp hn))
      · intro n hn hnot
        have hz : d.inverseTest.profile u t (idealNorm K n / X) = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr
            ⟨(d.inverseTest.support_spec u t X n).mpr hne, (Finset.mem_filter.mp hn).2⟩)
        change _ * d.inverseTest.profile u t (idealNorm K n / X) * _ = 0
        rw [hz, mul_zero, zero_mul]
    _ = ∑ n ∈ (ProviderMarkedPools.pool X).filter Squarefree, f n := by
      rw [← squarefree_pool_image X,
        Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]

variable {d : ℕ}

theorem live_coefficient_primeProduct (χ : HeckeCharacter K)
    (p : Fin d → HeightOneSpectrum (𝓞 K)) :
    idealCoefficient (primeCoefficient K χ) (primeProduct Finset.univ p) =
      ∏ i, primeCoefficient K χ (p i) := by
  change (idealCoefficientHom (primeCoefficient K χ)) (∏ i, (p i).asIdeal) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealCoefficient_prime _ _

/-- Each original slot keeps its own relative arithmetic coefficient
and its own original profile. The original masks form the whole-index
mask of the original prime product. -/
theorem relative_tuple_product (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (Z t : ℝ)
    (hmask : ∀ I, d.commonMask u I = contextOriginalMask K c u I)
    (p : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K)) :
    (∏ i, sourceRelativeSlotTerm d u Z t i (p i)) =
      (∏ i, (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹) *
        idealCoefficient (primeCoefficient K (d.inverseBackground * d.rowCharacter u))
          (primeProduct Finset.univ p) *
        (∏ i, primeWeight d Z t i (p i).asIdeal) *
        maskValue d u (primeProduct Finset.univ p) := by
  have hm (I : Ideal (𝓞 K)) : maskValue d u I =
      ProviderMarkedMask.value (fun p => p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) u.val I := by
    rw [maskValue, hmask, ProviderMarkedMask.context_value]
  have hpMask : (∏ i, maskValue d u (p i).asIdeal) =
      maskValue d u (primeProduct Finset.univ p) := by
    simp only [hm]
    exact (ProviderMarkedMask.value_prod Finset.univ _ u.val (fun i => (p i).asIdeal)).symm
  calc
    _ = ∏ i, (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        primeCoefficient K (d.inverseBackground * d.rowCharacter u) (p i) *
        primeWeight d Z t i (p i).asIdeal * maskValue d u (p i).asIdeal := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [sourceRelativeSlotTerm, primeWeight_asIdeal]
      ring
    _ = _ := by
      simp only [Finset.prod_mul_distrib]
      rw [← live_coefficient_primeProduct, hpMask]

/-- The complete literal marked polynomial, before the actual gcd
partition. Its source can be consumed by `full_source_decomposition`.
The complete original common mask remains in every summand. -/
theorem inverse_marked_eq_complete_source (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (X Z t : ℝ) (hX : 0 < X) (hdir : d.direction = 1)
    (hW : Function.support (d.inverseTest.profile u t) ⊆ Set.Iic 2)
    (hmask : ∀ I, d.commonMask u I = contextOriginalMask K c u I)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ places K c → UnramifiedAt K d.inverseBackground p)
    (hθ : ∀ i p, p ∉ places K c → UnramifiedAt K (d.slotCoefficient i) p) :
    inversePolynomial d u X t * slotProduct d u Z t = normalization d X Z *
      ∑ p ∈ tuples (lists d Z t),
        ∑ n ∈ (ProviderMarkedPools.pool X).filter Squarefree,
          (moebius n : ℂ) * idealCoefficient (primeCoefficient K
            (d.inverseBackground * d.rowCharacter u)) n *
            idealCoefficient (primeCoefficient K (d.inverseBackground * d.rowCharacter u))
              (primeProduct Finset.univ p) *
            (∏ i, primeWeight d Z t i (p i).asIdeal) *
            d.inverseTest.profile u t (ProviderMarkedPools.norm n / X) *
            maskValue d u n * maskValue d u (primeProduct Finset.univ p) := by
  have hmaskPrime (p : HeightOneSpectrum (𝓞 K))
      (hp : d.commonMask u p.asIdeal = true) : p ∉ places K c := by
    exact contextOriginalMask_exterior K c u p (by rw [← hmask]; exact hp)
  have hνn (n : NonzeroIdeal K) (hm : d.commonMask u n.val = true)
      (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ n.val) :
      UnramifiedAt K d.inverseBackground p := by
    rw [hmask] at hm
    unfold contextOriginalMask at hm
    split_ifs at hm with h
    exact hν p (h.1 p hp).1
  rw [inverse_eq_complete_live_source d u X t hX hdir hW hνn,
    slotProduct_eq_relative_tuples d u Z t
      (fun i p hp hm => hν p (hmaskPrime p hm))
      (fun i p hp hm => hθ i p (hmaskPrime p hm))]
  simp_rw [relative_tuple_product c d u Z t hmask]
  change _ = normalization d X Z * ∑ p ∈ sourceSlotTuples d Z t, _
  conv_lhs => rw [Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  conv_lhs => rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  unfold normalization
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedOriginal
