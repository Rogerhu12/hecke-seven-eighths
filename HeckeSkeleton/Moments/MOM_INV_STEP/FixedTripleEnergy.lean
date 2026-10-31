module

public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Ring

/-!
# The positive energy after the second transform

The input to this module is the literal reconstruction tuple of
`FixedTripleFibers`, including the original prime lists and zero masks.
The fiber bound is proved there, rather than assumed here. The label
divisor weight is put in the label measure and the frozen-triple divisor
weight is put in the outer measure. The latter measure is charged once
after the two Cauchy square roots.

This is the finite, positive part of the single-step argument. Identifying
the signed sum with the second Poisson transform is a separate analytic
identity; the theorems below do not posit such an identity as an energy
bound.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy

open NumberField IsDedekindDomain DedekindZetaZeroFree.LargeSieve
open FixedTripleFibers
open scoped BigOperators Classical NumberField

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}

/-- A row has its ideal and its sector; a child also records the frozen
puncture triple and the averaged squarefree label. -/
abbrev SecondChild (K : Type*) [Field K] [NumberField K] (Sector : Type*) :=
  OuterTriple K × Ideal (𝓞 K) × (Ideal (𝓞 K) × Sector)

def secondChild
    (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))
    {Jo Jn : ℕ} (x : SecondTuple K Sector Jo Jn) : SecondChild K Sector :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    (x.core 7 * x.core 2 * x.frequency.1,
      sectorTransport (x.core 7) (x.core 2) x.frequency.2))

def labelDivisorWeight (slotCap : ℕ) (f : Ideal (𝓞 K)) : ℝ :=
  ((idealDivisors f).card : ℝ) ^ (9 + 4 * slotCap)

theorem labelDivisorWeight_nonneg (slotCap : ℕ) (f : Ideal (𝓞 K)) :
    0 ≤ labelDivisorWeight slotCap f := by
  unfold labelDivisorWeight
  positivity

def childEnergy (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) : ℝ :=
  ∑ f ∈ labels, labelDivisorWeight slotCap f * ∑ k ∈ rows, ‖F (γ, f, k)‖ ^ 2

theorem childEnergy_nonneg (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) :
    0 ≤ childEnergy slotCap labels rows F γ := by
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (labelDivisorWeight_nonneg slotCap f)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The actual column normalization and the one averaged-label
normalization in the canonical family. -/
def normalizedChildEnergy (Z N V : ℝ) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) : ℝ :=
  Z ^ (-V) * ∑ f ∈ labels, labelDivisorWeight slotCap f *
    ∑ k ∈ rows, ‖((Z ^ (-N / 2) : ℝ) : ℂ) * F (γ, f, k)‖ ^ 2

theorem normalizedChildEnergy_eq (Z N V : ℝ) (hZ : 0 < Z) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) :
    normalizedChildEnergy Z N V slotCap labels rows F γ =
      Z ^ (-(N + V)) * childEnergy slotCap labels rows F γ := by
  have hs : ‖((Z ^ (-N / 2) : ℝ) : ℂ)‖ ^ 2 = Z ^ (-N) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    congr 1
    norm_num
  have he : (∑ f ∈ labels, labelDivisorWeight slotCap f *
      ∑ k ∈ rows, ‖((Z ^ (-N / 2) : ℝ) : ℂ) * F (γ, f, k)‖ ^ 2) =
      Z ^ (-N) * childEnergy slotCap labels rows F γ := by
    simp only [norm_mul, mul_pow, hs, childEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [normalizedChildEnergy, he, ← mul_assoc, ← Real.rpow_add hZ]
  congr 2
  ring

/-- Restoring the child normalization contributes exactly N+V. -/
theorem childEnergy_restore (Z N V : ℝ) (hZ : 0 < Z) (slotCap : ℕ)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) :
    childEnergy slotCap labels rows F γ =
      Z ^ (N + V) * normalizedChildEnergy Z N V slotCap labels rows F γ := by
  rw [normalizedChildEnergy_eq Z N V hZ, ← mul_assoc, ← Real.rpow_add hZ,
    add_neg_cancel, Real.rpow_zero, one_mul]

/-- The induction hypothesis is on the normalized canonical energy.
The raw positive reconstruction therefore has exponent 2(N+V)+ε. -/
theorem childEnergy_bound_of_normalized (Z N V eps C : ℝ) (hZ : 0 < Z)
    (slotCap : ℕ) (labels : Finset (Ideal (𝓞 K)))
    (rows : Finset (Ideal (𝓞 K) × Sector))
    (F : SecondChild K Sector → ℂ) (γ : OuterTriple K)
    (h : normalizedChildEnergy Z N V slotCap labels rows F γ ≤ C * Z ^ (N + V + eps)) :
    childEnergy slotCap labels rows F γ ≤ C * Z ^ (2 * (N + V) + eps) := by
  rw [childEnergy_restore Z N V hZ]
  apply (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hZ.le _)).trans_eq
  calc
    Z ^ (N + V) * (C * Z ^ (N + V + eps)) = C * (Z ^ (N + V) * Z ^ (N + V + eps)) := by ring
    _ = _ := rw [← Real.rpow_add hZ]; congr 2 <;> ring

variable (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))

theorem secondChild_eq_iff_valid {Jo Jn : ℕ} (x : SecondTuple K Sector Jo Jn)
    (hx : Valid sectorTransport x (secondChild sectorTransport x).1
      (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2)
    (c : SecondChild K Sector) :
    secondChild sectorTransport x = c ↔ Valid sectorTransport x c.1 c.2.1 c.2.2 := by
  constructor
  · intro he
    simpa only [he] using hx
  · intro hv
    apply Prod.ext hv.outer_eq
    exact Prod.ext hv.label (Prod.ext hv.row_eq hv.sector_eq)

/-- Weighted pushforward of the literal reconstruction. No mass estimate
for arbitrary abstract fibers is an input to this theorem. -/
theorem secondChild_fiber_weight {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid sectorTransport x (secondChild sectorTransport x).1
        (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2)
    (c : SecondChild K Sector) (hf : c.2.1 ≠ 0) (hq : c.1.q0 ≠ 0)
    (ht : c.1.quotient ≠ 0) (hr : c.1.residual ≠ 0)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (w : SecondTuple K Sector Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1) :
    (∑ x ∈ (originalSource source oldLists newLists keep).filter
      (fun x => secondChild sectorTransport x = c), w x) ≤
        labelDivisorWeight slotCap c.2.1 * tripleDivisorWeight slotCap c.1 := by
  have hfilter : (originalSource source oldLists newLists keep).filter
      (fun x => secondChild sectorTransport x = c) =
      secondFiber sectorTransport source oldLists newLists keep c.1 c.2.1 c.2.2 := by
    apply Finset.filter_congr
    intro x hx
    exact secondChild_eq_iff_valid sectorTransport x (hvalid x hx) c
  calc
    _ ≤ ∑ _x ∈ (originalSource source oldLists newLists keep).filter
        (fun x => secondChild sectorTransport x = c), (1 : ℝ) :=
      Finset.sum_le_sum fun x hx => hw x (Finset.mem_filter.mp hx).1
    _ = ((secondFiber sectorTransport source oldLists newLists keep c.1 c.2.1 c.2.2).card : ℝ) := by
      rw [hfilter]
      simp
    _ ≤ labelDivisorWeight slotCap c.2.1 * tripleDivisorWeight slotCap c.1 := by
      have h := secondFiber_card_le (sectorTransport := sectorTransport) source
        oldLists newLists keep c.1 c.2.1 c.2.2 hf hq ht hr slotCap ho hn
      dsimp only [labelDivisorWeight, tripleDivisorWeight]
      have hR : ((secondFiber sectorTransport source oldLists newLists keep c.1 c.2.1 c.2.2).card : ℝ) ≤
          ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4 * slotCap) *
          ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2 * slotCap) *
          ((idealDivisors c.1.quotient).card : ℝ) ^ (2 * slotCap) *
          ((idealDivisors c.1.residual).card : ℝ) ^ (2 * slotCap) := by
        exact_mod_cast h
      simpa only [mul_assoc] using hR

/-- A positive energy is reindexed only after Cauchy. Its outer sum runs
over distinct triples from the original support. -/
theorem source_energy_projection {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid sectorTransport x (secondChild sectorTransport x).1
        (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild sectorTransport x).2.1 ∈ labels ∧
        (secondChild sectorTransport x).2.2 ∈ rows)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (w : SecondTuple K Sector Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1)
    (F : SecondChild K Sector → ℂ) :
    (∑ x ∈ originalSource source oldLists newLists keep,
      w x * ‖F (secondChild sectorTransport x)‖ ^ 2) ≤
      ∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight slotCap γ * childEnergy slotCap labels rows F γ := by
  let T := sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows)
  have hmaps : ∀ x ∈ originalSource source oldLists newLists keep,
      secondChild sectorTransport x ∈ T := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  calc
    _ = ∑ c ∈ T, ∑ x ∈ (originalSource source oldLists newLists keep).filter
        (fun x => secondChild sectorTransport x = c),
          w x * ‖F (secondChild sectorTransport x)‖ ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ c ∈ T, (∑ x ∈ (originalSource source oldLists newLists keep).filter
        (fun x => secondChild sectorTransport x = c), w x) * ‖F c‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ ∑ c ∈ T,
        (labelDivisorWeight slotCap c.2.1 * tripleDivisorWeight slotCap c.1) * ‖F c‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hγ, hfk⟩ := Finset.mem_product.mp hc
      obtain ⟨hq, ht, hr⟩ := houter c.1 hγ
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact secondChild_fiber_weight sectorTransport source oldLists newLists keep hvalid c
        (hf c.2.1 (Finset.mem_product.mp hfk).1) hq ht hr slotCap ho hn w hw
    _ = _ := by
      simp only [T, Finset.sum_product, childEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      apply Finset.sum_congr rfl
      intro f hfm
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Weighted Cauchy with the signed outer scalar retained until taking
the norm. This also permits the scalar to vanish on the original masks. -/
theorem signed_cauchy {ι : Type*} (s : Finset ι) (a f g : ι → ℂ) :
    ‖∑ i ∈ s, a i * f i * star (g i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖a i‖ * ‖f i‖ ^ 2) *
        Real.sqrt (∑ i ∈ s, ‖a i‖ * ‖g i‖ ^ 2) := by
  have hf : (∑ i ∈ s, (Real.sqrt ‖a i‖ * ‖f i‖) ^ 2) =
      ∑ i ∈ s, ‖a i‖ * ‖f i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hg : (∑ i ∈ s, (Real.sqrt ‖a i‖ * ‖g i‖) ^ 2) =
      ∑ i ∈ s, ‖a i‖ * ‖g i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
  calc
    _ ≤ ∑ i ∈ s, ‖a i * f i * star (g i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, (Real.sqrt ‖a i‖ * ‖f i‖) * (Real.sqrt ‖a i‖ * ‖g i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_mul, norm_star]
      calc
        ‖a i‖ * ‖f i‖ * ‖g i‖ =
            (Real.sqrt ‖a i‖ * Real.sqrt ‖a i‖) * ‖f i‖ * ‖g i‖ := by
          rw [Real.mul_self_sqrt (norm_nonneg _)]
        _ = _ := by ring
    _ ≤ _ := by
      simpa only [hf, hg] using Real.sum_mul_le_sqrt_mul_sqrt s
        (fun i => Real.sqrt ‖a i‖ * ‖f i‖)
        (fun i => Real.sqrt ‖a i‖ * ‖g i‖)

/-- The second Cauchy inequality followed by the proved reconstruction
bound. Both positive energies have the same label and triple measures. -/
theorem second_source_cauchy {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid sectorTransport x (secondChild sectorTransport x).1
        (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild sectorTransport x).2.1 ∈ labels ∧
        (secondChild sectorTransport x).2.2 ∈ rows)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (a : SecondTuple K Sector Jo Jn → ℂ)
    (ha : ∀ x ∈ originalSource source oldLists newLists keep, ‖a x‖ ≤ 1)
    (F G : SecondChild K Sector → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      a x * F (secondChild sectorTransport x) * star (G (secondChild sectorTransport x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight slotCap γ * childEnergy slotCap labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight slotCap γ * childEnergy slotCap labels rows G γ) := by
  apply (signed_cauchy (originalSource source oldLists newLists keep) a
    (F ∘ secondChild sectorTransport) (G ∘ secondChild sectorTransport)).trans
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (source_energy_projection sectorTransport source oldLists newLists keep
      hvalid labels rows hf houter hchild slotCap ho hn (fun x => ‖a x‖) ha F)
  · exact Real.sqrt_le_sqrt (source_energy_projection sectorTransport source oldLists newLists keep
      hvalid labels rows hf houter hchild slotCap ho hn (fun x => ‖a x‖) ha G)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

/-- The mass of one common positive measure occurs once, after both
square roots. No second label or triple multiplicity is introduced. -/
theorem common_mass_after_cauchy {ι : Type*} (s : Finset ι)
    (w L R : ι → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hL : ∀ i ∈ s, L i ≤ H) (hR : ∀ i ∈ s, R i ≤ H) :
    Real.sqrt (∑ i ∈ s, w i * L i) * Real.sqrt (∑ i ∈ s, w i * R i) ≤
      H * ∑ i ∈ s, w i := by
  have hsumL : (∑ i ∈ s, w i * L i) ≤ H * ∑ i ∈ s, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [mul_comm H] using mul_le_mul_of_nonneg_left (hL i hi) (hw i hi)
  have hsumR : (∑ i ∈ s, w i * R i) ≤ H * ∑ i ∈ s, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      simpa only [mul_comm H] using mul_le_mul_of_nonneg_left (hR i hi) (hw i hi)
  calc
    _ ≤ Real.sqrt (H * ∑ i ∈ s, w i) * Real.sqrt (H * ∑ i ∈ s, w i) :=
      mul_le_mul (Real.sqrt_le_sqrt hsumL) (Real.sqrt_le_sqrt hsumR)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = H * ∑ i ∈ s, w i :=
      Real.mul_self_sqrt (mul_nonneg hH (Finset.sum_nonneg hw))

/-- Exact preservation of every source zero when the live support is
formed. This precedes enlargement of the positive label and row ranges. -/
theorem signed_sum_restrict {ι : Type*} (s : Finset ι) (a F : ι → ℂ) :
    (∑ i ∈ s, a i * F i) = ∑ i ∈ s with a i ≠ 0, a i * F i := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have ha : a i = 0 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
  simp only [ha, zero_mul]

/-- Conditional on the inductive child bound, the actual reconstruction
has the correct unnormalized mass, with the count used once. The only
energy premise here is the smaller child's bound. -/
theorem second_source_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple K Sector Jo Jn))
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))
    (keep : SecondTuple K Sector Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid sectorTransport x (secondChild sectorTransport x).1
        (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2)
    (labels : Finset (Ideal (𝓞 K))) (rows : Finset (Ideal (𝓞 K) × Sector))
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild sectorTransport x).2.1 ∈ labels ∧
        (secondChild sectorTransport x).2.2 ∈ rows)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (a : SecondTuple K Sector Jo Jn → ℂ)
    (ha : ∀ x ∈ originalSource source oldLists newLists keep, ‖a x‖ ≤ 1)
    (F G : SecondChild K Sector → ℂ) (H : ℝ) (hH : 0 ≤ H)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      childEnergy slotCap labels rows F γ ≤ H)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      childEnergy slotCap labels rows G γ ≤ H) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      a x * F (secondChild sectorTransport x) * star (G (secondChild sectorTransport x))‖ ≤
      H * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight slotCap γ := by
  apply (second_source_cauchy sectorTransport source oldLists newLists keep hvalid labels rows hf
    houter hchild slotCap ho hn a ha F G).trans
  exact common_mass_after_cauchy _ (tripleDivisorWeight slotCap) _ _ H hH
    (fun γ _ => tripleDivisorWeight_nonneg slotCap γ) hF hG

/-- A source-validated reconstruction packet. Every field is either a
finite support, an arithmetic reconstruction equality, a surviving original
slot list, or a scalar contraction. No parent or child energy bound is a
field of this structure. -/
structure ReconstructionPacket (slotCap Jo Jn : ℕ) where
  source : Finset (SecondTuple K Sector Jo Jn)
  oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K))
  newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))
  keep : SecondTuple K Sector Jo Jn → Prop
  labels : Finset (Ideal (𝓞 K))
  rows : Finset (Ideal (𝓞 K) × Sector)
  scalar : SecondTuple K Sector Jo Jn → ℂ
  valid : ∀ x ∈ originalSource source oldLists newLists keep,
    Valid sectorTransport x (secondChild sectorTransport x).1
      (secondChild sectorTransport x).2.1 (secondChild sectorTransport x).2.2
  label_squarefree : ∀ f ∈ labels, Squarefree f
  label_nonzero : ∀ f ∈ labels, f ≠ 0
  outer_nonzero : ∀ γ ∈ sourceTriples source oldLists newLists keep,
    γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0
  child_mem : ∀ x ∈ originalSource source oldLists newLists keep,
    (secondChild sectorTransport x).2.1 ∈ labels ∧
      (secondChild sectorTransport x).2.2 ∈ rows
  old_cap : Jo ≤ 2 * slotCap
  new_cap : Jn ≤ 2 * slotCap
  scalar_norm : ∀ x ∈ originalSource source oldLists newLists keep, ‖scalar x‖ ≤ 1

namespace ReconstructionPacket

variable {sectorTransport} {slotCap Jo Jn : ℕ}
variable (P : ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn)

def triples : Finset (OuterTriple K) := sourceTriples P.source P.oldLists P.newLists P.keep

def signedValue (F G : SecondChild K Sector → ℂ) : ℂ :=
  ∑ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
    P.scalar x * F (secondChild sectorTransport x) * star (G (secondChild sectorTransport x))

def energy (F : SecondChild K Sector → ℂ) (γ : OuterTriple K) : ℝ :=
  childEnergy slotCap P.labels P.rows F γ

def tripleMass : ℝ := ∑ γ ∈ P.triples, tripleDivisorWeight slotCap γ

theorem signedValue_le (F G : SecondChild K Sector → ℂ) (H : ℝ) (hH : 0 ≤ H)
    (hF : ∀ γ ∈ P.triples, P.energy F γ ≤ H)
    (hG : ∀ γ ∈ P.triples, P.energy G γ ≤ H) :
    ‖P.signedValue F G‖ ≤ H * P.tripleMass :=
  second_source_child_bound sectorTransport P.source P.oldLists P.newLists P.keep P.valid
    P.labels P.rows P.label_nonzero P.outer_nonzero P.child_mem slotCap P.old_cap P.new_cap
    P.scalar P.scalar_norm F G H hH hF hG

/-- The count and its small-power loss are derived from actual source
norm bounds. In particular no fiber-mass or total-mass hypothesis is part
of the reconstruction packet. -/
theorem exists_tripleMass_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (P : ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn)
      (Xq Xt Xr : ℝ), 1 ≤ Xq → 1 ≤ Xt → 1 ≤ Xr →
      (∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr) →
      P.tripleMass ≤ C * (Xq * Xt * Xr) ^ (1 + ε) := by
  obtain ⟨C, hC, hmass⟩ := exists_sourceTriples_normalized_mass_bound
    (K := K) (Sector := Sector) slotCap ε hε
  refine ⟨C, hC, ?_⟩
  intro Jo Jn P Xq Xt Xr hq ht hr hs
  have hX : 0 < Xq * Xt * Xr := by positivity
  have hz : ∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
      x.outer.q0 ≠ 0 ∧ x.outer.quotient ≠ 0 ∧ x.outer.residual ≠ 0 := by
    intro x hx
    exact P.outer_nonzero x.outer (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hm := (div_le_iff₀ hX).mp
    (hmass P.source P.oldLists P.newLists P.keep Xq Xt Xr hq ht hr hs hz)
  change P.tripleMass ≤ (C * (Xq * Xt * Xr) ^ ε) * (Xq * Xt * Xr) at hm
  calc
    _ ≤ (C * (Xq * Xt * Xr) ^ ε) * (Xq * Xt * Xr) := hm
    _ = C * (Xq * Xt * Xr) ^ (1 + ε) := by
      rw [Real.rpow_add hX, Real.rpow_one]
      ring

/-- An empty original block needs no lower bound for its three norm
scales. A nonempty block supplies those lower bounds through its actual
nonzero ideal witnesses. -/
theorem exists_tripleMass_bound_of_norm_box (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Jo Jn : ℕ}
      (P : ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn)
      (Xq Xt Xr : ℝ), 0 < Xq → 0 < Xt → 0 < Xr →
      (∀ x ∈ originalSource P.source P.oldLists P.newLists P.keep,
        (Ideal.absNorm x.outer.q0 : ℝ) ≤ Xq ∧
        (Ideal.absNorm x.outer.quotient : ℝ) ≤ Xt ∧
        (Ideal.absNorm x.outer.residual : ℝ) ≤ Xr) →
      P.tripleMass ≤ C * (Xq * Xt * Xr) ^ (1 + ε) := by
  obtain ⟨C, hC, hb⟩ := exists_tripleMass_bound (K := K)
    (Sector := Sector) (sectorTransport := sectorTransport) (slotCap := slotCap) ε hε
  refine ⟨C, hC, ?_⟩
  intro Jo Jn P Xq Xt Xr hq ht hr hs
  by_cases hsrc : (originalSource P.source P.oldLists P.newLists P.keep).Nonempty
  · obtain ⟨x, hx⟩ := hsrc
    obtain ⟨hxq, hxt, hxr⟩ := hs x hx
    obtain ⟨hzq, hzt, hzr⟩ := P.outer_nonzero x.outer (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    have hone (I : Ideal (𝓞 K)) (hI : I ≠ 0) : (1 : ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact hb P Xq Xt Xr ((hone _ hzq).trans hxq) ((hone _ hzt).trans hxt)
      ((hone _ hzr).trans hxr) hs
  · have he : originalSource P.source P.oldLists P.newLists P.keep = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsrc
    have hzero : P.tripleMass = 0 := by
      simp only [tripleMass, triples, sourceTriples, he, Finset.image_empty, Finset.sum_empty]
    rw [hzero]
    positivity

end ReconstructionPacket

end HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy

end
