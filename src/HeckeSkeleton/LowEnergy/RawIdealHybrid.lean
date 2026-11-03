import HeckeSkeleton.LowEnergy.UniformIdealHybrid
import HeckeSkeleton.LowEnergy.IdealCanonicalColumns

/-!
# The full raw hybrid bound on actual integral ideals

This module starts from the original finite `(n,b),P,k` sum.  Canonical
square extraction, zero extension, finite Mobius masks and weighted
operator assembly are all proved in the dependency closure.  The only
analytic inputs are the two arbitrary-coefficient sieve inequalities.
The kernel hypotheses are local multiplicativity, collision zeros and the
exact quadratic square mask, which the actual sextic symbols satisfy.
-/

noncomputable section
namespace HeckeSkeleton.LowEnergy.RawIdealHybrid

open NumberField Ideal UniqueFactorizationMonoid
open HeckeSkeleton.LowEnergy.KeepOriginalRow
open HeckeSkeleton.LowEnergy.IdealCanonicalColumns
open scoped NumberField Classical BigOperators
variable {K : Type} [Field K] [NumberField K]

abbrev Quadruple (K : Type) [Field K] [NumberField K] :=
  Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K) × Ideal (𝓞 K)

def quadIndex (d : HybridColumnData K) : Quadruple K :=
  (d.square, d.common, d.residualN, d.residualB)

theorem quadIndex_injective : Function.Injective (quadIndex (K := K)) := by
  intro d e h
  apply HybridColumnData.reconstruct_injective
  have ht := congrArg (fun u : Quadruple K => u.1) h
  have hc := congrArg (fun u : Quadruple K => u.2.1) h
  have hm := congrArg (fun u : Quadruple K => u.2.2.1) h
  have hh := congrArg (fun u : Quadruple K => u.2.2.2) h
  change d.square = e.square at ht
  change d.common = e.common at hc
  change d.residualN = e.residualN at hm
  change d.residualB = e.residualB at hh
  simp only [HybridColumnData.reconstruct, ht, hc, hm, hh]

def quadSupport (s : Finset (HybridColumnData K)) : Finset (Quadruple K) :=
  s.image quadIndex

def tSupport (s : Finset (HybridColumnData K)) : Finset (Ideal (𝓞 K)) :=
  s.image HybridColumnData.square

def cSupport (s : Finset (HybridColumnData K)) : Finset (Ideal (𝓞 K)) :=
  s.image HybridColumnData.common

def mSupport (s : Finset (HybridColumnData K)) : Finset (Ideal (𝓞 K)) :=
  s.image HybridColumnData.residualN

def hSupport (s : Finset (HybridColumnData K)) : Finset (Ideal (𝓞 K)) :=
  s.image HybridColumnData.residualB

theorem quadSupport_subset_rectangle (s : Finset (HybridColumnData K)) :
    quadSupport s ⊆ tSupport s ×ˢ (cSupport s ×ˢ (mSupport s ×ˢ hSupport s)) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
  simp only [quadIndex, Finset.mem_product]
  exact ⟨Finset.mem_image.mpr ⟨d, hd, rfl⟩,
    Finset.mem_image.mpr ⟨d, hd, rfl⟩,
    Finset.mem_image.mpr ⟨d, hd, rfl⟩,
    Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩

/-- The zero extension remembers the entire canonical support. -/
def rectangularBeta (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t c m h : Ideal (𝓞 K)) : ℂ :=
  if (t, c, m, h) ∈ quadSupport s then beta (c * m) ((c * h) * t ^ 2) else 0

theorem rectangularBeta_witness (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t c m h : Ideal (𝓞 K)) (hb : rectangularBeta s beta t c m h ≠ 0) :
    ∃ d ∈ s, d.square = t ∧ d.common = c ∧ d.residualN = m ∧ d.residualB = h := by
  have hmem : (t, c, m, h) ∈ quadSupport s := by
    by_contra hn
    exact hb (by simp [rectangularBeta, hn])
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hmem
  refine ⟨d, hd, ?_⟩
  simpa only [quadIndex, Prod.mk.injEq] using he

theorem rectangularBeta_on_data (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (d : HybridColumnData K) (hd : d ∈ s) :
    rectangularBeta s beta d.square d.common d.residualN d.residualB =
      beta d.reconstruct.1 d.reconstruct.2 := by
  have hmem : (d.square, d.common, d.residualN, d.residualB) ∈ quadSupport s :=
    Finset.mem_image.mpr ⟨d, hd, rfl⟩
  simp only [rectangularBeta, if_pos hmem, HybridColumnData.reconstruct]

/-- Exact rectangularization, with zero values on every newly adjoined tuple. -/
theorem rectangular_reindex (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    (∑ d ∈ s, beta d.reconstruct.1 d.reconstruct.2 *
      F d.square d.common d.residualN d.residualB) =
      ∑ t ∈ tSupport s, ∑ c ∈ cSupport s, ∑ m ∈ mSupport s, ∑ h ∈ hSupport s,
        rectangularBeta s beta t c m h * F t c m h := by
  let f : Quadruple K → ℂ := fun u =>
    rectangularBeta s beta u.1 u.2.1 u.2.2.1 u.2.2.2 *
      F u.1 u.2.1 u.2.2.1 u.2.2.2
  calc
    _ = ∑ d ∈ s, f (quadIndex d) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [f, quadIndex, rectangularBeta_on_data s beta d hd]
    _ = ∑ u ∈ quadSupport s, f u := by
      symm
      exact Finset.sum_image (fun d _ e _ he => quadIndex_injective he)
    _ = ∑ u ∈ tSupport s ×ˢ (cSupport s ×ˢ (mSupport s ×ˢ hSupport s)), f u := by
      apply Finset.sum_subset (quadSupport_subset_rectangle s)
      intro u _hu hnot
      simp only [f, rectangularBeta]
      have hnot' : (u.1, u.2.1, u.2.2.1, u.2.2.2) ∉ quadSupport s := by
        simpa only [Prod.eta] using hnot
      rw [if_neg hnot', zero_mul]
    _ = _ := by simp only [Finset.sum_product, f]

theorem rectangularBeta_support (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (N B : ℝ)
    (hN : ∀ d ∈ s, (Ideal.absNorm d.reconstruct.1 : ℝ) ≤ N)
    (hB : ∀ d ∈ s, (Ideal.absNorm d.reconstruct.2 : ℝ) ≤ B) :
    ReconstructedSupport (rectangularBeta s beta) N B := by
  constructor
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact d.n_squarefree
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact d.g_squarefree
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact d.residual_coprime
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact d.square_ne_zero
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact hN d hd
  · intro t c m h hb
    obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hb
    exact hB d hd

theorem rectangularBeta_norm (s : Finset (HybridColumnData K))
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : ∀ d ∈ s, ‖beta d.reconstruct.1 d.reconstruct.2‖ ≤ 1) :
    ∀ t c m h, ‖rectangularBeta s beta t c m h‖ ≤ 1 := by
  intro t c m h
  by_cases hz : rectangularBeta s beta t c m h = 0
  · simp only [hz, norm_zero, zero_le_one]
  · obtain ⟨d, hd, rfl, rfl, rfl, rfl⟩ := rectangularBeta_witness s beta t c m h hz
    rw [rectangularBeta_on_data s beta d hd]
    exact hb d hd

/-- The exact rectangular finite row is the one fed to the weighted theorem. -/
theorem reconstructedRow_rectangle
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (s : Finset (HybridColumnData K)) (ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K)) :
    reconstructedRow cubic quad (tSupport s) (cSupport s) (mSupport s) (hSupport s)
      ps a (rectangularBeta s beta) k =
      ∑ d ∈ s, ∑ P ∈ ps, reconstructedHybridTerm cubic quad a beta k P d := by
  let F := fun (t c m h : Ideal (𝓞 K)) =>
    ∑ P ∈ ps, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      (mask k t * mask k (P * c) * quad k (m * h) * cubic P (c * m) * mask P (h * t))
  have hreindex := rectangular_reindex s beta F
  calc
    _ = ∑ t ∈ tSupport s, ∑ c ∈ cSupport s, ∑ m ∈ mSupport s, ∑ h ∈ hSupport s,
        rectangularBeta s beta t c m h * F t c m h := by
      unfold reconstructedRow F
      simp_rw [Finset.mul_sum]
      rw [three_by_two_sum_order (tSupport s) (cSupport s) (mSupport s) (hSupport s) ps
        (fun t c m h P => mask k t * quad k (m * h) *
          (mask k P * mask k c *
            (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
              rectangularBeta s beta t c m h * cubic P (c * m) * mask P (h * t))))]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro P hP
      rw [mask_mul_right k P c]
      ring
    _ = ∑ d ∈ s, beta d.reconstruct.1 d.reconstruct.2 *
        F d.square d.common d.residualN d.residualB := hreindex.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      unfold reconstructedHybridTerm HybridColumnData.reconstruct mask
      ring

variable (Ext : Ideal (𝓞 K) → Prop)

/-- All four factors inherit any support closed under actual ideal divisors. -/
theorem canonical_factor_support
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (nset bset : Finset (Ideal (𝓞 K))) (N B : ℝ)
    (hn : ∀ n ∈ nset, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N)
    (hb : ∀ b ∈ bset, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B)
    (d : HybridColumnData K) (hd : d ∈ hybridColumnSupport (nset ×ˢ bset)) :
    (Ext d.square ∧ (Ideal.absNorm d.square : ℝ) ≤ B) ∧
    (Ext d.common ∧ (Ideal.absNorm d.common : ℝ) ≤ N) ∧
    (Ext d.residualN ∧ (Ideal.absNorm d.residualN : ℝ) ≤ N) ∧
    (Ext d.residualB ∧ (Ideal.absNorm d.residualB : ℝ) ≤ B) := by
  have hd0 := Finset.mem_product.mp ((mem_hybridColumnSupport _ d).mp hd)
  have hn0 := hn _ hd0.1
  have hb0 := hb _ hd0.2
  have htd : d.square ∣ d.reconstruct.2 := by
    refine ⟨(d.common * d.residualB) * d.square, ?_⟩
    simp only [HybridColumnData.reconstruct, pow_two]
    ac_rfl
  have hhd : d.residualB ∣ d.reconstruct.2 :=
    dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)
  have hcd : d.common ∣ d.reconstruct.1 := dvd_mul_right _ _
  have hmd : d.residualN ∣ d.reconstruct.1 := dvd_mul_left _ _
  exact ⟨⟨hext_dvd _ _ hb0.1 htd,
      (ideal_norm_le_of_dvd _ _ (hext_ne _ hb0.1) htd).trans hb0.2⟩,
    ⟨hext_dvd _ _ hn0.1 hcd,
      (ideal_norm_le_of_dvd _ _ (hext_ne _ hn0.1) hcd).trans hn0.2.2⟩,
    ⟨hext_dvd _ _ hn0.1 hmd,
      (ideal_norm_le_of_dvd _ _ (hext_ne _ hn0.1) hmd).trans hn0.2.2⟩,
    ⟨hext_dvd _ _ hb0.1 hhd,
      (ideal_norm_le_of_dvd _ _ (hext_ne _ hb0.1) hhd).trans hb0.2⟩⟩

/-- Every field is constructed from the original finite support and coefficients. -/
def canonicalReconstruction
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (K0 N0 B0 L0 : ℝ)
    (rows nset bset ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hrows : ∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0)
    (hn : ∀ n ∈ nset, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0)
    (hb : ∀ b ∈ bset, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0)
    (hp : ∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0)
    (ha : ∀ P ∈ ps, ‖a P‖ ≤ 1)
    (hbeta : ∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) :
    FiniteReconstruction Ext K0 N0 B0 L0 := by
  let s := hybridColumnSupport (nset ×ˢ bset)
  have hfactor := canonical_factor_support Ext hext_ne hext_dvd nset bset N0 B0 hn hb
  refine {
    rows := rows, ts := tSupport s, cs := cSupport s, ms := mSupport s,
    hs := hSupport s, ps := ps, a := a, beta := rectangularBeta s beta,
    divisors := IdealDivisorMasks.divisors, mu := IdealDivisorMasks.sign,
    row_support := hrows, p_support := hp, a_norm := ha,
    t_support := ?_, c_support := ?_, m_support := ?_, h_support := ?_,
    beta_norm := ?_, coefficient_support := ?_, mu_norm := ?_,
    divisor_dvd := ?_, mobius := ?_ }
  · intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact (hfactor d hd).1
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    exact (hfactor d hd).2.1
  · intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    exact (hfactor d hd).2.2.1
  · intro h hh
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hh
    exact (hfactor d hd).2.2.2
  · apply rectangularBeta_norm s beta
    intro d hd
    have hp0 := Finset.mem_product.mp ((mem_hybridColumnSupport _ d).mp hd)
    exact hbeta _ hp0.1 _ hp0.2
  · apply rectangularBeta_support s beta N0 B0
    · intro d hd
      exact (hn _ (Finset.mem_product.mp ((mem_hybridColumnSupport _ d).mp hd)).1).2.2
    · intro d hd
      exact (hb _ (Finset.mem_product.mp ((mem_hybridColumnSupport _ d).mp hd)).2).2
  · exact IdealDivisorMasks.sign_norm
  · intro k hk D hD
    exact (IdealDivisorMasks.mem_divisors k D (hext_ne k (hrows k hk).1)).mp hD
  · intro k hk n
    exact IdealDivisorMasks.coprime_mask_expansion k n (hrows k hk).2.1

theorem canonicalReconstruction_row
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (K0 N0 B0 L0 : ℝ)
    (rows nset bset ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hrows : ∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0)
    (hn : ∀ n ∈ nset, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0)
    (hb : ∀ b ∈ bset, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0)
    (hp : ∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0)
    (ha : ∀ P ∈ ps, ‖a P‖ ≤ 1)
    (hbeta : ∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1)
    (k : Ideal (𝓞 K)) (hk : k ∈ rows) :
    (canonicalReconstruction Ext hext_ne hext_dvd K0 N0 B0 L0 rows nset bset ps a beta
      hrows hn hb hp ha hbeta).row cubic quad k =
      hybridRow cubic quad ps nset bset a beta k := by
  change reconstructedRow _ _ (tSupport (hybridColumnSupport (nset ×ˢ bset)))
    (cSupport _) (mSupport _) (hSupport _) ps a (rectangularBeta _ beta) k = _
  rw [reconstructedRow_rectangle, ← supportedHybridRow_product]
  symm
  apply supportedHybridRow_reconstruct hκ
  · intro p hp0
    have hp1 := Finset.mem_product.mp hp0
    exact ⟨(hn _ hp1.1).2.1, hext_ne _ (hb _ hp1.2).1,
      (hn _ hp1.1).1, (hb _ hp1.2).1⟩
  · intro P hP
    exact (hp P hP).1
  · intro d hd
    have hf := canonical_factor_support Ext hext_ne hext_dvd nset bset N0 B0 hn hb d
      ((mem_hybridColumnSupport _ d).mpr hd)
    exact hsquare k d.common d.residualN d.residualB d.square
      (hrows k hk).1 hf.2.1.1 hf.1.1

/-- Complete raw ideal hybrid estimate.  There is no reconstruction,
coefficient separation, divisor loss or block-energy hypothesis. -/
theorem raw_ideal_hybrid_energy
    (hext_ne : ∀ I, Ext I → I ≠ ⊥)
    (hext_mul : ∀ I J, Ext I → Ext J → Ext (I * J))
    (hext_dvd : ∀ I J, Ext I → J ∣ I → Ext J)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hκ : CubicKernelAxioms Ext cubic)
    (hsquare : ∀ k c m h t, Ext k → Ext c → Ext t →
      quad k ((c * m) * ((c * h) * t ^ 2)) = mask k (c * t) * quad k (m * h))
    (hquadratic : IdealQuadraticInput Ext quad)
    (hcubic : IdealCubicInput Ext cubic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K0 N0 B0 L0 : ℝ,
      1 ≤ K0 → 1 ≤ N0 → 1 ≤ B0 → 1 ≤ L0 →
      ∀ rows nset bset ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, Ext k ∧ Squarefree k ∧ (Ideal.absNorm k : ℝ) ≤ K0) →
      (∀ n ∈ nset, Ext n ∧ Squarefree n ∧ (Ideal.absNorm n : ℝ) ≤ N0) →
      (∀ b ∈ bset, Ext b ∧ (Ideal.absNorm b : ℝ) ≤ B0) →
      (∀ P ∈ ps, Ext P ∧ Squarefree P ∧ (Ideal.absNorm P : ℝ) ≤ L0) →
      ∀ a : Ideal (𝓞 K) → ℂ, ∀ beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ,
      (∀ P ∈ ps, ‖a P‖ ≤ 1) →
      (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow cubic quad ps nset bset a beta k‖ ^ 2) ≤
        C * (K0 * N0 * B0 * L0) ^ eps * (K0 + N0 * B0) * B0 *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := finite_reconstructed_hybrid_energy
    Ext hext_ne hext_mul hext_dvd cubic quad hκ.mul_left hκ.mul_right hκ.norm_le_one
    hquadratic hcubic eps heps
  refine ⟨C, hC, ?_⟩
  intro K0 N0 B0 L0 hK hN hB hL rows nset bset ps hrows hn hb hp a beta ha hbeta
  let d := canonicalReconstruction Ext hext_ne hext_dvd K0 N0 B0 L0
    rows nset bset ps a beta hrows hn hb hp ha hbeta
  have h := hbound K0 N0 B0 L0 hK hN hB hL d
  have he : (∑ k ∈ d.rows, ‖d.row cubic quad k‖ ^ 2) =
      ∑ k ∈ rows, ‖hybridRow cubic quad ps nset bset a beta k‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [canonicalReconstruction_row Ext hext_ne hext_dvd cubic quad hκ hsquare
      K0 N0 B0 L0 rows nset bset ps a beta hrows hn hb hp ha hbeta k hk]
  rw [he] at h
  exact h

#print axioms rectangular_reindex
#print axioms canonicalReconstruction_row
#print axioms raw_ideal_hybrid_energy

end HeckeSkeleton.LowEnergy.RawIdealHybrid
end

