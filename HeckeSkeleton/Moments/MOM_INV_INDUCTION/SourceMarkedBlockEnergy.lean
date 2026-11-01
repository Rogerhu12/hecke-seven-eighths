import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderMarkedWindows

/-!
# A genuine fixed-overlap Mellin block on all complete rows

The two finite prime sums and the original quotient profile are retained
on the left.  Fourier inversion, the exact common-prime identity, the
twenty-four supported tests and the complete physical calibration give
the right hand side.  One pointwise Fourier majorant handles all
independent rowwise profile parameters without a row-count loss.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedBlockEnergy

open NumberField IsDedekindDomain UniqueFactorizationMonoid MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open ProviderMarkedOverlap ProviderMarkedSlots ProviderMarkedReindex
  ProviderMarkedMellin ProviderMarkedMaskedMellin ProviderMarkedTests CommonKernel
open scoped Classical BigOperators nonZeroDivisors FourierTransform

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K} {J : ℕ}

def block (d : MomentData K ω ψ)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (j : Ideal (𝓞 K)) (X U : ℝ) (F : NonzeroIdeal K → SchwartzMap ℝ ℂ)
    (u : NonzeroIdeal K) : ℂ :=
  ∑ p ∈ tuples lists, ∑ n ∈ ProviderMarkedPools.sourcePool X j (primeProduct Finset.univ p),
    originalCoefficient (d.inverseBackground * d.rowCharacter u) a j p n *
      ProviderMarkedMask.value good u.val n *
      ProviderMarkedMask.value good u.val (j * primeProduct Finset.univ p) *
      Expansion.Dyadic.annularProfile
        (ProviderMarkedPools.norm (forward j (primeProduct Finset.univ p) n) / U) *
      ProviderMarkedLogMellin.profile (F u) (ProviderMarkedPools.norm n / X)

def extracted (d : MomentData K ω ψ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (j : Ideal (𝓞 K)) (u : NonzeroIdeal K) : ℂ :=
  ProviderMarkedMask.value good u.val j * extractedScalar (d.inverseBackground * d.rowCharacter u) j

theorem extracted_norm (d : MomentData K ω ψ) (good : HeightOneSpectrum (𝓞 K) → Prop)
    (j : Ideal (𝓞 K)) (u : NonzeroIdeal K) : ‖extracted d good j u‖ ≤ 1 := by
  have he : extracted d good j u =
      (moebius j : ℂ) * idealCoefficient (primeCoefficient K
        (d.inverseBackground * d.rowCharacter u)) j ^ 2 * ProviderMarkedMask.value good u.val j := by
    unfold extracted extractedScalar
    ring
  rw [he]
  exact ProviderMarkedMask.extracted_scalar_norm_le good u.val j _

/-- The actual column after Fourier inversion is the finite sum of
supported original marked polynomials with their exact square-root
scale factors. -/
theorem weighted_column_energy (d : MomentData K ω ψ)
    (rows : Finset (NonzeroIdeal K)) (hdir : d.direction = 1)
    (good : HeightOneSpectrum (𝓞 K) → Prop)
    (hmask : ∀ u ∈ rows, ∀ n, maskValue d u n = ProviderMarkedMask.value good u.val n)
    (hν : ∀ u ∈ rows, ∀ n : NonzeroIdeal K, d.commonMask u n.val = true →
      ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (j : Ideal (𝓞 K))
    (U Y t B : ℝ) (hU : 0 < U) (hY : 0 ≤ Y) (hB : 0 ≤ B)
    (hscale : ∀ i : SchwartzTestPartition.Index,
      SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U ≤ Y)
    (hphysical : ∀ i : SchwartzTestPartition.Index,
      (∑ u ∈ rows, ‖SourceMarkedPhysical.polynomial K d
        (SourceMarkedPhysical.mark Finset.univ
          (fun k => (lists k).image HeightOneSpectrum.asIdeal) (primeWeight a t) j)
        u (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) (piece t i)‖ ^ 2) ≤ B) :
    (∑ u ∈ rows, ‖weightedCanonicalColumn (d.inverseBackground * d.rowCharacter u) lists a
      (ProviderMarkedMask.value good u.val) (columns Y j) U t‖ ^ 2) ≤ 576 * Y * B := by
  have heq : (∑ u ∈ rows, ‖weightedCanonicalColumn (d.inverseBackground * d.rowCharacter u)
      lists a (ProviderMarkedMask.value good u.val) (columns Y j) U t‖ ^ 2) =
      ∑ u ∈ rows, ‖∑ i : SchwartzTestPartition.Index,
        (Real.sqrt (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) : ℂ) *
          SourceMarkedPhysical.polynomial K d
            (SourceMarkedPhysical.mark Finset.univ
              (fun k => (lists k).image HeightOneSpectrum.asIdeal) (primeWeight a t) j)
            u (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) (piece t i)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [weightedColumn_eq_physical_pieces d u hdir good (hmask u hu) (hν u hu)
      lists a j U Y t hU hscale]
  rw [heq]
  have hb := finite_piece_energy rows (Finset.univ : Finset SchwartzTestPartition.Index)
    (fun i u => SourceMarkedPhysical.polynomial K d
      (SourceMarkedPhysical.mark Finset.univ
        (fun k => (lists k).image HeightOneSpectrum.asIdeal) (primeWeight a t) j)
      u (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) (piece t i))
    (fun i => (Real.sqrt
      (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) : ℂ)) Y B hY hB
    (fun i hi => by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (mul_pos (SchwartzTestPartition.scale_pos _) hU).le]
      exact hscale i) (fun i hi => hphysical i)
  have hcard : ((Finset.univ : Finset SchwartzTestPartition.Index).card : ℝ) ^ 2 = 576 := by
    norm_num [SchwartzTestPartition.Index]
  simpa only [hcard] using hb

variable (K) (c : TargetContext K)

/-- The Fourier constant and height exponent are fixed before the
complete row ball and every actual rowwise parameter.  The physical
piece bounds used here are supplied by `SourceMarkedComplete`; this
theorem is only the finite Fubini and shared-kernel assembly. -/
theorem exists_block_bound (degree : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (rows : Finset (NonzeroIdeal K)), d.direction = 1 →
      ∀ (good : HeightOneSpectrum (𝓞 K) → Prop),
      (∀ u ∈ rows, ∀ n, maskValue d u n = ProviderMarkedMask.value good u.val n) →
      (∀ u ∈ rows, ∀ n : NonzeroIdeal K, d.commonMask u n.val = true →
        ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ n.val → UnramifiedAt K d.inverseBackground p) →
      ∀ {J : ℕ} (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K))),
      Pairwise (Disjoint on lists) →
      ∀ (a : Fin J → Ideal (𝓞 K) → ℂ) (j : Ideal (𝓞 K)), Squarefree j →
      (∀ p ∈ tuples lists, IsCoprime j (primeProduct Finset.univ p)) →
      ∀ (X U Pcap Y T E : ℝ), 0 < X → 0 < U → 0 ≤ Y → 0 ≤ T → 0 ≤ E →
      (∀ p ∈ tuples lists, ProviderMarkedPools.norm (primeProduct Finset.univ p) ≤ Pcap) →
      X * Pcap / ProviderMarkedPools.norm j = Y →
      (∀ i : SchwartzTestPartition.Index,
        SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U ≤ Y) →
      ∀ (B D ar ni xi : NonzeroIdeal K → ℝ),
      (∀ u ∈ rows, 0 < B u) → (∀ u ∈ rows, 0 ≤ D u) →
      (∀ u ∈ rows, |ar u| ≤ 8) →
      (∀ u ∈ rows, |ni u| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T)) →
      (∀ u ∈ rows, Function.support (ProviderMarkedLogMellin.profile
        (actualInverseLogProfile (B u) (D u) (ar u) (ni u) (xi u))) ⊆ Set.Iic 2) →
      (∀ t : ℝ, ∀ i : SchwartzTestPartition.Index,
        (∑ u ∈ rows, ‖SourceMarkedPhysical.polynomial K d
          (SourceMarkedPhysical.mark Finset.univ
            (fun k => (lists k).image HeightOneSpectrum.asIdeal) (primeWeight a t) j)
          u (SchwartzTestPartition.scale (SchwartzTestPartition.exponent i) * U) (piece t i)‖ ^ 2) ≤
          E * ((1 + |t|) ^ degree) ^ 2) →
      (∑ u ∈ rows, ‖block d lists a good j X U
        (fun u => actualInverseLogProfile (B u) (D u) (ar u) (ni u) (xi u)) u‖ ^ 2) ≤
        C * ((1 + T) ^ (degree + 2)) ^ 2 * Y * E := by
  obtain ⟨CF, hCF, hfourier⟩ := actual_source_rowwise_fourier_envelope K c degree
  refine ⟨576 * CF ^ 2, by positivity, ?_⟩
  intro ω ψ d rows hdir good hmask hν J lists hdis a j hj hcop
    X U Pcap Y T E hX hU hY hT hE hPcap hYeq hscale B D ar ni xi hB hD har hni hsupport hphysical
  let F : NonzeroIdeal K → SchwartzMap ℝ ℂ := fun u =>
    actualInverseLogProfile (B u) (D u) (ar u) (ni u) (xi u)
  let child : ℝ → {u // u ∈ rows} → ℂ := fun t u =>
    extracted d good j u.val * columnPhase t (Real.log (ProviderMarkedPools.norm j)) *
      columnPhase t (-Real.log X) * columnPhase t (Real.log U) *
        weightedCanonicalColumn (d.inverseBackground * d.rowCharacter u.val) lists a
          (ProviderMarkedMask.value good u.val.val) (columns Y j) U t
  have hchild_meas (u : {u // u ∈ rows}) : AEStronglyMeasurable (fun t : ℝ => child t u) := by
    apply Continuous.aestronglyMeasurable
    exact (((continuous_const.mul (continuous_columnPhase _)).mul (continuous_columnPhase _)).mul
      (continuous_columnPhase _)).mul (weightedColumn_continuous _ lists a _ (columns Y j)
        (fun n hn => (Finset.mem_filter.mp hn).2.1.ne_zero) U hU)
  have hpoint (t : ℝ) : Real.sqrt (∑ u : {u // u ∈ rows}, ‖child t u‖ ^ 2) ≤
      Real.sqrt (576 * Y * E) * (1 + ‖t‖) ^ degree := by
    have hcol := weighted_column_energy d rows hdir good hmask hν lists a j U Y t
      (E * ((1 + |t|) ^ degree) ^ 2) hU hY (by positivity) hscale (hphysical t)
    have hs : (∑ u : {u // u ∈ rows}, ‖child t u‖ ^ 2) ≤
        576 * Y * (E * ((1 + |t|) ^ degree) ^ 2) := by
      apply le_trans _ hcol
      rw [← Finset.sum_attach rows]
      apply Finset.sum_le_sum
      intro u hu
      simp only [child, norm_mul, norm_columnPhase, mul_one, mul_pow]
      have hscalar := extracted_norm d good j u.val
      exact mul_le_of_le_one_left (sq_nonneg _)
        (by nlinarith [norm_nonneg (extracted d good j u.val)])
    apply (Real.sqrt_le_sqrt hs).trans_eq
    rw [show 576 * Y * (E * ((1 + |t|) ^ degree) ^ 2) =
      (576 * Y * E) * ((1 + |t|) ^ degree) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.norm_eq_abs]
  have h := hfourier T hT {u // u ∈ rows} (fun u => B u.val) (fun u => D u.val)
    (fun u => ar u.val) (fun u => ni u.val) (fun u => xi u.val)
    (fun u => hB u.val u.property) (fun u => hD u.val u.property)
    (fun u => har u.val u.property) (fun u => hni u.val u.property)
    child hchild_meas (Real.sqrt (576 * Y * E)) (Real.sqrt_nonneg _) hpoint
  have hid (u : {u // u ∈ rows}) :
      block d lists a good j X U F u.val = ∫ t : ℝ, (𝓕 (F u.val)) t * child t u := by
    rw [block, ProviderMarkedLogMellin.fixed_selected_masked_annular_eq_integral lists hdis
      a good u.val.val j hj hcop (d.inverseBackground * d.rowCharacter u.val)
      X U Pcap hX hU hPcap (F u.val) (hsupport u.val u.property), hYeq,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by dsimp only [child, extracted]; ring
  have hsum : (∑ u ∈ rows, ‖block d lists a good j X U F u‖ ^ 2) =
      ∑ u : {u // u ∈ rows}, ‖∫ t : ℝ, (𝓕 (F u.val)) t * child t u‖ ^ 2 := by
    rw [← Finset.sum_attach rows]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hid u]
  rw [hsum]
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 576 * Y * E)] at hs
  exact hs.trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.SourceMarkedBlockEnergy

end
