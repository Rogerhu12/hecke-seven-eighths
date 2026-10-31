import HeckeSkeleton.GramAssembly.Bookkeeping

/-!
GR-12-ASSEMBLY, aggregation over the gcd parts `C` and the Mobius divisors `D`:
partial sums of the residual majorant over finite sets of frequency orbits.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.GramAssembly.Aggregate

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.Arithmetic.AllowedGeneratorSectionDraft
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
open ActualProbeGaussFourierDraft ActualProbePairNormDraft ActualAdditiveGramDraft
open ActualGramJointChartDraft ActualGramJointChartCoverDraft
open ActualGramMajorantDraft ActualRowBallDualChartDraft
open ActualDenominatorGramWeightDraft ActualRowBallResidualAnalyticDraft
open ActualRowBallResidualMaskedDraft ActualAllowedTotalNormProviderDraft
open ActualChoiceMaskedTotalNormDraft ActualGeneratorChoiceDraft ActualGramJointMeanDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualGoodPrimeDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallResidualScalarDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualRowBallDualResidualNormDraft
open HeckeGeneral.Analysis.ActualGramExceptionalCountDraft HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.ActualExceptionalWeightedShellDraft
open HeckeSkeleton.GramAssembly.Bookkeeping
open scoped Classical BigOperators ContDiff nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (w : GeneratorMaskWitness K)
local notation "S" => (w.S : Set (HeightOneSpectrum (𝓞 K)))
local notation "E" => ExteriorIdeal K S
local notation "NZ" => NonzeroRingElements (Set.integer S K)
local notation "gen" => probeGenerator K S w.D
local notation "Orb" => SIntegerOrbits K S (sixthPowerUnits K S)

variable [MeasurableSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (w.S : Set (HeightOneSpectrum (𝓞 K))))]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
variable [∀ v, (μv v).IsAddHaarMeasure]
variable (P : ProbeData K (w.S : Set (HeightOneSpectrum (𝓞 K))))

theorem sq_div_mul_eq (Y x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (Y / (x * y)) ^ 2 = Y ^ 2 * (x ^ (-(2 : ℝ)) * y ^ (-(2 : ℝ))) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le, Real.rpow_two, Real.rpow_two]
  field_simp

theorem exteriorNorm_eq_idealNorm (I : E) : exteriorNorm K S I = idealNorm K I.val := rfl

/-- The exceptional part of the aggregation. -/
theorem exc_total (C0e : ℝ)
    (hexc : ∀ (A D : Finset (NonzeroIdeal K)) (Q Y T M : ℝ), 0 < Q → 0 < Y → 0 < T → 0 ≤ M →
      (Q / Y ^ 3) * M * (∑ C ∈ A, ∑ d ∈ D, exceptionalShellColumnMass K S C d Y T) ≤
        C0e * M * (Q / Y) * T ^ (1 / 6 : ℝ))
    (hC0e : 0 ≤ C0e) (u0 : ℝ) (hu0 : 0 ≤ u0) (Y : ℝ) (hY : 0 < Y) (a : ℝ) (ha : 0 < a)
    (M : ℕ) (cp : Finset E) (divs : E → Finset E) :
    ∑ C ∈ cp, ∑ D ∈ divs C,
      (u0 * exteriorNorm K S C * (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        ∑ k ∈ Finset.range M,
          (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
            Dyadic.mfun a ((2 : ℝ) ^ k / 2) ≤
      u0 * (C0e * Y ^ 2 * (Dyadic.Ke * a ^ (1 / 6 : ℝ))) := by
  have hY3 : (0 : ℝ) < Y ^ 3 := by positivity
  have hq : ∀ C : E, 0 < exteriorNorm K S C := fun C => idealNorm_pos K C.val
  set Dall : Finset (NonzeroIdeal K) := (cp.biUnion divs).image (fun D : E => D.val) with hDall
  set A : Finset (NonzeroIdeal K) := cp.image (fun C : E => C.val) with hA
  have hmass0 : ∀ (C D : E) (k : ℕ), 0 ≤ exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
    intro C D k
    unfold exceptionalShellColumnMass
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (idealNorm_pos K C.val).le (sq_nonneg _))
  have hSk : ∀ k : ℕ, ∑ C ∈ cp, ∑ D ∈ divs C,
      exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) ≤
      C0e * Y ^ 2 * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ) := by
    intro k
    have hT : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h1 : ∑ C ∈ cp, ∑ D ∈ divs C, exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) ≤
        ∑ C ∈ cp, ∑ D ∈ cp.biUnion divs,
          exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro D hD
        exact Finset.mem_biUnion.mpr ⟨C, hC, hD⟩
      · intro D _ _
        exact hmass0 C D k
    have h2 : ∑ C ∈ cp, ∑ D ∈ cp.biUnion divs,
          exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) =
        ∑ c ∈ A, ∑ d ∈ Dall, exceptionalShellColumnMass K S c d Y ((2 : ℝ) ^ k) := by
      rw [hA, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro C _
      rw [hDall, Finset.sum_image (fun x _ y _ h => Subtype.ext h)]
    have h3 := hexc A Dall (Y ^ 3) Y ((2 : ℝ) ^ k) 1 hY3 hY hT zero_le_one
    have h4 : (Y ^ 3 / Y ^ 3) * 1 * (∑ c ∈ A, ∑ d ∈ Dall,
        exceptionalShellColumnMass K S c d Y ((2 : ℝ) ^ k)) = ∑ c ∈ A, ∑ d ∈ Dall,
        exceptionalShellColumnMass K S c d Y ((2 : ℝ) ^ k) := by
      rw [div_self hY3.ne']; ring
    rw [h4] at h3
    have h5 : C0e * 1 * (Y ^ 3 / Y) * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ) =
        C0e * Y ^ 2 * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ) := by
      field_simp
    rw [h5] at h3
    exact h1.trans (h2.le.trans h3)
  -- rewrite the summand as `u0 * ∑ k, m_k * mass_k`
  have hrew : ∀ (C D : E), (u0 * exteriorNorm K S C *
        (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
      ∑ k ∈ Finset.range M,
        (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) =
      u0 * ∑ k ∈ Finset.range M, Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
        exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
    intro C D
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold exceptionalShellColumnMass
    rw [exteriorNorm_eq_idealNorm K w C, exteriorNorm_eq_idealNorm K w D]
    ring
  simp_rw [hrew]
  have hfin : ∑ C ∈ cp, ∑ D ∈ divs C, u0 * ∑ k ∈ Finset.range M, Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
        exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) =
      u0 * ∑ k ∈ Finset.range M, Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
        ∑ C ∈ cp, ∑ D ∈ divs C, exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
    have e1 : ∑ C ∈ cp, ∑ D ∈ divs C, u0 * ∑ k ∈ Finset.range M,
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
            exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) =
        u0 * ∑ C ∈ cp, ∑ D ∈ divs C, ∑ k ∈ Finset.range M,
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
            exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
      simp only [Finset.mul_sum]
    have e2 : ∑ C ∈ cp, ∑ D ∈ divs C, ∑ k ∈ Finset.range M,
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
            exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) =
        ∑ k ∈ Finset.range M, ∑ C ∈ cp, ∑ D ∈ divs C,
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
            exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) := by
      calc _ = ∑ C ∈ cp, ∑ k ∈ Finset.range M, ∑ D ∈ divs C,
            Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
              exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k) :=
            Finset.sum_congr rfl (fun C _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    rw [e1, e2]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.mul_sum]
  rw [hfin]
  have hser := Dyadic.exceptional_series a ha M
  have hm0 : ∀ k : ℕ, 0 ≤ Dyadic.mfun a ((2 : ℝ) ^ k / 2) := fun k =>
    Dyadic.mfun_nonneg a _ ha (by positivity)
  calc u0 * ∑ k ∈ Finset.range M, Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
        ∑ C ∈ cp, ∑ D ∈ divs C, exceptionalShellColumnMass K S C.val D.val Y ((2 : ℝ) ^ k)
      ≤ u0 * ∑ k ∈ Finset.range M, Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
          (C0e * Y ^ 2 * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hu0
        exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hSk k) (hm0 k))
    _ = u0 * ((C0e * Y ^ 2) * ∑ k ∈ Finset.range M,
          Dyadic.mfun a ((2 : ℝ) ^ k / 2) * ((2 : ℝ) ^ k) ^ (1 / 6 : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ u0 * ((C0e * Y ^ 2) * (Dyadic.Ke * a ^ (1 / 6 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hu0
        exact mul_le_mul_of_nonneg_left hser (by positivity)


/-- The ordinary part of the aggregation (uses the ideal double shell bound). -/
theorem ord_total (c0 : ℝ) (hc0 : 0 ≤ c0) (C9 : ℝ) (hC9 : 0 < C9)
    (h9 : ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C9 * (1 + Real.log (2 + Λ)) / Λ)
    (u0 : ℝ) (hu0 : 0 ≤ u0) (Y : ℝ) (hY : 0 < Y) (a : ℝ) (ha : 0 < a)
    (M : ℕ) (cp : Finset E) (divs : E → Finset E) :
    ∑ C ∈ cp, ∑ D ∈ divs C,
      (u0 * exteriorNorm K S C * (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        ∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3)) ≤
      u0 * (c0 * Dyadic.Ko * C9 * a ^ 2 * Y * (1 + Real.log (2 + Y / a))) := by
  have hΛ : 0 < Y / a := div_pos hY ha
  obtain ⟨hsum, htsum⟩ := h9 (Y / a) hΛ
  set f : NonzeroIdeal K × NonzeroIdeal K → ℝ := fun IJ =>
    (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
      min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / (Y / a)) ^ 3) with hf
  have hf0 : ∀ IJ, 0 ≤ f IJ := fun IJ => mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (idealNorm_pos K IJ.1).le _)
      (Real.rpow_nonneg (idealNorm_pos K IJ.2).le _))
    (le_min zero_le_one (pow_nonneg (div_nonneg (mul_nonneg (idealNorm_pos K IJ.1).le
      (idealNorm_pos K IJ.2).le) hΛ.le) 3))
  -- pointwise bound
  have hpt : ∀ C ∈ cp, ∀ D ∈ divs C,
      (u0 * exteriorNorm K S C * (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        ∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun a ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3)) ≤
      (u0 * c0 * Dyadic.Ko * a * Y ^ 2) * f (C.val, D.val) := by
    intro C _ D _
    have hqC : 0 < exteriorNorm K S C := idealNorm_pos K C.val
    have hqD : 0 < exteriorNorm K S D := idealNorm_pos K D.val
    set Nn : ℝ := Y / (exteriorNorm K S C * exteriorNorm K S D) with hNn
    have hNpos : 0 < Nn := by positivity
    have hser := Dyadic.ordinary_series a Nn ha hNpos M
    have hrew : (u0 * exteriorNorm K S C * Nn ^ 2) *
        ∑ k ∈ Finset.range M, (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
          (Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3)) =
        (u0 * c0 * Nn ^ 2) * ∑ k ∈ Finset.range M, (2 : ℝ) ^ k *
          (Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    rw [hrew]
    have hNsq : Nn ^ 2 = Y ^ 2 * (exteriorNorm K S C ^ (-(2 : ℝ)) * exteriorNorm K S D ^ (-(2 : ℝ))) :=
      sq_div_mul_eq Y _ _ hqC hqD
    have hamin : a / Nn = exteriorNorm K S C * exteriorNorm K S D / (Y / a) := by
      rw [hNn]; field_simp
    calc (u0 * c0 * Nn ^ 2) * ∑ k ∈ Finset.range M, (2 : ℝ) ^ k *
          (Dyadic.mfun a ((2 : ℝ) ^ k / 2) * min 1 (((2 : ℝ) ^ k / Nn) ^ 3))
        ≤ (u0 * c0 * Nn ^ 2) * (Dyadic.Ko * a * min 1 ((a / Nn) ^ 3)) :=
          mul_le_mul_of_nonneg_left hser (by positivity)
      _ = (u0 * c0 * Dyadic.Ko * a * Y ^ 2) * f (C.val, D.val) := by
          rw [hNsq, hamin]
          simp only [hf]
          rw [exteriorNorm_eq_idealNorm K w C, exteriorNorm_eq_idealNorm K w D]
          ring
  -- summing
  have hsum1 : ∑ C ∈ cp, ∑ D ∈ divs C, f (C.val, D.val) ≤ ∑' IJ, f IJ := by
    have hinj : Function.Injective (fun x : (Σ _ : E, E) => (x.1.val, x.2.val)) := by
      rintro ⟨C, D⟩ ⟨C', D'⟩ h
      simp only [Prod.mk.injEq] at h
      have h1 : C = C' := Subtype.ext h.1
      have h2 : D = D' := Subtype.ext h.2
      subst h1; subst h2; rfl
    calc ∑ C ∈ cp, ∑ D ∈ divs C, f (C.val, D.val)
        = ∑ x ∈ cp.sigma divs, f (x.1.val, x.2.val) := Finset.sum_sigma' _ _ _
      _ = ∑ p ∈ (cp.sigma divs).image (fun x : (Σ _ : E, E) => (x.1.val, x.2.val)), f p :=
          (Finset.sum_image (fun x _ y _ h => hinj h)).symm
      _ ≤ ∑' IJ, f IJ := hsum.sum_le_tsum _ (fun p _ => hf0 p)
  calc ∑ C ∈ cp, ∑ D ∈ divs C, _ ≤ ∑ C ∈ cp, ∑ D ∈ divs C,
        (u0 * c0 * Dyadic.Ko * a * Y ^ 2) * f (C.val, D.val) :=
        Finset.sum_le_sum (fun C hC => Finset.sum_le_sum (fun D hD => hpt C hC D hD))
    _ = (u0 * c0 * Dyadic.Ko * a * Y ^ 2) * ∑ C ∈ cp, ∑ D ∈ divs C, f (C.val, D.val) := by
        simp only [Finset.mul_sum]
    _ ≤ (u0 * c0 * Dyadic.Ko * a * Y ^ 2) * (C9 * (1 + Real.log (2 + Y / a)) / (Y / a)) := by
        apply mul_le_mul_of_nonneg_left (hsum1.trans htsum)
        have := Dyadic.Ko_nonneg
        positivity
    _ = _ := by
        field_simp


/-- Partial sums of the residual majorant over a finite set of frequency orbits. -/
theorem majorant_partial_le (hP : P.arithmetic = w.D) (Bg Bt K1 : ℝ) (Jg Jt J : ℕ)
    (hgood : GoodScalar K w μv P Bg Jg) (htriv : TrivScalar K w μv P Bt Jt)
    (hBg : 0 ≤ Bg) (hBt : 0 ≤ Bt) (hg : Bg ≤ K1) (ht : Bt ≤ K1) (hJg : Jg ≤ J) (hJt : Jt ≤ J)
    (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hdiv : ∀ (C : E) (T : ℝ), 0 < T → ∀ G : Finset Orb,
      (∀ q ∈ G, w.D.generator C ∣ q.out.val ∧
        (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val ≤ T) →
      (G.card : ℝ) ≤ c0 * T / exteriorNorm K S C)
    (C0e : ℝ) (hC0e : 0 ≤ C0e)
    (hexc : ∀ (A D : Finset (NonzeroIdeal K)) (Q Y T M : ℝ), 0 < Q → 0 < Y → 0 < T → 0 ≤ M →
      (Q / Y ^ 3) * M * (∑ C ∈ A, ∑ d ∈ D, exceptionalShellColumnMass K S C d Y T) ≤
        C0e * M * (Q / Y) * T ^ (1 / 6 : ℝ))
    (C9 : ℝ) (hC9 : 0 < C9)
    (h9 : ∀ Λ : ℝ, 0 < Λ →
      Summable (fun IJ : NonzeroIdeal K × NonzeroIdeal K =>
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ∧
      (∑' IJ : NonzeroIdeal K × NonzeroIdeal K,
        (idealNorm K IJ.1) ^ (-(2 : ℝ)) * (idealNorm K IJ.2) ^ (-(2 : ℝ)) *
          min 1 ((idealNorm K IJ.1 * idealNorm K IJ.2 / Λ) ^ 3)) ≤
        C9 * (1 + Real.log (2 + Λ)) / Λ)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) (F : Finset Orb) (M : ℕ)
    (hM : ∀ q ∈ F, Dyadic.shellIndex (sIntegerOrbitNorm K S (sixthPowerUnits K S) q).val < M) :
    ∑ q ∈ F, residualMajorant K w μv P Y η r q ≤
      (K1 * (1 + |η|) ^ J) *
        (C0e * Y ^ 2 * (Dyadic.Ke * (r.val * Y ^ 2) ^ (1 / 6 : ℝ)) +
         c0 * Dyadic.Ko * C9 * (r.val * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (r.val * Y ^ 2)))) := by
  have ha : 0 < r.val * Y ^ 2 := mul_pos r.property (pow_pos hY 2)
  have hK1 : 0 ≤ K1 := hBg.trans hg
  have hu0 : 0 ≤ K1 * (1 + |η|) ^ J := by positivity
  set cp := finiteCommonParts K S (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y)
    (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y) with hcp
  set divs : E → Finset E := fun C => residualMobiusDivisorSet K w C
    (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y)
    (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y) with hdivs
  have hswap : ∑ q ∈ F, residualMajorant K w μv P Y η r q =
      ∑ C ∈ cp, ∑ D ∈ divs C, ∑ q ∈ F, ‖rowBallResidualSum K w μv P Y η r C D q.out‖ := by
    unfold residualMajorant
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    rw [Finset.sum_comm]
  rw [hswap]
  have hper : ∀ C ∈ cp, ∀ D ∈ divs C, ∑ q ∈ F, ‖rowBallResidualSum K w μv P Y η r C D q.out‖ ≤
      (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
            Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2)) +
      (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3))) := by
    intro C _ D _
    have := perCD_sum K w μv P hP Bg Bt K1 Jg Jt J hgood htriv hBg hBt hg ht hJg hJt c0 hdiv
      C D Y η hY r F M hM
    rw [← mul_add]
    exact this
  calc _ ≤ ∑ C ∈ cp, ∑ D ∈ divs C,
        ((K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
            Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2)) +
      (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3)))) :=
        Finset.sum_le_sum (fun C hC => Finset.sum_le_sum (fun D hD => hper C hC D hD))
    _ = (∑ C ∈ cp, ∑ D ∈ divs C,
        (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (Nat.card (ActualExceptionalOrbitCutoff K S C.val ((2 : ℝ) ^ k / exteriorNorm K S C)) : ℝ) *
            Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2))) +
      (∑ C ∈ cp, ∑ D ∈ divs C,
      (K1 * (1 + |η|) ^ J * exteriorNorm K S C *
          (Y / (exteriorNorm K S C * exteriorNorm K S D)) ^ 2) *
        (∑ k ∈ Finset.range M,
          (c0 * (2 : ℝ) ^ k / exteriorNorm K S C) *
            (Dyadic.mfun (r.val * Y ^ 2) ((2 : ℝ) ^ k / 2) *
              min 1 (((2 : ℝ) ^ k / (Y / (exteriorNorm K S C * exteriorNorm K S D))) ^ 3)))) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ (K1 * (1 + |η|) ^ J) * (C0e * Y ^ 2 * (Dyadic.Ke * (r.val * Y ^ 2) ^ (1 / 6 : ℝ))) +
        (K1 * (1 + |η|) ^ J) * (c0 * Dyadic.Ko * C9 * (r.val * Y ^ 2) ^ 2 * Y *
          (1 + Real.log (2 + Y / (r.val * Y ^ 2)))) :=
        add_le_add (exc_total K w C0e hexc hC0e _ hu0 Y hY _ ha M cp divs)
          (ord_total K w c0 hc0 C9 hC9 h9 _ hu0 Y hY _ ha M cp divs)
    _ = _ := by ring

end HeckeSkeleton.GramAssembly.Aggregate
