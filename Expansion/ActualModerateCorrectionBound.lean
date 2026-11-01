import HeckeSkeleton.ExpansionModels.LargeRowAllScales
import Expansion.ActualRowStripBounds

/-!
# A fixed polynomial scale budget on the full moderate sweep

The original finite tuple/subset correction is estimated directly on the
larger high-bin swept tube.  Prime-window counting and actual tuple
injectivity turn its finite scalar mass into a fixed Z power.  No final
prime cancellation, local compensation quotient, or moving bound is
assumed.  This coarse estimate is used only for truncations and faces.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.CoarseEuler
open HighBinVerified.NormFormActual HighBinVerified.NormFormFullCorrection
open HeckeSkeleton.Expansion.SmallRows HeckeSkeleton.Expansion.LargeRows
open HeckeSkeleton.HeckeUniformStripGrowth HeckeSkeleton.HeckeDeletedEulerControl
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.ActualEulerLogarithm HeckeGeneral.Bridge
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem exists_actual_moderate_fullCorrection_mass_bound
    {e eta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
      (Z : ℝ) (a : ℝ), 51 / 100 ≤ a → a ≤ 1 → ∀ (P : ProbeData K S) (psi : HeckeCharacter K)
      (u : FrequencyRow K S) (s w z : ℂ), (s, w, z) ∈ sweptTube a e →
      s.re ≤ 5 → -(1 / 1000 : ℝ) ≤ w.re → z.re ≤ 3 →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤
            (C * largeCorrectionMass K S g T Z (10 : ℝ)) * frequencyRowNorm K S u ^ eta := by
  obtain ⟨C, hC, hrow⟩ := exists_uniform_rowCorrection_subpower K S
    he he1 heta
  refine ⟨C, hC, ?_⟩
  intro g T Z a ha ha1 P psi u s w z hv hs hw hz
  have hinner (p : Fin g.slots → ExteriorPrime K S) :
      ‖∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        (-1 : ℂ) ^ J.card * (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1) *
          conj (heckeIdealCoefficient K psi (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
          (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^ (s + z - 1) *
          rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
            ((Finset.univ \ J).image p) u s w z‖ ≤
        (∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) *
            exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) *
            markedBound ^ ((Finset.univ \ J).image p).card) *
          (C * frequencyRowNorm K S u ^ eta) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro J _
    have hselpos : 0 < exteriorNorm K S (subsetPrimeIdeal K S p J) :=
      idealNorm_pos K _
    have hmarkpos : 0 < exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) :=
      idealNorm_pos K _
    have hsel : ‖(exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1)‖ ≤
        exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hselpos]
      apply Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ exteriorNorm K S (subsetPrimeIdeal K S p J) from one_le_idealNorm K _)
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hmark : ‖(exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^
        (s + z - 1)‖ ≤
        exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hmarkpos]
      apply Real.rpow_le_rpow_of_exponent_le
        (show 1 ≤ exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) from
          one_le_idealNorm K _)
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re]
      linarith
    have hc := norm_heckeIdealCoefficient_le_one K psi
      (subsetPrimeIdeal K S p (Finset.univ \ J)).val
    have he := hrow P psi ((Finset.univ \ J).image p) u a ha ha1 (s, w, z) hv
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_conj]
    calc
      _ ≤ (exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) * 1) *
          exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) *
          (C * frequencyRowNorm K S u ^ eta * markedBound ^ ((Finset.univ \ J).image p).card) := by
        have hsel0 := Real.rpow_nonneg hselpos.le ((10 : ℝ) - 3)
        have hmark0 := Real.rpow_nonneg hmarkpos.le ((10 : ℝ) + 1)
        exact mul_le_mul
          (mul_le_mul (mul_le_mul hsel hc (norm_nonneg _) hsel0)
            hmark (norm_nonneg _) (mul_nonneg hsel0 zero_le_one))
          he (norm_nonneg _)
          (mul_nonneg (mul_nonneg hsel0 zero_le_one) hmark0)
      _ = _ := by ring
  unfold compensatedRowFullCorrection
  dsimp only
  calc
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ‖(∏ i : Fin g.slots, windowWeight K S g Z i (p i)) *
          ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            (-1 : ℂ) ^ J.card * (exteriorNorm K S (subsetPrimeIdeal K S p J) : ℂ) ^ (z - w - 1) *
              conj (heckeIdealCoefficient K psi (subsetPrimeIdeal K S p (Finset.univ \ J)).val) *
              (exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) : ℂ) ^ (s + z - 1) *
              rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
                ((Finset.univ \ J).image p) u s w z‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i : Fin g.slots, ‖windowWeight K S g Z i (p i)‖) *
          ((∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
            exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) *
              exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) *
              markedBound ^ ((Finset.univ \ J).image p).card) *
            (C * frequencyRowNorm K S u ^ eta)) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_left (hinner p) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (C * largeCorrectionMass K S g T Z (10 : ℝ)) * frequencyRowNorm K S u ^ eta := by
      unfold largeCorrectionMass
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro J _
      ring

/-- The original finite mass has one fixed polynomial bound, uniformly
in the ray filter and original scale.  Tuple injectivity is obtained from
the disjoint windows, and every subset norm is its actual ideal norm. -/
theorem exists_actual_moderate_correctionMass_bound (g : PrimeWindowGeometry) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ T : Finset (HeckeCharacter K),
        largeCorrectionMass K S g T Z 10 ≤ C * Z ^ (19 / 6 : ℝ) := by
  obtain ⟨A, hA, hcount⟩ := exists_primeWindow_linear_count K S
  obtain ⟨M, hM, hprofile⟩ := exists_primeWindow_profile_norm_bound g
  obtain ⟨Z0, hZ0, hscale⟩ := HighBinVerified.NormFormPrimeCap.exists_primeScale_cutoff g
  have hmarked0 : 0 ≤ markedBound := zero_le_one.trans one_le_markedBound
  let C : ℝ := A ^ g.slots * M ^ g.slots * (2 : ℝ) ^ g.slots *
    ((2 : ℝ) ^ g.slots) ^ 18 * markedBound ^ g.slots
  have hC : 0 < C := by
    have hmark : 0 < markedBound := zero_lt_one.trans_le one_le_markedBound
    dsimp [C]
    positivity
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z hZ T
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  let X : ℝ := primeScale g Z
  have hX : 1 ≤ X := (by norm_num : (1 : ℝ) ≤ 2).trans (hscale Z hZ)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  let Q : ℝ := (2 * X) ^ g.slots
  have hQ : 1 ≤ Q := one_le_pow₀ (by linarith)
  let tuples := Fintype.piFinset (fun i => primeWindow K S g T Z i)
  have hsubset (p : Fin g.slots → ExteriorPrime K S) (hp : p ∈ tuples)
      (J : Finset (Fin g.slots)) : exteriorNorm K S (subsetPrimeIdeal K S p J) ≤ Q := by
    have hp' := Fintype.mem_piFinset.mp hp
    have hinj := actual_primeWindow_tuple_injective K S g T Z p hp'
    rw [subsetPrimeIdeal_norm_eq_prod K S g p hinj]
    calc
      _ ≤ ∏ _i ∈ J, 2 * X := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro i _
        exact (actual_primeWindow_norm_range K S g T Z i (p i) (hp' i)).2.2.le
      _ = (2 * X) ^ J.card := by simp only [Finset.prod_const]
      _ ≤ Q := pow_le_pow_right₀ (by linarith)
        (by simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ J))
  have hmarked (p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) :
      markedBound ^ ((Finset.univ \ J).image p).card ≤ markedBound ^ g.slots := by
    apply pow_le_pow_right₀ one_le_markedBound
    exact (Finset.card_image_le).trans
      (by simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := J)))
  have hweights (p : Fin g.slots → ExteriorPrime K S) :
      (∏ i : Fin g.slots, ‖windowWeight K S g Z i (p i)‖) ≤ M ^ g.slots := by
    calc
      _ ≤ ∏ _i : Fin g.slots, M :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hprofile i _)
      _ = _ := by simp
  have hinner (p : Fin g.slots → ExteriorPrime K S) (hp : p ∈ tuples) :
      (∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) *
          exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) *
          markedBound ^ ((Finset.univ \ J).image p).card) ≤
        (2 : ℝ) ^ g.slots * (Q ^ 18 * markedBound ^ g.slots) := by
    have hterm (J : Finset (Fin g.slots)) :
        exteriorNorm K S (subsetPrimeIdeal K S p J) ^ ((10 : ℝ) - 3) *
          exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) ^ ((10 : ℝ) + 1) *
          markedBound ^ ((Finset.univ \ J).image p).card ≤ Q ^ 18 * markedBound ^ g.slots := by
      have hsel0 : 0 ≤ exteriorNorm K S (subsetPrimeIdeal K S p J) :=
        (idealNorm_pos K _).le
      have hmark0 : 0 ≤ exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)) :=
        (idealNorm_pos K _).le
      have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
      norm_num only [show (10 : ℝ) - 3 = 7 by norm_num,
        show (10 : ℝ) + 1 = 11 by norm_num, Real.rpow_ofNat]
      calc
        _ ≤ (Q ^ 7 * Q ^ 11) * markedBound ^ g.slots := by
          exact mul_le_mul
            (mul_le_mul
              (pow_le_pow_left₀ hsel0 (hsubset p hp J) 7)
              (pow_le_pow_left₀ hmark0 (hsubset p hp (Finset.univ \ J)) 11)
              (pow_nonneg hmark0 11) (pow_nonneg hQ0 7))
            (hmarked p J) (pow_nonneg hmarked0 _)
            (mul_nonneg (pow_nonneg hQ0 7) (pow_nonneg hQ0 11))
        _ = _ := by rw [← pow_add]
    calc
      _ ≤ ∑ _J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          Q ^ 18 * markedBound ^ g.slots := Finset.sum_le_sum (fun J _ => hterm J)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
          Finset.card_univ, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have hcard : (tuples.card : ℝ) ≤ (A * X) ^ g.slots := by
    dsimp only [tuples]
    rw [Fintype.card_piFinset, Nat.cast_prod]
    calc
      _ ≤ ∏ _i : Fin g.slots, A * X :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcount g T Z i hX)
      _ = _ := by simp
  have hXJ : X ^ g.slots = Z ^ (1 / 6 : ℝ) := by
    have hJ : 0 < (g.slots : ℝ) := by exact_mod_cast g.slots_pos
    rw [← Real.rpow_natCast]
    dsimp only [X, primeScale]
    rw [← Real.rpow_mul hZpos.le]
    congr 1
    field_simp [hJ.ne']
  have hpower : X ^ g.slots * (X ^ g.slots) ^ 18 = Z ^ (19 / 6 : ℝ) := by
    calc
      _ = (X ^ g.slots) ^ 19 := by ring
      _ = (Z ^ (1 / 6 : ℝ)) ^ 19 := by rw [hXJ]
      _ = _ := by
        rw [← Real.rpow_mul_natCast hZpos.le]
        congr 1
        norm_num
  unfold largeCorrectionMass
  change (∑ p ∈ tuples, _) ≤ _
  calc
    _ ≤ ∑ _p ∈ tuples, M ^ g.slots *
        ((2 : ℝ) ^ g.slots * (Q ^ 18 * markedBound ^ g.slots)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul (hweights p) (hinner p hp)
        (Finset.sum_nonneg (fun J _ => mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (idealNorm_pos K _).le _)
            (Real.rpow_nonneg (idealNorm_pos K _).le _))
          (pow_nonneg hmarked0 _))) (by positivity)
    _ = (tuples.card : ℝ) * (M ^ g.slots *
        ((2 : ℝ) ^ g.slots * (Q ^ 18 * markedBound ^ g.slots))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A * X) ^ g.slots * (M ^ g.slots *
        ((2 : ℝ) ^ g.slots * (Q ^ 18 * markedBound ^ g.slots))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C * (X ^ g.slots * (X ^ g.slots) ^ 18) := by
      dsimp only [C, Q]
      simp only [mul_pow]
      ring
    _ = _ := by rw [hpower]

/-- The full original correction on every moderate initial sweep has
the fixed coarse scale power 19/6.  C and Z0 precede a, the actual row,
every original character, and all imaginary coordinates. -/
theorem exists_actual_moderate_fullCorrection_bound (g : PrimeWindowGeometry)
    {e eta : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heta : 0 < eta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ (P : ProbeData K S) (psi : HeckeCharacter K) (T : Finset (HeckeCharacter K))
        (u : FrequencyRow K S) (a : ℝ), 51 / 100 ≤ a → a ≤ 1 → ∀ s w z : ℂ,
        (s, w, z) ∈ sweptTube a e → s.re ≤ 5 → -(1 / 1000 : ℝ) ≤ w.re → z.re ≤ 3 →
        ‖compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
          g T u Z s w z‖ ≤ C * frequencyRowNorm K S u ^ eta * Z ^ (19 / 6 : ℝ) := by
  obtain ⟨Cr, hCr, hr⟩ := exists_actual_moderate_fullCorrection_mass_bound K S he he1 heta
  obtain ⟨Cm, Z0, hCm, hZ0, hm⟩ := exists_actual_moderate_correctionMass_bound K S g
  refine ⟨Cr * Cm, Z0, mul_pos hCr hCm, hZ0, ?_⟩
  intro Z hZ P psi T u a ha ha1 s w z hv hs hw hz
  have hNnonneg : 0 ≤ frequencyRowNorm K S u := (idealNorm_pos K u.ideal.val).le
  exact (hr g T Z a ha ha1 P psi u s w z hv hs hw hz).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm Z hZ T) hCr.le)
      (Real.rpow_nonneg hNnonneg eta)).trans_eq (by ring))

/-- The actual finite-order nonprincipal numerator is controlled across
the small negative-w part of every moderate starting contour. -/
theorem exists_actual_nonprincipal_numerator_moderateStrip
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (R : RowCharacterInput K S P),
      AllowedGeneratorInput K S P.arithmetic → ∀ u : FrequencyRow K S,
      ¬principalFrequencyRow K S u → ∀ w : ℂ, -(1 / 1000 : ℝ) ≤ w.re →
        ‖heckeDeletedContinuation K (R.character u) (exceptionalPrimes K S) w‖ ≤
          C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨D, hD, hstrip⟩ := exists_uniform_fixedType_strip_bound K hcomplex
    (fun _ => 0) (fun _ => 0) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨A, hA, hconductor⟩ := exists_row_conductorScale_bound K S
  obtain ⟨E, hE, hright⟩ := exists_uniform_rightHalfPlane_bound K (11 / 10) (by norm_num)
  let F : ℝ := deletionUpperConstant K (exceptionalPrimes K S)
  have hF : 0 < F := deletionUpperConstant_pos K (exceptionalPrimes K S)
  let C : ℝ := D * A ^ (3 / 5 : ℝ) + E
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨F * C, mul_pos hF hC, ?_⟩
  intro P R hAllowed u hu w hw
  have hN : 0 < frequencyRowNorm K S u := idealNorm_pos K u.ideal.val
  have hNp : 1 ≤ frequencyRowNorm K S u ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (one_le_idealNorm K u.ideal.val) (by norm_num)
  have hheight : 1 ≤ (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) :=
    one_le_pow₀ (by linarith [abs_nonneg w.im])
  have hfull : ‖heckeContinuation K (R.character u) w‖ ≤
      C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
        (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    by_cases hwupper : w.re ≤ 11 / 10
    · have hτ : (fun v => heckeRadialParameter K v (R.character u)) = fun _ => 0 := by
        funext v
        exact heckeRadialParameter_finiteOrder K v (R.finite_order u)
      have hm : heckeArchWeight K (R.character u) = fun _ => 0 := by
        funext v
        rw [heckeArchWeight_of_complex K (R.character u) v (hcomplex v)]
        exact heckeComplexWeight_finiteOrder K v (hcomplex v) (R.finite_order u)
      have hL := hstrip (R.character u)
        (rowCharacterInput_ne_normTwist_of_not_principal K S P R hAllowed u hu)
        hτ hm w ⟨by linarith, by linarith⟩
      norm_num only at hL
      have hscale : heckeConductorScale K (R.character u) ^ (3 / 5 : ℝ) ≤
          A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ) := by
        calc
          _ ≤ (A * frequencyRowNorm K S u) ^ (3 / 5 : ℝ) :=
            Real.rpow_le_rpow (conductorScale_pos K _).le (hconductor P R u) (by norm_num)
          _ = _ := Real.mul_rpow hA.le hN.le
      apply hL.trans
      have hc : D * A ^ (3 / 5 : ℝ) ≤ C := le_add_of_nonneg_right hE.le
      calc
        _ ≤ D * (A ^ (3 / 5 : ℝ) * frequencyRowNorm K S u ^ (3 / 5 : ℝ)) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by gcongr
        _ ≤ C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) *
            (2 + |w.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    · apply (hright (R.character u) w (le_of_not_ge hwupper)).trans
      calc
        E ≤ C := le_add_of_nonneg_left (by positivity)
        _ ≤ C * frequencyRowNorm K S u ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC.le hNp
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hheight
  have hEuler : ‖heckeEulerDeletionPolynomial K (R.character u)
      (exceptionalPrimes K S) w‖ ≤ F :=
    norm_heckeEulerDeletionPolynomial_le K (exceptionalPrimes K S) (R.character u) w (by linarith)
  rw [heckeDeletedContinuation, norm_mul]
  exact (mul_le_mul hEuler hfull (norm_nonneg _) hF.le).trans_eq (by ring)

end Expansion.Project

#print axioms Expansion.Project.exists_actual_moderate_correctionMass_bound
#print axioms Expansion.Project.exists_actual_moderate_fullCorrection_bound

#print axioms Expansion.Project.exists_actual_nonprincipal_numerator_moderateStrip
