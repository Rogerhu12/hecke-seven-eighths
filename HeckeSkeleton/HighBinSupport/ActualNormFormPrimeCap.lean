import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeContour
import HeckeSkeleton.HighBinSupport.HighNormFormHeight
import HeckeSkeleton.HeckeConductorNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The prime cap after choosing a fixed internal power height.

The Mellin tail order is chosen once from the fixed window length and
internal-height exponent. Its error is then at most one for every later
scale and is absorbed together with all higher prime powers. The scale
cutoff, like the analytic constant, precedes every row and moving height.
-/

noncomputable section
namespace HighBinVerified.NormFormPrimeCap

open NumberField IsDedekindDomain MeasureTheory Complex Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.HeckePhysicalFamilyBufferedControl
open NormFormActual NormFormPrimeContour
open scoped Classical Topology BigOperators

theorem exists_primeScale_cutoff (g : PrimeWindowGeometry) :
    ∃ Z0 : ℝ, 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z → 2 ≤ primeScale g Z := by
  have hj : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
  have hp : 0 < (1 / 6 : ℝ) / g.slots := div_pos (by norm_num) hj
  obtain ⟨Z0, hZ0⟩ := (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hp)) 2
  exact ⟨max 1 Z0, le_max_left _ _, fun Z hZ => hZ0 Z ((le_max_right _ _).trans hZ)⟩

theorem primeScale_tail_le_one (g : PrimeWindowGeometry) (Z H kappa : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hH : Z ^ kappa ≤ H)
    (hn : (1 / 6 : ℝ) / g.slots ≤ kappa * n) :
    primeScale g Z / (1 + H) ^ n ≤ 1 := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hH0 : 0 ≤ H := (Real.rpow_nonneg hZ0 _).trans hH
  apply (div_le_one₀ (pow_pos (by linarith : 0 < 1 + H) n)).mpr
  calc
    primeScale g Z = Z ^ ((1 / 6 : ℝ) / g.slots) := rfl
    _ ≤ Z ^ (kappa * n) := Real.rpow_le_rpow_of_exponent_le hZ hn
    _ = (Z ^ kappa) ^ n := Real.rpow_mul_natCast hZ0 kappa n
    _ ≤ H ^ n := pow_le_pow_left₀ (Real.rpow_nonneg hZ0 _) hH n
    _ ≤ (1 + H) ^ n := pow_le_pow_left₀ hH0 (by linarith) n

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem one_le_heckeConductorScale (chi : HeckeCharacter K) :
    1 ≤ heckeConductorScale K chi := by
  have hd : (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) := by
    have hnat : 1 ≤ (NumberField.discr K).natAbs :=
      Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
    exact_mod_cast hnat
  have hc : (1 : ℝ) ≤ ((finiteConductor K chi).val.absNorm : ℝ) := by
    have hnat : 1 ≤ (finiteConductor K chi).val.absNorm :=
      Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K chi)
    exact_mod_cast hnat
  exact one_le_mul_of_one_le_of_one_le hd hc

/-- The whole physical family has one actual radical conductor bound.
It is derived from the canonical Kummer row and the finite background
list, uniformly before every probe, provider and frequency row. -/
theorem exists_physicalFamily_radical_conductor_bound
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (probe : ProbeData K S) (E : RowEulerData K S probe)
      (u : FrequencyRow K S) (chi : HeckeCharacter K),
      chi ∈ physicalRowFamily K S psi companions probe E u →
      heckeConductorScale K chi ≤ A * (u.ideal.val.val.radical.absNorm : ℝ) := by
  obtain ⟨C, hC, hrow⟩ :=
    HeckeSkeleton.ActualCanonicalRowConsumers.exists_fixed_real_radical_bound_constant K S
  let B : ℝ := 1 + ∑ beta ∈ physicalBackgrounds K psi companions,
    ((finiteConductor K beta).val.absNorm : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let A : ℝ := max 1 (B * ((NumberField.discr K).natAbs : ℝ) * C)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro probe E u chi hchi
  obtain ⟨beta, hbeta, hdecomp⟩ := physical_member_background_decomposition
    K S psi companions probe E u chi hchi
  have hbetaB : ((finiteConductor K beta).val.absNorm : ℝ) ≤ B := by
    have hsum := Finset.single_le_sum (s := physicalBackgrounds K psi companions)
      (f := fun eta => ((finiteConductor K eta).val.absNorm : ℝ))
      (fun eta _ => Nat.cast_nonneg _) hbeta
    dsimp only [B]
    linarith
  have hb : heckeConductorScale K chi ≤
      ((finiteConductor K beta).val.absNorm : ℝ) * heckeConductorScale K (E.rows.character u) := by
    rcases hdecomp with hdecomp | hdecomp
    · rw [hdecomp]
      exact conductorScale_mul_le K beta (E.rows.character u)
    · rw [hdecomp]
      exact conductorScale_mul_conjugate_le K beta (E.rows.character u)
  have hr : heckeConductorScale K (E.rows.character u) ≤
      ((NumberField.discr K).natAbs : ℝ) * (C * (u.ideal.val.val.radical.absNorm : ℝ)) :=
    mul_le_mul_of_nonneg_left (hrow probe E u) (Nat.cast_nonneg _)
  calc
    heckeConductorScale K chi ≤
        ((finiteConductor K beta).val.absNorm : ℝ) * heckeConductorScale K (E.rows.character u) := hb
    _ ≤ B * heckeConductorScale K (E.rows.character u) :=
      mul_le_mul_of_nonneg_right hbetaB (conductorScale_pos K _).le
    _ ≤ B * (((NumberField.discr K).natAbs : ℝ) *
        (C * (u.ideal.val.val.radical.absNorm : ℝ))) := mul_le_mul_of_nonneg_left hr hB
    _ = (B * ((NumberField.discr K).natAbs : ℝ) * C) *
        (u.ideal.val.val.radical.absNorm : ℝ) := by ring
    _ ≤ A * (u.ideal.val.val.radical.absNorm : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)

/-- Genuine prime-window power cancellation from the buffered zero
detector. There is no prime bound, Mellin hypothesis, explicit non-norm
exclusion, or L'/L estimate among the inputs. -/
theorem exists_actual_primeWindow_power_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a H U t : ℝ, 1 / 2 ≤ a → a ≤ 1 → Z ^ kappa ≤ H → H + |t| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots,
        ‖actualWindowPrimePolynomial K S g chi Z t i‖ ≤ C *
          (1 + heckeConductorScale K chi ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)) *
          (primeScale g Z) ^ (a - 1 / 2 + 8 * e) := by
  obtain ⟨Z1, hZ1, hcap⟩ := exists_actual_primeWindow_cap K S psi companions probe E g
    he he' heps he
  obtain ⟨Z2, hZ2, hscale⟩ := exists_primeScale_cutoff g
  obtain ⟨n, hn⟩ := exists_nat_gt (((1 / 6 : ℝ) / g.slots) / kappa)
  have hn' : (1 / 6 : ℝ) / g.slots ≤ kappa * n := by
    have := (div_lt_iff₀ hkappa).mp hn
    nlinarith
  obtain ⟨C, hC, hbound⟩ := hcap n
  refine ⟨3 * C, max Z1 Z2, by positivity, hZ1.trans (le_max_left _ _), ?_⟩
  intro Z hZ d hd u hu a H U t ha ha1 hH hHU hbelow chi hchi i
  have hZZ1 : Z1 ≤ Z := (le_max_left _ _).trans hZ
  have hZZ2 : Z2 ≤ Z := (le_max_right _ _).trans hZ
  have hZone : 1 ≤ Z := hZ1.trans hZZ1
  have hP : 2 ≤ primeScale g Z := hscale Z hZZ2
  have hP1 : 1 ≤ primeScale g Z := by linarith
  have hP0 : 0 ≤ primeScale g Z := by linarith
  have hH0 : 0 ≤ H := (Real.rpow_nonneg (zero_le_one.trans hZone) _).trans hH
  have htail := primeScale_tail_le_one g Z H kappa n hZone hH hn'
  have hmain : 1 ≤ (primeScale g Z) ^ (a - 1 / 2 + 8 * e) :=
    Real.one_le_rpow hP1 (by linarith)
  have hsmall : (primeScale g Z) ^ e ≤ (primeScale g Z) ^ (a - 1 / 2 + 8 * e) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hU : 0 ≤ 2 + U := by linarith [abs_nonneg t]
  have hQ : 0 ≤ heckeConductorScale K chi := by unfold heckeConductorScale; positivity
  let G : ℝ := heckeConductorScale K chi ^ eps *
    (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)
  have hG : 0 ≤ G := mul_nonneg (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hU _)
  have hb := hbound Z hZZ1 d hd u hu a H U t ha ha1 hH0 hHU hbelow chi hchi i hP
  change ‖actualWindowPrimePolynomial K S g chi Z t i‖ ≤
    (3 * C) * (1 + G) * (primeScale g Z) ^ (a - 1 / 2 + 8 * e)
  apply hb.trans
  calc
    _ ≤ C * ((1 + G) * (2 * (primeScale g Z) ^ (a - 1 / 2 + 8 * e)) +
        (primeScale g Z) ^ (a - 1 / 2 + 8 * e)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hsmall
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg hC.le hG)
        (Real.rpow_nonneg hP0 (a - 1 / 2 + 8 * e))]

/-- The power cap is available at the actual fixed internal height even
when the external height T is small. -/
theorem exists_actual_primeWindow_internalHeight_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U t : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      NormForm.internalHeight Z T kappa + |t| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots,
        ‖actualWindowPrimePolynomial K S g chi Z t i‖ ≤ C *
          (1 + heckeConductorScale K chi ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)) *
          (primeScale g Z) ^ (a - 1 / 2 + 8 * e) := by
  obtain ⟨C, Z0, hC, hZ0, hbound⟩ := exists_actual_primeWindow_power_cap K S
    psi companions probe E g he he' heps hkappa
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z T hZ d hd u hu a U t ha ha1 hU hbelow chi hchi i
  exact hbound Z hZ d hd u hu a (NormForm.internalHeight Z T kappa) U t ha ha1
    (NormForm.power_le_internalHeight Z T kappa) hU hbelow chi hchi i

/-- The internal-height cap with the actual row radical retained. This
is the conductor variable needed for the later repeated-prime allocation;
no comparison with an arbitrary row norm is supplied as an assumption. -/
theorem exists_actual_primeWindow_radical_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U t : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      NormForm.internalHeight Z T kappa + |t| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots,
        ‖actualWindowPrimePolynomial K S g chi Z t i‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 1 / 2 + 8 * e) := by
  obtain ⟨C, Z0, hC, hZ0, hcap⟩ := exists_actual_primeWindow_internalHeight_cap K S
    psi companions probe E g he he' heps hkappa
  obtain ⟨A, hA, hconductor⟩ := exists_physicalFamily_radical_conductor_bound K S psi companions
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  refine ⟨2 * C * A ^ eps, Z0, by positivity, hZ0, ?_⟩
  intro Z T hZ d hd u hu a U t ha ha1 hU hbelow chi hchi i
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hH : 0 ≤ NormForm.internalHeight Z T kappa :=
    (Real.rpow_nonneg (zero_le_one.trans hZ1) _).trans
      (NormForm.power_le_internalHeight Z T kappa)
  have hU1 : 1 ≤ 2 + U := by linarith [abs_nonneg t]
  have hk : 0 ≤ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) :=
    mul_nonneg (Nat.cast_nonneg _) heps.le
  have hQ1 : 1 ≤ heckeConductorScale K chi ^ eps :=
    Real.one_le_rpow (one_le_heckeConductorScale K chi) heps.le
  have hheight1 : 1 ≤ (2 + U) ^
      (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) :=
    Real.one_le_rpow hU1 hk
  have hG1 : 1 ≤ heckeConductorScale K chi ^ eps *
      (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) :=
    one_le_mul_of_one_le_of_one_le hQ1 hheight1
  have hQbound : heckeConductorScale K chi ^ eps ≤
      A ^ eps * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps := by
    calc
      _ ≤ (A * (u.ideal.val.val.radical.absNorm : ℝ)) ^ eps :=
        Real.rpow_le_rpow (conductorScale_pos K chi).le
          (hconductor probe E u chi hchi) heps.le
      _ = _ := Real.mul_rpow hA0.le (Nat.cast_nonneg _)
  have hb := hcap Z T hZ d hd u hu a U t ha ha1 hU hbelow chi hchi i
  have hP0 : 0 ≤ primeScale g Z := Real.rpow_nonneg (zero_le_one.trans hZ1) _
  have hHp : 0 ≤ (2 + U) ^
      (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) :=
    Real.rpow_nonneg (zero_le_one.trans hU1) _
  apply hb.trans
  calc
    _ ≤ C * (2 * (heckeConductorScale K chi ^ eps *
        (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps))) *
        (primeScale g Z) ^ (a - 1 / 2 + 8 * e) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hC.le) (Real.rpow_nonneg hP0 _)
    _ ≤ C * (2 * ((A ^ eps * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps) *
        (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps))) *
        (primeScale g Z) ^ (a - 1 / 2 + 8 * e) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQbound hHp) (by norm_num)) hC.le)
        (Real.rpow_nonneg hP0 _)
    _ = _ := by ring

end HighBinVerified.NormFormPrimeCap

#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_power_cap
#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_internalHeight_cap
#print axioms HighBinVerified.NormFormPrimeCap.exists_physicalFamily_radical_conductor_bound
#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_radical_cap
