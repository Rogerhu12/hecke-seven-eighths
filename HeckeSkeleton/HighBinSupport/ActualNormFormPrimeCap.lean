import HeckeSkeleton.HighBinSupport.ActualNormFormPrimeContour
import HeckeSkeleton.HighBinSupport.HighNormFormHeight
import HeckeSkeleton.HeckeConductorNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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
open scoped Classical Topology BigOperators ContDiff

/-- A fixed real power changes the annular profile, without changing its
support or the actual finite prime window. -/
def powerWeightedProfile (V : SmoothAnnularTest) (r y : ℝ) : ℂ :=
  V.toFun y * (y ^ r : ℝ)

theorem powerWeightedProfile_support (V : SmoothAnnularTest) (r : ℝ) :
    Function.support (powerWeightedProfile V r) = Function.support V.toFun := by
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hz
    exact hy (by simp only [powerWeightedProfile, Function.notMem_support.mp hz, zero_mul])
  · intro y hy
    have hy0 : 0 < y := V.lower_pos.trans_le (V.support hy).1
    exact mul_ne_zero hy (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy0 r).ne')

theorem contDiff_powerWeightedProfile (V : SmoothAnnularTest) (r : ℝ) :
    ContDiff ℝ ∞ (powerWeightedProfile V r) := by
  have hs : tsupport V.toFun ⊆ Icc V.lower V.upper :=
    closure_minimal V.support isClosed_Icc
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport V.toFun
  · have hy0 : 0 < y := V.lower_pos.trans_le (hs hy).1
    have hp : ContDiffAt ℝ ∞ (fun x : ℝ => ((x ^ r : ℝ) : ℂ)) y :=
      (Complex.ofRealCLM.contDiff (𝕜 := ℝ)).contDiffAt.comp y
        (Real.contDiffAt_rpow_const_of_ne hy0.ne')
    exact V.smooth.contDiffAt.mul hp
  · have hz : V.toFun =ᶠ[𝓝 y] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hy
    have hz' : powerWeightedProfile V r =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [hz] with x hx
      simp only [powerWeightedProfile, hx, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz'

def powerWeightedTest (V : SmoothAnnularTest) (r : ℝ) : SmoothAnnularTest where
  toFun := powerWeightedProfile V r
  smooth := contDiff_powerWeightedProfile V r
  lower := V.lower
  upper := V.upper
  lower_pos := V.lower_pos
  upper_ge := V.upper_ge
  support := by rw [powerWeightedProfile_support]; exact V.support

def powerWeightedGeometry (g : PrimeWindowGeometry) (r : ℝ) : PrimeWindowGeometry where
  slots := g.slots
  slots_pos := g.slots_pos
  slots_even := g.slots_even
  weight i := powerWeightedTest (g.weight i) r
  nonnegative i y := by
    change 0 ≤ ((g.weight i).toFun y * ((y ^ r : ℝ) : ℂ)).re
    by_cases hy : (g.weight i).toFun y = 0
    · simp only [hy, zero_mul, Complex.zero_re, le_refl]
    · have hy0 : 0 < y := (g.weight i).lower_pos.trans_le ((g.weight i).support hy).1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (g.nonnegative i y) (Real.rpow_nonneg hy0.le r)
  real_valued i y := by
    change ((g.weight i).toFun y * ((y ^ r : ℝ) : ℂ)).im = 0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      g.real_valued i y, mul_zero, zero_mul, zero_add]
  nonzero i := by
    obtain ⟨y, hy⟩ := g.nonzero i
    refine ⟨y, ?_⟩
    change y ∈ Function.support (powerWeightedProfile (g.weight i) r)
    rw [powerWeightedProfile_support]
    exact hy
  support_annular i := by
    change Function.support (powerWeightedProfile (g.weight i) r) ⊆ Ioo (1 : ℝ) 2
    rw [powerWeightedProfile_support]
    exact g.support_annular i
  disjoint i j hij := by
    change Disjoint (Function.support (powerWeightedProfile (g.weight i) r))
      (Function.support (powerWeightedProfile (g.weight j) r))
    rw [powerWeightedProfile_support, powerWeightedProfile_support]
    exact g.disjoint i j hij

@[simp] theorem primeScale_powerWeightedGeometry (g : PrimeWindowGeometry) (r Z : ℝ) :
    primeScale (powerWeightedGeometry g r) Z = primeScale g Z := rfl

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

theorem primeWindow_powerWeightedGeometry (g : PrimeWindowGeometry) (r : ℝ)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots) :
    primeWindow K S (powerWeightedGeometry g r) T Z i = primeWindow K S g T Z i := by
  ext p
  rw [mem_physicalPrimeWindow_iff_analytic K S (powerWeightedGeometry g r) T Z i p,
    mem_physicalPrimeWindow_iff_analytic K S g T Z i p]
  change (p.val ∈ analyticPrimeSupport K (powerWeightedProfile (g.weight i) r)
      (primeScale g Z) ∧ _) ↔
    (p.val ∈ analyticPrimeSupport K (g.weight i).toFun (primeScale g Z) ∧ _)
  rw [analyticPrimeSupport_spec K (powerWeightedProfile (g.weight i) r)
      ((powerWeightedGeometry g r).support_annular i) (primeScale g Z) p.val,
    analyticPrimeSupport_spec K (g.weight i).toFun (g.support_annular i) (primeScale g Z) p.val]
  change (((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ∈
      Function.support (powerWeightedProfile (g.weight i) r) ∧ _) ↔
    (((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ∈ Function.support (g.weight i).toFun ∧ _)
  rw [powerWeightedProfile_support]

/-- Exact scale extraction for the real power in the genuine local
compensation. The finite windows on both sides are identical. -/
theorem powerWeighted_primeWindow_identity (g : PrimeWindowGeometry) (r : ℝ)
    (chi : HeckeCharacter K) (Z t : ℝ) (i : Fin g.slots)
    (hP : 0 < primeScale g Z) :
    (∑ p ∈ primeWindow K S g ∅ Z i, windowWeight K S g Z i p *
      primeCoefficient K chi p.val *
        (p.val.asIdeal.absNorm : ℂ) ^ ((r : ℂ) - 1 / 2 + (t : ℂ) * Complex.I)) =
      ((primeScale g Z ^ r : ℝ) : ℂ) *
        actualWindowPrimePolynomial K S (powerWeightedGeometry g r) chi Z t i := by
  unfold actualWindowPrimePolynomial
  rw [primeWindow_powerWeightedGeometry K S g r ∅ Z i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hq : (0 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)
  have hqC : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)).ne'
  have hscaled : ((primeScale g Z ^ r : ℝ) : ℂ) *
      ((((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ^ r : ℝ) : ℂ) =
      (p.val.asIdeal.absNorm : ℂ) ^ (r : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.mul_rpow hP.le (div_pos hq hP).le]
    have hmul : primeScale g Z * ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) =
        (p.val.asIdeal.absNorm : ℝ) := by field_simp [hP.ne']
    rw [hmul, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  change (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) *
      primeCoefficient K chi p.val *
      (p.val.asIdeal.absNorm : ℂ) ^ ((r : ℂ) - 1 / 2 + (t : ℂ) * Complex.I) =
    ((primeScale g Z ^ r : ℝ) : ℂ) *
      (((g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) *
        ((((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ^ r : ℝ) : ℂ)) *
        primeCoefficient K chi p.val *
        (p.val.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I))
  calc
    _ = (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) *
        primeCoefficient K chi p.val *
        ((p.val.asIdeal.absNorm : ℂ) ^ (r : ℂ) *
          (p.val.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [← Complex.cpow_add _ _ hqC]
      congr 2
      ring
    _ = _ := by rw [← hscaled]; ring

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

/-- The same actual prime detector controls every fixed real power of
the original window. The new profile is constructed above, and its
support equality identifies the finite sum exactly. -/
theorem exists_actual_powerWeighted_primeWindow_radical_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    (r : ℝ) {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U t : ℝ, 1 / 2 ≤ a → a ≤ 1 →
      NormForm.internalHeight Z T kappa + |t| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots,
        ‖∑ p ∈ primeWindow K S g ∅ Z i, windowWeight K S g Z i p *
          primeCoefficient K chi p.val *
            (p.val.asIdeal.absNorm : ℂ) ^ ((r : ℂ) - 1 / 2 + (t : ℂ) * Complex.I)‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (r + a - 1 / 2 + 8 * e) := by
  obtain ⟨C, Z0, hC, hZ0, hcap⟩ := exists_actual_primeWindow_radical_cap K S
    psi companions probe E (powerWeightedGeometry g r) he he' heps hkappa
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z T hZ d hd u hu a U t ha ha1 hU hbelow chi hchi i
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  have hP : 0 < primeScale g Z :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ1) _
  have hb := hcap Z T hZ d hd u hu a U t ha ha1 hU hbelow chi hchi i
  rw [powerWeighted_primeWindow_identity K S g r chi Z t i hP, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hP r)]
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hP.le r)).trans_eq
  simp only [primeScale_powerWeightedGeometry]
  rw [show r + a - 1 / 2 + 8 * e = r + (a - 1 / 2 + 8 * e) by ring,
    Real.rpow_add hP r (a - 1 / 2 + 8 * e)]
  ring

/-- The exact q^(z-1) main term of the complete compensation on Re z=17/50.
This closes the real-power mismatch between the original local factor
and the square-root-normalized Mellin prime detector. -/
theorem exists_actual_compensation_main_cap
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (probe : ProbeData K S) (E : RowEulerData K S probe) (g : PrimeWindowGeometry)
    {e eps kappa : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → ∀ d : ℝ, (1 / 16 : ℝ) ≤ d →
      ∀ u : FrequencyRow K S, Z ^ d ≤ frequencyRowNorm K S u →
      ∀ a U : ℝ, ∀ z : ℂ, 1 / 2 ≤ a → a ≤ 1 → z.re = 17 / 50 →
      NormForm.internalHeight Z T kappa + |z.im| + 2 ≤ U →
      rowZeroBelow K S psi companions probe E u U (a + 2 * e) →
      ∀ chi ∈ physicalRowFamily K S psi companions probe E u,
      ∀ i : Fin g.slots,
        ‖∑ p ∈ primeWindow K S g ∅ Z i, windowWeight K S g Z i p *
          primeCoefficient K chi p.val * (p.val.asIdeal.absNorm : ℂ) ^ (z - 1)‖ ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) ^ eps *
            (2 + U) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) *
            (primeScale g Z) ^ (a - 33 / 50 + 8 * e) := by
  obtain ⟨C, Z0, hC, hZ0, hcap⟩ := exists_actual_powerWeighted_primeWindow_radical_cap
    K S psi companions probe E g (-(4 / 25 : ℝ)) he he' heps hkappa
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z T hZ d hd u hu a U z ha ha1 hz hU hbelow chi hchi i
  have h := hcap Z T hZ d hd u hu a U z.im ha ha1 hU hbelow chi hchi i
  have hzexpr : z - 1 = ((-(4 / 25 : ℝ)) : ℂ) - 1 / 2 + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;>
      norm_num [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
        Complex.mul_re, Complex.mul_im, hz]
  have hexp : -(4 / 25 : ℝ) + a - 1 / 2 + 8 * e = a - 33 / 50 + 8 * e := by ring
  rw [hzexpr]
  simpa only [hexp] using h

end HighBinVerified.NormFormPrimeCap

#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_power_cap
#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_internalHeight_cap
#print axioms HighBinVerified.NormFormPrimeCap.exists_physicalFamily_radical_conductor_bound
#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_primeWindow_radical_cap
#print axioms HighBinVerified.NormFormPrimeCap.powerWeighted_primeWindow_identity
#print axioms HighBinVerified.NormFormPrimeCap.exists_actual_compensation_main_cap
