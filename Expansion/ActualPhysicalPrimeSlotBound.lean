import Expansion.ActualPrimePowerBound
import Expansion.ActualCompensationSlotIdentity
import ActualCanonicalRowConsumers
import HeckeSkeleton.HeckeFiniteBackgroundControl
import HeckeSkeleton.HighNormBackgroundExclusion

/-!
# Uniform prime-slot caps on the original physical bins

The row conductor, finite character fibers, fixed infinity type and
non-norm threshold are supplied by the actual original Euler provider.
The original finite zero predicate is used only at 3(h+2)T. The contour
height is T=Z^tau, and its center is the original physical coordinate p 2.
No prime cancellation, smoothness, conductor or finite-fiber bound is an
input. Constants and cutoffs precede the bin, row and physical point.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Bridge HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeFiniteBackgroundControl HeckeSkeleton.HeckeBufferedReciprocal
open ExpansionInterfaces.Mellin
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (E : RowEulerData K S P)

theorem all_complex_of_original_probe : ∀ v : InfinitePlace K, v.IsComplex := by
  have hz : InfinitePlace.nrRealPlaces K = 0 :=
    InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
      (by norm_num : 2 < (6 : ℕ)) P.arithmetic.primitive6
  exact (NumberField.nrRealPlaces_eq_zero_iff.mp hz).isComplex

/-- The original row conductor fits a fixed multiple of the complete row
norm. The underlying radical bound itself is an actual arithmetic theorem. -/
theorem exists_original_row_conductorScale_bound :
    ∃ R : ℝ, 0 < R ∧ ∀ u : FrequencyRow K S,
      heckeConductorScale K (E.rows.character u) ≤ R * frequencyRowNorm K S u := by
  obtain ⟨C, hC, hb⟩ :=
    HeckeSkeleton.ActualCanonicalRowConsumers.exists_fixed_real_radical_bound_constant K S
  let D : ℝ := ((NumberField.discr K).natAbs : ℝ)
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro u
  have hrad : (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S u := by
    change (u.ideal.val.val.radical.absNorm : ℝ) ≤ (u.ideal.val.val.absNorm : ℝ)
    exact_mod_cast absNorm_nonzeroIdealRadical_le K u.ideal.val
  have hh := mul_le_mul_of_nonneg_left
    ((hb P E u).trans (mul_le_mul_of_nonneg_left hrad hC.le)) hD.le
  simpa only [heckeConductorScale, D, mul_assoc] using hh

theorem original_row_mem_physical_family (ψ : HeckeCharacter K)
    (Θ : Finset (HeckeCharacter K)) (hΘ : (1 : HeckeCharacter K) ∈ Θ)
    (u : FrequencyRow K S) :
    E.rows.character u ∈ physicalRowFamily K S ψ Θ P E u := by
  apply Finset.mem_biUnion.mpr
  refine ⟨1, hΘ, ?_⟩
  simp

theorem physical_prime_frequency_le (p : Fin 3 → ℝ) {T : ℝ} (hp : ‖p‖ ≤ T) :
    |(vertical (17 / 50) (p 2)).im| ≤ T := by
  rw [vertical_im]
  exact (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm p 2).trans hp

variable (omega ψ : HeckeCharacter K) (Θ : Finset (HeckeCharacter K))

/-- The explicit width budget retains both the bin padding 2e and every
analytic small loss. The remaining fixed constant is uniform in all slots. -/
theorem exists_actual_physical_primeSlot_bound
    (hΘ : (1 : HeckeCharacter K) ∈ Θ)
    (presentation : PolynomialPresentation K ψ) (g : PrimeWindowGeometry)
    (V W : IdealTest K) (e δ ε η τ h width : ℝ)
    (he : 0 ≤ e) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hε : 0 < ε)
    (hloss : ε + δ * ((1 / 6 : ℝ) / g.slots) ≤ η)
    (hτ : 0 < τ) (hτ' : τ ≤ 1) (hh : 0 ≤ h)
    (hwidth : 2 * e * ((1 / 6 : ℝ) / g.slots) + η ≤
      ((1 / 6 : ℝ) / g.slots) * width) :
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, 1 / 16 ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S,
        Z ^ d ≤ frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 → ∀ p : Fin 3 → ℝ, ‖p‖ ≤ Z ^ τ →
        rowZeroBelow K S ψ Θ P E u (3 * (h + 2) * Z ^ τ) (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖primePolynomial
          (sharedMomentData K S P E.rows omega ψ presentation
            (compensationPrimeGeometry K g (vertical (17 / 50) (p 2)))
            (fun _ => 1) u.sector V W) i u.ideal.val Z 0‖ ≤
          C * Z ^ (((1 / 6 : ℝ) / g.slots) * (a - 1 / 2 + width)) := by
  let ell : ℝ := (1 / 6 : ℝ) / g.slots
  change ε + δ * ell ≤ η at hloss
  change 2 * e * ell + η ≤ ell * width at hwidth
  have hell : 0 < ell := div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  have hcomplex := all_complex_of_original_probe K S P
  obtain ⟨R, hR, hQ⟩ := exists_original_row_conductorScale_bound K S P E
  have hlocal := fun i : Fin g.slots => exists_actual_normalized_prime_power_bound
    K S hcomplex (fun v => heckeRadialParameter K v (1 : HeckeCharacter K))
    (heckeArchWeight K (1 : HeckeCharacter K)) (2 * R) (by positivity)
    (actualCompensationPrimeProfile g i) (contDiff_actualCompensationPrimeProfile g i)
    (actualCompensationPrimeProfile_support_Icc g i)
    ell δ ε η τ 1 hell.le hδ hδ' hε hloss hτ hτ' (by norm_num)
  choose Pmin Ci hPmin hCi hbound using hlocal
  let C := (∑ i : Fin g.slots, Ci i) + 1
  have hC : 0 < C := by
    have hsum := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin g.slots)))
      (fun i _ => hCi i)
    exact hsum.trans_lt (lt_add_one _)
  obtain ⟨Zprime, hZprime⟩ :=
    (tendsto_atTop_atTop.mp (tendsto_rpow_atTop hell)) (∑ i : Fin g.slots, Pmin i)
  have hFib := HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S P E
  let v : InfinitePlace K := Classical.choice inferInstance
  obtain ⟨Znon, hZnon, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v ({1} : Finset (HeckeCharacter K))
  refine ⟨C, max Znon Zprime, hC, hZnon.trans (le_max_left _ _), ?_⟩
  intro Z hZ d hd hd' u hu hu' a ha ha' p hp hbelow i
  have hZnon' : Znon ≤ Z := (le_max_left _ _).trans hZ
  have hZprime' : Zprime ≤ Z := (le_max_right _ _).trans hZ
  have hZone : 1 ≤ Z := hZnon.trans hZnon'
  have hZpos : 0 < Z := zero_lt_one.trans_le hZone
  have hTZ : 1 ≤ Z ^ τ := Real.one_le_rpow hZone hτ.le
  have hUd : Z ^ d ≤ Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZone hd'
  have huZ : frequencyRowNorm K S u ≤ 2 * Z :=
    hu'.trans (mul_le_mul_of_nonneg_left hUd (by norm_num))
  have hQi : heckeConductorScale K (E.rows.character u) ≤ (2 * R) * Z :=
    ((hQ u).trans (mul_le_mul_of_nonneg_left huZ hR.le)).trans_eq (by ring)
  have hchi : ∀ t : ℝ, E.rows.character u ≠ heckeNormTwist K t := by
    simpa only [one_mul] using
      (hnon Z hZnon' d hd u hu 1 (Finset.mem_singleton_self 1)).1
  have harch : (fun v => heckeRadialParameter K v (E.rows.character u)) =
      (fun v => heckeRadialParameter K v (1 : HeckeCharacter K)) := by
    simpa only [one_mul] using radialParameters_mul_finiteOrder K
      (1 : HeckeCharacter K) (E.rows.character u) (E.rows.finite_order u)
  have hweight : heckeArchWeight K (E.rows.character u) =
      heckeArchWeight K (1 : HeckeCharacter K) := by
    simpa only [one_mul] using archWeight_mul_finiteOrder_of_complex K hcomplex
      (1 : HeckeCharacter K) (E.rows.character u) (E.rows.finite_order u)
  let beta : ℝ := min (a + 2 * e) 1
  let z : ℂ := vertical (17 / 50) (p 2)
  have hbeta : 1 / 2 ≤ beta := le_min (by linarith only [ha, he]) (by norm_num)
  have hbeta' : beta ≤ 1 := min_le_right _ _
  have hnu : |z.im| ≤ 1 * Z ^ τ := by
    simpa only [one_mul, z] using physical_prime_frequency_le p hp
  have hpadding : |z.im| + Z ^ τ + 3 / 2 ≤ 3 * (h + 2) * Z ^ τ := by
    have hht := mul_nonneg hh (Real.rpow_nonneg hZpos.le τ)
    nlinarith only [hnu, hTZ, hht]
  have hupper : ZeroUpperBound K (E.rows.character u) (3 * (h + 2) * Z ^ τ) beta :=
    zeroUpperBound_min_one K _ _ _
      (hbelow _ (original_row_mem_physical_family K S P E ψ Θ hΘ u))
  have hPi : Pmin i ≤ Z ^ ell :=
    (Finset.single_le_sum (s := (Finset.univ : Finset (Fin g.slots)))
      (f := Pmin) (fun j _ => (by norm_num : (0 : ℝ) ≤ 2).trans (hPmin j))
        (Finset.mem_univ i)).trans
      (hZprime Z hZprime')
  have hcover : ∀ q, actualCompensationPrimeProfile g i (actualPrimeNorm K q / Z ^ ell) ≠ 0 →
      q ∈ (analyticMomentPrimeWindow K g i).support 0 (Z ^ ell) := by
    intro q hq
    apply ((analyticMomentPrimeWindow K g i).support_spec 0 (Z ^ ell) q).mpr
    exact left_ne_zero_of_mul hq
  have hb := hbound i (E.rows.character u) u.ideal.val Z beta z.im
    (3 * (h + 2) * Z ^ τ) ((analyticMomentPrimeWindow K g i).support 0 (Z ^ ell))
    hZone hPi huZ hchi harch hweight hQi hbeta hbeta' hnu hpadding hupper hcover
  have hbetaa : beta ≤ a + 2 * e := min_le_left _ _
  have hexponent : (beta - 1 / 2) * ell + η ≤ ell * (a - 1 / 2 + width) := by
    have hm := mul_le_mul_of_nonneg_right hbetaa hell.le
    nlinarith only [hm, hwidth]
  have hCiC : Ci i ≤ C :=
    (Finset.single_le_sum (s := (Finset.univ : Finset (Fin g.slots)))
      (f := Ci) (fun j _ => hCi j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right zero_le_one)
  have hfinal := hb.trans ((mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZone hexponent) (hCi i)).trans
      (mul_le_mul_of_nonneg_right hCiC (Real.rpow_nonneg hZpos.le _)))
  have hslot :
      primePolynomial
        (sharedMomentData K S P E.rows omega ψ presentation
          (compensationPrimeGeometry K g z) (fun _ => 1) u.sector V W) i u.ideal.val Z 0 =
        (Real.sqrt (Z ^ ell) : ℂ)⁻¹ *
          actualOriginalMaskedPrimeSum K S (E.rows.character u) u.ideal.val
            (fun y => (g.weight i).toFun y * profilePower (conj z - 1) y) (Z ^ ell)
            ((analyticMomentPrimeWindow K g i).support 0 (Z ^ ell)) := by
    calc
      _ = (Real.sqrt (Z ^ ell) : ℂ)⁻¹ *
          actualOriginalMaskedPrimeSum K S (E.rows.character u * 1) u.ideal.val
            (fun y => (g.weight i).toFun y * profilePower (conj z - 1) y) (Z ^ ell)
            ((analyticMomentPrimeWindow K g i).support 0 (Z ^ ell)) :=
        shared_primePolynomial_eq_actualOriginalMaskedPrimeSum K S P E.rows omega ψ
          presentation (compensationPrimeGeometry K g z) (fun _ => 1) V W u i Z 0
      _ = _ := by rw [mul_one]
  calc
    _ = ‖(Real.sqrt (Z ^ ell) : ℂ)⁻¹ *
        actualOriginalMaskedPrimeSum K S (E.rows.character u) u.ideal.val
          (fun y => (g.weight i).toFun y * profilePower (conj z - 1) y) (Z ^ ell)
          ((analyticMomentPrimeWindow K g i).support 0 (Z ^ ell))‖ := congrArg norm hslot
    _ ≤ _ := by
      rw [show (fun y => (g.weight i).toFun y * profilePower (conj z - 1) y) =
          (fun y => actualCompensationPrimeProfile g i y * profilePower (-vertical 0 z.im) y) from
        funext (actualCompensationPrimeProfile_frequency g i z (vertical_re _ _))]
      exact hfinal

/-- A positive, explicit width reserve absorbs the common constant after
one more cutoff. The reserve is chosen before all physical bins and rows. -/
theorem exists_actual_physical_primeSlot_absorbed
    (hΘ : (1 : HeckeCharacter K) ∈ Θ)
    (presentation : PolynomialPresentation K ψ) (g : PrimeWindowGeometry)
    (V W : IdealTest K) (e δ ε η τ h width lam : ℝ)
    (he : 0 ≤ e) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (hε : 0 < ε)
    (hloss : ε + δ * ((1 / 6 : ℝ) / g.slots) ≤ η)
    (hτ : 0 < τ) (hτ' : τ ≤ 1) (hh : 0 ≤ h) (hlam : 0 < lam)
    (hwidth : 2 * e * ((1 / 6 : ℝ) / g.slots) + η ≤
      ((1 / 6 : ℝ) / g.slots) * (width - lam)) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, 1 / 16 ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S,
        Z ^ d ≤ frequencyRowNorm K S u → frequencyRowNorm K S u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 1 → ∀ p : Fin 3 → ℝ, ‖p‖ ≤ Z ^ τ →
        rowZeroBelow K S ψ Θ P E u (3 * (h + 2) * Z ^ τ) (a + 2 * e) →
      ∀ i : Fin g.slots,
        ‖primePolynomial
          (sharedMomentData K S P E.rows omega ψ presentation
            (compensationPrimeGeometry K g (vertical (17 / 50) (p 2)))
            (fun _ => 1) u.sector V W) i u.ideal.val Z 0‖ ≤
          Z ^ (((1 / 6 : ℝ) / g.slots) * (a - 1 / 2 + width)) := by
  obtain ⟨C, Z₁, hC, hZ₁, hb⟩ := exists_actual_physical_primeSlot_bound
    K S P E omega ψ Θ hΘ presentation g V W e δ ε η τ h (width - lam)
      he hδ hδ' hε hloss hτ hτ' hh hwidth
  let ell : ℝ := (1 / 6 : ℝ) / g.slots
  have hell : 0 < ell := div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  obtain ⟨Z₂, hZ₂⟩ :=
    (tendsto_atTop_atTop.mp (tendsto_rpow_atTop (mul_pos hell hlam))) C
  refine ⟨max Z₁ Z₂, hZ₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ d hd hd' u hu hu' a ha ha' p hp hbelow i
  have hZZ₁ : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZZ₂ : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZone : 1 ≤ Z := hZ₁.trans hZZ₁
  have hZpos : 0 < Z := zero_lt_one.trans_le hZone
  calc
    _ ≤ C * Z ^ (ell * (a - 1 / 2 + (width - lam))) :=
      hb Z hZZ₁ d hd hd' u hu hu' a ha ha' p hp hbelow i
    _ ≤ Z ^ (ell * lam) * Z ^ (ell * (a - 1 / 2 + (width - lam))) :=
      mul_le_mul_of_nonneg_right (hZ₂ Z hZZ₂) (Real.rpow_nonneg hZpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hZpos]
      congr 1
      ring

end Expansion.Project

#print axioms Expansion.Project.exists_original_row_conductorScale_bound
#print axioms Expansion.Project.exists_actual_physical_primeSlot_bound
#print axioms Expansion.Project.exists_actual_physical_primeSlot_absorbed
