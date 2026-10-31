import HeckeSkeleton.LowCauchy.MarkedCauchy
import HeckeGeneral.Analysis.PhysicalProbePrincipal
import HeckeGeneral.Analysis.IdealAmplifierSmallPower
import HeckeGeneral.Analysis.IdealEulerProduct

/-!
# Low compensation bound for general probe data (revised Proposition 6.2)

For arbitrary probe data, window geometry and ray filter, the literal
compensated probe is `O(Z^(3/16+δ))`, given the c = 1 Gram bound and the
marked completed theta energy on the actual row box.  For a fixed rescaled
subset `J` the window tuples are grouped by their selected part; the marked
completions of each selected tuple are summed BEFORE the spectral Cauchy bound
(`lc_marked_physical_bound`).  Selected primes have norm in
`(primeScale, 2 * primeScale)`, the windows are disjoint (so tuples are
injective) and the linear ideal count bounds the number of selected tuples.

Everything here is stated for general data; `HeckeSkeleton.LowCauchy` (the file
`HeckeSkeleton/LowCauchy.lean`) specializes it to the target context.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.LowCauchy

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators Topology ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "NZ" => NonzeroRingElements (S.integer K)

/-- General-data form of `completedMarkedRow` (Principal.lean), same body:
surviving marked slots are summed before taking the row norm. -/
def markedRow (P : ProbeData K S) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (m : NZ) : ℂ :=
  ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    if ∀ i ∈ J, p' i = p i then
      (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p' i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p' (Finset.univ \ J)).val) *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') logGaussianProfile
        (Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J)))
    else 0

/-- General-data form of `CompletedMarkedEnergy` (Principal.lean), same body. -/
def MarkedEnergy (P : ProbeData K S) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) : Prop :=
  ∀ B ε : ℝ, 0 < B → 0 < ε → ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
  ∀ Z : ℝ, Z₀ ≤ Z → ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
  ∀ J : Finset (Fin g.slots),
    let q := exteriorNorm K S (subsetPrimeIdeal K S p J)
    (∑' u : HeckeSkeleton.Gram.Orbit K S,
      if (sIntegerOrbitNorm K S (sixthPowerUnits K S) u).val ≤ B * Z ^ (5 / 6 : ℝ) / q ^ 2
      then ‖markedRow K S P ψ g T Z p J u.out‖ ^ 2 else 0) ≤
      C * Z ^ (5 / 6 + ε) / q ^ 2

/-- The selected scalar of a rescaled subset term. -/
def selectedFactor (g : PrimeWindowGeometry) (Z : ℝ) (r : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) : ℂ :=
  (∏ i ∈ J, windowWeight K S g Z i (r i)) * (-1 : ℂ) ^ J.card *
    (exteriorNorm K S (subsetPrimeIdeal K S r J) : ℂ) ^ (-(3 / 2 : ℂ))

/-- The marked coefficient of a completion `p` of the selected tuple `r`. -/
def markedCoeff (ψ : HeckeCharacter K) (g : PrimeWindowGeometry) (Z : ℝ)
    (r p : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) : ℂ :=
  if ∀ i ∈ J, p i = r i then
    (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p (Finset.univ \ J)).val)
  else 0

theorem markedRow_eq_sum (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (r : Fin g.slots → ExteriorPrime K S) (J : Finset (Fin g.slots)) (m : NZ) :
    markedRow K S P ψ g T Z r J m =
      ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        markedCoeff K S ψ g Z r p J *
          completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) ((Finset.univ \ J).image p) logGaussianProfile
            (Z * exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J))) := by
  unfold markedRow markedCoeff
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> ring

omit [Fintype S] in
theorem lc_exteriorNorm_pos (I : ExteriorIdeal K S) : 0 < exteriorNorm K S I := by
  change (0 : ℝ) < (I.val.val.absNorm : ℝ)
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val

/-- Compact support and continuity bound every window profile uniformly. -/
theorem lc_exists_weight_bound (g : PrimeWindowGeometry) :
    ∃ W : ℝ, 0 < W ∧ ∀ (i : Fin g.slots) (y : ℝ), ‖(g.weight i).toFun y‖ ≤ W := by
  have hb : ∀ i : Fin g.slots, ∃ B : ℝ, 0 < B ∧ ∀ y, ‖(g.weight i).toFun y‖ ≤ B := by
    intro i
    have hs : HasCompactSupport (g.weight i).toFun :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc (g.weight i).support
    obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous (g.weight i).smooth.continuous
    exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
      fun y => (hB y).trans (le_max_right _ _)⟩
  choose B hB hbound using hb
  have hsum : 0 ≤ ∑ i : Fin g.slots, B i := Finset.sum_nonneg (fun j _ => (hB j).le)
  refine ⟨1 + ∑ i : Fin g.slots, B i, by linarith, fun i y => ?_⟩
  have hi : B i ≤ ∑ j : Fin g.slots, B j :=
    Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
  linarith [hbound i y]

theorem lc_rpow_eq_pow {Z u : ℝ} (hZ : 0 ≤ Z) (hu : u = Z ^ (1 / 48 : ℝ)) (n : ℕ) (a : ℝ)
    (ha : a = n / 48) : Z ^ a = u ^ n := by
  rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hZ, ha]
  congr 1
  ring

/-- The Gram hypotheses at the rescaled scales `X = u^17/q`, `Y = u^23/q`
(with `u = Z^(1/48)`), and `gramScale ≤ 3 u^18`. -/
theorem lc_gram_window_conditions {u q : ℝ} (hu : 1 ≤ u) (hq : 1 ≤ q) (hqu : q ≤ u ^ 9) :
    1 ≤ u ^ 17 / q * (u ^ 23 / q) ∧ 1 ≤ u ^ 23 / q ∧
      u ^ 17 / q * (u ^ 23 / q) ≤ u ^ 48 ∧ u ^ 23 / q ≤ u ^ 48 ∧
      1 ≤ HeckeSkeleton.Gram.Pa (u ^ 17 / q * (u ^ 23 / q)) (u ^ 23 / q) ∧
      HeckeSkeleton.Gram.gramScale (u ^ 17 / q * (u ^ 23 / q)) (u ^ 23 / q) ≤ 3 * u ^ 18 := by
  have hu0 : 0 < u := by linarith
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hune : u ≠ 0 := hu0.ne'
  have hXY : u ^ 17 / q * (u ^ 23 / q) = u ^ 40 / q ^ 2 := by ring
  have hq2 : q ^ 2 ≤ u ^ 40 := by
    calc q ^ 2 ≤ (u ^ 9) ^ 2 := pow_le_pow_left₀ hq0.le hqu 2
      _ = u ^ 18 := by ring
      _ ≤ u ^ 40 := pow_le_pow_right₀ hu (by norm_num)
  have hq23 : q ≤ u ^ 23 := hqu.trans (pow_le_pow_right₀ hu (by norm_num))
  have hPa : HeckeSkeleton.Gram.Pa (u ^ 17 / q * (u ^ 23 / q)) (u ^ 23 / q) = u ^ 6 := by
    unfold HeckeSkeleton.Gram.Pa
    rw [hXY, div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hqne), div_eq_iff
      (pow_ne_zero 40 hune)]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hXY, le_div_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hq0]
    linarith
  · rw [hXY, div_le_iff₀ (by positivity)]
    have h1 : u ^ 40 ≤ u ^ 48 := pow_le_pow_right₀ hu (by norm_num)
    have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
    have h3 : 0 < u ^ 48 := by positivity
    nlinarith
  · rw [div_le_iff₀ hq0]
    have h1 : u ^ 23 ≤ u ^ 48 := pow_le_pow_right₀ hu (by norm_num)
    have h3 : 0 < u ^ 48 := by positivity
    nlinarith
  · rw [hPa]
    exact one_le_pow₀ hu
  · unfold HeckeSkeleton.Gram.gramScale
    rw [hPa]
    have hroot : (u ^ 6) ^ (1 / 6 : ℝ) = u := by
      rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hu0.le (by norm_num)
    rw [hroot]
    have hQY : u ^ 17 / q * (u ^ 23 / q) / (u ^ 23 / q) = u ^ 17 / q := by
      rw [mul_div_assoc, div_self (by positivity), mul_one]
    rw [hQY]
    have hlast : (u ^ 6) ^ 2 / (u ^ 23 / q) ≤ 1 := by
      rw [div_le_one (by positivity), le_div_iff₀ hq0]
      calc (u ^ 6) ^ 2 * q ≤ (u ^ 6) ^ 2 * u ^ 9 :=
            mul_le_mul_of_nonneg_left hqu (by positivity)
        _ = u ^ 21 := by ring
        _ ≤ u ^ 23 := pow_le_pow_right₀ hu (by norm_num)
    calc u ^ 17 / q * (1 + u + (u ^ 6) ^ 2 / (u ^ 23 / q))
        ≤ u ^ 17 * (3 * u) :=
          mul_le_mul (div_le_self (by positivity) hq) (by linarith) (by positivity)
            (by positivity)
      _ = 3 * u ^ 18 := by ring

section Window

variable {K S}

omit [Fintype S]

theorem lc_weight_ne_zero_of_mem_window {g : PrimeWindowGeometry}
    {T : Finset (HeckeCharacter K)} {Z : ℝ} {i : Fin g.slots} {p : ExteriorPrime K S}
    (hp : p ∈ primeWindow K S g T Z i) :
    (g.weight i).toFun ((p.val.asIdeal.absNorm : ℝ) / primeScale g Z) ≠ 0 := by
  simp only [primeWindow, Finset.mem_image, Finset.mem_attach, true_and] at hp
  obtain ⟨⟨p', hp'⟩, rfl⟩ := hp
  exact (Finset.mem_filter.mp hp').2.2.2

theorem lc_norm_mem_window {g : PrimeWindowGeometry} {T : Finset (HeckeCharacter K)}
    {Z : ℝ} (hZ : 0 < Z) {i : Fin g.slots} {p : ExteriorPrime K S}
    (hp : p ∈ primeWindow K S g T Z i) :
    primeScale g Z < (p.val.asIdeal.absNorm : ℝ) ∧
      (p.val.asIdeal.absNorm : ℝ) < 2 * primeScale g Z := by
  have hps : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  have hw := lc_weight_ne_zero_of_mem_window hp
  have hmem := g.support_annular i (Function.mem_support.mpr hw)
  constructor
  · have h := hmem.1
    rwa [one_lt_div hps] at h
  · have h := hmem.2
    rwa [div_lt_iff₀ hps] at h

theorem lc_injective_of_mem_piFinset {g : PrimeWindowGeometry}
    {T : Finset (HeckeCharacter K)} {Z : ℝ} {r : Fin g.slots → ExteriorPrime K S}
    (hr : r ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i)) :
    Function.Injective r := by
  intro i j hij
  by_contra hne
  have hi := lc_weight_ne_zero_of_mem_window (Fintype.mem_piFinset.mp hr i)
  have hj := lc_weight_ne_zero_of_mem_window (Fintype.mem_piFinset.mp hr j)
  rw [hij] at hi
  exact Set.disjoint_left.mp (g.disjoint i j hne) (Function.mem_support.mpr hi)
    (Function.mem_support.mpr hj)

theorem lc_exteriorNorm_subsetPrimeIdeal {g : PrimeWindowGeometry}
    {r : Fin g.slots → ExteriorPrime K S} (hr : Function.Injective r)
    (J : Finset (Fin g.slots)) :
    exteriorNorm K S (subsetPrimeIdeal K S r J) = ∏ i ∈ J, ((r i).val.asIdeal.absNorm : ℝ) := by
  calc exteriorNorm K S (subsetPrimeIdeal K S r J)
      = idealNorm K (squarefreeIdeal K ((J.image r).image Subtype.val)) := rfl
    _ = ∏ p ∈ (J.image r).image Subtype.val, (Ideal.absNorm p.asIdeal : ℝ) :=
        idealNorm_squarefreeIdeal_eq_prod K _
    _ = ∏ p ∈ J.image (Subtype.val ∘ r), (Ideal.absNorm p.asIdeal : ℝ) := by
        rw [Finset.image_image]
    _ = ∏ i ∈ J, ((r i).val.asIdeal.absNorm : ℝ) :=
        Finset.prod_image (fun i _ j _ hij => hr (Subtype.ext hij))

theorem lc_subsetNorm_bounds {g : PrimeWindowGeometry} {T : Finset (HeckeCharacter K)}
    {Z : ℝ} (hZ : 0 < Z) {r : Fin g.slots → ExteriorPrime K S}
    (hr : r ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i))
    (J : Finset (Fin g.slots)) :
    primeScale g Z ^ J.card ≤ exteriorNorm K S (subsetPrimeIdeal K S r J) ∧
      exteriorNorm K S (subsetPrimeIdeal K S r J) ≤ (2 * primeScale g Z) ^ J.card := by
  rw [lc_exteriorNorm_subsetPrimeIdeal (lc_injective_of_mem_piFinset hr) J]
  have hb (i : Fin g.slots) := lc_norm_mem_window hZ (Fintype.mem_piFinset.mp hr i)
  have hps : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ _
  constructor
  · calc primeScale g Z ^ J.card = ∏ _i ∈ J, primeScale g Z := (Finset.prod_const _).symm
      _ ≤ ∏ i ∈ J, ((r i).val.asIdeal.absNorm : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => hps.le) (fun i _ => (hb i).1.le)
  · calc ∏ i ∈ J, ((r i).val.asIdeal.absNorm : ℝ) ≤ ∏ _i ∈ J, 2 * primeScale g Z :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => (hb i).2.le)
      _ = (2 * primeScale g Z) ^ J.card := Finset.prod_const _

/-- Linear upper bound for the window size; no prime ideal theorem is used. -/
theorem lc_card_primeWindow_le {g : PrimeWindowGeometry} {T : Finset (HeckeCharacter K)}
    {Z : ℝ} (hZ : 1 ≤ Z) (i : Fin g.slots) {Clin : ℝ}
    (hcount : ∀ U : ℝ, 1 ≤ U → ((dyadicIdealSupport K (U / 2)).card : ℝ) ≤ Clin * U) :
    ((primeWindow K S g T Z i).card : ℝ) ≤ Clin * (2 * primeScale g Z) := by
  have hZ0 : 0 < Z := by linarith
  have hps1 : 1 ≤ primeScale g Z := Real.one_le_rpow hZ (by positivity)
  have hcard : (primeWindow K S g T Z i).card ≤
      (dyadicIdealSupport K (primeScale g Z)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ExteriorPrime K S => primeNonzeroIdeal K p.val)
    · intro p hp
      rw [Finset.mem_coe] at hp ⊢
      rw [mem_dyadicIdealSupport_iff K (by linarith)]
      exact (lc_norm_mem_window hZ0 hp).2.le
    · intro p _ p' _ h
      exact Subtype.ext (primeNonzeroIdeal_injective K h)
  have h2 : dyadicIdealSupport K (primeScale g Z) =
      dyadicIdealSupport K (2 * primeScale g Z / 2) := by
    congr 1
    ring
  calc ((primeWindow K S g T Z i).card : ℝ)
      ≤ ((dyadicIdealSupport K (primeScale g Z)).card : ℝ) := by exact_mod_cast hcard
    _ = ((dyadicIdealSupport K (2 * primeScale g Z / 2)).card : ℝ) := by rw [← h2]
    _ ≤ Clin * (2 * primeScale g Z) := hcount _ (by linarith)

end Window

variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

/-- The combined marked physical probe of a selected tuple `r`: all marked
completions summed, with the selected rescaling `X, Y`. -/
def markedPhysical (P : ProbeData K S) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (r : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) : ℂ :=
  ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    markedCoeff K S ψ g Z r p J *
      physicalProbe K S P ψ ((Finset.univ \ J).image p)
        (Z ^ (17 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S r J))
        (Z ^ (23 / 48 : ℝ) / exteriorNorm K S (subsetPrimeIdeal K S r J))
        (Z * exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)))

/-- Grouping the `J`-part of the compensation by the selected part.  The
representatives keep the selected coordinates and a fixed tuple elsewhere. -/
theorem lc_J_part_eq (P : ProbeData K S) (ψ : HeckeCharacter K) (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (J : Finset (Fin g.slots))
    (p₀ : Fin g.slots → ExteriorPrime K S) :
    ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J =
      ∑ r ∈ Fintype.piFinset (fun i => if i ∈ J then primeWindow K S g T Z i else {p₀ i}),
        selectedFactor K S g Z r J * markedPhysical K S P ψ g T Z r J := by
  let σ : (Fin g.slots → ExteriorPrime K S) → (Fin g.slots → ExteriorPrime K S) :=
    fun p i => if i ∈ J then p i else p₀ i
  have hσ : ∀ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
      σ p ∈ Fintype.piFinset
        (fun i => if i ∈ J then primeWindow K S g T Z i else {p₀ i}) := by
    intro p hp
    rw [Fintype.mem_piFinset] at hp ⊢
    intro i
    by_cases hi : i ∈ J
    · simp [σ, hi, hp i]
    · simp [σ, hi]
  rw [← Finset.sum_fiberwise_of_maps_to hσ
    (fun p => (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J)]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have hrJ : ∀ i, i ∉ J → r i = p₀ i := by
    intro i hi
    have h := Fintype.mem_piFinset.mp hr i
    simpa [hi] using h
  rw [Finset.sum_filter]
  unfold markedPhysical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hpr : ∀ i ∈ J, p i = r i
  · have hσpr : σ p = r := by
      funext i
      by_cases hi : i ∈ J
      · simp [σ, hi, hpr i hi]
      · simp [σ, hi, hrJ i hi]
    have himage : J.image p = J.image r := Finset.image_congr (fun i hi => hpr i hi)
    have hsel : subsetPrimeIdeal K S p J = subsetPrimeIdeal K S r J := by
      unfold subsetPrimeIdeal
      rw [himage]
    have hprod : (∏ i, windowWeight K S g Z i (p i)) =
        (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p i)) *
          ∏ i ∈ J, windowWeight K S g Z i (r i) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ J)]
      congr 1
      exact Finset.prod_congr rfl (fun i hi => by rw [hpr i hi])
    rw [ite_eq_left hσpr]
    simp only [markedCoeff, ite_eq_left hpr, selectedFactor, compensationTerm, hsel, hprod]
    ring
  · have hσpr : σ p ≠ r := by
      intro h
      apply hpr
      intro i hi
      have h' := congrFun h i
      simpa [σ, hi] using h'
    rw [ite_eq_right hσpr]
    simp only [markedCoeff, ite_eq_right hpr, zero_mul, mul_zero]

/-- LOW-CAUCHY-COMPENSATION for general data: the literal compensated probe. -/
theorem lc_compensatedProbe_isBigO (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (hgram : HeckeSkeleton.Gram.GramBound K S P) (henergy : MarkedEnergy K S P ψ g T)
    (δ : ℝ) (hδ : 0 < δ) :
    compensatedProbe K S P ψ g T =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + δ)) := by
  obtain ⟨Cball, hCball, hphys⟩ := lc_marked_physical_bound K S P ψ
  obtain ⟨JG, CG, Z₀G, hCG, _hZ₀G, hG⟩ :=
    hgram Cball 1 hCball one_pos δ hδ
  obtain ⟨K₀, hK₀, hphysJ⟩ := hphys JG
  obtain ⟨CE, Z₀E, hCE, _hZ₀E, hE⟩ := henergy Cball δ hCball hδ
  obtain ⟨Clin, hClin, hcount⟩ := dyadicIdealSupport_linear_count K
  obtain ⟨Wmax, hWmax, hw⟩ := lc_exists_weight_bound g
  have hC1 : 0 ≤ 2 * Clin * Wmax := by positivity
  refine IsBigO.of_bound
    ((∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset, (2 * Clin * Wmax) ^ J.card) *
      (K₀ * Real.sqrt (3 * CG * CE))) ?_
  filter_upwards [eventually_ge_atTop (max (max Z₀G Z₀E) 1),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 48)).eventually_ge_atTop
      ((2 : ℝ) ^ g.slots)] with Z hZ hu2
  have hZ1 : 1 ≤ Z := le_trans (le_max_right _ _) hZ
  have hZG : Z₀G ≤ Z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hZ
  have hZE : Z₀E ≤ Z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hZ
  have hZ0 : 0 < Z := by linarith
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = Z ^ (1 / 48 : ℝ) := ⟨_, rfl⟩
  rw [← hu_def] at hu2
  have h2s : (1 : ℝ) ≤ 2 ^ g.slots := one_le_pow₀ (by norm_num)
  have hu1 : 1 ≤ u := le_trans h2s hu2
  have hu0 : 0 < u := by linarith
  have hp17 : Z ^ (17 / 48 : ℝ) = u ^ 17 := lc_rpow_eq_pow hZ0.le hu_def 17 _ (by norm_num)
  have hp23 : Z ^ (23 / 48 : ℝ) = u ^ 23 := lc_rpow_eq_pow hZ0.le hu_def 23 _ (by norm_num)
  have hp40 : Z ^ (5 / 6 : ℝ) = u ^ 40 := lc_rpow_eq_pow hZ0.le hu_def 40 _ (by norm_num)
  have hp9 : Z ^ (3 / 16 : ℝ) = u ^ 9 := lc_rpow_eq_pow hZ0.le hu_def 9 _ (by norm_num)
  have hp8 : Z ^ (1 / 6 : ℝ) = u ^ 8 := lc_rpow_eq_pow hZ0.le hu_def 8 _ (by norm_num)
  have hp48 : Z ^ (1 : ℝ) = u ^ 48 := lc_rpow_eq_pow hZ0.le hu_def 48 _ (by norm_num)
  have hps0 : 0 < primeScale g Z := Real.rpow_pos_of_pos hZ0 _
  have hps1 : 1 ≤ primeScale g Z := Real.one_le_rpow hZ1 (by positivity)
  have hZδ : 0 ≤ Z ^ δ := Real.rpow_nonneg hZ0.le _
  have hKu : 0 ≤ K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ) := by positivity
  -- one rescaled subset `J`
  have hJbound : ∀ J : Finset (Fin g.slots),
      ‖∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J‖ ≤
        (2 * Clin * Wmax) ^ J.card * (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ)) := by
    intro J
    have hk : J.card ≤ g.slots := (Finset.card_le_univ J).trans_eq (Fintype.card_fin _)
    have hpsk1 : 1 ≤ primeScale g Z ^ J.card := one_le_pow₀ hps1
    have hpsk : primeScale g Z ^ J.card ≤ u ^ 8 := by
      have hslots : (0 : ℝ) < g.slots := by exact_mod_cast g.slots_pos
      have hslots' : (g.slots : ℝ) ≠ 0 := hslots.ne'
      calc primeScale g Z ^ J.card = Z ^ ((1 / 6 : ℝ) / g.slots * J.card) := by
            unfold primeScale
            rw [Real.rpow_mul_natCast hZ0.le]
        _ ≤ Z ^ (1 / 6 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hZ1
            have hk' : (J.card : ℝ) ≤ g.slots := by exact_mod_cast hk
            calc (1 / 6 : ℝ) / g.slots * J.card ≤ (1 / 6 : ℝ) / g.slots * g.slots := by
                  gcongr
              _ = 1 / 6 := div_mul_cancel₀ _ hslots'
        _ = u ^ 8 := hp8
    -- the selected scalar
    have hsel : ∀ r ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ‖selectedFactor K S g Z r J‖ ≤ Wmax ^ J.card * (primeScale g Z ^ J.card)⁻¹ := by
      intro r hr
      obtain ⟨hlow, -⟩ := lc_subsetNorm_bounds hZ0 hr J
      have hq1 : 1 ≤ exteriorNorm K S (subsetPrimeIdeal K S r J) := le_trans hpsk1 hlow
      have hq0 : 0 < exteriorNorm K S (subsetPrimeIdeal K S r J) := by linarith
      have hre : (-(3 / 2 : ℂ)).re = -(3 / 2 : ℝ) := by
        have h : (-(3 / 2 : ℂ)) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
        rw [h, Complex.ofReal_re]
      have hwJ : ‖∏ i ∈ J, windowWeight K S g Z i (r i)‖ ≤ Wmax ^ J.card := by
        rw [norm_prod]
        calc ∏ i ∈ J, ‖windowWeight K S g Z i (r i)‖ ≤ ∏ _i ∈ J, Wmax :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hw i _)
          _ = Wmax ^ J.card := Finset.prod_const _
      have hq : exteriorNorm K S (subsetPrimeIdeal K S r J) ^ (-(3 / 2 : ℝ)) ≤
          (primeScale g Z ^ J.card)⁻¹ := by
        calc exteriorNorm K S (subsetPrimeIdeal K S r J) ^ (-(3 / 2 : ℝ))
            ≤ exteriorNorm K S (subsetPrimeIdeal K S r J) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
          _ = (exteriorNorm K S (subsetPrimeIdeal K S r J))⁻¹ := Real.rpow_neg_one _
          _ ≤ (primeScale g Z ^ J.card)⁻¹ := inv_anti₀ (by positivity) hlow
      unfold selectedFactor
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one,
        Complex.norm_cpow_eq_rpow_re_of_pos hq0, hre]
      exact mul_le_mul hwJ hq (Real.rpow_nonneg hq0.le _) (by positivity)
    -- the combined marked physical probe of one selected tuple
    have hcomb : ∀ r ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
        ‖markedPhysical K S P ψ g T Z r J‖ ≤
          K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ) := by
      intro r hr
      obtain ⟨hlow, hup⟩ := lc_subsetNorm_bounds hZ0 hr J
      obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = exteriorNorm K S (subsetPrimeIdeal K S r J) :=
        ⟨_, rfl⟩
      rw [← hq_def] at hlow hup
      have hq1 : 1 ≤ q := le_trans hpsk1 hlow
      have hq0 : 0 < q := by linarith
      have hqu : q ≤ u ^ 9 := by
        have h2k : (2 : ℝ) ^ J.card ≤ 2 ^ g.slots := pow_le_pow_right₀ (by norm_num) hk
        calc q ≤ (2 * primeScale g Z) ^ J.card := hup
          _ = 2 ^ J.card * primeScale g Z ^ J.card := mul_pow _ _ _
          _ ≤ 2 ^ g.slots * u ^ 8 := mul_le_mul h2k hpsk (by positivity) (by positivity)
          _ ≤ u * u ^ 8 := mul_le_mul_of_nonneg_right hu2 (by positivity)
          _ = u ^ 9 := by ring
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := lc_gram_window_conditions hu1 hq1 hqu
      have hXpos : 0 < Z ^ (17 / 48 : ℝ) / q := by rw [hp17]; positivity
      have hYpos : 0 < Z ^ (23 / 48 : ℝ) / q := by rw [hp23]; positivity
      have hEG : 0 ≤ 3 * CG * u ^ 18 * Z ^ δ := by positivity
      have hET : 0 ≤ CE * Z ^ δ := by positivity
      have hgramE : ∀ ν : ℝ, HeckeSkeleton.Gram.rowEnergy K S P
          P.denominator.toSmoothAnnularTest Cball
          (Z ^ (17 / 48 : ℝ) / q * (Z ^ (23 / 48 : ℝ) / q)) (Z ^ (23 / 48 : ℝ) / q) ν ≤
          (3 * CG * u ^ 18 * Z ^ δ) * (1 + |ν|) ^ JG := by
        intro ν
        rw [hp17, hp23]
        have h := hG Z (u ^ 17 / q * (u ^ 23 / q)) (u ^ 23 / q) ν hZG c1 c2
          (by rw [hp48]; exact c3) (by rw [hp48]; exact c4) c5
        calc _ ≤ CG * (1 + |ν|) ^ JG *
              HeckeSkeleton.Gram.gramScale (u ^ 17 / q * (u ^ 23 / q)) (u ^ 23 / q) *
                Z ^ δ := h
          _ ≤ CG * (1 + |ν|) ^ JG * (3 * u ^ 18) * Z ^ δ := by gcongr
          _ = (3 * CG * u ^ 18 * Z ^ δ) * (1 + |ν|) ^ JG := by ring
      have hthetaE : (∑' w : SIntegerOrbits K S (sixthPowerUnits K S),
          if (sIntegerOrbitNorm K S (sixthPowerUnits K S) w).val ≤
              Cball * (Z ^ (17 / 48 : ℝ) / q * (Z ^ (23 / 48 : ℝ) / q))
          then ‖markedRow K S P ψ g T Z r J w.out‖ ^ 2 else 0) ≤
          (CE * Z ^ δ) * (Z ^ (17 / 48 : ℝ) / q * (Z ^ (23 / 48 : ℝ) / q)) := by
        have h := hE Z hZE r hr J
        dsimp only at h
        rw [← hq_def] at h
        have hbox : Cball * (Z ^ (17 / 48 : ℝ) / q * (Z ^ (23 / 48 : ℝ) / q)) =
            Cball * Z ^ (5 / 6 : ℝ) / q ^ 2 := by
          rw [hp17, hp23, hp40]
          ring
        rw [hbox]
        calc _ ≤ CE * Z ^ (5 / 6 + δ) / q ^ 2 := h
          _ = (CE * Z ^ δ) * (Z ^ (17 / 48 : ℝ) / q * (Z ^ (23 / 48 : ℝ) / q)) := by
            rw [Real.rpow_add hZ0, hp17, hp23, hp40]
            ring
      have hb := hphysJ (Z ^ (17 / 48 : ℝ) / q) (Z ^ (23 / 48 : ℝ) / q) hXpos hYpos
        (Fintype.piFinset (fun i => primeWindow K S g T Z i))
        (fun p => markedCoeff K S ψ g Z r p J) (fun p => (Finset.univ \ J).image p)
        (fun p => Z * exteriorNorm K S (subsetPrimeIdeal K S p (Finset.univ \ J)))
        (fun p _ => mul_pos hZ0 (lc_exteriorNorm_pos K S _))
        (markedRow K S P ψ g T Z r J) (markedRow_eq_sum K S P ψ g T Z r J)
        (3 * CG * u ^ 18 * Z ^ δ) (CE * Z ^ δ) hEG hET hgramE hthetaE
      have hsq : Real.sqrt (3 * CG * u ^ 18 * Z ^ δ) * Real.sqrt (CE * Z ^ δ) =
          Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ) := by
        rw [← Real.sqrt_mul hEG]
        have h : 3 * CG * u ^ 18 * Z ^ δ * (CE * Z ^ δ) =
            3 * CG * CE * (u ^ 9 * Z ^ δ) ^ 2 := by ring
        rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      calc ‖markedPhysical K S P ψ g T Z r J‖
          ≤ K₀ * (Real.sqrt (3 * CG * u ^ 18 * Z ^ δ) * Real.sqrt (CE * Z ^ δ)) := by
            rw [hq_def] at hb
            exact hb
        _ = K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ) := by rw [hsq]; ring
    -- group the tuples by their selected part
    rcases (Fintype.piFinset (fun i => primeWindow K S g T Z i)).eq_empty_or_nonempty
      with hPF | ⟨p₀, hp₀⟩
    · rw [hPF, Finset.sum_empty, norm_zero]
      exact mul_nonneg (pow_nonneg hC1 _) hKu
    rw [lc_J_part_eq K S P ψ g T Z J p₀]
    set R := Fintype.piFinset
      (fun i => if i ∈ J then primeWindow K S g T Z i else {p₀ i}) with hR
    have hRPF : ∀ r ∈ R, r ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i) := by
      intro r hr
      rw [hR, Fintype.mem_piFinset] at hr
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ J
      · have h := hr i
        rw [ite_eq_left hi] at h
        exact h
      · have h := hr i
        rw [ite_eq_right hi, Finset.mem_singleton] at h
        rw [h]
        exact Fintype.mem_piFinset.mp hp₀ i
    have hcardR : (R.card : ℝ) ≤ (Clin * (2 * primeScale g Z)) ^ J.card := by
      rw [hR, Fintype.card_piFinset, Nat.cast_prod]
      calc ∏ i, (((if i ∈ J then primeWindow K S g T Z i else {p₀ i}) :
              Finset (ExteriorPrime K S)).card : ℝ)
          ≤ ∏ i : Fin g.slots, (if i ∈ J then Clin * (2 * primeScale g Z) else 1) := by
            apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
            intro i _
            by_cases hi : i ∈ J
            · rw [ite_eq_left hi, ite_eq_left hi]
              exact lc_card_primeWindow_le hZ1 i hcount
            · rw [ite_eq_right hi, ite_eq_right hi]
              simp
        _ = (Clin * (2 * primeScale g Z)) ^ J.card := by
            rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    have hper : ∀ r ∈ R,
        ‖selectedFactor K S g Z r J * markedPhysical K S P ψ g T Z r J‖ ≤
          Wmax ^ J.card * (primeScale g Z ^ J.card)⁻¹ *
            (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ)) := by
      intro r hr
      rw [norm_mul]
      exact mul_le_mul (hsel r (hRPF r hr)) (hcomb r (hRPF r hr)) (norm_nonneg _)
        (by positivity)
    have hpsJ0 : primeScale g Z ^ J.card ≠ 0 := pow_ne_zero _ hps0.ne'
    calc ‖∑ r ∈ R, selectedFactor K S g Z r J * markedPhysical K S P ψ g T Z r J‖
        ≤ ∑ r ∈ R, ‖selectedFactor K S g Z r J * markedPhysical K S P ψ g T Z r J‖ :=
          norm_sum_le _ _
      _ ≤ R.card • (Wmax ^ J.card * (primeScale g Z ^ J.card)⁻¹ *
            (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ))) :=
          Finset.sum_le_card_nsmul _ _ _ hper
      _ = (R.card : ℝ) * (Wmax ^ J.card * (primeScale g Z ^ J.card)⁻¹ *
            (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ))) := nsmul_eq_mul _ _
      _ ≤ (Clin * (2 * primeScale g Z)) ^ J.card * (Wmax ^ J.card *
            (primeScale g Z ^ J.card)⁻¹ * (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ))) :=
          mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = (2 * Clin * Wmax) ^ J.card * (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ)) *
            (primeScale g Z ^ J.card * (primeScale g Z ^ J.card)⁻¹) := by ring
      _ = (2 * Clin * Wmax) ^ J.card * (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ)) := by
          rw [mul_inv_cancel₀ hpsJ0, mul_one]
  -- all rescaled subsets
  have hexp : compensatedProbe K S P ψ g T Z =
      ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J := by
    unfold compensatedProbe
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have hnormZ : ‖Z ^ (3 / 16 + δ)‖ = u ^ 9 * Z ^ δ := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hZ0.le _), Real.rpow_add hZ0, hp9]
  rw [hexp, hnormZ]
  calc ‖∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
        ∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
          (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J‖
      ≤ ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          ‖∑ p ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
            (∏ i, windowWeight K S g Z i (p i)) * compensationTerm K S P ψ g Z p J‖ :=
        norm_sum_le _ _
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset,
          (2 * Clin * Wmax) ^ J.card * (K₀ * Real.sqrt (3 * CG * CE) * (u ^ 9 * Z ^ δ)) :=
        Finset.sum_le_sum (fun J _ => hJbound J)
    _ = (∑ J ∈ (Finset.univ : Finset (Fin g.slots)).powerset, (2 * Clin * Wmax) ^ J.card) *
          (K₀ * Real.sqrt (3 * CG * CE)) * (u ^ 9 * Z ^ δ) := by
        rw [← Finset.sum_mul]
        ring

variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)]

/-- LOW-CAUCHY-COMPENSATION for general data: the normalized probe.  The
residue normalizer is a constant (no nonvanishing is needed for an upper
bound) and the reciprocal prime normalizer costs an arbitrarily small power. -/
theorem lc_normalizedProbe_isBigO (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (μ : (p : S) → Measure (p.val.adicCompletion K)) [∀ p : S, (μ p).IsAddHaarMeasure]
    (hgram : HeckeSkeleton.Gram.GramBound K S P) (henergy : MarkedEnergy K S P ψ g T)
    (hnorm : ∀ ε : ℝ, 0 < ε →
      (fun Z => (primeNormalizer K S g T Z)⁻¹) =O[atTop] (fun Z : ℝ => Z ^ ε)) :
    ∀ ε : ℝ, 0 < ε →
      normalizedProbe K S μ P ψ g T =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε)) := by
  intro ε hε
  have h1 := lc_compensatedProbe_isBigO K S P ψ g T hgram henergy (ε / 2) (by positivity)
  have h2 := hnorm (ε / 2) (by positivity)
  have h3 := (h1.mul h2).const_mul_left ((physicalResidueNormalizer K S μ P)⁻¹)
  refine h3.congr' ?_ ?_
  · refine Filter.Eventually.of_forall (fun Z => ?_)
    simp only [normalizedProbe, div_eq_mul_inv, mul_inv]
    ring
  · filter_upwards [eventually_gt_atTop 0] with Z hZ
    show Z ^ (3 / 16 + ε / 2) * Z ^ (ε / 2) = Z ^ (3 / 16 + ε)
    rw [← Real.rpow_add hZ]
    congr 1
    ring

end HeckeSkeleton.LowCauchy
