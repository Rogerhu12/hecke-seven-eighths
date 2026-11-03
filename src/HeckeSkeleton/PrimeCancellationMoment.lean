import HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE.Source
import HeckeSkeleton.PrimeCancellationPolynomials
import HeckeGeneral.Analysis.ActualMomentPolynomialBridges
import PrimeCancellationAux
import PrimeCancellationPaired
import PrimeCancellationMaskCount
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeSkeleton.ExplicitHeckeFunctionalEquation

/-!
# Actual prime-slot moment adapters

Finite arithmetic and energy plumbing for `Moments.lean`.  Every row in the
model's `pairedRows` is covered.  The common mask retains both the fixed bad
primes and the prime divisors of the complete row ideal.

The numerical transfer lemmas consume slot estimates proved by the analytic
adapter; no zero-free assertion is identified with a moment inequality.
-/
set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.PrimeCancellationMoment

open NumberField IsDedekindDomain
open HeckeSkeleton.Moments.MOM_PRIME_BELOW_ONE
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-! ## The existing default exceptional-character choice -/

/-- The actual complete-ideal constructor has theta `{1}` and every slot
coefficient equal to one, so the inverse-membership condition is literal. -/
theorem decomposedMomentDataWithSlots_inverse_mem
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (ω' η : HeckeCharacter K) (ξ : SixthUnitClasses K S)
    (W : IdealTest K) (g : SlotGeometry K) (j : Fin g.slotCount) :
    ((decomposedMomentDataWithSlots K S P R ω' η ξ W g).slotCoefficient j)⁻¹ ∈
      (decomposedMomentDataWithSlots K S P R ω' η ξ W g).theta := by
  change (1 : HeckeCharacter K)⁻¹ ∈ ({1} : Finset (HeckeCharacter K))
  simp

/-- The original selected-slot operation preserves inverse membership. -/
theorem inverse_mem_restrictSlots (d : MomentData K ω ψ)
    (I : Finset (Fin d.geometry.slotCount))
    (hinverse : ∀ j, (d.slotCoefficient j)⁻¹ ∈ d.theta) (j : Fin I.card) :
    ((d.restrictSlots I).slotCoefficient j)⁻¹ ∈ (d.restrictSlots I).theta :=
  hinverse (selectedSlotIndex I j)

/-! ## The actual mask at a prime ideal -/

variable {c : TargetContext K}

theorem prime_eq_of_asIdeal_dvd {p q : HeightOneSpectrum (𝓞 K)}
    (h : q.asIdeal ∣ p.asIdeal) : q = p := by
  apply HeightOneSpectrum.asIdeal_injective
  exact (p.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm

theorem prime_divisor_condition_iff (p : HeightOneSpectrum (𝓞 K)) :
    (∀ q : HeightOneSpectrum (𝓞 K), q.asIdeal ∣ p.asIdeal →
      q ∉ places K c ∧ (6 : 𝓞 K) ∉ q.asIdeal) ↔
    p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal := by
  constructor
  · intro h
    exact h p dvd_rfl
  · intro h q hqp
    have heq : q = p := prime_eq_of_asIdeal_dvd hqp
    simpa only [heq] using h

theorem prime_isCoprime_iff_not_dvd (p : HeightOneSpectrum (𝓞 K))
    (I : Ideal (𝓞 K)) : IsCoprime p.asIdeal I ↔ ¬p.asIdeal ∣ I := by
  rw [Ideal.isCoprime_iff_sup_eq]
  constructor
  · intro hcop hdvd
    have hsup : p.asIdeal ⊔ I = p.asIdeal := sup_eq_left.mpr (Ideal.dvd_iff_le.mp hdvd)
    exact p.isPrime.ne_top (hsup.symm.trans hcop)
  · intro hnot
    by_contra hsup
    have heq : p.asIdeal = p.asIdeal ⊔ I :=
      p.isMaximal.eq_of_le hsup le_sup_left
    apply hnot
    apply Ideal.dvd_iff_le.mpr
    exact le_sup_right.trans heq.ge

/-- This is the literal formula in the supplied `Moments.lean`.
The final divisor condition is row-dependent. -/
theorem originalMomentMask_prime (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) :
    originalMomentMask (c := c) u p.asIdeal =
      if p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal ∧ ¬p.asIdeal ∣ u.val
      then true else false := by
  simp only [originalMomentMask, prime_divisor_condition_iff,
    prime_isCoprime_iff_not_dvd, and_assoc]

theorem deleted_prime_cases (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K))
    (hdeleted : originalMomentMask (c := c) u p.asIdeal = false) :
    p ∈ places K c ∨ (6 : 𝓞 K) ∈ p.asIdeal ∨ p.asIdeal ∣ u.val := by
  by_cases hS : p ∈ places K c
  · exact Or.inl hS
  by_cases hsix : (6 : 𝓞 K) ∈ p.asIdeal
  · exact Or.inr (Or.inl hsix)
  by_cases hu : p.asIdeal ∣ u.val
  · exact Or.inr (Or.inr hu)
  have hkept : originalMomentMask (c := c) u p.asIdeal = true := by
    rw [originalMomentMask_prime]
    simp only [hS, hsix, hu, not_false_eq_true, and_self, ite_true]
  have hbad : (false : Bool) = true := hdeleted.symm.trans hkept
  cases hbad

/-- A fixed nonzero ideal supporting S and the primes above 2 and 3.
The canonical choice is the product of the fixed excluded primes.
This record contains arithmetic data only, not an analytic estimate. -/
structure FixedBadPrimeSupport (c : TargetContext K) where
  ideal : NonzeroIdeal K
  places_dvd : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ places K c → p.asIdeal ∣ ideal.val
  six_dvd : ∀ p : HeightOneSpectrum (𝓞 K), (6 : 𝓞 K) ∈ p.asIdeal → p.asIdeal ∣ ideal.val

/-- The existing arithmetic choice already puts all primes above six in
`places`; its squarefree product is a canonical fixed deletion support. -/
def canonicalFixedBadPrimeSupport (c : TargetContext K) : FixedBadPrimeSupport c where
  ideal := squarefreeIdeal K (excludedPlaces K c)
  places_dvd := by
    intro p hp
    exact (prime_dvd_primeProduct_iff K p (excludedPlaces K c)).mpr hp
  six_dvd := by
    intro p hp
    apply (prime_dvd_primeProduct_iff K p (excludedPlaces K c)).mpr
    by_contra houtside
    exact (arithmeticData K c).away_six p houtside hp

theorem deleted_prime_dvd_fixed_mul_row (D : FixedBadPrimeSupport c)
    (u : NonzeroIdeal K) (p : HeightOneSpectrum (𝓞 K))
    (hdeleted : originalMomentMask (c := c) u p.asIdeal = false) :
    p.asIdeal ∣ D.ideal.val * u.val := by
  rcases deleted_prime_cases u p hdeleted with hS | hsix | hu
  · exact dvd_mul_of_dvd_left (D.places_dvd p hS) u.val
  · exact dvd_mul_of_dvd_left (D.six_dvd p hsix) u.val
  · exact dvd_mul_of_dvd_right hu D.ideal.val

/-- The norm of the supporting ideal has only the fixed multiplier ND. -/
theorem bad_support_norm_mul (D : FixedBadPrimeSupport c) (u : NonzeroIdeal K) :
    (Ideal.absNorm (D.ideal.val * u.val) : ℝ) =
      (Ideal.absNorm D.ideal.val : ℝ) * (Ideal.absNorm u.val : ℝ) := by
  simp only [map_mul, Nat.cast_mul]

/-- The fixed portion of the mask, without the row-coprimality condition. -/
def fixedMomentMask (I : Ideal (𝓞 K)) : Bool :=
  if ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
    p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal then true else false

/-- A fixed-mask reduction is valid only after proving the displayed
coefficient-zero property.  No such property is assumed by the source data. -/
theorem coefficient_mul_originalMask_eq_fixedMask
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) (a : ℂ)
    (hzero : ¬IsCoprime I u.val → a = 0) :
    a * (if originalMomentMask (c := c) u I then 1 else 0) =
      a * (if fixedMomentMask (c := c) I then 1 else 0) := by
  by_cases hcop : IsCoprime I u.val
  · by_cases hgood : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
        p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal
    · simp [originalMomentMask, fixedMomentMask, hcop, hgood]
    · simp [originalMomentMask, fixedMomentMask, hcop, hgood]
  · rw [hzero hcop]
    simp

/-! ## Wiring the actual model interfaces -/

variable {Z T : ℝ}

theorem source_paired_row_norm_le (M : ActualSourceModels K c)
    (i : ActualSourceIndex K c Z T) (s : SixthUnitClasses K (places K c))
    (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)) :
    idealNorm K u ≤ 2 * momentBaseFor i := by
  have h := norm_le_of_mem_pairedRows (pairedModelFor M i s) (pairedParametersFor i)
    (momentBaseFor i) u hu
  have hw := (recipeMoment_rowWidth_spec (R := expansionRecipeRaw K c) i).2.2
  have h' : idealNorm K u ≤ momentBaseFor i ^ (rowWidthFor i + 0) := h
  rw [add_zero] at h'
  exact h'.trans_eq hw

/-- Every actual source base is at least two. -/
theorem source_momentBase_ge_two (i : ActualSourceIndex K c Z T) : 2 ≤ momentBaseFor i :=
  recipeMomentBase_ge_two (R := expansionRecipeRaw K c) i

/-- Capacity controls the total selected length using the fixed slot
count and mesh, independently of the plain witness lengths. -/
theorem selectedLength_le_slots_mul_mesh_of_pairedCapacity
    (i : ActualSourceIndex K c Z T) (hcap : pairedCapacityFor i) :
    selectedLengthFor i ≤ (c.geometry.slots : ℝ) * (momentMesh K c.family).val := by
  unfold selectedLengthFor
  calc
    (∑ _j ∈ i.selected,
      HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlockFor i).shell)
        ≤ ∑ _j ∈ i.selected, (momentMesh K c.family).val := by
          exact Finset.sum_le_sum (fun j hj => hcap.1 j hj)
    _ = (i.selected.card : ℝ) * (momentMesh K c.family).val := by simp
    _ ≤ (c.geometry.slots : ℝ) * (momentMesh K c.family).val := by
      apply mul_le_mul_of_nonneg_right _ (momentMesh K c.family).property.le
      have hcard : i.selected.card ≤ c.geometry.slots := by
        simpa only [Fintype.card_fin] using Finset.card_le_univ i.selected
      exact_mod_cast hcard

/-- At subunit base all filtered ideal rows vanish, since nonzero integral
ideals have norm at least one. No shell sign hypothesis is needed. -/
theorem pairedRows_eq_empty_of_base_lt_one
    (M : ActualSourceModels K c) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (hbase : momentBaseFor i < 1) :
    pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) = ∅ := by
  exact absurd hbase (not_lt.mpr (by linarith [source_momentBase_ge_two i]))

theorem source_paired_slot_finite_factors (M : ActualSourceModels K c)
    (hrows : SourceRowEligibilityFor M) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (j : Fin (pairedModelFor M i s).geometry.slotCount) :
    FiniteOrder ((pairedModelFor M i s).rowCharacter u) ∧
      FiniteOrder ((pairedModelFor M i s).slotCoefficient j) :=
  ⟨(pairedModelFor M i s).rowCharacter_finite u, hrows.paired_finite_slots Z T i s j⟩

/-- Finite-order closure is supplied by the actual character group. -/
theorem source_paired_slot_finite
    (M : ActualSourceModels K c) (hrows : SourceRowEligibilityFor M)
    (i : ActualSourceIndex K c Z T) (s : SixthUnitClasses K (places K c))
    (u : NonzeroIdeal K) (j : Fin (pairedModelFor M i s).geometry.slotCount) :
    FiniteOrder ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j) := by
  rcases source_paired_slot_finite_factors M hrows i s u j with ⟨hu, hj⟩
  exact hu.mul hj

theorem source_paired_slot_character_ne_one (M : ActualSourceModels K c)
    (hrows : SourceRowEligibilityFor M) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c))
    (hinverse : ∀ j, ((pairedModelFor M i s).slotCoefficient j)⁻¹ ∈ (pairedModelFor M i s).theta)
    (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i))
    (j : Fin (pairedModelFor M i s).geometry.slotCount) :
    (pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j ≠ 1 := by
  apply paired_slot_character_ne_one (pairedModelFor M i s) (pairedParametersFor i)
    (momentBaseFor i) ((hrows.geometry Z T i s).2) hinverse u hu j

theorem source_paired_slotCount_le_of_selected_equiv (M : ActualSourceModels K c)
    (i : ActualSourceIndex K c Z T) (s : SixthUnitClasses K (places K c))
    (e : Fin (pairedModelFor M i s).geometry.slotCount ≃ {j // j ∈ i.selected}) :
    (pairedModelFor M i s).geometry.slotCount ≤ c.geometry.slots := by
  apply slotCount_le_of_embedding (pairedModelFor M i s).geometry c.geometry.slots
  exact ⟨fun j => (e j).val, Subtype.val_injective.comp e.injective⟩

theorem source_paired_zero_slot_product (M : ActualSourceModels K c)
    (hrows : SourceRowEligibilityFor M) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (hz : selectedLengthFor i = 0)
    (u : NonzeroIdeal K) (t : ℝ) :
    slotProduct (pairedModelFor M i s) u (momentBaseFor i) t = 1 := by
  apply slotProduct_eq_one_of_totalLength_zero
  exact ((hrows.geometry Z T i s).2).trans hz

theorem source_paired_deleted_prime_dvd
    (R : RowCharacterInput K (places K c) (probeData K c))
    (M : ActualSourceModels K c) (hcal : SourcePolynomialCalibrationFor R M)
    (D : FixedBadPrimeSupport c) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K))
    (hdeleted : (pairedModelFor M i s).commonMask u p.asIdeal = false) :
    p.asIdeal ∣ D.ideal.val * u.val := by
  apply deleted_prime_dvd_fixed_mul_row D u p
  rw [← (hcal.mask Z T i s u p.asIdeal).2]
  exact hdeleted

/-- Transfer any uniform linear ideal count to the actual filtered rows. -/
theorem source_paired_card_le_of_ideal_count (M : ActualSourceModels K c)
    (i : ActualSourceIndex K c Z T) (s : SixthUnitClasses K (places K c))
    (Crows : ℝ)
    (hcount : ∀ rows : Finset (NonzeroIdeal K),
      (∀ u ∈ rows, idealNorm K u ≤ 2 * momentBaseFor i) →
      (rows.card : ℝ) ≤ Crows * momentBaseFor i) :
    ((pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)).card : ℝ)
      ≤ Crows * momentBaseFor i := by
  apply hcount
  intro u hu
  exact source_paired_row_norm_le M i s u hu

/-- The fixed number-field ideal-count theorem covers every model row,
including rows not represented by a physical witness. -/
theorem exists_source_paired_linear_count :
    ∃ Crows : ℝ, 0 < Crows ∧ ∀ (M : ActualSourceModels K c)
      (Z T : ℝ) (i : ActualSourceIndex K c Z T)
      (s : SixthUnitClasses K (places K c)), 1 ≤ momentBaseFor i →
      ((pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)).card : ℝ)
        ≤ Crows * momentBaseFor i := by
  obtain ⟨Crows, hCrows, hcount⟩ := dyadicIdealSupport_linear_count K
  refine ⟨2 * Crows, by linarith, ?_⟩
  intro M Z T i s hbase
  have h2 : 1 ≤ 2 * momentBaseFor i := by linarith
  apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans
    ((hcount _ h2).trans_eq (by ring))
  intro u hu
  apply (mem_dyadicIdealSupport_iff K (by linarith : 0 ≤ 2 * momentBaseFor i / 2) u).mpr
  have hn := source_paired_row_norm_le M i s u hu
  linarith

/-- The number of deleted primes is logarithmic in the complete row ideal.
The prime annulus can replace the lower threshold 2 by a larger `B`. -/
theorem source_paired_deleted_count
    (R : RowCharacterInput K (places K c) (probeData K c))
    (M : ActualSourceModels K c) (hcal : SourcePolynomialCalibrationFor R M)
    (D : FixedBadPrimeSupport c) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (pool : Finset (HeightOneSpectrum (𝓞 K))) (B : ℝ) (hB : 1 < B)
    (hlower : ∀ p ∈ pool, B ≤ (Ideal.absNorm p.asIdeal : ℝ)) :
    ((pool.filter (fun p => (pairedModelFor M i s).commonMask u p.asIdeal = false)).card : ℝ)
      ≤ Real.log (idealNorm K (D.ideal * u)) / Real.log B := by
  apply PrimeCancellation.MaskCount.card_prime_divisors_le_log
    Ideal.absNorm _ (D.ideal.val * u.val) B
    (Ideal.absNorm_pos_of_nonZeroDivisors (D.ideal * u)) hB
  · intro p hp
    exact hlower p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact source_paired_deleted_prime_dvd R M hcal D i s u p
      (Finset.mem_filter.mp hp).2

/-- The simplest deletion bound is uniform over all paired rows of norm at
most twice the moment base, without a lower bound on slot lengths. -/
theorem source_paired_deleted_count_le_base
    (R : RowCharacterInput K (places K c) (probeData K c))
    (M : ActualSourceModels K c) (hcal : SourcePolynomialCalibrationFor R M)
    (D : FixedBadPrimeSupport c) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (u : NonzeroIdeal K)
    (hu : u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i))
    (pool : Finset (HeightOneSpectrum (𝓞 K))) :
    ((pool.filter (fun p => (pairedModelFor M i s).commonMask u p.asIdeal = false)).card : ℝ)
      ≤ (Real.log (idealNorm K D.ideal) + Real.log (2 * momentBaseFor i)) / Real.log 2 := by
  have hdel := source_paired_deleted_count R M hcal D i s u pool 2 (by norm_num)
    (fun p _ => by exact_mod_cast (Nat.succ_le_iff.mpr
      (NumberField.HeightOneSpectrum.one_lt_absNorm p)))
  have hprod : idealNorm K (D.ideal * u) = idealNorm K D.ideal * idealNorm K u := by
    simp only [idealNorm, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  have hlog := Real.log_le_log (idealNorm_pos K u) (source_paired_row_norm_le M i s u hu)
  rw [hprod, Real.log_mul (idealNorm_pos K D.ideal).ne' (idealNorm_pos K u).ne'] at hdel
  exact hdel.trans ((div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    (add_le_add (le_refl (Real.log (idealNorm K D.ideal))) hlog))

/-- A standard all-row polynomial conductor bound supplies the exact
logarithmic conductor field used by the uniform model contract, with `q=0`.
The positivity premise is provided by the actual Hecke adapter for every
nonprincipal finite-order slot character. -/
theorem source_conductor_control_of_polynomial
    (M : ActualSourceModels K c) (C₀ r : ℝ) (hC₀ : 1 ≤ C₀) (hr : 0 ≤ r)
    (hpositive : ∀ Z T (i : ActualSourceIndex K c Z T) s u,
      1 ≤ Z → 1 ≤ T → 1 ≤ momentBaseFor i →
      u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) →
      ∀ j, 0 < heckeConductorScale K
        ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j))
    (hpoly : ∀ Z T (i : ActualSourceIndex K c Z T) s u,
      1 ≤ Z → 1 ≤ T → 1 ≤ momentBaseFor i →
      u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) →
      ∀ j, heckeConductorScale K
        ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j) ≤
          C₀ * (idealNorm K u) ^ r) :
    ∃ D q : ℝ, 1 ≤ D ∧ 0 ≤ q ∧
      ∀ Z T (i : ActualSourceIndex K c Z T) s u,
        1 ≤ Z → 1 ≤ T → 1 ≤ momentBaseFor i →
        u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i) →
        ∀ j, Real.log (heckeConductorScale K
          ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j)) ≤
            D * (1 + Real.log (momentBaseFor i)) * (1 + T) ^ q := by
  refine ⟨2 * (1 + Real.log C₀ + r), 0, ?_, le_rfl, ?_⟩
  · linarith [Real.log_nonneg hC₀]
  · intro Z T i s u hZ hT hX hu j
    have hX2 : 1 ≤ 2 * momentBaseFor i := by linarith
    have hlog := logQ_le_of_norm_polynomial
      (heckeConductorScale K
        ((pairedModelFor M i s).rowCharacter u * (pairedModelFor M i s).slotCoefficient j))
      C₀ (idealNorm K u) (2 * momentBaseFor i) r
      (hpositive Z T i s u hZ hT hX hu j) hC₀ (idealNorm_pos K u)
      (source_paired_row_norm_le M i s u hu) hX2 hr (hpoly Z T i s u hZ hT hX hu j)
    have hbpos : 0 < momentBaseFor i := by linarith
    have hl2 : Real.log (2 * momentBaseFor i) = Real.log 2 + Real.log (momentBaseFor i) :=
      Real.log_mul (by norm_num) hbpos.ne'
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogb : 0 ≤ Real.log (momentBaseFor i) := Real.log_nonneg hX
    have hcoef : 0 ≤ 1 + Real.log C₀ + r := by linarith [Real.log_nonneg hC₀]
    rw [Real.rpow_zero, mul_one]
    calc
      _ ≤ (1 + Real.log C₀ + r) * (1 + Real.log (2 * momentBaseFor i)) := hlog
      _ ≤ (1 + Real.log C₀ + r) * (2 * (1 + Real.log (momentBaseFor i))) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        rw [hl2]
        linarith
      _ = _ := by ring

/-! ## Numerical transfer after the analytic estimate is proved -/

theorem source_paired_energy_le_of_slot_bounds (M : ActualSourceModels K c)
    (hrows : SourceRowEligibilityFor M) (i : ActualSourceIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) (κ eps Crows : ℝ)
    (hbase : 1 ≤ momentBaseFor i)
    (C loss : Fin (pairedModelFor M i s).geometry.slotCount → ℝ)
    (hC : ∀ j, 0 ≤ C j) (hloss : (∑ j, loss j) ≤ eps)
    (hcard : ((pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)).card : ℝ)
      ≤ Crows * momentBaseFor i)
    (hslot : ∀ u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i),
      ∀ j, ‖primePolynomial (pairedModelFor M i s) j u (momentBaseFor i) 0‖ ^ 2 ≤
        C j * (momentBaseFor i) ^
          (κ * ((pairedModelFor M i s).geometry.slots j).length + loss j)) :
    (∑ u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i),
      ‖slotProduct (pairedModelFor M i s) u (momentBaseFor i) 0‖ ^ 2) ≤
      (Crows * ∏ j, C j) * (momentBaseFor i) ^ (1 + (κ * selectedLengthFor i + eps)) := by
  have hcard' :
      ((pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)).card : ℝ)
        ≤ Crows * (momentBaseFor i) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hcard
  have htransfer := PrimeCancellationAux.paired_sum_le_of_slot_bounds
    (pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i)) Finset.univ
    (fun u j => primePolynomial (pairedModelFor M i s) j u (momentBaseFor i) 0)
    C (fun j => ((pairedModelFor M i s).geometry.slots j).length) loss
    (momentBaseFor i) κ eps Crows 1 hbase (fun j _ => hC j) hcard' hloss
    (fun u hu j _ => hslot u hu j)
  change
    (∑ u ∈ pairedRows (pairedModelFor M i s) (pairedParametersFor i) (momentBaseFor i),
      ‖slotProduct (pairedModelFor M i s) u (momentBaseFor i) 0‖ ^ 2) ≤
      (Crows * ∏ j, C j) * (momentBaseFor i) ^
        (1 + (κ * (pairedModelFor M i s).geometry.totalLength + eps)) at htransfer
  rw [(hrows.geometry Z T i s).2] at htransfer
  exact htransfer

end HeckeSkeleton.PrimeCancellationMoment
