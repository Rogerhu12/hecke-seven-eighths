import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalFrequency
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildRows

/-!
# Actual exceptional rows retain the extracted fourth-power base

The complete correlation constructs the residual ideal and its frequency.
The primitive inducing-character classification is only a congruence of
the original valuations and a prescribed sixth-power-free part.  The
fourth-power divisibility, the lower bound for this part, and the resulting
row count are proved here.  Every original unit sector is retained through
the actual residual-ideal fibers.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open UniqueFactorizationMonoid HeckePort.CenteredMomentCounting

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual extracted row, together with its ideal factorization.
The constructor below obtains both from the complete correlation. -/
structure ActualExceptionalRow
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (Ih : A.Exterior) (h : A.R)
    extends ActualChildRow Ih h
      (primePowerProductGenerator C p (fun i => min (m i) (n i)) *
        nonunitFrequencyGenerator C p m n h)
      ((Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
        A.exteriorNorm (nonunitFrequencyRadical C p m n h)) where
  ideal_factor : Ih.val =
    gcd (primePowerProduct p m).val (primePowerProduct p n).val *
      (nonunitFrequencyRadical C p m n h).val * ideal.val

/-- No extraction or exceptional-row count is supplied by the caller. -/
theorem exists_actual_exceptional_row
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (a b : A.R) (ha : A.Generates (primePowerProduct p m) a)
    (hb : A.Generates (primePowerProduct p n) b)
    (Ih : A.Exterior) (h : A.R) (hh : A.Generates Ih h)
    (hne : generatedIdealCorrelation (σ := σ) (primePowerProduct p m)
      (primePowerProduct p n) a b ha hb h ≠ 0) :
    Nonempty (ActualExceptionalRow C p m n Ih h) := by
  obtain ⟨h', Ir, hgen, hfreq, hideal, hnorm⟩ :=
    actual_product_correlation_frequency_ideal_extract_of_generates
      C p hp m n a b ha hb Ih h hh hne
  exact ⟨⟨⟨Ir, h', hgen, hfreq, hnorm⟩, hideal⟩⟩

namespace ActualExceptionalRow

variable {C : A.GeneralArithmeticContext σ η hS}
variable {p : ι → ExteriorPrime A} {m n : ι → ℕ}
variable {Ih : A.Exterior} {h : A.R}

theorem base_fourth_power (r : ActualExceptionalRow C p m n Ih h)
    (hp : Function.Injective p)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes C p m n h,
      6 ∣ (normalizedFactors Ih.val).count (p i).val.asIdeal)
    (base factor : Ideal (𝓞 F)) (hfactor : r.ideal.val = base * factor ^ 6) :
    (multiplicityOneNonunitRadical C p m n h).val ^ 4 ∣ base ∧
      A.exteriorNorm (multiplicityOneNonunitRadical C p m n h) ^ 4 ≤
        (Ideal.absNorm base : ℝ) :=
  exceptional_frequency_base_fourth_power C p hp m n h Ih r.ideal
    r.ideal_factor hclass base factor hfactor

theorem base_lower (r : ActualExceptionalRow C p m n Ih h)
    (hp : Function.Injective p)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes C p m n h,
      6 ∣ (normalizedFactors Ih.val).count (p i).val.asIdeal)
    (base factor : Ideal (𝓞 F)) (hfactor : r.ideal.val = base * factor ^ 6)
    (Z v : ℝ) (hZ : 0 < Z)
    (hwindow : Z ^ v ≤ A.exteriorNorm (multiplicityOneNonunitRadical C p m n h)) :
    Z ^ (4 * v) ≤ (Ideal.absNorm base : ℝ) := by
  have hw := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le v) hwindow 4
  have he : (Z ^ v) ^ (4 : ℕ) = Z ^ (4 * v) := by
    rw [← Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num <;> ring
  rw [he] at hw
  exact hw.trans (r.base_fourth_power hp hclass base factor hfactor).2

end ActualExceptionalRow

/-- The real exceptional count from the actual extracted rows.  The
only arithmetic classification inputs are the original six-congruences
and the prescribed common sixth-power-free part.  A subunit residual
range is handled by the proved ideal count as well. -/
theorem actual_exceptional_sector_count {H : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (rows : Finset H) (Ih : H → A.Exterior) (h : H → A.R)
    (r : ∀ x, ActualExceptionalRow C p m n (Ih x) (h x))
    (base : Ideal (𝓞 F))
    (hclass : ∀ x ∈ rows, ∀ i ∈ multiplicityOneNonunitPrimes C p m n (h x),
      6 ∣ (normalizedFactors (Ih x).val).count (p i).val.asIdeal)
    (hfactor : ∀ x ∈ rows, ∃ a : Ideal (𝓞 F), (r x).ideal.val = base * a ^ 6)
    (Z width v sectors : ℝ) (hZ : 1 ≤ Z) (hv : 0 ≤ v) (hsectors : 0 ≤ sectors)
    (hwindow : ∀ x ∈ rows, Z ^ v ≤
      A.exteriorNorm (multiplicityOneNonunitRadical C p m n (h x)))
    (hcutoff : ∀ x ∈ rows, A.exteriorNorm (Ih x) ≤
      ((Ideal.absNorm (gcd (primePowerProduct p m).val (primePowerProduct p n).val) : ℝ) *
        A.exteriorNorm (nonunitFrequencyRadical C p m n (h x))) * Z ^ width)
    (hfiber : ∀ I ∈ rows.image (fun x => (r x).ideal.val),
      ((rows.filter (fun x => (r x).ideal.val = I)).card : ℝ) ≤ sectors) :
    (rows.card : ℝ) ≤
      sectors * idealCountConstant F * Z ^ ((width - 2 * v) / 6) := by
  by_cases hne : rows.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨factor, hfac⟩ := hfactor x hx
    have hbase : Z ^ (2 * (2 * v)) ≤ (Ideal.absNorm base : ℝ) := by
      convert (r x).base_lower hp (hclass x hx) base factor hfac Z v
        (zero_lt_one.trans_le hZ) (hwindow x hx) using 1 <;> ring
    apply exceptional_sector_row_count rows (fun x => (r x).ideal.val) base
      (fun x _ => (r x).ideal.property.1) hfactor Z width (2 * v) sectors hZ
      (by linarith) hsectors hbase
    · intro x hx
      exact (r x).toActualChildRow.norm_le _ (hcutoff x hx)
    · exact hfiber
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hsectors
      (zero_le_one.trans (one_le_idealCountConstant F)))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_actual_exceptional_row
#print axioms HeckeSkeleton.Moments.EngineStep.actual_exceptional_sector_count
