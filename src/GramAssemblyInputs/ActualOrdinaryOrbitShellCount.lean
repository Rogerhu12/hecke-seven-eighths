import ActualExceptionalSixthOrbitCount
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Arithmetic.SIntegerOrbitDilation

/-!
UNCOMPILED / native 0. Linear norm-cutoff counting on the original sixth-unit
quotient, retaining all finite unit sectors. The counting constant precedes
P and every moving frequency, divisor and scale. Ordinary ring divisibility
is transported only through the proved original-orbit dilation equivalence.
No frequency distribution or Gram estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.Analysis.ActualOrdinaryOrbitShellCountDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.ActualGramExceptionalCountDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "Γ" => sixthPowerUnits K S
local notation "OQ" => SIntegerOrbits K S (sixthPowerUnits K S)
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- The genuine original-Gamma norm cutoff, with every unit sector. -/
def ordinaryOrbitCutoff (X : ℝ) :=
  {q : OQ // (sIntegerOrbitNorm K S Γ q).val ≤ X}

instance finite_ordinaryOrbitCutoff (X : ℝ) : Finite (ordinaryOrbitCutoff K S X) :=
  inferInstanceAs (Finite (ActualBoundedSIntegerOrbits K S X))

/-- Literal complete-ideal and unit-sector coordinates, with no primitive
or sixth-power-free restriction on the complete ideal. -/
def ordinaryOrbitCutoffEmbedding (P : ProbeData K S) {X : ℝ} (hX : 0 ≤ X) :
    ordinaryOrbitCutoff K S X ↪
      ({I : NonzeroIdeal K // I ∈ dyadicIdealSupport K (X / 2)} × SixthUnitClasses K S) where
  toFun q :=
    (⟨((exteriorIdealSectorsEquivActualOrbits K S P).symm q.val).1.val, by
      apply (mem_dyadicIdealSupport_iff K (div_nonneg hX (by norm_num)) _).mpr
      have hq : idealNorm K
          ((exteriorIdealSectorsEquivActualOrbits K S P).symm q.val).1.val ≤ X :=
        (actualOrbitCoordinates_norm K S P q.val).le.trans q.property
      simpa only [show 2 * (X / 2) = X by ring] using hq⟩,
      ((exteriorIdealSectorsEquivActualOrbits K S P).symm q.val).2)
  inj' q r h := by
    apply Subtype.ext
    apply (exteriorIdealSectorsEquivActualOrbits K S P).symm.injective
    have h1 := congrArg (fun x :
        {I : NonzeroIdeal K // I ∈ dyadicIdealSupport K (X / 2)} × SixthUnitClasses K S =>
          x.1.val) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Subtype.ext h1) h2

theorem ordinaryOrbitCutoff_card_le_support (P : ProbeData K S)
    {X : ℝ} (hX : 0 ≤ X) :
    Nat.card (ordinaryOrbitCutoff K S X) ≤
      Nat.card (SixthUnitClasses K S) * (dyadicIdealSupport K (X / 2)).card := by
  have h := Nat.card_le_card_of_injective (ordinaryOrbitCutoffEmbedding K S P hX)
    (ordinaryOrbitCutoffEmbedding K S P hX).injective
  simpa only [Nat.card_prod, Nat.card_eq_finsetCard, Nat.mul_comm] using h

/-- Small cutoffs are genuinely empty, including all sectors. -/
theorem ordinaryOrbitCutoff_card_eq_zero_of_lt_one (X : ℝ) (hX : X < 1) :
    Nat.card (ordinaryOrbitCutoff K S X) = 0 := by
  letI : IsEmpty (ordinaryOrbitCutoff K S X) := ⟨fun q =>
    (not_le_of_gt hX) ((one_le_actualSIntegerOrbitNorm K S q.val).trans q.property)⟩
  exact Nat.card_of_isEmpty

/-- A single linear constant is chosen before even the generator/probe data. -/
theorem exists_ordinaryOrbitCutoff_linear_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (X : ℝ), 0 < X →
      (Nat.card (ordinaryOrbitCutoff K S X) : ℝ) ≤ C * X := by
  obtain ⟨B, hB, hb⟩ := dyadicIdealSupport_linear_count K
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  refine ⟨(Nat.card (SixthUnitClasses K S) : ℝ) * B, mul_pos hM hB, ?_⟩
  intro P X hX
  by_cases h1 : 1 ≤ X
  · have hc : (Nat.card (ordinaryOrbitCutoff K S X) : ℝ) ≤
        (Nat.card (SixthUnitClasses K S) : ℝ) *
          ((dyadicIdealSupport K (X / 2)).card : ℝ) := by
      exact_mod_cast ordinaryOrbitCutoff_card_le_support K S P hX.le
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hb X h1) hM.le)
  · rw [ordinaryOrbitCutoff_card_eq_zero_of_lt_one K S X (lt_of_not_ge h1)]
    simp only [Nat.cast_zero]
    positivity

/-- Every genuinely divisible orbit, with its actual original norm bound. -/
def divisibleOrdinaryOrbitCutoff (d : NZ) (T : ℝ) :=
  {q : OQ // sIntegerOrbitDivisible K S Γ d q ∧
    (sIntegerOrbitNorm K S Γ q).val ≤ T}

instance finite_divisibleOrdinaryOrbitCutoff (d : NZ) (T : ℝ) :
    Finite (divisibleOrdinaryOrbitCutoff K S d T) :=
  Finite.of_injective (β := ordinaryOrbitCutoff K S T)
    (fun q : divisibleOrdinaryOrbitCutoff K S d T =>
      (⟨q.val, q.property.2⟩ : ordinaryOrbitCutoff K S T))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ordinaryOrbitCutoff K S T => z.val) h))

/-- Restriction of the existing literal dilation bijection to norm cutoffs.
The source radius is divided by the actual element norm, not an ideal label. -/
def ordinaryOrbitDilationCutoffEquiv (d : NZ) (T : ℝ) :
    ordinaryOrbitCutoff K S (T / (sIntegerElementNorm K S d).val) ≃
      divisibleOrdinaryOrbitCutoff K S d T :=
  Equiv.ofBijective
    (fun p : ordinaryOrbitCutoff K S (T / (sIntegerElementNorm K S d).val) =>
      (⟨sIntegerOrbitDilation K S Γ d p.val,
      (sIntegerOrbitDivisible_iff_exists K S Γ d _).mpr ⟨p.val, rfl⟩, by
        rw [sIntegerOrbitNorm_dilation, mul_comm]
        exact (le_div_iff₀ (sIntegerElementNorm K S d).property).mp p.property⟩ :
        divisibleOrdinaryOrbitCutoff K S d T))
    ⟨fun _ _ h => Subtype.ext
        (sIntegerOrbitDilation_injective K S Γ d (congrArg Subtype.val h)), by
      intro q
      obtain ⟨p, hp⟩ := (sIntegerOrbitDivisible_iff_exists K S Γ d q.val).mp q.property.1
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      apply (le_div_iff₀ (sIntegerElementNorm K S d).property).mpr
      have hn := q.property.2
      rw [← hp, sIntegerOrbitNorm_dilation] at hn
      simpa only [mul_comm] using hn⟩

theorem divisibleOrdinaryOrbitCutoff_card_eq (d : NZ) (T : ℝ) :
    Nat.card (divisibleOrdinaryOrbitCutoff K S d T) =
      Nat.card (ordinaryOrbitCutoff K S (T / (sIntegerElementNorm K S d).val)) :=
  (Nat.card_congr (ordinaryOrbitDilationCutoffEquiv K S d T)).symm

/-- The constant precedes P,d,T; the gain is the true element-norm divisor. -/
theorem exists_divisibleOrdinaryOrbitCutoff_linear_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (d : NZ) (T : ℝ), 0 < T →
      (Nat.card (divisibleOrdinaryOrbitCutoff K S d T) : ℝ) ≤
        C * T / (sIntegerElementNorm K S d).val := by
  obtain ⟨C, hC, hb⟩ := exists_ordinaryOrbitCutoff_linear_count K S
  refine ⟨C, hC, ?_⟩
  intro P d T hT
  rw [divisibleOrdinaryOrbitCutoff_card_eq]
  simpa only [mul_div_assoc] using
    hb P (T / (sIntegerElementNorm K S d).val)
      (div_pos hT (sIntegerElementNorm K S d).property)

/-- Finite rows may be specified by the actual nonzero representative q.out.
The bound does not discard any sixth-unit sector or assume a row count. -/
theorem exists_divisible_ordinaryOrbit_finset_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (d : NZ) (T : ℝ), 0 < T →
      ∀ F : Finset OQ,
        (∀ q ∈ F, d.val ∣ q.out.val ∧ (sIntegerOrbitNorm K S Γ q).val ≤ T) →
        (F.card : ℝ) ≤ C * T / (sIntegerElementNorm K S d).val := by
  obtain ⟨C, hC, hb⟩ := exists_divisibleOrdinaryOrbitCutoff_linear_count K S
  refine ⟨C, hC, ?_⟩
  intro P d T hT F hF
  let f : {q : OQ // q ∈ F} → divisibleOrdinaryOrbitCutoff K S d T := fun q =>
    ⟨q.val, by
      have hd : sIntegerOrbitDivisible K S Γ d (Quotient.mk _ q.val.out) :=
        (hF q.val q.property).1
      simpa only [Quotient.out_eq] using hd,
      (hF q.val q.property).2⟩
  have hf : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : divisibleOrdinaryOrbitCutoff K S d T => z.val) h)
  have hc : (F.card : ℝ) ≤
      (Nat.card (divisibleOrdinaryOrbitCutoff K S d T) : ℝ) := by
    have h := Nat.card_le_card_of_injective f hf
    exact_mod_cast (by simpa only [Nat.card_eq_finsetCard] using h :
      F.card ≤ Nat.card (divisibleOrdinaryOrbitCutoff K S d T))
  exact hc.trans (hb P d T hT)

end HeckeGeneral.Analysis.ActualOrdinaryOrbitShellCountDraft
