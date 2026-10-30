import HeckeGeneral.Analysis.SIntegerSexticDyadicAmplification
import HeckeGeneral.Arithmetic.SUnitFiniteGeneration
import HeckeGeneral.Arithmetic.SIntegerOrbitCounting
import HeckeGeneral.Arithmetic.SIntegerModulusNorm
import HeckeGeneral.Characters.InfinityPacket

/-!
Actual inverse rows on the quotient by sixth powers of the original S-units.
The row symbol is the actual sextic evaluation, with its fixed S/6 deletion;
no row-to-Hecke extension or CanonicalAdmissibility predicate is used.

The fixed-scale zero-slot MI and the OPTIONAL independent-scale supremum
input are distinct explicit analytic assertions. The latter is stated by
nonnegative rowwise majorants, avoiding an unbounded real sSup convention.
No derivation of this supremum control from Q Lemma 4.5 is supplied. The
compact-in-s family is the literal W_s(y)=W(y)y^(-s); its finite-seminorm
estimates and the calibration of ALL Gamma-sectors to source allowed rows
remain separate obligations. There is no seed or zero-free conclusion.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The literal sixth-power subgroup of the original global S-unit group. -/
def sixthPowerSUnitSubgroup : Subgroup (S.unit K) :=
  (powMonoidHom 6 : S.unit K →* S.unit K).range

instance sixthPowerSUnitSubgroup_finiteIndex : (sixthPowerSUnitSubgroup K S).FiniteIndex :=
  sUnit_power_range_finiteIndex K S 6 (by norm_num)

abbrev ActualSIntegerOrbit := SIntegerOrbits K S (sixthPowerSUnitSubgroup K S)

/-- The genuine local product norm on the actual quotient. -/
def actualSIntegerOrbitNorm (q : ActualSIntegerOrbit K S) : ℝ :=
  (sIntegerOrbitNorm K S (sixthPowerSUnitSubgroup K S) q).val

theorem actualSIntegerOrbitNorm_pos (q : ActualSIntegerOrbit K S) :
    0 < actualSIntegerOrbitNorm K S q :=
  (sIntegerOrbitNorm K S (sixthPowerSUnitSubgroup K S) q).property

@[simp] theorem actualSIntegerOrbitNorm_mk
    (a : NonzeroRingElements (S.integer K)) :
    actualSIntegerOrbitNorm K S (Quotient.mk _ a) = (sIntegerElementNorm K S a).val := rfl

theorem one_le_actualSIntegerOrbitNorm (q : ActualSIntegerOrbit K S) :
    1 ≤ actualSIntegerOrbitNorm K S q := by
  change 1 ≤ (sIntegerOrbitNorm K S (sixthPowerSUnitSubgroup K S) q).val
  rw [← sIntegerOrbitNorm_out]
  exact one_le_sIntegerElementNorm K S q.out

abbrev ActualBoundedSIntegerOrbits (H : ℝ) :=
  {q : ActualSIntegerOrbit K S // actualSIntegerOrbitNorm K S q ≤ H}

instance finite_actualBoundedSIntegerOrbits (H : ℝ) :
    Finite (ActualBoundedSIntegerOrbits K S H) :=
  inferInstanceAs (Finite
    (BoundedSIntegerOrbits K S (sixthPowerSUnitSubgroup K S) H))

instance fintype_actualBoundedSIntegerOrbits (H : ℝ) :
    Fintype (ActualBoundedSIntegerOrbits K S H) := Fintype.ofFinite _

/-- The actual Mellin test family; compact subsets of s will be quantified
in the estimates below. Its support still comes from the same fixed W. -/
def dyadicMellinWeight (s : ℂ) (y : ℝ) : ℂ :=
  sexticDyadicWeight y * (y : ℂ) ^ (-s)

@[simp] theorem dyadicMellinWeight_zero_parameter :
    dyadicMellinWeight 0 = sexticDyadicWeight := by
  funext y
  simp [dyadicMellinWeight]

theorem dyadicMellinWeight_zero_of_ge (s : ℂ) {y : ℝ} (hy : 2 ≤ y) :
    dyadicMellinWeight s y = 0 := by
  simp [dyadicMellinWeight, sexticDyadicWeight, fixedDyadicWeight_zero_of_ge hy]

theorem dyadicMellinWeight_zero_of_le (s : ℂ) {y : ℝ} (hy : y ≤ 1 / 2) :
    dyadicMellinWeight s y = 0 := by
  simp [dyadicMellinWeight, sexticDyadicWeight, fixedDyadicWeight_zero_of_le hy]

/-- Fixed-S zero extension retains the proved literal subgroup invariance. -/
theorem zeroExtendedSexticIdealEvaluation_sixthSubgroup_invariant
    (I : NonzeroIdeal K) (γ : sixthPowerSUnitSubgroup K S) (a : S.integer K) :
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I
        ((S.unitEquivUnitsInteger K γ.val).val * a) =
      zeroExtendedSexticIdealEvaluation K S ζ hζ σ I a := by
  unfold zeroExtendedSexticIdealEvaluation
  split_ifs with hI
  · exact sIntegerSexticIdealEvaluation_literal_invariant K S ζ hζ σ I.val
      (nonZeroDivisors.coe_ne_zero I) (fun p hp => (hI p hp).1)
      (fun p hp => (hI p hp).2) (sixthPowerSUnitSubgroup K S) le_rfl γ a
  · rfl

theorem sIntegerInversePolynomial_sixthSubgroup_invariant
    (η : HeckeCharacter K) (γ : sixthPowerSUnitSubgroup K S)
    (a : S.integer K) (D : ℝ) (s : ℂ) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
        ((S.unitEquivUnitsInteger K γ.val).val * a) D (dyadicMellinWeight s) =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
        a D (dyadicMellinWeight s) := by
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  simp only [sIntegerSexticInverseIdealTerm,
    zeroExtendedSexticIdealEvaluation_sixthSubgroup_invariant K S ζ hζ σ I γ a]

/-- The inverse polynomial on actual nonzero S-integer orbits. -/
def actualSIntegerInversePolynomial (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (D : ℝ) (s : ℂ) : ℂ :=
  Quotient.liftOn q
    (fun a => sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
      (dyadicIdealSupport K D) a.val D (dyadicMellinWeight s)) (by
        intro a b hab
        obtain ⟨γ, hγ⟩ :=
          (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) a b).mp hab
        have heq : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val :=
          Subtype.ext hγ
        rw [← heq]
        exact sIntegerInversePolynomial_sixthSubgroup_invariant K S ζ hζ σ η γ b.val D s)

@[simp] theorem actualSIntegerInversePolynomial_mk
    (η : HeckeCharacter K) (a : NonzeroRingElements (S.integer K)) (D : ℝ) (s : ℂ) :
    actualSIntegerInversePolynomial K S ζ hζ σ η (Quotient.mk _ a) D s =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
        a.val D (dyadicMellinWeight s) := rfl

theorem actualSIntegerInversePolynomial_out
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (D : ℝ) (s : ℂ) :
    sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η (dyadicIdealSupport K D)
        q.out.val D (dyadicMellinWeight s) =
      actualSIntegerInversePolynomial K S ζ hζ σ η q D s := by
  simpa only [actualSIntegerInversePolynomial_mk] using
    congrArg (fun q => actualSIntegerInversePolynomial K S ζ hζ σ η q D s)
      (Quotient.out_eq q)

theorem actualSIntegerInversePolynomial_zero_parameter
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (D : ℝ) :
    actualSIntegerInversePolynomial K S ζ hζ σ η q D 0 =
      dyadicSexticInversePolynomial K S ζ hζ σ η q.out.val D := by
  rw [← actualSIntegerInversePolynomial_out, dyadicMellinWeight_zero_parameter]
  rfl

def actualZeroSlotEnergy (η : HeckeCharacter K) (H D : ℝ) (s : ℂ) : ℝ :=
  ∑ q : ActualBoundedSIntegerOrbits K S H,
    ‖actualSIntegerInversePolynomial K S ζ hζ σ η q.val D s‖ ^ 2

/-- Fixed-scale zero-slot MI on the specified actual rows and actual compact
Mellin test family. rho is the exponent in D=H^rho, not the independent
scale itself. Real geometry and losses precede the target eta. Uniform
constants over the compact set are asserted, not proved by seminorm theory. -/
def ActualZeroSlotMI (ω : HeckeCharacter K) : Prop :=
  ∀ ρ ε : ℝ, 0 < ρ → ρ < 1 → 0 < ε →
    ∀ T : Set ℂ, IsCompact T →
      ∀ η : HeckeCharacter K, η ∈ HeckePacket K ω →
        ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
          ∀ H : ℝ, H₀ ≤ H → ∀ s ∈ T,
            actualZeroSlotEnergy K S ζ hζ σ η H (H ^ ρ) s ≤ C * H ^ (1 + ε)

/-- OPTIONAL independent-scale supremum input, separate from fixed-scale MI.
For each H, B simultaneously majorizes every row square for ALL independent
scales 0<D<=H^(1-delta) and all s in the fixed compact set. The sum of these
majorants has the MI size. This explicitly supplies the needed supremum
control; no implication from MI or Q Lemma 4.5 is claimed. -/
def ActualZeroSlotScaleSupInput (ω : HeckeCharacter K) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
    ∀ T : Set ℂ, IsCompact T →
      ∀ η : HeckeCharacter K, η ∈ HeckePacket K ω →
        ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
          ∀ H : ℝ, H₀ ≤ H →
            ∃ B : ActualSIntegerOrbit K S → ℝ,
              (∀ q, 0 ≤ B q) ∧
              (∀ q, actualSIntegerOrbitNorm K S q ≤ H →
                ∀ D : ℝ, 0 < D → D ≤ H ^ (1 - δ) → ∀ s ∈ T,
                  ‖actualSIntegerInversePolynomial K S ζ hζ σ η q D s‖ ^ 2 ≤ B q) ∧
              (∑ q : ActualBoundedSIntegerOrbits K S H, B q.val) ≤ C * H ^ (1 + ε)

/-- Only the easy direction is proved: optional supremum control implies
the fixed-scale input. The difficult converse is not asserted. -/
theorem ActualZeroSlotScaleSupInput.to_MI (ω : HeckeCharacter K)
    (h : ActualZeroSlotScaleSupInput K S ζ hζ σ ω) :
    ActualZeroSlotMI K S ζ hζ σ ω := by
  intro ρ ε hρ hρ1 hε T hT η hη
  obtain ⟨C, H₀, hC, hH₀, hbound⟩ :=
    h (1 - ρ) ε (by linarith) (by linarith) hε T hT η hη
  refine ⟨C, H₀, hC, hH₀, ?_⟩
  intro H hH s hs
  obtain ⟨B, _hB, hrow, hsum⟩ := hbound H hH
  have hHpos : 0 < H := lt_of_lt_of_le (by linarith : (0 : ℝ) < H₀) hH
  have hscale : H ^ ρ ≤ H ^ (1 - (1 - ρ)) := by
    rw [show 1 - (1 - ρ) = ρ by ring]
  exact (Finset.sum_le_sum (fun q _ => hrow q.val q.property (H ^ ρ)
    (Real.rpow_pos_of_pos hHpos ρ) hscale s hs)).trans hsum

end HeckeGeneral.Analysis.ActualSIntegerMoments
