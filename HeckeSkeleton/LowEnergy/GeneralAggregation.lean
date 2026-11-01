import HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
import HeckeSkeleton.LowEnergy.ActualFrozenStateCount
import HeckeSkeleton.LowEnergy.InactiveCore

/-!
# All frozen states and all local classes in a general reflected block

The state set may select any genuine local charge ranges.  Its cardinality
is bounded by the proved count of the actual `FrozenState`, including its
frequency unit.  The common constant and the small sieve/counting losses
are selected before the completed scale, row/label/puncture data, annular
profile and all finite ideal supports.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralAggregation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualFrozenStateCount
open HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.GeneralReflectedBlock
open HeckeSkeleton.LowEnergy.GeneralMarkedEnergy
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Data of one genuine dual block after the local choices are regrouped.
There is no analytic assertion among the fields. -/
structure FrozenBlock where
  fixed : FixedData K S
  states : Finset (FrozenState K S fixed.frozen fixed.puncture)
  X : ℝ
  rowScale : ℝ
  markScale : ℝ
  squarefreeScale : ℝ
  cubeScale : ℝ
  rows : Finset (Ideal (𝓞 K))
  marks : Finset (Ideal (𝓞 K))
  squarefreeColumns : Finset (Ideal (𝓞 K))
  cubeColumns : Finset (Ideal (𝓞 K))
  markWeight : Ideal (𝓞 K) → ℂ

namespace FrozenBlock

variable {K S}

def toBlock (b : FrozenBlock K S) (s : FrozenState K S b.fixed.frozen b.fixed.puncture)
    (q : FourClasses (SixthLocalClasses K S)) : ReflectedBlock K S where
  fixed := b.fixed
  state := s
  classes := q
  X := b.X
  rowScale := b.rowScale
  markScale := b.markScale
  squarefreeScale := b.squarefreeScale
  cubeScale := b.cubeScale
  rows := b.rows
  marks := b.marks
  squarefreeColumns := b.squarefreeColumns
  cubeColumns := b.cubeColumns
  markWeight := b.markWeight

def row (b : FrozenBlock K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ s ∈ b.states, ∑' q : FourClasses (SixthLocalClasses K S),
    slicedBlock K S D b.fixed s F θ q b.markWeight V.toFun b.X
      b.marks b.squarefreeColumns b.cubeColumns k

def energy (b : FrozenBlock K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : SmoothAnnularTest) : ℝ :=
  ∑ k ∈ b.rows, ‖b.row D F θ V k‖ ^ 2

/-- Zero extension retains the exact row exclusions of each inactive
tuple when several such row vectors share an ambient row set. -/
def restrictedRow (b : FrozenBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (k : Ideal (𝓞 K)) : ℂ :=
  if k ∈ b.rows then b.row D F θ V k else 0

theorem restrictedRow_energy (b : FrozenBlock K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : SmoothAnnularTest) (rows : Finset (Ideal (𝓞 K)))
    (hrows : b.rows ⊆ rows) :
    (∑ k ∈ rows, ‖b.restrictedRow D F θ V k‖ ^ 2) = b.energy D F θ V := by
  have he := Finset.sum_subset hrows
    (f := fun k => ‖b.restrictedRow D F θ V k‖ ^ 2)
    (fun k _ hk => by simp only [restrictedRow, if_neg hk, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  rw [← he]
  unfold energy
  apply Finset.sum_congr rfl
  intro k hk
  simp only [restrictedRow, if_pos hk]

/-- Only arithmetic support, local length and scalar bounds occur here. -/
structure Admissible (b : FrozenBlock K S) (Z W A E Fmax : ℝ) : Prop where
  fixedNorm_bound : ((b.fixed.frozen.val * b.fixed.puncture.val).val.absNorm : ℝ) ≤ Z ^ Fmax
  block_admissible : ∀ s ∈ b.states, ∀ q, (b.toBlock s q).Admissible Z W A
  exponent_bound : ∀ s ∈ b.states, ∀ q, (b.toBlock s q).exponent Z ≤ E

end FrozenBlock

/-- All actual frozen states and all four local classes are included in
the row sum.  The charge exponent may be common on any selected state set. -/
theorem general_frozen_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z A E : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) (b : FrozenBlock K S), b.Admissible Z W A E Fmax →
      b.energy D F θ V ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (E + eps) := by
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  obtain ⟨Cb, hCb, hb⟩ := general_marked_block_family K S D F hF θ hKernel hθ hD
    hquadratic hcubic W (eps / 2) hW (by linarith)
  let rho := eps / (2 * (Fmax + 1))
  have hrho : 0 < rho := div_pos heps (by linarith)
  obtain ⟨Cs, hCs, hs⟩ := squared_frozenState_count_small_power K S rho hrho
  let Q : ℝ := Fintype.card (FourClasses (SixthLocalClasses K S))
  refine ⟨Cs * (Q ^ 2 + 1) * Cb, by positivity, ?_⟩
  intro Z A E hZ hA V b hadm
  letI : Fintype (FrozenState K S b.fixed.frozen b.fixed.puncture) := Fintype.ofFinite _
  let E0 := Cb * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
    ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (E + eps / 2)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hblock (s : FrozenState K S b.fixed.frozen b.fixed.puncture) (hs : s ∈ b.states)
      (q : FourClasses (SixthLocalClasses K S)) :
      (b.toBlock s q).energy D F θ V ≤ E0 := by
    have h := hb Z A hZ hA V (b.toBlock s q) (hadm.block_admissible s hs q)
    apply h.trans
    apply mul_le_mul_of_nonneg_left
    · exact Real.rpow_le_rpow_of_exponent_le hZ.le
        (add_le_add (hadm.exponent_bound s hs q) (le_refl (eps / 2)))
    · positivity
  let Classes := FourClasses (SixthLocalClasses K S)
  let v := fun (sc : FrozenState K S b.fixed.frozen b.fixed.puncture × Classes)
      (k : Ideal (𝓞 K)) =>
    slicedBlock K S D b.fixed sc.1 F θ sc.2 b.markWeight V.toFun b.X
      b.marks b.squarefreeColumns b.cubeColumns k
  have hfinite := InactiveCore.finite_weighted_energy_le
    (b.states ×ˢ (Finset.univ : Finset Classes)) b.rows (fun _ => (1 : ℂ)) v
    (fun sc hsc => hblock sc.1 (Finset.mem_product.mp hsc).1 sc.2)
  have hcomb : b.energy D F θ V ≤ (b.states.card : ℝ) ^ 2 * Q ^ 2 * E0 := by
    simpa only [FrozenBlock.energy, FrozenBlock.row, Finset.sum_product, v, Classes,
      tsum_fintype, one_mul, norm_one, Finset.sum_const, Finset.card_product,
      Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_mul, mul_pow, Q] using hfinite
  have hcards : (b.states.card : ℝ) ^ 2 ≤
      (Nat.card (FrozenState K S b.fixed.frozen b.fixed.puncture) : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Finset.card_le_univ b.states)
  have hfixed0 : 0 ≤ ((b.fixed.frozen.val * b.fixed.puncture.val).val.absNorm : ℝ) :=
    Nat.cast_nonneg _
  have hnorm := Real.rpow_le_rpow hfixed0 hadm.fixedNorm_bound hrho.le
  have hexp : Fmax * rho ≤ eps / 2 := by
    have he : rho * (2 * (Fmax + 1)) = eps := by
      dsimp [rho]
      exact div_mul_cancel₀ eps (by linarith)
    nlinarith
  have hpow : ((b.fixed.frozen.val * b.fixed.puncture.val).val.absNorm : ℝ) ^ rho ≤
      Z ^ (eps / 2) := by
    apply hnorm.trans
    rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  have hstates : (b.states.card : ℝ) ^ 2 ≤ Cs * Z ^ (eps / 2) :=
    hcards.trans ((hs b.fixed.frozen b.fixed.puncture).trans
      (mul_le_mul_of_nonneg_left hpow hCs.le))
  have hcard := mul_le_mul hstates (by nlinarith [sq_nonneg Q] : Q ^ 2 ≤ Q ^ 2 + 1)
    (sq_nonneg Q) (by positivity : 0 ≤ Cs * Z ^ (eps / 2))
  have h := mul_le_mul_of_nonneg_right hcard hE0
  apply hcomb.trans
  apply h.trans_eq
  have hpower : Z ^ (eps / 2) * Z ^ (E + eps / 2) = Z ^ (E + eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  dsimp [E0]
  calc
    _ = (Cs * (Q ^ 2 + 1) * Cb) * A ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S b.fixed‖ ^ 2 *
        (Z ^ (eps / 2) * Z ^ (E + eps / 2)) := by ring
    _ = _ := by rw [hpower]

/-- The O/2 loss is paid once for actual powerful ideals, after every
frozen state and local class in each block has already been summed. -/
theorem general_powerful_frozen_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax)
    (hOmax : 0 ≤ Omax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O A R0 E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 0 ≤ R0 →
      ∀ (V : SmoothAnnularTest) (R : Finset (IdealRankin.PowerfulIdeal K))
        (blocks : IdealRankin.PowerfulIdeal K → FrozenBlock K S),
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, (blocks I).Admissible Z W A E Fmax) →
      (∀ I ∈ R, ‖inactiveWeight K S (blocks I).fixed‖ ^ 2 ≤ R0) →
      (∑ I ∈ R, (blocks I).energy D F θ V) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          R0 * Z ^ (O / 2 + E + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := general_frozen_block_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax (eps / 2) hW hFmax (by linarith)
  obtain ⟨Cp, hCp, hp⟩ := powerful_count_at_scale K Omax (eps / 2) hOmax (by linarith)
  refine ⟨Cb * Cp, mul_pos hCb hCp, ?_⟩
  intro Z O A R0 E hZ hO hO' hA hR0 V R blocks hnorm hadm hweight
  let L := Cb * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlocal (I : IdealRankin.PowerfulIdeal K) (hI : I ∈ R) :
      (blocks I).energy D F θ V ≤ L * R0 * Z ^ (E + eps / 2) := by
    have h := hb Z A E hZ hA V (blocks I) (hadm I hI)
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hweight I hI) hL) (by positivity)
  calc
    _ ≤ ∑ _I ∈ R, L * R0 * Z ^ (E + eps / 2) := Finset.sum_le_sum hlocal
    _ = (R.card : ℝ) * (L * R0 * Z ^ (E + eps / 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cp * Z ^ (O / 2 + eps / 2)) * (L * R0 * Z ^ (E + eps / 2)) :=
      mul_le_mul_of_nonneg_right (hp Z O hZ hO hO' R hnorm) (by positivity)
    _ = _ := by
      have hpow : Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2) =
          Z ^ (O / 2 + E + eps) := by
        rw [← Real.rpow_add (zero_lt_one.trans hZ)]
        congr 1
        ring
      dsimp [L]
      calc
        _ = (Cb * Cp) * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
            R0 * (Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2)) := by ring
        _ = _ := by rw [hpow]

/-- Every supported valuation-one part and every row-unit class is
included.  The supported ideal is the squarefree product of its literal
subset of the label/puncture support, so its count is a proved small
power of their norm.  No supported row fibre is discarded. -/
theorem general_powerful_supported_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax Lmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax)
    (hOmax : 0 ≤ Omax) (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O A R0 E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 0 ≤ R0 →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (blocks : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → FrozenBlock K S),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (fixedSupport K S label puncture).powerset, ∀ u,
        (blocks I T u).Admissible Z W A E Fmax) →
      (∀ I ∈ R, ∀ T ∈ (fixedSupport K S label puncture).powerset, ∀ u,
        ‖inactiveWeight K S (blocks I T u).fixed‖ ^ 2 ≤ R0) →
      (∑ I ∈ R, ∑ T ∈ (fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (blocks I T u).energy D F θ V) ≤
        C * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          R0 * Z ^ (O / 2 + E + eps) := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  obtain ⟨Cb, hCb, hb⟩ := general_powerful_frozen_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic W Fmax Omax (eps / 2) hW hFmax hOmax (by linarith)
  let rho := eps / (2 * (Lmax + 1))
  have hrho : 0 < rho := div_pos heps (by linarith)
  obtain ⟨Cs, hCs, hs⟩ := IdealSupportPowers.prime_support_states_small_power
    K 2 rho (by norm_num) hrho
  let U : ℝ := Fintype.card (SixthUnitClasses K S)
  have hU : 0 ≤ U := Nat.cast_nonneg _
  have hCs0 : 0 < Cs := zero_lt_one.trans_le hCs
  refine ⟨Cs * (U + 1) * Cb, by positivity, ?_⟩
  intro Z O A R0 E hZ hO hO' hA hR0 V label puncture R blocks hnorm hR hadm hweight
  let Support := fixedSupport K S label puncture
  let E0 := Cb * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
    R0 * Z ^ (O / 2 + E + eps / 2)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hpart (T : Finset (ExteriorPrime K S)) (hT : T ∈ Support.powerset)
      (u : SixthUnitClasses K S) :
      (∑ I ∈ R, (blocks I T u).energy D F θ V) ≤ E0 :=
    hb Z O A R0 E hZ hO hO' hA hR0 V R (fun I => blocks I T u) hR
      (fun I hI => hadm I hI T hT u) (fun I hI => hweight I hI T hT u)
  have hcomb :
      (∑ I ∈ R, ∑ T ∈ Support.powerset,
        ∑' u : SixthUnitClasses K S, (blocks I T u).energy D F θ V) ≤
      (Support.powerset.card : ℝ) * U * E0 := by
    simp_rw [tsum_fintype]
    rw [Finset.sum_comm]
    calc
      _ = ∑ T ∈ Support.powerset, ∑ u : SixthUnitClasses K S,
          ∑ I ∈ R, (blocks I T u).energy D F θ V := by
        apply Finset.sum_congr rfl
        intro T _
        rw [Finset.sum_comm]
      _ ≤ ∑ T ∈ Support.powerset, ∑ _u : SixthUnitClasses K S, E0 := by
        apply Finset.sum_le_sum
        intro T hT
        exact Finset.sum_le_sum (fun u _ => hpart T hT u)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, U]; ring
  have hcard : (Support.powerset.card : ℝ) =
      (2 : ℝ) ^ (primeExponents (label.val * puncture.val)).support.card := by
    simp only [Support, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat,
      fixedSupport_card]
  have hexp : Lmax * rho ≤ eps / 2 := by
    have he : rho * (2 * (Lmax + 1)) = eps := by
      dsimp [rho]
      exact div_mul_cancel₀ eps (by linarith)
    nlinarith
  have hnormpow : ((label.val * puncture.val).val.absNorm : ℝ) ^ rho ≤ Z ^ (eps / 2) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hrho.le).trans
    rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  have hcount : (Support.powerset.card : ℝ) ≤ Cs * Z ^ (eps / 2) := by
    rw [hcard]
    exact (hs (label.val * puncture.val)).trans
      (mul_le_mul_of_nonneg_left hnormpow hCs0.le)
  have hmass : (Support.powerset.card : ℝ) * U ≤
      Cs * Z ^ (eps / 2) * (U + 1) :=
    mul_le_mul hcount (by linarith) hU (by positivity)
  apply hcomb.trans
  apply (mul_le_mul_of_nonneg_right hmass hE0).trans_eq
  have hpower : Z ^ (eps / 2) * Z ^ (O / 2 + E + eps / 2) =
      Z ^ (O / 2 + E + eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  dsimp [E0]
  calc
    _ = (Cs * (U + 1) * Cb) * A ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * R0 *
        (Z ^ (eps / 2) * Z ^ (O / 2 + E + eps / 2)) := by ring
    _ = _ := by rw [hpower]

/-- The number of actual outer row fibres, including all supported
valuation-one parts and all row-unit classes. -/
theorem powerful_supported_count (Omax Lmax eps : ℝ)
    (hOmax : 0 ≤ Omax) (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O : ℝ), 1 < Z → 0 ≤ O → O ≤ Omax →
      ∀ (label puncture : ExteriorIdeal K S) (R : Finset (IdealRankin.PowerfulIdeal K)),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (R.card : ℝ) * ((fixedSupport K S label puncture).powerset.card : ℝ) *
        (Nat.card (SixthUnitClasses K S) : ℝ) ≤ C * Z ^ (O / 2 + eps) := by
  obtain ⟨Cp, hCp, hp⟩ := powerful_count_at_scale K Omax (eps / 2) hOmax (by linarith)
  let rho := eps / (2 * (Lmax + 1))
  have hrho : 0 < rho := div_pos heps (by linarith)
  obtain ⟨Cs, hCs, hs⟩ := IdealSupportPowers.prime_support_states_small_power
    K 2 rho (by norm_num) hrho
  let U : ℝ := Nat.card (SixthUnitClasses K S)
  have hU : 0 ≤ U := Nat.cast_nonneg _
  have hCs0 : 0 < Cs := zero_lt_one.trans_le hCs
  refine ⟨Cp * Cs * (U + 1), by positivity, ?_⟩
  intro Z O hZ hO hO' label puncture R hnorm hR
  have hcard : ((fixedSupport K S label puncture).powerset.card : ℝ) =
      (2 : ℝ) ^ (primeExponents (label.val * puncture.val)).support.card := by
    simp only [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat, fixedSupport_card]
  have hexp : Lmax * rho ≤ eps / 2 := by
    have he : rho * (2 * (Lmax + 1)) = eps := by
      dsimp [rho]
      exact div_mul_cancel₀ eps (by linarith)
    nlinarith
  have hnormpow : ((label.val * puncture.val).val.absNorm : ℝ) ^ rho ≤ Z ^ (eps / 2) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hrho.le).trans
    rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hexp
  have hsupport : ((fixedSupport K S label puncture).powerset.card : ℝ) ≤
      Cs * Z ^ (eps / 2) := by
    rw [hcard]
    exact (hs (label.val * puncture.val)).trans
      (mul_le_mul_of_nonneg_left hnormpow hCs0.le)
  have hcounts := mul_le_mul (hp Z O hZ hO hO' R hR) hsupport
    (Nat.cast_nonneg _) (by positivity : 0 ≤ Cp * Z ^ (O / 2 + eps / 2))
  have htotal := mul_le_mul hcounts (show U ≤ U + 1 by linarith) hU (by positivity)
  apply htotal.trans_eq
  have hpow : Z ^ (O / 2 + eps / 2) * Z ^ (eps / 2) = Z ^ (O / 2 + eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  calc
    _ = (Cp * Cs * (U + 1)) * (Z ^ (O / 2 + eps / 2) * Z ^ (eps / 2)) := by ring
    _ = _ := by rw [hpow]

#print axioms general_frozen_block_energy
#print axioms general_powerful_frozen_energy
#print axioms general_powerful_supported_energy
#print axioms powerful_supported_count

end HeckeSkeleton.LowEnergy.GeneralAggregation
