import HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
import HeckeSkeleton.LowEnergy.GeneralHeight

/-!
# Uniform canonical energy for finite characters and norm twists

The one constant is chosen before the finite-order child and its real
norm-twist parameter.  The proved common-profile polynomial height is
carried through each actual row sum, without replacing it by an arbitrary
constant depending on the child.  All tuple and arithmetic support
conditions are the same as in the general source-block theorem.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralUniformEnergy

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
open HeckeSkeleton.LowEnergy.GeneralAggregation
open HeckeSkeleton.LowEnergy.GeneralInactiveEnergy
open HeckeSkeleton.LowEnergy.GeneralCanonicalBlock
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def heightFactor (t : ℝ) : ℝ := (1 + |t|) ^ (18 * ThetaKernel.ncx K)

theorem heightFactor_pos (t : ℝ) : 0 < heightFactor K t := by
  unfold heightFactor
  positivity

theorem uniform_frozen_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z A E : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) (b : FrozenBlock K S), b.Admissible Z W A E Fmax →
      b.energy D F (ν * θ₀ * heckeNormTwist K t) V ≤
        C * heightFactor K t * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (E + eps) := by
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  obtain ⟨Cb, hCb, hb⟩ := GeneralMarkedEnergy.general_marked_block_family_height K S D F hF θ₀ hD
    hquadratic hcubic W (eps / 2) hW (by linarith)
  let rho := eps / (2 * (Fmax + 1))
  have hrho : 0 < rho := div_pos heps (by linarith)
  obtain ⟨Cs, hCs, hs⟩ := squared_frozenState_count_small_power K S rho hrho
  let Q : ℝ := Fintype.card (FourClasses (SixthLocalClasses K S))
  refine ⟨Cs * (Q ^ 2 + 1) * Cb, by positivity, ?_⟩
  intro ν hν t hKernel hθ Z A E hZ hA V b hadm
  let θ := ν * θ₀ * heckeNormTwist K t
  have hheight := heightFactor_pos K t
  letI : Fintype (FrozenState K S b.fixed.frozen b.fixed.puncture) := Fintype.ofFinite _
  let E0 := Cb * heightFactor K t * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
    ‖inactiveWeight K S b.fixed‖ ^ 2 * Z ^ (E + eps / 2)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hblock (s : FrozenState K S b.fixed.frozen b.fixed.puncture) (hs : s ∈ b.states)
      (q : FourClasses (SixthLocalClasses K S)) :
      (b.toBlock s q).energy D F θ V ≤ E0 := by
    have h := hb ν hν t hKernel hθ Z A hZ hA V (b.toBlock s q) (hadm.block_admissible s hs q)
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
    _ = (Cs * (Q ^ 2 + 1) * Cb) * heightFactor K t * A ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S b.fixed‖ ^ 2 *
        (Z ^ (eps / 2) * Z ^ (E + eps / 2)) := by ring
    _ = _ := by rw [hpower]

theorem uniform_frozen_weighted_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax eps : ℝ) (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z A E : ℝ), 1 < Z → 0 < A →
      ∀ (V : SmoothAnnularTest) {ι : Type*} (I : Finset ι)
        (blocks : ι → FrozenBlock K S) (a : ι → ℂ) (rows : Finset (Ideal (𝓞 K))),
      (∀ i ∈ I, (blocks i).Admissible Z W A E Fmax) →
      (∀ i ∈ I, (blocks i).rows ⊆ rows) →
      (∑ k ∈ rows, ‖∑ i ∈ I, a i * (blocks i).restrictedRow D F (ν * θ₀ * heckeNormTwist K t) V k‖ ^ 2) ≤
        C * heightFactor K t * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          (∑ i ∈ I, ‖a i * inactiveWeight K S (blocks i).fixed‖) ^ 2 * Z ^ (E + eps) := by
  obtain ⟨C, hC, hb⟩ := uniform_frozen_block_energy K S D F hF θ₀ hD
    hquadratic hcubic W Fmax eps hW hFmax heps
  refine ⟨C, hC, ?_⟩
  intro ν hν t hKernel hθ Z A E hZ hA V ι I blocks a rows hadm hrows
  let θ := ν * θ₀ * heckeNormTwist K t
  have hheight := heightFactor_pos K t
  let L := C * heightFactor K t * A ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2
  let E0 := L * Z ^ (E + eps)
  let v := fun i k => (inactiveWeight K S (blocks i).fixed)⁻¹ *
    (blocks i).restrictedRow D F θ V k
  have hinner (i : ι) (hi : i ∈ I) : (∑ k ∈ rows, ‖v i k‖ ^ 2) ≤ E0 := by
    have hblock := hb ν hν t hKernel hθ Z A E hZ hA V (blocks i) (hadm i hi)
    have hcancel : ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
        ‖inactiveWeight K S (blocks i).fixed‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, inv_mul_cancel₀ (inactiveWeight_ne_zero K S _),
        norm_one, one_pow]
    calc
      _ = ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 * (blocks i).energy D F θ V := by
        simp only [v, norm_mul, mul_pow, ← Finset.mul_sum]
        rw [FrozenBlock.restrictedRow_energy D (blocks i) F θ V rows (hrows i hi)]
      _ ≤ ‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
          (L * ‖inactiveWeight K S (blocks i).fixed‖ ^ 2 * Z ^ (E + eps)) :=
        mul_le_mul_of_nonneg_left hblock (sq_nonneg _)
      _ = L * (‖(inactiveWeight K S (blocks i).fixed)⁻¹‖ ^ 2 *
          ‖inactiveWeight K S (blocks i).fixed‖ ^ 2) * Z ^ (E + eps) := by ring
      _ = E0 := by rw [hcancel, mul_one]
  have hfinite := InactiveCore.finite_weighted_energy_le I rows
    (fun i => a i * inactiveWeight K S (blocks i).fixed) v hinner
  have hrow (k : Ideal (𝓞 K)) :
      (∑ i ∈ I, (a i * inactiveWeight K S (blocks i).fixed) * v i k) =
      ∑ i ∈ I, a i * (blocks i).restrictedRow D F θ V k := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [v]
    calc
      _ = a i * (inactiveWeight K S (blocks i).fixed *
          (inactiveWeight K S (blocks i).fixed)⁻¹) * (blocks i).restrictedRow D F θ V k := by ring
      _ = _ := by rw [mul_inv_cancel₀ (inactiveWeight_ne_zero K S _), mul_one]
  simp_rw [hrow] at hfinite
  apply hfinite.trans_eq
  dsimp [E0, L]
  ring

theorem uniform_inactive_block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z A B E : ℝ), 1 < Z → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (b : InactiveFamily K S),
      b.Admissible Z W A B E Fmax rmax →
      b.energy D F (ν * θ₀ * heckeNormTwist K t) V ≤
        C * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := uniform_frozen_weighted_energy K S D F hF θ₀ hD
    hquadratic hcubic W Fmax eps hW hFmax heps
  obtain ⟨M, hM, hm⟩ := GeneralInactiveMass.exists_uniform_contracted_mass_constant K rmax
  refine ⟨Cb * M ^ 2, mul_pos hCb (sq_pos_of_pos (zero_lt_one.trans_le hM)), ?_⟩
  intro ν hν t hKernel hθ Z A B E hZ hA hB V b hadm
  let θ := ν * θ₀ * heckeNormTwist K t
  have hheight := heightFactor_pos K t
  have he := hb ν hν t hKernel hθ Z A E hZ hA V b.tuples b.blocks b.coefficient b.rows
    hadm.block_admissible hadm.row_subset
  have hslots : Fintype.card (Fin b.slots) ≤ rmax := by
    simpa only [Fintype.card_fin] using hadm.slots_le
  have hmass0 := hm S hslots b.windows b.scales hadm.scale_ge hadm.window_norm B hB
    b.slotCoefficient hadm.coefficient_bound b.tuples hadm.tuple_subset b.phase hadm.phase_bound
  have heq : (∑ p ∈ b.tuples, ‖b.coefficient p * inactiveWeight K S (b.blocks p).fixed‖) =
      ∑ p ∈ b.tuples,
        ‖GeneralInactiveMass.inactiveCoefficient K S b.slotCoefficient p * b.phase p‖ := by
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    unfold InactiveFamily.coefficient GeneralInactiveMass.inactiveCoefficient
      GeneralInactiveMass.distinctPrefactor GeneralInactiveMass.tupleSupport inactiveWeight
    rw [hadm.inactive_eq p hp]
    ring
  have hmass : (∑ p ∈ b.tuples, ‖b.coefficient p * inactiveWeight K S (b.blocks p).fixed‖) ≤
      M * B ^ rmax := by rw [heq]; exact hmass0
  have hmass2 := pow_le_pow_left₀
    (Finset.sum_nonneg (fun p _ => norm_nonneg _)) hmass 2
  apply he.trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass2
      (by positivity : 0 ≤ Cb * heightFactor K t * A ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2))
    (by positivity : 0 ≤ Z ^ (E + eps))
  apply h.trans_eq
  rw [mul_pow]
  ring

theorem uniform_marked_family_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z A B E : ℝ), 1 < Z → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (b : MarkedFamily K S rmax),
      b.Admissible Z W A B E Fmax →
      b.energy D F (ν * θ₀ * heckeNormTwist K t) V ≤
        C * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps) := by
  obtain ⟨Cb, hCb, hb⟩ := uniform_inactive_block_energy K S D F hF θ₀ hD
    hquadratic hcubic W Fmax rmax eps hW hFmax heps
  refine ⟨(2 ^ rmax : ℝ) ^ 2 * Cb, by positivity, ?_⟩
  intro ν hν t hKernel hθ Z A B E hZ hA hB V b hadm
  let θ := ν * θ₀ * heckeNormTwist K t
  have hheight := heightFactor_pos K t
  let E0 := Cb * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
    testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hpart (a : Finset (Fin rmax)) (ha : a ∈ b.patterns) :
      (∑ k ∈ b.rows, ‖(b.components a).restrictedRow D F θ V k‖ ^ 2) ≤ E0 := by
    rw [InactiveFamily.restrictedRow_energy D (b.components a) F θ V b.rows
      (hadm.row_subset a ha)]
    exact hb ν hν t hKernel hθ Z A B E hZ hA hB V (b.components a) (hadm.component_admissible a ha)
  have hfinite := InactiveCore.finite_weighted_energy_le b.patterns b.rows (fun _ => (1 : ℂ))
    (fun a k => (b.components a).restrictedRow D F θ V k) hpart
  have hcomb : b.energy D F θ V ≤ (b.patterns.card : ℝ) ^ 2 * E0 := by
    simpa only [MarkedFamily.energy, MarkedFamily.row, one_mul, norm_one,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hfinite
  have hcard : (b.patterns.card : ℝ) ≤ (2 ^ rmax : ℝ) := by
    have h := Finset.card_le_univ b.patterns
    simp only [Fintype.card_finset, Fintype.card_fin] at h
    exact_mod_cast h
  have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  apply hcomb.trans
  apply (mul_le_mul_of_nonneg_right hcard2 hE0).trans_eq
  dsimp [E0]
  ring

theorem uniform_complete_family_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (hOmax : 0 ≤ Omax)
    (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z O A B E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (families : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → MarkedFamily K S rmax),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, (families I T u).Admissible Z W A B E Fmax) →
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F (ν * θ₀ * heckeNormTwist K t) V) ≤
        C * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          Z ^ (O / 2 + E + eps) := by
  letI : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  obtain ⟨Cb, hCb, hb⟩ := uniform_marked_family_energy K S D F hF θ₀ hD
    hquadratic hcubic W Fmax rmax (eps / 2) hW hFmax (by linarith)
  obtain ⟨Cp, hCp, hc⟩ := powerful_supported_count K S Omax Lmax (eps / 2)
    hOmax hLmax (by linarith)
  refine ⟨Cb * Cp, mul_pos hCb hCp, ?_⟩
  intro ν hν t hKernel hθ Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm
  let θ := ν * θ₀ * heckeNormTwist K t
  have hheight := heightFactor_pos K t
  let E0 := Cb * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
    testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 * Z ^ (E + eps / 2)
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have hlocal (I : IdealRankin.PowerfulIdeal K) (hI : I ∈ R)
      (T : Finset (ExteriorPrime K S))
      (hT : T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset)
      (u : SixthUnitClasses K S) : (families I T u).energy D F θ V ≤ E0 :=
    hb ν hν t hKernel hθ Z A B E hZ hA hB V (families I T u) (hadm I hI T hT u)
  have hcomb :
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F θ V) ≤
      ((R.card : ℝ) * ((ActualFrozenStateCount.fixedSupport K S label puncture).powerset.card : ℝ) *
        (Nat.card (SixthUnitClasses K S) : ℝ)) * E0 := by
    simp_rw [tsum_fintype]
    calc
      _ ≤ ∑ _I ∈ R, ∑ _T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
          ∑ _u : SixthUnitClasses K S, E0 := by
        apply Finset.sum_le_sum
        intro I hI
        apply Finset.sum_le_sum
        intro T hT
        exact Finset.sum_le_sum (fun u _ => hlocal I hI T hT u)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
        ring
  apply hcomb.trans
  apply (mul_le_mul_of_nonneg_right (hc Z O hZ hO hO' label puncture R hnorm hR) hE0).trans_eq
  have hpow : Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2) = Z ^ (O / 2 + E + eps) := by
    rw [← Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    ring
  dsimp [E0]
  calc
    _ = (Cb * Cp) * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
        testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        (Z ^ (O / 2 + eps / 2) * Z ^ (E + eps / 2)) := by ring
    _ = _ := by rw [hpow]

theorem canonical_complete_family_energy_height [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ₀ : HeckeCharacter K)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (W Fmax Omax Lmax : ℝ) (rmax : ℕ) (eps : ℝ)
    (hW : 0 ≤ W) (hFmax : 0 ≤ Fmax) (hOmax : 0 ≤ Omax)
    (hLmax : 0 ≤ Lmax) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : HeckeCharacter K), FiniteOrder ν →
      ∀ (t : ℝ), MellinKernelInput K S F (ν * θ₀ * heckeNormTwist K t) →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ S →
        UnramifiedAt K (ν * θ₀ * heckeNormTwist K t) p) → ∀ (Z O A B E : ℝ),
      1 < Z → 0 ≤ O → O ≤ Omax → 0 < A → 1 ≤ B →
      ∀ (V : SmoothAnnularTest) (label puncture : ExteriorIdeal K S)
        (R : Finset (IdealRankin.PowerfulIdeal K))
        (families : IdealRankin.PowerfulIdeal K → Finset (ExteriorPrime K S) →
          SixthUnitClasses K S → MarkedFamily K S rmax),
      ((label.val * puncture.val).val.absNorm : ℝ) ≤ Z ^ Lmax →
      (∀ I ∈ R, IdealRankin.powerfulNorm K I ≤ Z ^ O) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, (families I T u).Admissible Z W A B E Fmax) →
      (∀ I ∈ R, ∀ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∀ u, FamilySourceSupported K S (families I T u)) →
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (families I T u) F (ν * θ₀ * heckeNormTwist K t) V) ≤
        C * heightFactor K t * A ^ 2 * (B ^ rmax) ^ 2 *
          testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
          Z ^ (O / 2 + E + eps) := by
  obtain ⟨C, hC, hb⟩ := uniform_complete_family_energy K S D F hF θ₀ hD
    hquadratic hcubic W Fmax Omax Lmax rmax eps hW hFmax hOmax hLmax heps
  refine ⟨C, hC, ?_⟩
  intro ν hν t hKernel hθ Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm hsource
  let θ := ν * θ₀ * heckeNormTwist K t
  have he :
      (∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, sourceMarkedEnergy K S D (families I T u) F θ V) =
      ∑ I ∈ R, ∑ T ∈ (ActualFrozenStateCount.fixedSupport K S label puncture).powerset,
        ∑' u : SixthUnitClasses K S, (families I T u).energy D F θ V := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro T hT
    apply tsum_congr
    intro u
    exact sourceMarkedEnergy_eq K S D hD (families I T u) (hsource I hI T hT u) F θ V
  rw [he]
  exact hb ν hν t hKernel hθ Z O A B E hZ hO hO' hA hB V label puncture R families hnorm hR hadm

#print axioms canonical_complete_family_energy_height
#print axioms uniform_frozen_block_energy
#print axioms uniform_frozen_weighted_energy
#print axioms uniform_inactive_block_energy
#print axioms uniform_marked_family_energy
#print axioms uniform_complete_family_energy

end HeckeSkeleton.LowEnergy.GeneralUniformEnergy
