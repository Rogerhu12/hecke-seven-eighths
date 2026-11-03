import HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy
import HeckeSkeleton.LowEnergy.ActualFrozenStateCount
import HeckeSkeleton.LowEnergy.InactiveCore

/-!
# All actual frozen states and local class slices

The inactive reciprocal norm is extracted as a scalar; its norm remains in
the physical kernel argument.  This makes the subsequent inactive-tuple
sum an L1 weighted sum.  The actual finite frozen-state count is absorbed
by an arbitrary small power of the powerful ideal norm.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualFrozenAggregation

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy
open HeckeSkeleton.LowEnergy.ActualFrozenStateCount
open HeckeSkeleton.LowEnergy.ClassSlices
open scoped Classical BigOperators NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem inactiveWeight_ne_zero (f : FixedData K S) : inactiveWeight K S f ≠ 0 := by
  unfold inactiveWeight
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hN : p.val.asIdeal.absNorm ≠ 0 :=
    (Ideal.absNorm_pos_of_nonZeroDivisors (exteriorPrimeIdeal K S p).val).ne'
  exact inv_ne_zero (Nat.cast_ne_zero.mpr hN)

def reducedAnnularDualRow (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (classes : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (i : GaussianEnergyAssembly.Index) (k : Ideal (𝓞 K)) : ℂ :=
  (inactiveWeight K S f)⁻¹ * annularDualRow K S D f s F θ classes a Z ps i k

theorem annularDualRow_eq_inactive_mul (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (classes : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (i : GaussianEnergyAssembly.Index) (k : Ideal (𝓞 K)) :
    annularDualRow K S D f s F θ classes a Z ps i k =
      inactiveWeight K S f * reducedAnnularDualRow K S D f s F θ classes a Z ps i k := by
  rw [reducedAnnularDualRow, ← mul_assoc, mul_inv_cancel₀ (inactiveWeight_ne_zero K S f), one_mul]

def frozenReflectedRow (f : FixedData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (k : Ideal (𝓞 K)) : ℂ :=
  ∑' s : FrozenState K S f.frozen f.puncture,
    ∑' classes : FourClasses (SixthLocalClasses K S),
      ∑' i, reducedAnnularDualRow K S D f s F θ classes a Z ps i k

theorem reducedAnnularDualRow_zero_of_markWeight (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (classes : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (i : GaussianEnergyAssembly.Index) (k : Ideal (𝓞 K))
    (ha : ∀ P ∈ ps, a P = 0) :
    reducedAnnularDualRow K S D f s F θ classes a Z ps i k = 0 := by
  unfold reducedAnnularDualRow annularDualRow
  rw [slicedPhysicalBlock_zero_of_markWeight K S D f s F θ classes a _ _ _ _ _ _ ha,
    mul_zero]

theorem frozenReflectedRow_zero_of_markWeight (f : FixedData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (Z : ℝ) (ps : Finset (Ideal (𝓞 K)))
    (k : Ideal (𝓞 K)) (ha : ∀ P ∈ ps, a P = 0) :
    frozenReflectedRow K S D f F θ a Z ps k = 0 := by
  have hzero (s : FrozenState K S f.frozen f.puncture)
      (classes : FourClasses (SixthLocalClasses K S)) (i : GaussianEnergyAssembly.Index) :
      reducedAnnularDualRow K S D f s F θ classes a Z ps i k = 0 :=
    reducedAnnularDualRow_zero_of_markWeight K S D f s F θ classes a Z ps i k ha
  simp only [frozenReflectedRow, hzero, tsum_zero]

theorem actual_reduced_annuli_dual_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta eps C0 : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1)
    (heps : 0 < eps) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (classes : FourClasses (SixthLocalClasses K S)) (Z Klo Plo q d Ccut Cwin : ℝ),
      1 < Z → 1 ≤ Klo → 1 ≤ Plo → 0 < q → 0 < Ccut → 0 < Cwin →
      0 ≤ d → d ≤ (1 / 6 : ℝ) →
      IdealRows.Powerful f.frozen.val → f.puncture = primeSetIdeal K S ∅ →
      Z ^ d ≤ q →
      exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤ Cwin * Z ^ ((1 / 6 : ℝ) - d) →
      Real.log Ccut ≤ C0 → Real.log Cwin ≤ C0 →
      ∀ rows ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      ∀ (a : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A → (∀ P ∈ ps, ‖a P‖ ≤ A) →
      (∀ k ∈ rows, Summable (fun i => reducedAnnularDualRow K S D f s F θ classes a Z ps i k)) ∧
      (∑ k ∈ rows, ‖∑' i, reducedAnnularDualRow K S D f s F θ classes a Z ps i k‖ ^ 2) ≤
        C * A ^ 2 * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps) := by
  obtain ⟨C, hC, hbound⟩ := actual_all_annuli_dual_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta eps C0 hdelta hdelta' heps hC0
  refine ⟨C, hC, ?_⟩
  intro f s classes Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin hd hd' hf hpunc
    hselected hrow hwindow hlogCut hlogWin rows ps hrows hps hkr hpr a A hA ha
  obtain ⟨hpoint, he⟩ := hbound f s classes Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin
    hd hd' hf hpunc hselected hrow hwindow hlogCut hlogWin rows ps hrows hps hkr hpr a A hA ha
  refine ⟨fun k hk => (hpoint k hk).mul_left _, ?_⟩
  have hw : ‖(inactiveWeight K S f)⁻¹‖ ^ 2 * ‖inactiveWeight K S f‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, inv_mul_cancel₀ (inactiveWeight_ne_zero K S f), norm_one, one_pow]
  simp only [reducedAnnularDualRow, tsum_mul_left, norm_mul, mul_pow, ← Finset.mul_sum]
  calc
    _ ≤ ‖(inactiveWeight K S f)⁻¹‖ ^ 2 *
        (C * A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps)) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = C * A ^ 2 * (‖(inactiveWeight K S f)⁻¹‖ ^ 2 * ‖inactiveWeight K S f‖ ^ 2) *
        exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps) := by ring
    _ = _ := by rw [hw, mul_one]

/-- All frequency classes and actual frozen states are included.  Their
squared cardinality is paid by the proved small-power state count.  The
energy constant is uniform in the inactive tuple; that tuple enters only
the physical kernel scale and its displayed window inequality. -/
theorem actual_frozen_row_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (delta eps C0 rho : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1)
    (heps : 0 < eps) (hC0 : 0 ≤ C0) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (Z Klo Plo q d Ccut Cwin : ℝ),
      1 < Z → 1 ≤ Klo → 1 ≤ Plo → 0 < q → 0 < Ccut → 0 < Cwin →
      0 ≤ d → d ≤ (1 / 6 : ℝ) →
      IdealRows.Powerful f.frozen.val → f.puncture = primeSetIdeal K S ∅ →
      Z ^ d ≤ q →
      exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2 →
      exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤ Cwin * Z ^ ((1 / 6 : ℝ) - d) →
      Real.log Ccut ≤ C0 → Real.log Cwin ≤ C0 →
      ∀ rows ps : Finset (Ideal (𝓞 K)),
      (∀ k ∈ rows, IsExterior K S k ∧ Squarefree k ∧ (k.absNorm : ℝ) ≤ 2 * Klo) →
      (∀ P ∈ ps, IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo) →
      (∀ k ∈ rows, 1 ≤ safeNorm k / Klo ∧ safeNorm k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2) →
      ∀ (a : Ideal (𝓞 K) → ℂ) (A : ℝ), 0 < A → (∀ P ∈ ps, ‖a P‖ ≤ A) →
      (∀ s : FrozenState K S f.frozen f.puncture, ∀ classes : FourClasses (SixthLocalClasses K S),
        ∀ k ∈ rows, Summable (fun i => reducedAnnularDualRow K S D f s F θ classes a Z ps i k)) ∧
      (∑ k ∈ rows, ‖frozenReflectedRow K S D f F θ a Z ps k‖ ^ 2) ≤
        C * A ^ 2 * exteriorNorm K S f.frozen ^ (-(1 / 2 : ℝ) + rho) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps) := by
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  obtain ⟨Ce, hCe, henergy⟩ := actual_reduced_annuli_dual_energy K S D F hF θ hKernel hθ hD
    hquadratic hcubic delta eps C0 hdelta hdelta' heps hC0
  obtain ⟨Cs, hCs, hstates⟩ := squared_frozenState_count_small_power K S rho hrho
  let Q : ℝ := Fintype.card (FourClasses (SixthLocalClasses K S))
  refine ⟨Cs * (Q ^ 2 + 1) * Ce, by dsimp [Q]; positivity, ?_⟩
  intro f Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin hd hd' hf hpunc
    hselected hrow hwindow hlogCut hlogWin rows ps hrows hps hkr hpr a A hA ha
  letI : Fintype (FrozenState K S f.frozen f.puncture) := Fintype.ofFinite _
  let E : ℝ := Ce * A ^ 2 * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) *
    Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hCe.le (sq_nonneg A))
        (Real.rpow_nonneg (exteriorNorm_pos K S f.frozen).le _))
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hs (s : FrozenState K S f.frozen f.puncture)
      (classes : FourClasses (SixthLocalClasses K S)) :=
    henergy f s classes Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin hd hd' hf hpunc
      hselected hrow hwindow hlogCut hlogWin rows ps hrows hps hkr hpr a A hA ha
  refine ⟨fun s classes => (hs s classes).1, ?_⟩
  let States := FrozenState K S f.frozen f.puncture
  let Classes := FourClasses (SixthLocalClasses K S)
  let row : States × Classes → Ideal (𝓞 K) → ℂ := fun sc k =>
    ∑' i, reducedAnnularDualRow K S D f sc.1 F θ sc.2 a Z ps i k
  have hfinite := InactiveCore.finite_weighted_energy_le
    (Finset.univ : Finset (States × Classes)) rows (fun _ => (1 : ℂ)) row
    (fun sc _ => (hs sc.1 sc.2).2)
  have hcomb : (∑ k ∈ rows, ‖frozenReflectedRow K S D f F θ a Z ps k‖ ^ 2) ≤
      (Fintype.card States : ℝ) ^ 2 * Q ^ 2 * E := by
    simpa only [Classes, row, frozenReflectedRow, tsum_fintype, one_mul, Fintype.sum_prod_type,
      norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_prod, Nat.cast_mul, mul_pow, Q, E] using hfinite
  have hnorm : (((f.frozen.val * f.puncture.val).val.absNorm : ℝ)) = exteriorNorm K S f.frozen := by
    change (((f.frozen.val.val * f.puncture.val.val).absNorm : ℕ) : ℝ) = _
    have hp : f.puncture.val.val = (1 : Ideal (𝓞 K)) := by rw [hpunc, emptyPrimeIdeal_val]
    rw [hp, mul_one]
    rfl
  have hstates' : (Fintype.card States : ℝ) ^ 2 ≤
      Cs * exteriorNorm K S f.frozen ^ rho := by
    have h := hstates f.frozen f.puncture
    rw [hnorm] at h
    simpa only [Nat.card_eq_fintype_card, States] using h
  have hcard := mul_le_mul hstates' (by linarith : Q ^ 2 ≤ Q ^ 2 + 1)
    (sq_nonneg Q) (mul_nonneg hCs.le
      (Real.rpow_nonneg (exteriorNorm_pos K S f.frozen).le _))
  have h := mul_le_mul_of_nonneg_right hcard hE
  apply hcomb.trans
  apply h.trans_eq
  have hp : exteriorNorm K S f.frozen ^ rho * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ) =
      exteriorNorm K S f.frozen ^ (-(1 / 2 : ℝ) + rho) := by
    rw [← Real.rpow_add (exteriorNorm_pos K S f.frozen)]
    congr 1
    ring
  dsimp [E]
  calc
    _ = (Cs * (Q ^ 2 + 1) * Ce) * A ^ 2 *
        (exteriorNorm K S f.frozen ^ rho * exteriorNorm K S f.frozen ^ (-1 / 2 : ℝ)) *
          Z ^ ((5 / 6 : ℝ) - 2 * d + 23 * delta + 2 * eps) := by ring
    _ = _ := by rw [hp]

#print axioms inactiveWeight_ne_zero
#print axioms actual_reduced_annuli_dual_energy
#print axioms actual_frozen_row_energy

end HeckeSkeleton.LowEnergy.ActualFrozenAggregation
