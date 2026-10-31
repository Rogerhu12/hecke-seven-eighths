import ThetaGlobal.ReflectedArithmetic
import HeckeGeneral.Analysis.IdealSummability

/-!
# Absolute convergence of the project's actual marked reflected series

The only analytic input is `MellinKernelInput`, whose kernel estimates are
already proved in the task's upstream `HeckeSkeleton.ThetaKernel` modules.
All arithmetic bounds are proved from the literal finite sums in
`ReflectedArithmetic`.  In particular the sharp exterior Weyl table is not
an assumption here.  No global reflection identity is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ThetaGlobal.ReflectedAbsoluteProject

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.ReflectedAbsolute ThetaGlobal.ReflectedArithmetic
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S) (d : MarkedDatum K S)

/-- The finite choices: active mark set, active frozen set, frequency-unit
sector.  Proof fields are retained in the subtypes. -/
abbrev ReflectionBranch :=
  {A : Finset (ExteriorPrime K S) // A ∈ d.marks.powerset} ×
  {f : Finset (ExteriorPrime K S) // f ∈ (frozenPrimes K S d).powerset} ×
    SixthUnitClasses K S

instance reflectionBranch_finite : Finite (ReflectionBranch K S d) := by
  dsimp only [ReflectionBranch]
  infer_instance

/-- Forget only restrictions and proof fields, never an independent datum.
The resulting ambient ideal space has three, rather than two, coordinates. -/
def reflectionEncode (i : ReflectionIndex K S d) :
    ReflectionBranch K S d × ExteriorIdeal K S × ExteriorIdeal K S × ExteriorIdeal K S :=
  ((⟨i.activeMarks, Finset.mem_powerset.mpr i.marks_subset⟩,
    ⟨i.activeFrozen, Finset.mem_powerset.mpr i.frozen_subset⟩,
    i.unitSector), i.numeratorFrozen, i.c, i.n)

theorem reflectionEncode_injective : Function.Injective (reflectionEncode K S d) := by
  intro i j hij
  have hm : i.activeMarks = j.activeMarks := congrArg (fun x => x.1.1.val) hij
  have hf : i.activeFrozen = j.activeFrozen := congrArg (fun x => x.1.2.1.val) hij
  have hu : i.unitSector = j.unitSector := congrArg (fun x => x.1.2.2) hij
  have ha : i.numeratorFrozen = j.numeratorFrozen := congrArg (fun x => x.2.1) hij
  have hc : i.c = j.c := congrArg (fun x => x.2.2.1) hij
  have hn : i.n = j.n := congrArg (fun x => x.2.2.2) hij
  cases i
  cases j
  cases hm
  cases hf
  cases hu
  cases ha
  cases hc
  cases hn
  rfl

def branchScale (X : ℝ) (b : ReflectionBranch K S d) : ℝ :=
  X / (exteriorNorm K S d.moving * exteriorNorm K S (primeSetIdeal K S b.2.1.val) *
    exteriorNorm K S (primeSetIdeal K S b.1.val)) ^ 2

theorem branchScale_pos {X : ℝ} (hX : 0 < X) (b : ReflectionBranch K S d) :
    0 < branchScale K S d X b := by
  apply div_pos hX
  exact sq_pos_of_pos (mul_pos
    (mul_pos (ReflectedArithmetic.exteriorNorm_pos K S _)
      (ReflectedArithmetic.exteriorNorm_pos K S _))
    (ReflectedArithmetic.exteriorNorm_pos K S _))

def branchArithmeticBound (b : ReflectionBranch K S d) : ℝ :=
  frozenArithmeticBound K S D d b.2.1.val * rowArithmeticBound K S D d

theorem branchArithmeticBound_nonneg (b : ReflectionBranch K S d) :
    0 ≤ branchArithmeticBound K S D d b :=
  mul_nonneg (frozenArithmeticBound_nonneg K S D d _)
    (rowArithmeticBound_nonneg K S D d)

/-- Mathlib's Dedekind-zeta majorant supplies the one actual number-field
counting estimate used in this proof. -/
theorem summable_exterior_inverseSquare :
    Summable (fun I : ExteriorIdeal K S => inverseSquare (exteriorNorm K S I)) := by
  have h := (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)).subtype
    (fun I => ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
  have heq (I : ExteriorIdeal K S) :
      (I.val.val.absNorm : ℝ) ^ (-2 : ℝ) = inverseSquare (exteriorNorm K S I) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _) 2, Real.rpow_two]
    rfl
  simpa only [Function.comp_def, heq] using h

theorem testSeminorm_nonneg (V : ℝ → ℂ) (J : ℕ) (A : ℝ) :
    0 ≤ testSeminorm V J A := by
  exact le_trans (le_max_left 0 (testIntegral V 0 A))
    (Finset.le_sup' (fun j => max 0 (testIntegral V j A)) (by simp))

/-- Only the zeroth Euler derivative and the large-argument tail A=2 are
needed for this fixed-row summability argument. -/
theorem kernel_quadratic_tail (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hkernel : MellinKernelInput K S F θ) (V : SmoothAnnularTest)
    (u : SixthUnitClasses K S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ κ y, 0 < y →
      ‖mellinReflectionKernel K S F θ u κ V.toFun 0 y‖ ≤ B * inverseSquare y := by
  let r := Fintype.card {v : InfinitePlace K // v.IsComplex}
  let J : ℕ := 8 * r + 2
  have hJ : 4 * (Fintype.card {v : InfinitePlace K // v.IsComplex} : ℝ) *
      (2 : ℝ) + (0 : ℕ) + 1 < (J : ℝ) := by
    dsimp [J, r]
    push_cast
    linarith
  obtain ⟨C, hC, hbound⟩ := hkernel.derivative_bound 2 0 J (by norm_num) hJ
  refine ⟨C * testSeminorm V.toFun J 2,
    mul_nonneg hC (testSeminorm_nonneg V.toFun J 2), ?_⟩
  intro κ y hy
  have h := hbound V u κ y hy
  simp only [eulerDerivativeOrder, Function.iterate_zero, id_eq] at h
  calc
    _ ≤ C * testSeminorm V.toFun J 2 * min (y ^ (1 / 4 : ℝ)) (y ^ (-2 : ℝ)) := h
    _ ≤ C * testSeminorm V.toFun J 2 * y ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg hC (testSeminorm_nonneg V.toFun J 2))
    _ = _ := by rw [Real.rpow_neg hy.le 2, Real.rpow_two]; rfl

theorem reflectedTerm_eq_coefficient_kernel (i : ReflectionIndex K S d)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ) (X : ℝ) :
    reflectedTerm K S D d i F θ V X =
      reflectedCoefficient K S D d i θ *
        mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
          (frequencyClass K S D d i) V 0
          (branchScale K S d X (reflectionEncode K S d i).1 *
            exteriorNorm K S (reflectionEncode K S d i).2.1 *
            exteriorNorm K S (reflectionEncode K S d i).2.2.1 *
            exteriorNorm K S (reflectionEncode K S d i).2.2.2 ^ 3) := by
  unfold reflectedTerm reflectedCoefficient
  congr 2
  simp only [branchScale, reflectionEncode, activeFrozenIdeal, activeMarkedIdeal,
    div_eq_mul_inv]
  ring

/-- **TH-MARKED-REFLECTED-ABSOLUTE.**  This is the actual project series,
with no new local, arithmetic, or automorphic assumptions. -/
theorem marked_reflected_absolute (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hkernel : MellinKernelInput K S F θ) (V : SmoothAnnularTest)
    {X : ℝ} (hX : 0 < X) :
    Summable (fun i : ReflectionIndex K S d => reflectedTerm K S D d i F θ V.toFun X) := by
  obtain ⟨B, hB, htail⟩ := kernel_quadratic_tail K S F θ hkernel V
    (QuotientGroup.mk d.rowUnit)
  have hsum := summable_reflected_of_quadratic_tail
    (exteriorNorm K S) (exteriorNorm_ge_one K S) (summable_exterior_inverseSquare K S)
    (reflectionEncode K S d) (reflectionEncode_injective K S d)
    (frequencyClass K S D d) (branchScale K S d X) (branchArithmeticBound K S D d)
    (branchScale_pos K S d hX) (branchArithmeticBound_nonneg K S D d)
    (fun i => reflectedCoefficient K S D d i θ)
    (fun i => norm_reflectedCoefficient_le K S D d i θ)
    (fun κ y => mellinReflectionKernel K S F θ (QuotientGroup.mk d.rowUnit)
      κ V.toFun 0 y) B hB htail
  exact hsum.congr (fun i =>
    (reflectedTerm_eq_coefficient_kernel K S D d i F θ V.toFun X).symm)

end ThetaGlobal.ReflectedAbsoluteProject
