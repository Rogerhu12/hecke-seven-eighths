import HeckeSkeleton.LowEnergy.ActualFrozenAggregation

/-!
# Literal reconstruction of the complete reflected Gaussian row

The jointly summable annular and dual series comes from the derived
two-sieve estimate.  Finite frozen-state and four-class sums can therefore
be exchanged with the annular sum.  Each annulus is then identified with
the original absolutely convergent reflected columns.  A mark coefficient
may vanish outside the admissible support.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualFrozenReconstruction

open NumberField IsDedekindDomain
open HeckePort.CenteredMomentGenerator
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualSymbols HeckeSkeleton.LowEnergy.ActualSieveDictionary
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualDyadicReflection
open HeckeSkeleton.LowEnergy.ActualAnnularBlockEnergy
open HeckeSkeleton.LowEnergy.ActualFrozenAggregation
open HeckeSkeleton.LowEnergy.ClassSlices
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- One actual active marked ideal, with all frozen states and complete
reflected columns, after extraction of the inactive reciprocal scalar. -/
def fixedPhysicalRow (f : FixedData K S) (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (V : ℝ → ℂ) (Z : ℝ)
    (k P : ExteriorIdeal K S) : ℂ :=
  (inactiveWeight K S f)⁻¹ *
    ∑' s : FrozenState K S f.frozen f.puncture,
      ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        physicalAtom K S D f s F θ (fun _ => 1) V Z k P cb.1 cb.2

theorem weighted_physical_atoms_eq_fixedRows
    (f : FixedData K S) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) :
    (inactiveWeight K S f)⁻¹ *
        (∑' s : FrozenState K S f.frozen f.puncture,
          ∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
            physicalAtom K S D f s F θ a V Z k P cb.1 cb.2) =
      ∑ P ∈ ps, a P.val.val * fixedPhysicalRow K S D f F θ V Z k P := by
  letI : Fintype (FrozenState K S f.frozen f.puncture) := Fintype.ofFinite _
  have hw (s : FrozenState K S f.frozen f.puncture) (P : ExteriorIdeal K S) :
      (∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        physicalAtom K S D f s F θ a V Z k P cb.1 cb.2) =
      a P.val.val * ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        physicalAtom K S D f s F θ (fun _ => 1) V Z k P cb.1 cb.2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro cb
    exact physicalAtom_markWeight K S D f s F θ a V Z k P cb.1 cb.2
  simp_rw [hw]
  rw [tsum_fintype, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [← Finset.mul_sum, fixedPhysicalRow, tsum_fintype]
  ring

/-- Exact reconstruction under the convergence conclusion of
`actual_frozen_row_energy`.  The theorem below derives that convergence
from the original two sieves, so it is not an additional analytic input. -/
theorem frozenReflectedRow_eq_physical_atoms [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (f : FixedData K S) (a : Ideal (𝓞 K) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (ps : Finset (ExteriorIdeal K S))
    (k : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hp : ∀ P ∈ ps, a P.val.val ≠ 0 → MarkAdmissible K S f P)
    (hpoint : ∀ s : FrozenState K S f.frozen f.puncture,
      ∀ classes : FourClasses (SixthLocalClasses K S),
        Summable (fun i => reducedAnnularDualRow K S D f s F θ classes a Z
          (ps.image (fun P => P.val.val)) i k.val.val)) :
    Summable (fun shift : ℤ => (inactiveWeight K S f)⁻¹ *
      (∑' s : FrozenState K S f.frozen f.puncture,
        ∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
          physicalAtom K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
            (Z * Real.exp (shift : ℝ)) k P cb.1 cb.2)) ∧
    frozenReflectedRow K S D f F θ a Z (ps.image (fun P => P.val.val)) k.val.val =
      (inactiveWeight K S f)⁻¹ *
        ∑' shift : ℤ, ∑' s : FrozenState K S f.frozen f.puncture,
          ∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
            physicalAtom K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
              (Z * Real.exp (shift : ℝ)) k P cb.1 cb.2 := by
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  letI : Fintype (FrozenState K S f.frozen f.puncture) := Fintype.ofFinite _
  let States := FrozenState K S f.frozen f.puncture
  let Classes := FourClasses (SixthLocalClasses K S)
  let B : States → Classes → GaussianEnergyAssembly.Index → ℂ := fun s classes i =>
    annularDualRow K S D f s F θ classes a Z (ps.image (fun P => P.val.val)) i k.val.val
  have hB (s : States) (classes : Classes) : Summable (B s classes) := by
    have h := (hpoint s classes).mul_left (inactiveWeight K S f)
    exact h.congr (fun i => (annularDualRow_eq_inactive_mul K S D f s F θ classes a Z
      (ps.image (fun P => P.val.val)) i k.val.val).symm)
  let H : States → Classes → ℤ → ℂ := fun s classes shift =>
    ∑' p : ℕ × ℕ, B s classes (shift, p)
  have hH (s : States) (classes : Classes) : Summable (H s classes) :=
    (hB s classes).prod
  have hsumH (s : States) : Summable (fun shift => ∑ classes : Classes, H s classes shift) :=
    summable_sum (fun classes _ => hH s classes)
  have hclass (s : States) (shift : ℤ) (p : ℕ × ℕ) :
      (∑ classes : Classes, B s classes (shift, p)) =
        physicalBlock K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
          (Z * Real.exp (shift : ℝ)) ps (squarefreeShell K S p.1) (idealShell K S p.2) k := by
    exact (physicalBlock_eq_class_sum K S D f s F θ a
      (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ))
      ps (squarefreeShell K S p.1) (idealShell K S p.2) k).symm
  have hsection (s : States) (shift : ℤ) :
      (∑ classes : Classes, H s classes shift) =
        ∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
          physicalAtom K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
            (Z * Real.exp (shift : ℝ)) k P cb.1 cb.2 := by
    have hpair : Summable (fun p : ℕ × ℕ => ∑ classes : Classes, B s classes (shift, p)) :=
      summable_sum (fun classes _ => (hB s classes).prod_factor shift)
    calc
      _ = ∑' p : ℕ × ℕ, ∑ classes : Classes, B s classes (shift, p) :=
        (Summable.tsum_finsetSum (fun classes _ => (hB s classes).prod_factor shift)).symm
      _ = ∑' j : ℕ, ∑' l : ℕ, ∑ classes : Classes, B s classes (shift, (j, l)) :=
        hpair.tsum_prod
      _ = ∑' j : ℕ, ∑' l : ℕ,
          physicalBlock K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
            (Z * Real.exp (shift : ℝ)) ps (squarefreeShell K S j) (idealShell K S l) k := by
        apply tsum_congr
        intro j
        apply tsum_congr
        intro l
        exact hclass s shift (j, l)
      _ = _ := (physicalBlock_dual_reconstruction_of_support K S D f s hD F θ hreflection
        ps k hk a hp (GaussianTheta.annulusTest shift) (Z * Real.exp (shift : ℝ))
          (mul_pos hZ (Real.exp_pos _))).symm
  have hcomm : (∑ s : States, ∑ classes : Classes, ∑' i, B s classes i) =
      ∑' shift : ℤ, ∑ s : States, ∑ classes : Classes, H s classes shift := by
    calc
      _ = ∑ s : States, ∑ classes : Classes, ∑' shift : ℤ, H s classes shift := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro classes _
        exact (hB s classes).tsum_prod
      _ = ∑ s : States, ∑' shift : ℤ, ∑ classes : Classes, H s classes shift := by
        apply Finset.sum_congr rfl
        intro s _
        exact (Summable.tsum_finsetSum (fun classes _ => hH s classes)).symm
      _ = _ := (Summable.tsum_finsetSum (fun s _ => hsumH s)).symm
  have hphysical : Summable (fun shift : ℤ =>
      ∑' s : FrozenState K S f.frozen f.puncture,
        ∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
          physicalAtom K S D f s F θ a (GaussianTheta.annulusTest shift).toFun
            (Z * Real.exp (shift : ℝ)) k P cb.1 cb.2) := by
    have hsum : Summable (fun shift : ℤ =>
        ∑ s : States, ∑ classes : Classes, H s classes shift) :=
      summable_sum (fun s _ => hsumH s)
    apply hsum.congr
    intro shift
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    exact hsection s shift
  refine ⟨hphysical.mul_left _, ?_⟩
  calc
    _ = (inactiveWeight K S f)⁻¹ *
        (∑ s : States, ∑ classes : Classes, ∑' i, B s classes i) := by
      simp only [frozenReflectedRow, tsum_fintype, reducedAnnularDualRow,
        tsum_mul_left, ← Finset.mul_sum, B, States, Classes]
    _ = (inactiveWeight K S f)⁻¹ *
        (∑' shift : ℤ, ∑ s : States, ∑ classes : Classes, H s classes shift) := by
      rw [hcomm]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro shift
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro s _
      exact hsection s shift

theorem frozenReflectedRow_eq_fixedPhysicalRows [Finite (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (f : FixedData K S) (a : Ideal (𝓞 K) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (ps : Finset (ExteriorIdeal K S))
    (k : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hp : ∀ P ∈ ps, a P.val.val ≠ 0 → MarkAdmissible K S f P)
    (hpoint : ∀ s : FrozenState K S f.frozen f.puncture,
      ∀ classes : FourClasses (SixthLocalClasses K S),
        Summable (fun i => reducedAnnularDualRow K S D f s F θ classes a Z
          (ps.image (fun P => P.val.val)) i k.val.val)) :
    Summable (fun shift : ℤ => ∑ P ∈ ps, a P.val.val *
      fixedPhysicalRow K S D f F θ (GaussianTheta.annulusTest shift).toFun
        (Z * Real.exp (shift : ℝ)) k P) ∧
    frozenReflectedRow K S D f F θ a Z (ps.image (fun P => P.val.val)) k.val.val =
      ∑' shift : ℤ, ∑ P ∈ ps, a P.val.val *
        fixedPhysicalRow K S D f F θ (GaussianTheta.annulusTest shift).toFun
          (Z * Real.exp (shift : ℝ)) k P := by
  obtain ⟨hs, he⟩ := frozenReflectedRow_eq_physical_atoms K S D hD F θ hreflection
    f a Z hZ ps k hk hp hpoint
  have hw (shift : ℤ) := weighted_physical_atoms_eq_fixedRows K S D f F θ a
    (GaussianTheta.annulusTest shift).toFun (Z * Real.exp (shift : ℝ)) ps k
  refine ⟨hs.congr hw, ?_⟩
  rw [he, ← tsum_mul_left]
  exact tsum_congr hw

/-- A fixed finite ratio-two row and mark block satisfies the convergence
needed above by the derived two-sieve theorem.  The scalar coefficient bound
and fixed logarithmic constants are chosen from these finite data only for
this identity; the energy theorem retains its uniform constants. -/
theorem actual_frozen_row_reconstruction [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ExteriorQuadraticBound K S D) (hcubic : ExteriorCubicBound K S D)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (f : FixedData K S) (Z Klo Plo q d Ccut Cwin : ℝ)
    (hZ : 1 < Z) (hK : 1 ≤ Klo) (hP : 1 ≤ Plo)
    (hq : 0 < q) (hCut : 0 < Ccut) (hWin : 0 < Cwin)
    (hd : 0 ≤ d) (hd' : d ≤ (1 / 6 : ℝ))
    (hf : IdealRows.Powerful f.frozen.val) (hpunc : f.puncture = primeSetIdeal K S ∅)
    (hselected : Z ^ d ≤ q)
    (hrow : exteriorNorm K S f.frozen * Klo ≤ Ccut * Z ^ (5 / 6 : ℝ) / q ^ 2)
    (hwindow : exteriorNorm K S (primeSetIdeal K S f.inactive) * Plo ≤
      Cwin * Z ^ ((1 / 6 : ℝ) - d))
    (ps : Finset (ExteriorIdeal K S))
    (hps : ∀ P ∈ ps, Squarefree P.val.val ∧
      Plo ≤ exteriorNorm K S P ∧ exteriorNorm K S P ≤ 2 * Plo)
    (k : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hkr : Klo ≤ exteriorNorm K S k ∧ exteriorNorm K S k ≤ 2 * Klo)
    (a : Ideal (𝓞 K) → ℂ)
    (hp : ∀ P ∈ ps, a P.val.val ≠ 0 → MarkAdmissible K S f P) :
    Summable (fun shift : ℤ => ∑ P ∈ ps, a P.val.val *
      fixedPhysicalRow K S D f F θ (GaussianTheta.annulusTest shift).toFun
        (Z * Real.exp (shift : ℝ)) k P) ∧
    frozenReflectedRow K S D f F θ a Z (ps.image (fun P => P.val.val)) k.val.val =
      ∑' shift : ℤ, ∑ P ∈ ps, a P.val.val *
        fixedPhysicalRow K S D f F θ (GaussianTheta.annulusTest shift).toFun
          (Z * Real.exp (shift : ℝ)) k P := by
  let C0 : ℝ := max 0 (max (Real.log Ccut) (Real.log Cwin))
  have hC0 : 0 ≤ C0 := le_max_left _ _
  have hlogCut : Real.log Ccut ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hlogWin : Real.log Cwin ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
  let A : ℝ := 1 + ∑ P ∈ ps, ‖a P.val.val‖
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : ∀ P ∈ ps.image (fun P => P.val.val), ‖a P‖ ≤ A := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    have h := Finset.single_le_sum (fun P _ => norm_nonneg (a P.val.val)) hQ
    dsimp [A]
    linarith
  have hrows : ∀ r ∈ ({k.val.val} : Finset (Ideal (𝓞 K))),
      IsExterior K S r ∧ Squarefree r ∧ (r.absNorm : ℝ) ≤ 2 * Klo := by
    intro r hr
    have hr' : r = k.val.val := Finset.mem_singleton.mp hr
    subst r
    exact ⟨exterior_isExterior K S k, hk.squarefree, hkr.2⟩
  have hmarks : ∀ P ∈ ps.image (fun P => P.val.val),
      IsExterior K S P ∧ Squarefree P ∧ (P.absNorm : ℝ) ≤ 2 * Plo := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨exterior_isExterior K S Q, (hps Q hQ).1, (hps Q hQ).2.2⟩
  have hrr : ∀ r ∈ ({k.val.val} : Finset (Ideal (𝓞 K))),
      1 ≤ safeNorm r / Klo ∧ safeNorm r / Klo ≤ 2 := by
    intro r hr
    have hr' : r = k.val.val := Finset.mem_singleton.mp hr
    subst r
    rw [safeNorm_exterior K S k]
    exact ⟨(le_div_iff₀ (zero_lt_one.trans_le hK)).mpr (by simpa using hkr.1),
      (div_le_iff₀ (zero_lt_one.trans_le hK)).mpr hkr.2⟩
  have hpr : ∀ P ∈ ps.image (fun P => P.val.val),
      1 ≤ safeNorm P / Plo ∧ safeNorm P / Plo ≤ 2 := by
    intro P hmem
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hmem
    rw [safeNorm_exterior K S Q]
    exact ⟨(le_div_iff₀ (zero_lt_one.trans_le hP)).mpr (by simpa using (hps Q hQ).2.1),
      (div_le_iff₀ (zero_lt_one.trans_le hP)).mpr (hps Q hQ).2.2⟩
  obtain ⟨C, hC, he⟩ := actual_frozen_row_energy K S D F hF θ hKernel hθ hD hquadratic hcubic
    1 1 C0 1 (by norm_num) (by norm_num) (by norm_num) hC0 (by norm_num)
  have hpoint := (he f Z Klo Plo q d Ccut Cwin hZ hK hP hq hCut hWin hd hd' hf hpunc
    hselected hrow hwindow hlogCut hlogWin {k.val.val} (ps.image (fun P => P.val.val))
    hrows hmarks hrr hpr a A hA ha).1
  exact frozenReflectedRow_eq_fixedPhysicalRows K S D hD F θ hreflection f a Z
    (zero_lt_one.trans hZ) ps k hk hp (fun s classes => hpoint s classes k.val.val (by simp))

#print axioms frozenReflectedRow_eq_physical_atoms
#print axioms weighted_physical_atoms_eq_fixedRows
#print axioms frozenReflectedRow_eq_fixedPhysicalRows
#print axioms actual_frozen_row_reconstruction

end HeckeSkeleton.LowEnergy.ActualFrozenReconstruction
