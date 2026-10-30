import HeckeSkeleton.LowEnergy.ActualSourceReindex
import HeckeSkeleton.LowEnergy.DyadicReindex

/-!
# Actual dual dyads inherit convergence from the supplied reflection

The squarefree column and the full cube use their actual integral ideal
norms.  The dyads are finite, disjoint and exhaustive.  Their series and its
sum follow from the original reflected absolute convergence after exact
zero extension; no independent convergence assumption is introduced.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.ActualDyadicReflection

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualBlockReindex
open HeckeSkeleton.LowEnergy.ActualSourceReindex
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def idealNatNorm (I : ExteriorIdeal K S) : ℕ := I.val.val.absNorm

theorem idealNatNorm_pos (I : ExteriorIdeal K S) : 0 < idealNatNorm K S I :=
  Ideal.absNorm_pos_of_nonZeroDivisors I.val

theorem finite_idealNatNorm_le (N : ℕ) :
    Set.Finite {I : ExteriorIdeal K S | idealNatNorm K S I ≤ N} := by
  have h := finite_exteriorNorm_le K S (N : ℝ)
  apply h.subset
  intro I hI
  change (I.val.val.absNorm : ℝ) ≤ (N : ℝ)
  exact_mod_cast hI

def idealShell (j : ℕ) : Finset (ExteriorIdeal K S) :=
  DyadicReindex.shell (idealNatNorm K S) (finite_idealNatNorm_le K S) j

def squarefreeShell (j : ℕ) : Finset (ExteriorIdeal K S) :=
  (idealShell K S j).filter (fun I => Squarefree I.val.val)

theorem idealShell_bounds {j : ℕ} {I : ExteriorIdeal K S}
    (hI : I ∈ idealShell K S j) :
    (2 : ℝ) ^ j ≤ exteriorNorm K S I ∧ exteriorNorm K S I < 2 * (2 : ℝ) ^ j := by
  have hj := (DyadicReindex.mem_shell (idealNatNorm K S)
    (finite_idealNatNorm_le K S) j I).mp hI
  simpa only [hj, pow_succ, mul_comm] using
    DyadicReindex.index_bounds_real (idealNatNorm K S) (idealNatNorm_pos K S I)

theorem squarefreeShell_bounds {j : ℕ} {I : ExteriorIdeal K S}
    (hI : I ∈ squarefreeShell K S j) :
    Squarefree I.val.val ∧
      (2 : ℝ) ^ j ≤ exteriorNorm K S I ∧ exteriorNorm K S I < 2 * (2 : ℝ) ^ j :=
  ⟨(Finset.mem_filter.mp hI).2, idealShell_bounds K S (Finset.mem_filter.mp hI).1⟩

variable (D : ThetaArithmeticData K S)
variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

theorem physicalAtom_markWeight (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ) (k P c b : ExteriorIdeal K S) :
    physicalAtom K S D f s F θ a V Z k P c b =
      a P.val.val * physicalAtom K S D f s F θ (fun _ => 1) V Z k P c b := by
  unfold physicalAtom ActualHybridEntry.hybridAtom
  simp only [div_eq_mul_inv]
  ring

theorem physicalAtom_zero_of_not_squarefree (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (k P c b : ExteriorIdeal K S) (hc : ¬Squarefree c.val.val) :
    physicalAtom K S D f s F θ a V Z k P c b = 0 := by
  have hcol : ¬ColumnCondition K S s c b := fun h => hc h.1
  simp [physicalAtom, columnCoefficient, extendColumn, hcol, ActualHybridEntry.hybridAtom]

theorem physicalAtom_weighted_summable (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k P : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (hP : MarkAdmissible K S f P) (a : Ideal (𝓞 K) → ℂ)
    (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2) := by
  have h := (physicalAtom_columns_summable_fixed K S D hD F θ hreflection f s
    k P hk hP V Z hZ).mul_left (a P.val.val)
  exact h.congr (fun cb => (physicalAtom_markWeight K S D f s F θ a V.toFun Z
    k P cb.1 cb.2).symm)

/-- A mark-only zero extension needs admissibility only where its actual
coefficient is nonzero.  This permits the physical window support to be
kept unchanged while its frozen-prime guard stays in the mark coefficient. -/
theorem physicalAtom_weighted_summable_of_support (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (k P : ExteriorIdeal K S) (hk : RowAdmissible K S f k)
    (a : Ideal (𝓞 K) → ℂ)
    (hP : a P.val.val ≠ 0 → MarkAdmissible K S f P)
    (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2) := by
  by_cases ha : a P.val.val = 0
  · simpa only [physicalAtom_zero_of_markWeight K S D f s F θ a V.toFun Z
      k P _ _ ha] using (summable_zero : Summable
        (fun _ : ExteriorIdeal K S × ExteriorIdeal K S => (0 : ℂ)))
  · exact physicalAtom_weighted_summable K S D f s hD F θ hreflection k P hk (hP ha)
      a V Z hZ

/-- A squarefree-shell filter is exact because the original coefficient
already vanishes outside that support. -/
theorem physicalBlock_filter_squarefree (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps : Finset (ExteriorIdeal K S)) (j l : ℕ) (k : ExteriorIdeal K S) :
    physicalBlock K S D f s F θ a V Z ps (idealShell K S j) (idealShell K S l) k =
      physicalBlock K S D f s F θ a V Z ps (squarefreeShell K S j) (idealShell K S l) k := by
  unfold physicalBlock squarefreeShell
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Squarefree c.val.val
  · simp only [if_pos hc]
  · simp [hc, physicalAtom_zero_of_not_squarefree K S D f s F θ a V Z k P c _ hc]

theorem physicalBlock_commute_columns (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (Z : ℝ)
    (ps cs bs : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S) :
    physicalBlock K S D f s F θ a V Z ps cs bs k =
      ∑ c ∈ cs, ∑ b ∈ bs, ∑ P ∈ ps,
        physicalAtom K S D f s F θ a V Z k P c b := by
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_comm

theorem physicalBlock_dual_summable (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (ps : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hp : ∀ P ∈ ps, MarkAdmissible K S f P)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun p : ℕ × ℕ => physicalBlock K S D f s F θ a V.toFun Z
      ps (squarefreeShell K S p.1) (idealShell K S p.2) k) := by
  let G : ExteriorIdeal K S × ExteriorIdeal K S → ℂ := fun cb =>
    ∑ P ∈ ps, physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2
  have hG : Summable G := summable_sum (fun P hP =>
    physicalAtom_weighted_summable K S D f s hD F θ hreflection k P hk (hp P hP) a V Z hZ)
  have h := DyadicReindex.summable_pair_shell_sums
    (fun cb : ExteriorIdeal K S × ExteriorIdeal K S => idealNatNorm K S cb.1)
    (fun cb : ExteriorIdeal K S × ExteriorIdeal K S => idealNatNorm K S cb.2)
    (fun M N => (finite_idealNatNorm_le K S M).prod (finite_idealNatNorm_le K S N)) G hG
  apply h.congr
  intro p
  rw [DyadicReindex.pairShell_product, Finset.sum_product]
  change (∑ c ∈ idealShell K S p.1, ∑ b ∈ idealShell K S p.2, G (c, b)) = _
  rw [← physicalBlock_filter_squarefree, physicalBlock_commute_columns]
  rfl

/-- The whole finite active-mark row is reconstructed from the genuine
dual dyads.  The equality precedes the row norm. -/
theorem physicalBlock_dual_reconstruction (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (ps : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (hp : ∀ P ∈ ps, MarkAdmissible K S f P)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    (∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
      physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2) =
      ∑' j : ℕ, ∑' l : ℕ, physicalBlock K S D f s F θ a V.toFun Z
        ps (squarefreeShell K S j) (idealShell K S l) k := by
  let G : ExteriorIdeal K S × ExteriorIdeal K S → ℂ := fun cb =>
    ∑ P ∈ ps, physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2
  have hsingle := fun P hP => physicalAtom_weighted_summable K S D f s hD F θ hreflection
    k P hk (hp P hP) a V Z hZ
  have hG : Summable G := summable_sum hsingle
  rw [← Summable.tsum_finsetSum hsingle]
  have h := DyadicReindex.tsum_eq_double_product_shell_sums
    (idealNatNorm K S) (idealNatNorm K S) (finite_idealNatNorm_le K S)
    (finite_idealNatNorm_le K S) G hG
  rw [h]
  apply tsum_congr
  intro j
  apply tsum_congr
  intro l
  rw [← physicalBlock_filter_squarefree, physicalBlock_commute_columns]
  rfl

theorem physicalBlock_dual_reconstruction_of_support (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (ps : Finset (ExteriorIdeal K S)) (k : ExteriorIdeal K S)
    (hk : RowAdmissible K S f k) (a : Ideal (𝓞 K) → ℂ)
    (hp : ∀ P ∈ ps, a P.val.val ≠ 0 → MarkAdmissible K S f P)
    (V : SmoothAnnularTest) (Z : ℝ) (hZ : 0 < Z) :
    (∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
      physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2) =
      ∑' j : ℕ, ∑' l : ℕ, physicalBlock K S D f s F θ a V.toFun Z
        ps (squarefreeShell K S j) (idealShell K S l) k := by
  let G : ExteriorIdeal K S × ExteriorIdeal K S → ℂ := fun cb =>
    ∑ P ∈ ps, physicalAtom K S D f s F θ a V.toFun Z k P cb.1 cb.2
  have hsingle := fun P hP => physicalAtom_weighted_summable_of_support K S D f s hD
    F θ hreflection k P hk a (hp P hP) V Z hZ
  have hG : Summable G := summable_sum hsingle
  rw [← Summable.tsum_finsetSum hsingle]
  have h := DyadicReindex.tsum_eq_double_product_shell_sums
    (idealNatNorm K S) (idealNatNorm K S) (finite_idealNatNorm_le K S)
    (finite_idealNatNorm_le K S) G hG
  rw [h]
  apply tsum_congr
  intro j
  apply tsum_congr
  intro l
  rw [← physicalBlock_filter_squarefree, physicalBlock_commute_columns]
  rfl

#print axioms idealShell_bounds
#print axioms physicalAtom_weighted_summable
#print axioms physicalBlock_dual_summable
#print axioms physicalBlock_dual_reconstruction
#print axioms physicalBlock_dual_reconstruction_of_support

end HeckeSkeleton.LowEnergy.ActualDyadicReflection
