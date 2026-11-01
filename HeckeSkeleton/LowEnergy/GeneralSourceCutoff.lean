import HeckeSkeleton.LowEnergy.GeneralColumnCutoff

/-!
# Finite dual projection of the actual reflected source

The static factor is the literal inactive, row and mark coefficient.
Expanding the four classes gives the existing source atom, and its
discarded series is controlled by `TailPiece` with exactly that factor.
All summability statements below are consequences of the original
kernel bound; none is an input to the source decomposition.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralSourceCutoff

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ActualDyadicReflection
open HeckeSkeleton.LowEnergy.ClassSlices
open HeckeSkeleton.LowEnergy.GeneralReconstruction
open HeckeSkeleton.LowEnergy.GeneralReflectedBlock
open HeckeSkeleton.LowEnergy.GeneralKernelTail
open HeckeSkeleton.LowEnergy.GeneralColumnCutoff
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

def rowMarkFactor (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (k P : ExteriorIdeal K S) : ℂ :=
  inactiveWeight K S f * ordinaryRow K S D f s θ q k.val.val *
    (a P.val.val * ordinaryMark K S D f s θ q P.val.val)

/-- The coefficient outside the column series is the original literal
row/mark coefficient, before taking norms or removing masks. -/
theorem slicedAtom_eq_factor_column
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (a : Ideal (𝓞 K) → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : ExteriorIdeal K S) :
    slicedAtom K S D f s F θ q a V X k.val.val P.val.val c.val.val b.val.val =
      rowMarkFactor K S D f s θ q a k P *
        columnAtom K S D f s F θ q V X k P (c, b) := by
  unfold slicedAtom rowMarkFactor columnAtom
  rw [safeNorm_exterior K S k, safeNorm_exterior K S P,
    safeNorm_exterior K S c, safeNorm_exterior K S b]
  ring

theorem generalAtom_eq_factor_class_sum [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) :
    generalAtom K S D f s F θ a V X k P c b =
      ∑ q : FourClasses (SixthLocalClasses K S),
        rowMarkFactor K S D f s θ q a k P *
          columnAtom K S D f s F θ q V X k P (c, b) := by
  rw [generalAtom_eq_class_sum K S D f s]
  exact Finset.sum_congr rfl (fun q _ =>
    slicedAtom_eq_factor_column K S D f s F θ q a V X k P c b)

def sourceTailPiece (θ : HeckeCharacter K) (q : FourClasses (SixthLocalClasses K S))
    (a : Ideal (𝓞 K) → ℂ) (X : ℝ) (k P : ExteriorIdeal K S) : TailPiece K S where
  fixed := f
  state := s
  classes := q
  X := X
  row := k
  mark := P
  weight := rowMarkFactor K S D f s θ q a k P

theorem generalAtom_norm_summable [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X)
    (k P : ExteriorIdeal K S) :
    Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      ‖generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2‖) := by
  have hs (q : FourClasses (SixthLocalClasses K S)) : Summable
      (fun cb => ‖rowMarkFactor K S D f s θ q a k P *
        columnAtom K S D f s F θ q V.toFun X k P cb‖) := by
    simpa only [norm_mul] using
      (column_norm_summable K S D F θ hKernel hθ hD f s q V X hX k P).mul_left
        ‖rowMarkFactor K S D f s θ q a k P‖
  have hsum := summable_sum (s := Finset.univ) (fun q _ => hs q)
  apply hsum.of_nonneg_of_le (fun cb => norm_nonneg _)
  intro cb
  rw [generalAtom_eq_factor_class_sum K S D f s]
  exact norm_sum_le _ _

def discardedSourceAtom (annuli : Finset (ℕ × ℕ))
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) : ℂ :=
  if columnIndex K S cb ∈ annuli then 0
    else generalAtom K S D f s F θ a V X k P cb.1 cb.2

theorem discardedSourceAtom_eq_class_sum [Fintype (SixthLocalClasses K S)]
    (annuli : Finset (ℕ × ℕ)) (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
    discardedSourceAtom K S D f s annuli F θ a V X k P cb =
      ∑ q : FourClasses (SixthLocalClasses K S), rowMarkFactor K S D f s θ q a k P *
        discardedColumn K S D f s annuli F θ q V X k P cb := by
  unfold discardedSourceAtom discardedColumn
  by_cases h : columnIndex K S cb ∈ annuli
  · simp only [if_pos h, mul_zero, Finset.sum_const_zero]
  · simp only [if_neg h]
    exact generalAtom_eq_factor_class_sum K S D f s F θ a V X k P cb.1 cb.2

theorem generalAtom_zero_of_not_squarefree
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P c b : ExteriorIdeal K S) (hc : ¬ Squarefree c.val.val) :
    generalAtom K S D f s F θ a V X k P c b = 0 := by
  have hcol : ¬ ColumnCondition K S s c b := fun h => hc h.1
  simp [generalAtom, columnCoefficient, extendColumn, hcol, ActualHybridEntry.hybridAtom]

theorem source_shell_filter_squarefree
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ideal (𝓞 K) → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (k P : ExteriorIdeal K S) (j l : ℕ) :
    (∑ c ∈ idealShell K S j, ∑ b ∈ idealShell K S l,
      generalAtom K S D f s F θ a V X k P c b) =
    ∑ c ∈ squarefreeShell K S j, ∑ b ∈ idealShell K S l,
      generalAtom K S D f s F θ a V X k P c b := by
  rw [squarefreeShell, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Squarefree c.val.val
  · simp only [if_pos hc]
  · simp [hc, generalAtom_zero_of_not_squarefree K S D f s F θ a V X k P c _ hc]

/-- Exact finite projection of the genuine, unsliced reflected source.
The squarefree/full-cube sum and the discarded sum are parts of the
same complete series. -/
theorem source_series_decomposition [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X)
    (k P : ExteriorIdeal K S) (annuli : Finset (ℕ × ℕ)) :
    Summable (fun cb => ‖discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb‖) ∧
      (∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
        generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2) =
        (∑ p ∈ annuli, ∑ c ∈ squarefreeShell K S p.1, ∑ b ∈ idealShell K S p.2,
          generalAtom K S D f s F θ a V.toFun X k P c b) +
        ∑' cb, discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb := by
  have hn := generalAtom_norm_summable K S D f s F θ hKernel hθ hD a V X hX k P
  have hd : Summable (fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
      ‖discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb‖) :=
    hn.of_nonneg_of_le (fun cb => norm_nonneg _)
      (fun cb => by unfold discardedSourceAtom; split_ifs <;> simp)
  refine ⟨hd, ?_⟩
  let r := fun cb : ExteriorIdeal K S × ExteriorIdeal K S =>
    if columnIndex K S cb ∈ annuli
      then generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2 else 0
  have hr : Summable r := hn.of_norm_bounded (fun cb => by
    dsimp [r]
    split_ifs <;> simp)
  have he (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2 =
        r cb + discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb := by
    dsimp [r, discardedSourceAtom]
    split_ifs <;> simp
  have hf : (∑' cb, r cb) = ∑ cb ∈ selectedColumns K S annuli,
      generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2 := by
    rw [tsum_eq_sum (s := selectedColumns K S annuli)
      (fun cb hcb => by dsimp [r]; rw [if_neg (by simpa only [mem_selectedColumns] using hcb)])]
    apply Finset.sum_congr rfl
    intro cb hcb
    exact if_pos ((mem_selectedColumns K S annuli cb).mp hcb)
  calc
    _ = ∑' cb, (r cb + discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb) :=
      tsum_congr he
    _ = (∑' cb, r cb) + ∑' cb,
        discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb := hr.tsum_add hd.of_norm
    _ = _ := by
      rw [hf, sum_selectedColumns]
      simp only [source_shell_filter_squarefree K S D f s F θ a V.toFun X k P]

/-- The finite active-mark sum is retained inside each reflected block.
The exact equality is established before any row norm is taken. -/
theorem source_row_decomposition [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X)
    (k : ExteriorIdeal K S) (ps : Finset (ExteriorIdeal K S)) (annuli : Finset (ℕ × ℕ)) :
    (∑ P ∈ ps, ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
      generalAtom K S D f s F θ a V.toFun X k P cb.1 cb.2) =
      (∑ p ∈ annuli, generalBlock K S D f s F θ a V.toFun X
        ps (squarefreeShell K S p.1) (idealShell K S p.2) k) +
      ∑ P ∈ ps, ∑' cb, discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb := by
  calc
    _ = ∑ P ∈ ps,
        ((∑ p ∈ annuli, ∑ c ∈ squarefreeShell K S p.1, ∑ b ∈ idealShell K S p.2,
          generalAtom K S D f s F θ a V.toFun X k P c b) +
          ∑' cb, discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb) :=
      Finset.sum_congr rfl (fun P _ =>
        (source_series_decomposition K S D f s F θ hKernel hθ hD a V X hX k P annuli).2)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      rfl

/-- The discarded unsliced source is bounded by the sum of its actual
class-tail pieces, with no artificial coefficient budget. -/
theorem source_discarded_mass_le [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (a : Ideal (𝓞 K) → ℂ) (V : SmoothAnnularTest)
    (X Klo Plo T : ℝ) (hX : 0 < X) (hK : 0 < Klo) (hP : 0 < Plo) (hT : 0 < T)
    (k P : ExteriorIdeal K S)
    (hk0 : 1 ≤ exteriorNorm K S k / Klo) (hk1 : exteriorNorm K S k / Klo ≤ 2)
    (hp0 : 1 ≤ exteriorNorm K S P / Plo) (hp1 : exteriorNorm K S P / Plo ≤ 2) :
    ‖∑' cb, discardedSourceAtom K S D f s
      (retainedAnnuli K S f s X Klo Plo T) F θ a V.toFun X k P cb‖ ≤
      ∑ q : FourClasses (SixthLocalClasses K S),
        (sourceTailPiece K S D f s θ q a X k P).tailMass D F θ V T := by
  let annuli := retainedAnnuli K S f s X Klo Plo T
  have hlocal (q : FourClasses (SixthLocalClasses K S)) :=
    weighted_discarded_mass_le K S D f s F θ hKernel hθ hD q V X Klo Plo T
      hX hK hP hT k P (rowMarkFactor K S D f s θ q a k P) hk0 hk1 hp0 hp1
  have hs := (source_series_decomposition K S D f s F θ hKernel hθ hD a V X hX k P annuli).1
  have hsum : Summable (fun cb => ∑ q : FourClasses (SixthLocalClasses K S),
      ‖rowMarkFactor K S D f s θ q a k P *
        discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖) :=
    summable_sum (fun q _ => (hlocal q).1)
  have hpoint (cb : ExteriorIdeal K S × ExteriorIdeal K S) :
      ‖discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb‖ ≤
      ∑ q : FourClasses (SixthLocalClasses K S),
        ‖rowMarkFactor K S D f s θ q a k P *
          discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖ := by
    rw [discardedSourceAtom_eq_class_sum]
    exact norm_sum_le _ _
  calc
    _ ≤ ∑' cb, ‖discardedSourceAtom K S D f s annuli F θ a V.toFun X k P cb‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' cb, ∑ q : FourClasses (SixthLocalClasses K S),
        ‖rowMarkFactor K S D f s θ q a k P *
          discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖ :=
      hs.tsum_le_tsum hpoint hsum
    _ = ∑ q : FourClasses (SixthLocalClasses K S), ∑' cb,
        ‖rowMarkFactor K S D f s θ q a k P *
          discardedColumn K S D f s annuli F θ q V.toFun X k P cb‖ :=
      Summable.tsum_finsetSum (fun q _ => (hlocal q).1)
    _ ≤ _ := Finset.sum_le_sum (fun q _ => (hlocal q).2)

#print axioms slicedAtom_eq_factor_column
#print axioms generalAtom_norm_summable
#print axioms source_series_decomposition
#print axioms source_row_decomposition
#print axioms source_discarded_mass_le

end HeckeSkeleton.LowEnergy.GeneralSourceCutoff
