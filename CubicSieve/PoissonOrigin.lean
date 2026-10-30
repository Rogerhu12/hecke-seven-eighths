import CubicSieve.GaussPairLiteral
import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
import DedekindZetaZeroFree.LFunctions.Tate.Local.AnnularFourierMellin
import HeckeGeneral.Bridge.SLocalSchwartzModel
import Mathlib.RingTheory.Ideal.GoingUp

/-! The actual origin terms in mixed cubic Poisson.
The original arithmetic set contains a prime over 2, so its finite unit-shell
test vanishes at zero. The mixed row is zero there except for two unit ideals;
in that case its literal value is one, including a trivial principal quotient. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.PoissonOrigin

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.Bridge
open CubicSieve.GaussPairLiteral
open scoped Classical BigOperators NumberField nonZeroDivisors

section FiniteShell

variable {K : Type} [Field K] [NumberField K]

/-- A prime above 2 belongs to the original arithmetic set through `above_six`. -/
theorem finiteSet_nonempty (A : SArithmeticData K) : A.Sf.Nonempty := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : p.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨P, hP, hpP⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral p (S := 𝓞 K)
  letI := hP
  letI := hpP
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, inferInstance,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  have h2 : (2 : 𝓞 K) ∈ v.asIdeal := by
    change (2 : 𝓞 K) ∈ P
    simpa using (Ideal.mem_of_liesOver P p (2 : ℤ)).mp
      (Ideal.subset_span (by simp [p]))
  refine ⟨v, A.above_six v ?_⟩
  convert P.mul_mem_left (3 : 𝓞 K) h2 using 1 <;> norm_num [v]

theorem annularTest_zero (v : HeightOneSpectrum (𝓞 K)) :
    TateFiniteShell.annularTest K v 0 = 0 := by
  have hzero : (0 : v.adicCompletion K) ∉ TateFiniteShell.unitShell K v := by
    intro h
    have hh := (TateFiniteShell.mem_unitShell_iff K v 0).mp h
    exact zero_ne_one (by simpa only [map_zero] using hh)
  simp only [TateFiniteShell.annularTest, Set.indicator_of_notMem hzero]

/-- This is definitionally the finite unit-shell test `Profile.finiteTest A`. -/
theorem finiteUnitShell_zero (A : SArithmeticData K) :
    (∏ v : ↥A.Sf, TateFiniteShell.annularTest K v.val
      ((0 : (w : ↥A.Sf) → w.val.adicCompletion K) v)) = 0 := by
  obtain ⟨v, hv⟩ := finiteSet_nonempty A
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨v, hv⟩ : ↥A.Sf))
    (annularTest_zero v)

theorem sIntegerFiniteTestFunction_zero (A : SArithmeticData K) :
    sIntegerFiniteTestFunction K A.Sf (TateFiniteShell.annularTest K) 0 = 0 :=
  finiteUnitShell_zero A

/-- The primal Poisson origin vanishes for every archimedean Schwartz test. -/
theorem sIntegerTensorTerm_zero (A : SArithmeticData K)
    (φ : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ) :
    sIntegerTensorTerm K A.Sf φ (TateFiniteShell.annularTest K) 0 = 0 := by
  obtain ⟨v, hv⟩ := finiteSet_nonempty A
  unfold sIntegerTensorTerm
  rw [mul_eq_zero]
  right
  apply Finset.prod_eq_zero hv
  simp only [map_zero, annularTest_zero]

end FiniteShell

section PairRow

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem idealSymbol_of_top (I : ExteriorIdeal K S) (hI : I.val.val = ⊤)
    (a : S.integer K) : idealSymbol K S D I a = 1 := by
  rcases I with ⟨⟨L, hL⟩, hLS⟩
  change L = ⊤ at hI
  subst L
  exact sIntegerSexticIdealEvaluation_top K S D.root6 D.primitive6 D.embedding
    hLS (fun p hp => D.away_six p (hLS p hp)) a

theorem idealSymbol_zero_of_ne_top (I : ExteriorIdeal K S) (hI : I.val.val ≠ ⊤) :
    idealSymbol K S D I 0 = 0 := by
  obtain ⟨p, hp⟩ :=
    (HeightOneSpectrum.ideal_ne_top_iff_exists (RingOfIntegers.not_isField K) I.val.val).mp hI
  apply (sIntegerSexticIdealEvaluation_eq_zero_iff K S
    D.root6 D.primitive6 D.embedding I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun q hq => D.away_six q (I.property q hq)) 0).mpr
  exact ⟨p, Ideal.dvd_iff_le.mpr hp, map_zero _⟩

theorem idealSymbol_zero (I : ExteriorIdeal K S) :
    idealSymbol K S D I 0 = if I.val.val = ⊤ then 1 else 0 := by
  by_cases hI : I.val.val = ⊤
  · rw [if_pos hI]
    exact idealSymbol_of_top K S D I hI 0
  · rw [if_neg hI]
    exact idealSymbol_zero_of_ne_top K S D I hI

/-- Both unit ideals give the exact value one; every other pair gives zero. -/
theorem literalRow_zero (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) :
    literalRow K S D I J hI hJ 0 =
      if I.val.val = ⊤ ∧ J.val.val = ⊤ then 1 else 0 := by
  calc
    _ = star (idealSymbol K S D I 0 ^ 2) * idealSymbol K S D J 0 ^ 2 := by
      simpa only [map_zero] using literalRow_mk K S D I J hI hJ (0 : S.integer K)
    _ = _ := by
      rw [idealSymbol_zero, idealSymbol_zero]
      by_cases hi : I.val.val = ⊤ <;> by_cases hj : J.val.val = ⊤ <;> simp [hi, hj]

theorem literalRow_zero_ne_zero_iff (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val) :
    literalRow K S D I J hI hJ 0 ≠ 0 ↔ I.val.val = ⊤ ∧ J.val.val = ⊤ := by
  rw [literalRow_zero]
  split_ifs <;> simp_all

theorem literalRow_zero_of_top (I J : ExteriorIdeal K S)
    (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (hi : I.val.val = ⊤) (hj : J.val.val = ⊤) :
    literalRow K S D I J hI hJ 0 = 1 := by
  rw [literalRow_zero, if_pos ⟨hi, hj⟩]

end PairRow
end CubicSieve.PoissonOrigin
