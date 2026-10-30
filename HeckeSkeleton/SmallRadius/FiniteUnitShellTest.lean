import HeckeGeneral.Characters.LocalResidueCosetFourier
import HeckeGeneral.Arithmetic.LocalValuationCompact

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
The actual finite-place test is the indicator of O_v minus its maximal
ideal. It is compactly supported and locally constant in the additive
completion. On the multiplicative group its support is the compact group
of integral units, and its norm is exactly one. No local test is supplied
as a hypothesis. Fourier or Mellin integral evaluations are not claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellTestDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open LanglandsTunnell.TateLocal
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def localUnitShellSet (v : HeightOneSpectrum (𝓞 K)) : Set (v.adicCompletion K) :=
  (v.adicCompletionIntegers K : Set (v.adicCompletion K)) \
    localResidueCosetSet K v 1 0

theorem mem_localUnitShellSet_integer_iff (v : HeightOneSpectrum (𝓞 K))
    (x : LocalIntegerRing K v) :
    (x : v.adicCompletion K) ∈ localUnitShellSet K v ↔ IsUnit x := by
  have hmax : x ∈ localMaximalIdeal K v ^ 1 ↔ ¬IsUnit x := by
    rw [pow_one]
    exact (IsLocalRing.mem_maximalIdeal x).trans mem_nonunits_iff
  calc
    _ ↔ ¬Ideal.Quotient.mk (localMaximalIdeal K v ^ 1) x = 0 := by
      constructor
      · intro hx hzero
        exact hx.2 ((mem_localResidueCosetSet_iff K v 1 0 x).mpr hzero)
      · intro hx
        exact ⟨x.property,
          fun hmem => hx ((mem_localResidueCosetSet_iff K v 1 0 x).mp hmem)⟩
    _ ↔ ¬x ∈ localMaximalIdeal K v ^ 1 :=
      not_congr (Ideal.Quotient.eq_zero_iff_mem (I := localMaximalIdeal K v ^ 1))
    _ ↔ IsUnit x := (not_congr hmax).trans not_not

theorem localUnitShellSet_eq_range (v : HeightOneSpectrum (𝓞 K)) :
    localUnitShellSet K v =
      Set.range (fun u : (LocalIntegerRing K v)ˣ =>
        ((u : LocalIntegerRing K v) : v.adicCompletion K)) := by
  ext x
  constructor
  · intro hx
    let a : LocalIntegerRing K v := ⟨x, hx.1⟩
    obtain ⟨u, hu⟩ := (mem_localUnitShellSet_integer_iff K v a).mp hx
    exact ⟨u, congrArg (fun a : LocalIntegerRing K v => (a : v.adicCompletion K)) hu⟩
  · rintro ⟨u, rfl⟩
    exact (mem_localUnitShellSet_integer_iff K v u.val).mpr u.isUnit

theorem isClopen_localUnitShellSet (v : HeightOneSpectrum (𝓞 K)) :
    IsClopen (localUnitShellSet K v) :=
  (Valued.isClopen_valuationSubring (v.adicCompletion K)).diff
    (isClopen_localResidueCosetSet K v 1 0)

theorem isCompact_localUnitShellSet (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (localUnitShellSet K v) := by
  letI : CompactSpace (LocalIntegerRing K v) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  exact hO.diff (isClopen_localResidueCosetSet K v 1 0).isOpen

def localUnitShellTest (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K → ℂ :=
  (localUnitShellSet K v).indicator (fun _ => 1)

theorem localUnitShellTest_locallyConstant (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (localUnitShellTest K v) :=
  (IsSchwartzBruhat.indicator_const (isClopen_localUnitShellSet K v)
    (isCompact_localUnitShellSet K v) (1 : ℂ)).1

theorem localUnitShellTest_compactSupport (v : HeightOneSpectrum (𝓞 K)) :
    HasCompactSupport (localUnitShellTest K v) :=
  (IsSchwartzBruhat.indicator_const (isClopen_localUnitShellSet K v)
    (isCompact_localUnitShellSet K v) (1 : ℂ)).2

theorem localUnitShellTest_one (v : HeightOneSpectrum (𝓞 K)) :
    localUnitShellTest K v 1 = 1 := by
  have h : (1 : v.adicCompletion K) ∈ localUnitShellSet K v :=
    (mem_localUnitShellSet_integer_iff K v 1).mpr isUnit_one
  exact Set.indicator_of_mem h _

theorem localUnitShellTest_norm_eq_one (v : HeightOneSpectrum (𝓞 K))
    {x : v.adicCompletion K} (hx : localUnitShellTest K v x ≠ 0) : ‖x‖ = 1 := by
  have hs : x ∈ localUnitShellSet K v := by
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  rw [localUnitShellSet_eq_range K v] at hs
  obtain ⟨u, rfl⟩ := hs
  exact localIntegerUnitsEmbedding_norm K v u

theorem localUnitShellTest_mem_unitRange (v : HeightOneSpectrum (𝓞 K))
    {x : (v.adicCompletion K)ˣ} (hx : localUnitShellTest K v x.val ≠ 0) :
    x ∈ Set.range (localIntegerUnitsEmbedding K v) := by
  have hs : x.val ∈ localUnitShellSet K v := by
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  rw [localUnitShellSet_eq_range K v] at hs
  obtain ⟨u, hu⟩ := hs
  exact ⟨u, Units.ext hu⟩

theorem localUnitShellTest_compactSupport_units (v : HeightOneSpectrum (𝓞 K)) :
    HasCompactSupport (fun x : (v.adicCompletion K)ˣ => localUnitShellTest K v x.val) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_range (localIntegerUnitsEmbedding K v).continuous)
  intro x hx
  exact localUnitShellTest_mem_unitRange K v hx

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def finiteUnitShellTensor (x : (p : S) → p.val.adicCompletion K) : ℂ :=
  ∏ p : S, localUnitShellTest K p.val (x p)

theorem finiteUnitShellTensor_one :
    finiteUnitShellTensor K S (fun _ => 1) = 1 := by
  simp only [finiteUnitShellTensor, localUnitShellTest_one, Finset.prod_const_one]

theorem finiteUnitShellTensor_norm_eq_one
    {x : (p : S) → p.val.adicCompletion K} (hx : finiteUnitShellTensor K S x ≠ 0) :
    ∀ p : S, ‖x p‖ = 1 := by
  intro p
  apply localUnitShellTest_norm_eq_one K p.val
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ p) hz)

theorem finiteUnitShellTensor_compactSupport_units :
    HasCompactSupport (fun x : (p : S) → (p.val.adicCompletion K)ˣ =>
      finiteUnitShellTensor K S (fun p => (x p).val)) := by
  let C : Set ((p : S) → (p.val.adicCompletion K)ˣ) :=
    Set.univ.pi (fun p => Set.range (localIntegerUnitsEmbedding K p.val))
  have hC : IsCompact C :=
    isCompact_univ_pi (fun p => isCompact_range (localIntegerUnitsEmbedding K p.val).continuous)
  apply HasCompactSupport.of_support_subset_isCompact hC
  intro x hx p _hp
  apply localUnitShellTest_mem_unitRange K p.val
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ p) hz)

end HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellTestDraft
