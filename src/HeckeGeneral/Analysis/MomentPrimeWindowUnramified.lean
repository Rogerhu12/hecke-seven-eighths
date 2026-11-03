import HeckeGeneral.Analysis.MomentPrimeWindows
import HeckeGeneral.Characters.FiniteRamification
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Every fixed finite family of genuine continuous Hecke characters is
unramified on all actual prime windows once the external scale is large
enough. The window geometry is fixed before the character family; only the
scale threshold depends on that family. No finite-order hypothesis and no
enlargement of S are required. This supplies the local unramified premise
needed for a subsequent character expansion of the ray filter.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- A finite family has a common bound for the norms of its ramified primes. -/
theorem exists_norm_bound_unramified_finset (T : Finset (HeckeCharacter K)) :
    ∃ N : ℕ, ∀ p : HeightOneSpectrum (𝓞 K), N < p.asIdeal.absNorm →
      ∀ χ ∈ T, UnramifiedAt K χ p := by
  let bad := fun χ : HeckeCharacter K => (finite_ramifiedPlaces K χ).toFinset
  let E := T.biUnion bad
  refine ⟨E.sup (fun p => p.asIdeal.absNorm), ?_⟩
  intro p hp χ hχ
  have hpE : p ∉ E := by
    intro h
    have hle : p.asIdeal.absNorm ≤ E.sup (fun p => p.asIdeal.absNorm) :=
      Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal.absNorm) h
    exact (not_lt_of_ge hle) hp
  by_contra h
  apply hpE
  exact Finset.mem_biUnion.mpr ⟨χ, hχ, by simpa [bad] using h⟩

end HeckeGeneral.Characters

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set Filter
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

/-- The lower annular support bound gives a strict lower bound on every
prime norm in the actual analytic support. -/
theorem analyticPrimeSupport_scale_lt_norm (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Ioo (1 : ℝ) 2) {P : ℝ} (hP : 0 < P)
    {p : HeightOneSpectrum (𝓞 K)} (hp : p ∈ analyticPrimeSupport K W P) :
    P < (p.asIdeal.absNorm : ℝ) := by
  have hw := (analyticPrimeSupport_spec K W hs P p).mp hp
  have hl := (hs hw).1
  simpa only [one_mul] using (lt_div_iff₀ hP).mp hl

/-- The scale cutoff may depend on a later finite character family; the
geometry and all slot exponents are unchanged. It works for every slot at
once and for every later external scale. -/
theorem exists_primeWindows_unramified (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ i : Fin g.slots, ∀ p ∈ analyticPrimeSupport K (g.weight i).toFun (primeScale g Z),
        ∀ χ ∈ T, UnramifiedAt K χ p := by
  obtain ⟨N, hN⟩ := exists_norm_bound_unramified_finset K T
  have he : 0 < (1 / 6 : ℝ) / g.slots :=
    div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  obtain ⟨Zh, hZh⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop he).eventually (eventually_ge_atTop (N : ℝ)))
  refine ⟨max 1 Zh, le_max_left _ _, ?_⟩
  intro Z hZ i p hp χ hχ
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ1
  have hPpos : 0 < primeScale g Z := Real.rpow_pos_of_pos hZpos _
  have hNP : (N : ℝ) ≤ primeScale g Z :=
    hZh Z ((le_max_right _ _).trans hZ)
  have hpN : (N : ℝ) < p.asIdeal.absNorm := hNP.trans_lt
    (analyticPrimeSupport_scale_lt_norm K _ (g.support_annular i) hPpos hp)
  exact hN p (by exact_mod_cast hpN) χ hχ

/-- Literal moment supports have the same cutoff, uniformly in their height
parameter (the actual pretarget profiles are height independent). -/
theorem exists_analyticMomentPrimeWindows_unramified (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) :
    ∃ Z₀ : ℝ, 1 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → ∀ (i : Fin g.slots) (t : ℝ),
      ∀ p ∈ (analyticMomentPrimeWindow K g i).support t (primeScale g Z),
        ∀ χ ∈ T, UnramifiedAt K χ p := by
  obtain ⟨Z₀, hZ₀, h⟩ := exists_primeWindows_unramified K g T
  exact ⟨Z₀, hZ₀, fun Z hZ i _t p hp χ hχ => h Z hZ i p hp χ hχ⟩

end HeckeGeneral.ThetaSkeleton.Physical
