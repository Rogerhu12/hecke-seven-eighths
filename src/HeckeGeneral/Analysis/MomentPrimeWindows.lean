import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Analysis.MomentInputs

/-! Literal bridge from the pretarget smooth prime windows to the actual
moment geometry. Analytic supports are defined before S and the ray filter.
The final membership identity retains those later arithmetic restrictions.
No prime density, uniform seminorm or moment admissibility is asserted. -/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.SquarefreeAmplification ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

def analyticPrimeSupport (W : ℝ → ℂ) (P : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePrimeEnvelope K (dyadicIdealSupport K P)).filter
    (fun p => W ((p.asIdeal.absNorm : ℝ) / P) ≠ 0)

theorem analyticPrimeSupport_spec (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Ioo (1 : ℝ) 2)
    (P : ℝ) (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ analyticPrimeSupport K W P ↔ W ((p.asIdeal.absNorm : ℝ) / P) ≠ 0 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hW
    let I : NonzeroIdeal K := ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩
    have hq : 0 < (p.asIdeal.absNorm : ℝ) := idealNorm_pos K I
    have hy := hs hW
    have hP : 0 < P := by
      by_contra hn
      have hbad := div_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_gt hn)
      linarith [hy.1]
    have hI : I ∈ dyadicIdealSupport K P :=
      (mem_dyadicIdealSupport_iff K hP.le I).mpr
        ((div_lt_iff₀ hP).mp hy.2).le
    have hp : p ∈ idealPrimeSupport K I :=
      (mem_idealPrimeSupport_iff K I p).mpr dvd_rfl
    exact Finset.mem_filter.mpr ⟨idealPrimeSupport_subset_envelope K _ I hI hp, hW⟩

def analyticMomentPrimeWindow (g : PrimeWindowGeometry) (i : Fin g.slots) : PrimeWindow K where
  length := (1 / 6 : ℝ) / g.slots
  length_pos := div_pos (by norm_num) (by exact_mod_cast g.slots_pos)
  profile _ y := (g.weight i).toFun y
  support _ P := analyticPrimeSupport K (g.weight i).toFun P
  support_spec _ P p := analyticPrimeSupport_spec K _ (g.support_annular i) P p

def momentPrimeGeometry (g : PrimeWindowGeometry) : SlotGeometry K where
  slotCount := g.slots
  slots := analyticMomentPrimeWindow K g

theorem momentPrimeGeometry_totalLength (g : PrimeWindowGeometry) :
    (momentPrimeGeometry K g).totalLength = 1 / 6 := by
  have hJ : (g.slots : ℝ) ≠ 0 := by exact_mod_cast g.slots_pos.ne'
  change (∑ _ : Fin g.slots, (1 / 6 : ℝ) / g.slots) = 1 / 6
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem momentPrimeGeometry_fitsMesh (g : PrimeWindowGeometry) {mesh : ℝ}
    (hmesh : (1 / 6 : ℝ) / g.slots ≤ mesh) :
    (momentPrimeGeometry K g).fitsMesh mesh := fun _ => hmesh

theorem momentPrimeGeometry_disjoint (g : PrimeWindowGeometry) (i j : Fin g.slots)
    (hij : i ≠ j) (t t' : ℝ) :
    Disjoint (Function.support ((momentPrimeGeometry K g).slots i |>.profile t))
      (Function.support ((momentPrimeGeometry K g).slots j |>.profile t')) :=
  g.disjoint i j hij

variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- Exact arithmetic filtering: the analytic support is still the fixed
pretarget window, while the exterior and identity-ray restrictions remain. -/
theorem mem_physicalPrimeWindow_iff_analytic (g : PrimeWindowGeometry)
    (T : Finset (HeckeCharacter K)) (Z : ℝ) (i : Fin g.slots) (p : ExteriorPrime K S) :
    p ∈ primeWindow K S g T Z i ↔
      p.val ∈ (analyticMomentPrimeWindow K g i).support 0 (primeScale g Z) ∧
        ∀ χ ∈ T, primeCoefficient K χ p.val = 1 := by
  constructor
  · intro h
    obtain ⟨q, _hq, he⟩ := Finset.mem_image.mp h
    have hq := Finset.mem_filter.mp q.property
    have hv : q.val = p.val := congrArg Subtype.val he
    rw [hv] at hq
    exact ⟨Finset.mem_filter.mpr ⟨hq.1, hq.2.2.2⟩, hq.2.2.1⟩
  · rintro ⟨hp, hT⟩
    have hh := Finset.mem_filter.mp hp
    apply Finset.mem_image.mpr
    refine ⟨⟨p.val, Finset.mem_filter.mpr ⟨hh.1, p.property, hT, hh.2⟩⟩,
      Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

end HeckeGeneral.ThetaSkeleton.Physical
