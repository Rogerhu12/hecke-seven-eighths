import Expansion.PhysicalInitialMellinAbsolute

/-!
# The original physical probe equals the initial triple Mellin integral

This is the full literal physical identity.  Original Haar integration,
completed theta ideals, finite Fourier coefficients, all frequency rows
and all amplifier ideals are connected before any contour deformation.
Both reindexing and integral/series interchange use the actual proved
absolute majorants; there is no remainder defined by subtraction.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.PhysicalInitialMellin

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open Expansion.Project Expansion.PhysicalInitialHeight
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "EIdeal" => ExteriorIdeal K Sset
local notation "CN" => EIdeal × EIdeal

abbrev PhysicalPoissonIndex := EIdeal × (CN × (FrequencyRow K Sset × EIdeal))

/-- Only reassociation and permutation of the original five indices. -/
def physicalPoissonIndexEquiv : PhysicalPoissonIndex K S ≃ PhysicalInitialIndex K S where
  toFun x := (x.2.2.1, (x.2.1, (x.1, x.2.2.2)))
  invFun y := (y.2.2.1, (y.2.1, (y.1, y.2.2.2)))
  left_inv x := by rcases x with ⟨d, cn, u, r⟩; rfl
  right_inv y := by rcases y with ⟨u, cn, d, r⟩; rfl

variable [IsTotallyComplex K]
  [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
  [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include ν μ in
theorem physicalProbe_eq_sum_physicalPoissonTerm (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      ∑' i : PhysicalInitialIndex K S, physicalPoissonTerm K S μv P ψ Q X Y Z hX i.1 i.2 := by
  let f : PhysicalInitialIndex K S → ℂ := fun i =>
    physicalPoissonTerm K S μv P ψ Q X Y Z hX i.1 i.2
  have hf : Summable f :=
    (summable_norm_physicalPoissonTerm K S μv ν P ψ Q X Y Z hX hY hZ).of_norm
  have he : Summable (fun x : PhysicalPoissonIndex K S => f (physicalPoissonIndexEquiv K S x)) :=
    hf.comp_injective (physicalPoissonIndexEquiv K S).injective
  have hgroup :
      (∑' x : PhysicalPoissonIndex K S, f (physicalPoissonIndexEquiv K S x)) =
        ∑' den : EIdeal, ∑' cn : CN, ∑' u : FrequencyRow K Sset, ∑' r : EIdeal,
          physicalPoissonTerm K S μv P ψ Q X Y Z hX u (cn, (den, r)) := by
    rw [he.tsum_prod]
    apply tsum_congr
    intro den
    rw [(he.prod_factor den).tsum_prod]
    apply tsum_congr
    intro cn
    exact ((he.prod_factor den).prod_factor cn).tsum_prod
  calc
    physicalProbe K Sset P ψ Q X Y Z =
        ∑' den : EIdeal, ∑' cn : CN, ∑' u : FrequencyRow K Sset, ∑' r : EIdeal,
          physicalPoissonTerm K S μv P ψ Q X Y Z hX u (cn, (den, r)) := by
      rw [physicalProbe_eq_completedFrequencyProfiles K S μv ν μ P hzero ψ Q X Y Z hX hY hZ]
      simp only [physicalPoissonTerm, mul_assoc, tsum_mul_left]
    _ = ∑' x : PhysicalPoissonIndex K S, f (physicalPoissonIndexEquiv K S x) := hgroup.symm
    _ = _ := (physicalPoissonIndexEquiv K S).tsum_eq f

include ν μ in
/-- The actual physical probe, before finite prime-window compensation,
equals the absolute initial Mellin integral on (s,w,z)=(5,5,3). -/
theorem physicalProbe_eq_initial_joint_integral (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, ∑' i : PhysicalInitialIndex K S,
        physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t := by
  rw [physicalProbe_eq_sum_physicalPoissonTerm K S μv ν μ P hzero ψ Q X Y Z hX hY hZ]
  simp_rw [physicalPoissonTerm_eq_initial_integral K S μv ν P ψ Q X Y Z hX hY hZ]
  rw [tsum_mul_left, (physicalInitial_sum_integral_interchange K S μv ν P ψ Q X Y Z hX hY hZ).2]

theorem physicalInitial_joint_sum_eq_rows (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ) (t : Fin 3 → ℝ) :
    (∑' i : PhysicalInitialIndex K S, physicalInitialMellinTerm K S μv P ψ Q X Y Z i.1 i.2 t) =
      ∑' u : FrequencyRow K Sset, physicalInitialRowKernel K S μv P ψ Q X Y Z u
        (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) := by
  rw [((summable_norm_physicalInitialMellinTerm K S μv P ψ Q X Y Z t).of_norm).tsum_prod]
  exact tsum_congr (fun u => (physicalInitialRowKernel_eq_tsum K S μv P ψ Q X Y Z u t).symm)

include ν in
theorem integrable_physicalInitial_row_sum (P : ProbeData K Sset) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K Sset)) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (fun t : Fin 3 → ℝ => ∑' u : FrequencyRow K Sset,
      physicalInitialRowKernel K S μv P ψ Q X Y Z u
        (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2))) := by
  simpa only [physicalInitial_joint_sum_eq_rows] using
    (physicalInitial_sum_integral_interchange K S μv ν P ψ Q X Y Z hX hY hZ).1

include ν μ in
theorem physicalProbe_eq_initial_rows (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      tripleMellinConstant * ∫ t : Fin 3 → ℝ, ∑' u : FrequencyRow K Sset,
        physicalInitialRowKernel K S μv P ψ Q X Y Z u
          (idealVerticalPoint 5 (t 0)) (idealVerticalPoint 5 (t 1)) (idealVerticalPoint 3 (t 2)) := by
  rw [physicalProbe_eq_initial_joint_integral K S μv ν μ P hzero ψ Q X Y Z hX hY hZ]
  simp only [physicalInitial_joint_sum_eq_rows]

include ν μ in
/-- The three original vertical integrations, in the order used by
rowContourBox.  This follows from proved three-dimensional integrability. -/
theorem physicalProbe_eq_initial_iterated_rows (P : ProbeData K Sset)
    (hzero : additiveFourierAtZero K Sset (fun v => μv v.val) P.additive = 0)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K Sset))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    physicalProbe K Sset P ψ Q X Y Z =
      tripleMellinConstant * ∫ ts : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, ∑' u : FrequencyRow K Sset,
        physicalInitialRowKernel K S μv P ψ Q X Y Z u
          (idealVerticalPoint 5 ts) (idealVerticalPoint 5 tw) (idealVerticalPoint 3 tz) := by
  rw [physicalProbe_eq_initial_rows K S μv ν μ P hzero ψ Q X Y Z hX hY hZ]
  rw [integral_eq_initial_order _
    (integrable_physicalInitial_row_sum K S μv ν P ψ Q X Y Z hX hY hZ)]
  rfl

end Expansion.PhysicalInitialMellin

#print axioms Expansion.PhysicalInitialMellin.physicalProbe_eq_initial_iterated_rows
