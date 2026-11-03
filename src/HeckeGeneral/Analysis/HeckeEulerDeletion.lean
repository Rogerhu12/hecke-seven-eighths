import HeckeGeneral.Analysis.HeckeNormPole
import HeckeGeneral.Analysis.EulerFactors
import HeckeGeneral.Analysis.MellinZeroDetector

/-!

Actual finite Euler deletion for the existing Hecke continuation.  The
local coefficients are `primeCoefficient`, including their ramified zero
extension, and the local cardinalities are the actual `residueCard`.

This file consumes a deleted-continuation Mellin or reciprocal identity.
Identifying this deleted continuation with the source's S-excluded ideal
series on the initial convergence domain remains a separate obligation.
In particular no dyadic reciprocal, physical probe, or theta transfer is
constructed here.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Characters Filter
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- The finite polynomial which deletes the actual local Euler factors. -/
def heckeEulerDeletionPolynomial (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℂ → ℂ :=
  finiteEulerPolynomial S (fun p => (residueCard K p : ℝ)) (primeCoefficient K χ)

theorem heckeEulerDeletionPolynomial_analyticAt (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    AnalyticAt ℂ (heckeEulerDeletionPolynomial K χ S) s := by
  apply finiteEulerPolynomial_analyticAt
  intro p _hp
  exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_residueCard K p)

theorem heckeEulerDeletionPolynomial_ne_zero (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) :
    heckeEulerDeletionPolynomial K χ S s ≠ 0 := by
  apply finiteEulerPolynomial_ne_zero
  · intro p _hp
    exact_mod_cast one_lt_residueCard K p
  · intro p _hp
    exact norm_primeCoefficient_le_one K χ p
  · exact hs

/-- This is a definition from the actual continuation.  Its equality to
the source's S-excluded ideal series has not been proved by this definition. -/
def heckeDeletedContinuation (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  heckeEulerDeletionPolynomial K χ S s * heckeContinuation K χ s

theorem meromorphicOn_heckeDeletedContinuation (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeromorphicOn (heckeDeletedContinuation K χ S) Set.univ := by
  intro s _hs
  exact (heckeEulerDeletionPolynomial_analyticAt K χ S s).meromorphicAt.mul
    (meromorphicOn_heckeContinuation K χ s (Set.mem_univ _))

/-- Positive-half-plane deletion also preserves order at norm poles. -/
theorem meromorphicOrderAt_heckeDeletedContinuation (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (heckeDeletedContinuation K χ S) s =
      meromorphicOrderAt (heckeContinuation K χ) s := by
  apply finite_euler_deletion_order_eq
  · intro p _hp
    exact_mod_cast one_lt_residueCard K p
  · intro p _hp
    exact norm_primeCoefficient_le_one K χ p
  · exact hs

/-- The endpoint b = 0 is also permitted because the half-plane is open. -/
theorem heckeDeletedContinuation_zeroFreeOn_iff (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {b : ℝ} (hb : 0 ≤ b) :
    MeromorphicZeroFreeOn (heckeDeletedContinuation K χ S) (rightHalfPlane b) ↔
      MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  apply finite_euler_deletion_zeroFreeOn_iff
  · intro p _hp
    exact_mod_cast one_lt_residueCard K p
  · intro p _hp
    exact norm_primeCoefficient_le_one K χ p
  · intro s hs
    exact lt_of_le_of_lt hb hs

/-- Keep the source numerator unchanged: first close the Mellin detector
for L^S, then remove the nonvanishing finite Euler polynomial. -/
theorem heckeContinuation_zeroFreeOn_of_deleted_initial_physicalMellin
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {f : ℝ → ℂ} {H : ℂ → ℂ} {b : ℝ} (hb : 0 ≤ b)
    (hf : PhysicalProbeBound f b)
    (hid : InitialMellinDetectorIdentity (heckeDeletedContinuation K χ S) f H b) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  apply (heckeDeletedContinuation_zeroFreeOn_iff K χ S hb).mp
  exact meromorphicZeroFreeOn_of_initial_physicalMellin
    (fun s _hs => meromorphicOn_heckeDeletedContinuation K χ S s (Set.mem_univ _))
    hf hid

/-- If G is the analytic reciprocal of L^S, then E_S G is the analytic
reciprocal of L.  This transformation needs no nonvanishing assertion for
E_S and keeps an initial punctured germ rather than dividing at a pole. -/
theorem heckeDeletedContinuation_reciprocal_to_full
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {G : ℂ → ℂ} {b : ℝ} (hG : AnalyticOnNhd ℂ G (rightHalfPlane b))
    {s₀ : ℂ}
    (hid : (fun w => heckeDeletedContinuation K χ S w * G w)
      =ᶠ[𝓝[≠] s₀] (fun _ => 1)) :
    AnalyticOnNhd ℂ (fun w => heckeEulerDeletionPolynomial K χ S w * G w)
        (rightHalfPlane b) ∧
      (fun w => heckeContinuation K χ w *
        (heckeEulerDeletionPolynomial K χ S w * G w))
        =ᶠ[𝓝[≠] s₀] (fun _ => 1) := by
  refine ⟨fun s hs => (heckeEulerDeletionPolynomial_analyticAt K χ S s).mul
    (hG s hs), ?_⟩
  filter_upwards [hid] with w hw
  change (heckeEulerDeletionPolynomial K χ S w * heckeContinuation K χ w) * G w = 1 at hw
  calc
    heckeContinuation K χ w * (heckeEulerDeletionPolynomial K χ S w * G w) =
        (heckeEulerDeletionPolynomial K χ S w * heckeContinuation K χ w) * G w := by ring
    _ = 1 := hw

/-- An initial deleted reciprocal identity gives full zero-freeness by
meromorphic identity propagation.  Its construction from the dyadic
ideal sums, with locally uniform seminorm control, remains outstanding. -/
theorem heckeContinuation_zeroFreeOn_of_deleted_initial_reciprocal
    (χ : HeckeCharacter K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {G : ℂ → ℂ} {b : ℝ} (hG : AnalyticOnNhd ℂ G (rightHalfPlane b))
    {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalfPlane b)
    (hid : (fun w => heckeDeletedContinuation K χ S w * G w)
      =ᶠ[𝓝[≠] s₀] (fun _ => 1)) :
    MeromorphicZeroFreeOn (heckeContinuation K χ) (rightHalfPlane b) := by
  obtain ⟨hfullG, hfullid⟩ := heckeDeletedContinuation_reciprocal_to_full K χ S hG hid
  have heq := meromorphic_germ_identity_of_preconnected
    (fun s hs => (meromorphicOn_heckeContinuation K χ s (Set.mem_univ _)).mul
      (hfullG s hs).meromorphicAt)
    (fun _ _ => (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) _).meromorphicAt)
    (isPreconnected_rightHalfPlane b) hs₀ hfullid
  refine ⟨fun s _hs => meromorphicOn_heckeContinuation K χ s (Set.mem_univ _), ?_⟩
  intro s hs
  exact order_nonpos_of_analytic_multiplier
    (meromorphicOn_heckeContinuation K χ s (Set.mem_univ _))
    (hfullG s hs) analyticAt_const (by norm_num : (1 : ℂ) ≠ 0) (heq s hs)

end HeckeGeneral.Analysis
