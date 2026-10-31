import Expansion.ActualRowKernelHolomorphy
import Expansion.FiniteTripleContourTransport

/-!
# Actual finite transport from the initial three lines

The original arithmetic nonprincipal kernel is moved from (5,5,3) to
either outer contour.  The entire swept tube lies in its proved region of
holomorphy.  All six horizontal faces remain explicit actual integrals.
The small-row sum is over exactly the original fixed finite enumeration.
No contour equality or tail estimate is an input.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain Set MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
local notation "muS" => (fun p : Sset => mu (Subtype.val p))

/-- Three explicit pairs of actual horizontal faces, with the original
normalization; the fixed vertical destination is not part of this term. -/
def actualOuterHorizontalFaces
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (Z H sigma nuLine zLine : ℝ) : ℂ :=
  let F := compensatedRowMellinKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z
  (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
    (FiniteTripleContour.sFaces F H 5 sigma 5 3 +
      FiniteTripleContour.wFaces F H sigma 5 nuLine 3 +
        FiniteTripleContour.zFaces F H sigma nuLine 3 zLine)

include nu in
/-- The original initial box equals the requested outer box plus its
literal horizontal faces.  The only arithmetic zero premise is the
original common packet boundary. -/
theorem actual_outer_finite_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset) (hu : ¬principalFrequencyRow K Sset u)
    {B e Z H sigma nuLine zLine : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hZ : 0 < Z) (hH : 0 ≤ H)
    (hsigma : B + e ≤ sigma) (hnu : 1 / 2 ≤ nuLine) (hz : 17 / 50 ≤ zLine)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 5 5 3 -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H sigma nuLine zLine =
      actualOuterHorizontalFaces K S mu P psi g T u Z H sigma nuLine zLine := by
  let F := compensatedRowMellinKernel K Sset muS P psi
    (arithmeticHighEulerData K Sset P psi) g T u Z
  have hsubset : FiniteTripleContour.sweptTube 5 sigma 5 nuLine 3 zLine ⊆
      actualNonprincipalRowRegion B := by
    intro v hv
    have hs : B + e ≤ v.1.re :=
      (le_min (by linarith : B + e ≤ 5) hsigma).trans hv.1.1
    have hw : 1 / 2 ≤ v.2.1.re :=
      (le_min (by norm_num : (1 / 2 : ℝ) ≤ 5) hnu).trans hv.2.1.1
    have hz' : 17 / 50 ≤ v.2.2.re :=
      (le_min (by norm_num : (17 / 50 : ℝ) ≤ 3) hz).trans hv.2.2.1
    exact small_swept_mem_actualNonprincipalRowRegion hB he v.1 v.2.1 v.2.2 hs hw hz'
  have ha := (analyticOnNhd_actual_nonprincipal_kernel K S mu nu P omega psi hpsi hAllowed
    g T u hu (by linarith : 1 / 2 ≤ B) hZ hboundary).mono hsubset
  have hh := FiniteTripleContour.boxIntegral_sub_eq_faces F H 5 sigma 5 nuLine 3 zLine hH ha
  change _ * FiniteTripleContour.boxIntegral F H 5 5 3 -
    _ * FiniteTripleContour.boxIntegral F H sigma nuLine zLine = _
  rw [← mul_sub, hh]
  rfl

/-- The actual small-row horizontal term uses the same row set as the
original finiteRowContourBlock on both endpoint contours. -/
def actualSmallRowHorizontalFaces
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z H B e : ℝ) : ℂ :=
  ∑ u ∈ (frequencyRows K Sset (Z ^ (1 / 16 : ℝ))).filter
      (fun u => 0 < frequencyRowNorm K Sset u ∧ ¬principalFrequencyRow K Sset u),
    actualOuterHorizontalFaces K S mu P psi g T u Z H (B + e) (1 / 2) (17 / 50)

include nu in
/-- Exact finite small-row transport, retaining every original row and
the real horizontal face sum. -/
theorem actual_small_initial_finite_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    {B e Z H : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hZ : 0 < Z) (hH : 0 ≤ H)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H 0 (Z ^ (1 / 16 : ℝ)) 5 5 3 -
      finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T Z H 0 (Z ^ (1 / 16 : ℝ)) (B + e) (1 / 2) (17 / 50) =
      actualSmallRowHorizontalFaces K S mu P psi g T Z H B e := by
  unfold finiteRowContourBlock actualSmallRowHorizontalFaces
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  exact actual_outer_finite_transport K S mu nu P omega psi hpsi hAllowed g T u
    (Finset.mem_filter.mp hu).2.2 hB hB1 he he1 hZ hH le_rfl le_rfl le_rfl hboundary

theorem frequencyRowNorm_of_principal (u : FrequencyRow K Sset)
    (hu : principalFrequencyRow K Sset u) : frequencyRowNorm K Sset u = 1 := by
  change idealNorm K u.ideal.val = 1
  rw [hu.1]
  simp [idealNorm]

include nu in
/-- Every genuine large-tail row is nonprincipal.  Thus its full initial
box transports to (2,2,1+3/zeta) without a numerator residue. -/
theorem actual_large_row_initial_finite_transport [IsTotallyComplex K]
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K) (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K Sset)
    {B e zeta Z H : ℝ} (hB : 7 / 8 < B) (hB1 : B ≤ 1)
    (he : 0 < e) (he1 : e < 1 / 1000) (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 0 ≤ H)
    (hu : Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 5 5 3 -
      rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g T u Z H 2 2 (1 + 3 / zeta) =
      actualOuterHorizontalFaces K S mu P psi g T u Z H 2 2 (1 + 3 / zeta) := by
  have hu1 : 1 < frequencyRowNorm K Sset u :=
    (Real.one_le_rpow hZ (by linarith : (0 : ℝ) ≤ 13 / 16 + zeta)).trans_lt hu
  have hnon : ¬principalFrequencyRow K Sset u := by
    intro hp
    rw [frequencyRowNorm_of_principal K S u hp] at hu1
    exact (lt_irrefl (1 : ℝ)) hu1
  apply actual_outer_finite_transport K S mu nu P omega psi hpsi hAllowed g T u hnon
    hB hB1 he he1 (zero_lt_one.trans_le hZ) hH (by linarith) (by norm_num) _ hboundary
  have hq : 0 < 3 / zeta := div_pos (by norm_num) hzeta
  linarith

end Expansion.Project

#print axioms Expansion.Project.actual_outer_finite_transport
#print axioms Expansion.Project.actual_small_initial_finite_transport
#print axioms Expansion.Project.actual_large_row_initial_finite_transport
