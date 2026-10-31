import Expansion.ActualPrincipalKernelBound
import HeckeSkeleton.ExpansionModels.SmallRowSum

/-!
# The two actual vertical principal remainders

These are the literal triple integral on (B+e,19/20,1/6+e) and the
w-residue double integral on (B+e,33/200).  Their savings are respectively
23/960 and 13/9600.  They are principal remainders, not height-decaying
horizontal errors.  All constants and degrees precede both Z and height.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.SmallRows
open ExpansionInterfaces.Mellin
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
local notation "muS" => (fun p : Sset => mu p.val)

def actualPrincipalWRemainder (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
    g ∅ (physicalPrincipalRow K Sset) Z H (B + e) (19 / 20) (1 / 6 + e)

/-- The w=1 residue kernel, before moving its z line. -/
def actualPrincipalWResidueKernel (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z : ℝ) (s z : ℂ) : ℂ :=
  actualPrincipalKernelCore K S mu P psi g Z s 1 z (deletedZetaResidue K Sset)

def actualPrincipalZRemainder (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (-(2 : ℤ)) *
    ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H,
      actualPrincipalWResidueKernel K S mu P psi g Z
        (vertical (B + e) ts) (vertical (33 / 200) tz)

private theorem height_volume_power_bound (H A : ℝ) (n : ℕ) (hH : 0 ≤ H) :
    (2 * H) ^ n * (1 + H) ^ A ≤ (2 : ℝ) ^ n * (1 + H) ^ (A + n) := by
  have hp : 0 < 1 + H := by linarith
  calc
    _ ≤ (2 * (1 + H)) ^ n * (1 + H) ^ A := by gcongr; linarith
    _ = _ := by rw [mul_pow, Real.rpow_add hp, Real.rpow_natCast]; ring

include nu in
theorem exists_actual_principalW_remainder_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e eta : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ‖actualPrincipalWRemainder K S mu P psi g Z H B e‖ ≤
        C * Z ^ (B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta) * (1 + H) ^ A := by
  obtain ⟨Cw, kw, hCw, hkw, hw⟩ := exists_actual_deletedZeta_line_bound K Sset hcomplex
    (19 / 20) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, Z0, A, hC, hZ0, hA, hcore⟩ := exists_actual_principalCore_bound K S mu nu
    hcomplex P omega psi hpsi hunram g (eta := eta) (wLine := 19 / 20)
    (zLine := 1 / 6 + e) hB hB1 he he1 heta (by norm_num) (by linarith)
    (by linarith) (by nlinarith)
    hboundary (heckeDeletedContinuation K 1 (exceptionalPrimes K Sset)) Cw kw hCw hkw hw
  let Cline : ℝ := (2 * Real.pi) ^ (-(3 : ℤ))
  have hCline : 0 < Cline := by dsimp [Cline]; positivity
  refine ⟨Cline * 8 * C, Z0, A + 3, by positivity, hZ0, by linarith, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hexp : B + e - 79 / 96 + (13 / 16) * (1 / 6 + e) +
      (23 / 48) * ((19 / 20) - 1) + eta =
      B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta := by ring
  have hb : ‖actualPrincipalWRemainder K S mu P psi g Z H B e‖ ≤
      Cline * (2 * H) ^ 3 *
        (C * Z ^ (B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta) * (1 + H) ^ A) := by
    apply norm_actual_rowContourBox_le K S mu P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ (physicalPrincipalRow K Sset) Z H (B + e) (19 / 20) (1 / 6 + e) hH0
    intro ts hts tw htw tz htz
    unfold rowKernelOnLines
    rw [actualPrincipalKernel_eq_core K S mu P psi hAllowed g Z hZpos]
    have hc := hcore Z H hZ hH ((B + e : ℝ) + (ts : ℂ) * Complex.I)
      ((19 / 20 : ℝ) + (tw : ℂ) * Complex.I)
      ((1 / 6 + e : ℝ) + (tz : ℂ) * Complex.I)
      (by simp) (by simp) (by simp)
      (by simpa using (abs_le.mpr hts : |ts| ≤ H))
      (by simpa using (abs_le.mpr htw : |tw| ≤ H))
      (by simpa using (abs_le.mpr htz : |tz| ≤ H))
    simpa only [hexp] using hc
  calc
    _ ≤ Cline * (2 * H) ^ 3 *
        (C * Z ^ (B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta) * (1 + H) ^ A) := hb
    _ = (Cline * C * Z ^ (B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta)) *
        ((2 * H) ^ 3 * (1 + H) ^ A) := by ring
    _ ≤ (Cline * C * Z ^ (B - 11 / 16 - 23 / 960 + (29 / 16) * e + eta)) *
        (2 ^ (3 : ℕ) * (1 + H) ^ (A + 3)) :=
      mul_le_mul_of_nonneg_left (height_volume_power_bound H A 3 hH0) (by positivity)
    _ = _ := by ring

include nu in
theorem exists_actual_principalZ_remainder_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e eta : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (heta : 0 < eta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ‖actualPrincipalZRemainder K S mu P psi g Z H B e‖ ≤
        C * Z ^ (B - 11 / 16 - 13 / 9600 + e + eta) * (1 + H) ^ A := by
  let R : ℂ := deletedZetaResidue K Sset
  have hR : ∀ w : ℂ, w.re = 1 → ‖R‖ ≤ (‖R‖ + 1) * (2 + |w.im|) ^ (0 : ℝ) := by
    intro w _
    simp only [Real.rpow_zero, mul_one]
    linarith
  obtain ⟨C, Z0, A, hC, hZ0, hA, hcore⟩ := exists_actual_principalCore_bound K S mu nu
    hcomplex P omega psi hpsi hunram g (eta := eta) (wLine := 1)
    (zLine := 33 / 200) hB hB1 he he1 heta (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hboundary (fun _ => R) (‖R‖ + 1) 0
    (by positivity) (by norm_num) hR
  let Cline : ℝ := (2 * Real.pi) ^ (-(2 : ℤ))
  have hCline : 0 < Cline := by dsimp [Cline]; positivity
  refine ⟨Cline * 4 * C, Z0, A + 2, by positivity, hZ0, by linarith, ?_⟩
  intro Z H hZ hH
  have hZpos : 0 < Z := zero_lt_one.trans_le (hZ0.trans hZ)
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hexp : B + e - 79 / 96 + (13 / 16) * (33 / 200) +
      (23 / 48) * (1 - 1) + eta = B - 11 / 16 - 13 / 9600 + e + eta := by ring
  let b : ℝ := C * Z ^ (B - 11 / 16 - 13 / 9600 + e + eta) * (1 + H) ^ A
  let F : ℝ → ℝ → ℂ := fun ts tz => actualPrincipalWResidueKernel K S mu P psi g Z
    (vertical (B + e) ts) (vertical (33 / 200) tz)
  have hpoint : ∀ ts ∈ Icc (-H) H, ∀ tz ∈ Icc (-H) H, ‖F ts tz‖ ≤ b := by
    intro ts hts tz htz
    have hc := hcore Z H hZ hH (vertical (B + e) ts) 1 (vertical (33 / 200) tz)
      (by simp) (by simp) (by simp) (by simpa using (abs_le.mpr hts : |ts| ≤ H))
      (by simpa using hH0) (by simpa using (abs_le.mpr htz : |tz| ≤ H))
    simpa only [hexp] using hc
  have hfinite : volume (Icc (-H) H) < ⊤ := isCompact_Icc.measure_lt_top
  have hvol : volume.real (Icc (-H) H) = 2 * H := by
    rw [Real.volume_real_Icc_of_le (by linarith : -H ≤ H)]
    ring
  have hzint : ∀ ts ∈ Icc (-H) H, ‖∫ tz in Icc (-H) H, F ts tz‖ ≤ b * (2 * H) := by
    intro ts hts
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite (hpoint ts hts)
  have hsint : ‖∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, F ts tz‖ ≤
      (b * (2 * H)) * (2 * H) := by
    simpa only [hvol] using norm_setIntegral_le_of_norm_le_const hfinite hzint
  have hfactor : ‖(2 * (Real.pi : ℂ)) ^ (-(2 : ℤ))‖ = Cline := by
    simp only [Cline, norm_zpow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  change ‖(2 * (Real.pi : ℂ)) ^ (-(2 : ℤ)) *
    ∫ ts in Icc (-H) H, ∫ tz in Icc (-H) H, F ts tz‖ ≤ _
  rw [norm_mul, hfactor]
  calc
    _ ≤ Cline * ((b * (2 * H)) * (2 * H)) :=
      mul_le_mul_of_nonneg_left hsint hCline.le
    _ = (Cline * C * Z ^ (B - 11 / 16 - 13 / 9600 + e + eta)) *
        ((2 * H) ^ 2 * (1 + H) ^ A) := by dsimp only [b]; ring
    _ ≤ (Cline * C * Z ^ (B - 11 / 16 - 13 / 9600 + e + eta)) *
        (2 ^ (2 : ℕ) * (1 + H) ^ (A + 2)) :=
      mul_le_mul_of_nonneg_left (height_volume_power_bound H A 2 hH0) (by positivity)
    _ = _ := by ring

end Expansion.Project

#print axioms Expansion.Project.exists_actual_principalW_remainder_bound
#print axioms Expansion.Project.exists_actual_principalZ_remainder_bound
