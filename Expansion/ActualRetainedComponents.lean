import Expansion.ActualSmallRowBound
import Expansion.ActualLargeRowBound
import Expansion.ActualPrincipalVerticalRemainders
import Expansion.ActualPrincipalSlotRemainder

/-!
# The actual retained principal, small, and large components

The principal component is the sum of the two literal vertical residue
remainders and the original compensated slot remainder.  The small component
is the original finite row contour block, and the large component is the
genuinely summable original strict tail on its fixed absolute contours.

The common loss is allocated before the scale and height.  In particular,
the W remainder's coefficient 29/16 on the contour displacement is absorbed
by e <= lamB/1000.  The final bounds use precisely the three exponents in
the expansion contract.  No retained component is defined by an error
identity, and no estimate on a retained component is an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.Expansion.LargeRows
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
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

/-- The three actual principal remainders on their retained contours. -/
def actualPrincipalRetained (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  actualPrincipalWRemainder K S mu P psi g Z H B e +
    actualPrincipalZRemainder K S mu P psi g Z H B e +
    actualPrincipalSlotRemainder K Sset P psi g Z H (B + e)

/-- The original small-row block, with its original open lower endpoint. -/
def actualSmallRetained (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H B e : ℝ) : ℂ :=
  finiteRowContourBlock K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
    g ∅ Z H 0 (Z ^ (1 / 16 : ℝ)) (B + e) (1 / 2) (17 / 50)

/-- A literal row in the strict large tail, retaining every sector. -/
def actualLargeRetainedTerm (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H zeta : ℝ) (u : FrequencyRow K Sset) : ℂ :=
  if Z ^ (13 / 16 + zeta) < frequencyRowNorm K Sset u then
    rowContourBox K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
      g ∅ u Z H 2 2 (1 + 3 / zeta)
  else 0

/-- The actual large-row sum, whose absolute convergence is proved below. -/
def actualLargeRetained (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H zeta : ℝ) : ℂ :=
  ∑' u, actualLargeRetainedTerm K S mu P psi g Z H zeta u

theorem norm_actualLargeRetainedTerm (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (g : PrimeWindowGeometry) (Z H zeta : ℝ) (u : FrequencyRow K Sset) :
    ‖actualLargeRetainedTerm K S mu P psi g Z H zeta u‖ =
      absoluteLargeRowTerm K Sset muS P psi (arithmeticHighEulerData K Sset P psi)
        g ∅ Z H zeta (1 + 3 / zeta) u := by
  unfold actualLargeRetainedTerm absoluteLargeRowTerm
  split_ifs <;> simp

include nu in
/-- Absolute convergence is available at every original scale Z >= 1,
independently of the eventual numerical cutoff. -/
theorem summable_norm_actualLargeRetainedTerm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    {zeta Z H : ℝ} (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Summable (fun u => ‖actualLargeRetainedTerm K S mu P psi g Z H zeta u‖) := by
  have hsigma : 1 < 1 + 3 / zeta := by
    have hq : 0 < 3 / zeta := div_pos (by norm_num) hzeta
    linarith
  simpa only [norm_actualLargeRetainedTerm] using
    summable_actual_absoluteLargeRowTerm K S mu nu hcomplex P psi g ∅
      hsigma zeta Z H hZ hH

include nu in
theorem summable_actualLargeRetainedTerm
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    {zeta Z H : ℝ} (hzeta : 0 < zeta) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Summable (actualLargeRetainedTerm K S mu P psi g Z H zeta) :=
  (summable_norm_actualLargeRetainedTerm K S mu nu hcomplex P psi g hzeta hZ hH).of_norm

private theorem retained_monomial_mono {C D Z H x y a b : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hZ : 1 ≤ Z) (hH : 1 ≤ H)
    (hxy : x ≤ y) (hab : a ≤ b) :
    C * Z ^ x * (1 + H) ^ a ≤ D * Z ^ y * (1 + H) ^ b := by
  have hD : 0 ≤ D := hC.trans hCD
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hH1 : 1 ≤ 1 + H := by linarith
  have hH0 : 0 ≤ 1 + H := zero_le_one.trans hH1
  exact mul_le_mul
    (mul_le_mul hCD (Real.rpow_le_rpow_of_exponent_le hZ hxy)
      (Real.rpow_nonneg hZ0 _) hD)
    (Real.rpow_le_rpow_of_exponent_le hH1 hab)
    (Real.rpow_nonneg hH0 _) (mul_nonneg hD (Real.rpow_nonneg hZ0 _))

include nu in
/-- The principal contract with its three distinct original savings. -/
theorem exists_actual_principalRetained_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e lamB : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hlam : 0 < lamB) (hecap : e ≤ lamB / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ‖actualPrincipalRetained K S mu P psi g Z H B e‖ ≤
        C * (Z ^ (B - 11 / 16 - 23 / 960 + lamB) +
          Z ^ (B - 11 / 16 - 13 / 9600 + lamB) +
          Z ^ (B - 11 / 16 - principalSlotSaving g + lamB)) * (1 + H) ^ A := by
  have heta : 0 < lamB / 2 := by linarith
  obtain ⟨Cw, Zw, Aw, hCw, hZw, hAw, hw⟩ :=
    exists_actual_principalW_remainder_bound K S mu nu hcomplex P omega psi hpsi
      hAllowed hunram g hB hB1 he he1 heta hboundary
  obtain ⟨Cz, Zz, Az, hCz, hZz, hAz, hz⟩ :=
    exists_actual_principalZ_remainder_bound K S mu nu hcomplex P omega psi hpsi
      hunram g hB hB1 he he1 heta hboundary
  obtain ⟨Cs, Zs, As, hCs, hZs, hAs, hs⟩ :=
    exists_actual_principalSlot_remainder_bound K Sset hcomplex P omega psi hpsi g
      hunram hB hB1 he he1 heta hboundary
  let C : ℝ := Cw + Cz + Cs
  let A : ℝ := Aw + Az + As
  have hC : 0 < C := by dsimp [C]; linarith
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hwloss : (29 / 16) * e + lamB / 2 ≤ lamB := by linarith
  have hsloss : e + lamB / 2 ≤ lamB := by linarith
  refine ⟨C, max Zw (max Zz Zs), A, hC, hZw.trans (le_max_left _ _), hA, ?_⟩
  intro Z H hZ hH
  have hwZ : Zw ≤ Z := (le_max_left _ _).trans hZ
  have hzZ : Zz ≤ Z := (le_max_left Zz Zs).trans ((le_max_right _ _).trans hZ)
  have hsZ : Zs ≤ Z := (le_max_right Zz Zs).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 ≤ Z := hZw.trans hwZ
  have hw' : ‖actualPrincipalWRemainder K S mu P psi g Z H B e‖ ≤
      C * Z ^ (B - 11 / 16 - 23 / 960 + lamB) * (1 + H) ^ A :=
    (hw Z H hwZ hH).trans (retained_monomial_mono hCw.le
      (by dsimp [C]; linarith) hZ1 hH (by linarith) (by dsimp [A]; linarith))
  have hz' : ‖actualPrincipalZRemainder K S mu P psi g Z H B e‖ ≤
      C * Z ^ (B - 11 / 16 - 13 / 9600 + lamB) * (1 + H) ^ A :=
    (hz Z H hzZ hH).trans (retained_monomial_mono hCz.le
      (by dsimp [C]; linarith) hZ1 hH (by linarith) (by dsimp [A]; linarith))
  have hs' : ‖actualPrincipalSlotRemainder K Sset P psi g Z H (B + e)‖ ≤
      C * Z ^ (B - 11 / 16 - principalSlotSaving g + lamB) * (1 + H) ^ A :=
    (hs Z H hsZ hH).trans (retained_monomial_mono hCs.le
      (by dsimp [C]; linarith) hZ1 hH (by linarith) (by dsimp [A]; linarith))
  unfold actualPrincipalRetained
  calc
    _ ≤ ‖actualPrincipalWRemainder K S mu P psi g Z H B e +
        actualPrincipalZRemainder K S mu P psi g Z H B e‖ +
        ‖actualPrincipalSlotRemainder K Sset P psi g Z H (B + e)‖ := norm_add_le _ _
    _ ≤ ‖actualPrincipalWRemainder K S mu P psi g Z H B e‖ +
        ‖actualPrincipalZRemainder K S mu P psi g Z H B e‖ +
        ‖actualPrincipalSlotRemainder K Sset P psi g Z H (B + e)‖ :=
      add_le_add_right (norm_add_le _ _) _
    _ ≤ C * Z ^ (B - 11 / 16 - 23 / 960 + lamB) * (1 + H) ^ A +
        C * Z ^ (B - 11 / 16 - 13 / 9600 + lamB) * (1 + H) ^ A +
        C * Z ^ (B - 11 / 16 - principalSlotSaving g + lamB) * (1 + H) ^ A :=
      add_le_add (add_le_add hw' hz') hs'
    _ = _ := by ring

include nu in
/-- The actual small block with the expansion contract's full common loss. -/
theorem exists_actual_smallRetained_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e lamB : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hlam : 0 < lamB) (hecap : e ≤ lamB / 1000)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ‖actualSmallRetained K S mu P psi g Z H B e‖ ≤
        C * Z ^ (B - 11 / 16 - 1 / 50 + lamB) * (1 + H) ^ A := by
  obtain ⟨C, Z0, A, hC, hZ0, hA, hb⟩ :=
    exists_actual_small_block_bound K S mu nu hcomplex P omega psi hpsi hAllowed
      hcal hunram g (loss := lamB / 2) hB hB1 he he1 (by linarith) hboundary
  refine ⟨C, Z0, A, hC, hZ0, hA, ?_⟩
  intro Z H hZ hH
  exact (hb Z H hZ hH).trans
    (retained_monomial_mono hC.le le_rfl (hZ0.trans hZ) hH (by linarith) le_rfl)

include nu in
/-- The original large component satisfies the stated target exponent;
the proved absolute estimate in fact has the stronger power Z^(-1/2). -/
theorem exists_actual_largeRetained_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B lamB zeta : ℝ}
    (hB : 7 / 8 < B) (hlam : 0 < lamB) (hzeta : 0 < zeta) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ,
      Z0 ≤ Z → 1 ≤ H → ‖actualLargeRetained K S mu P psi g Z H zeta‖ ≤
        C * Z ^ (B - 11 / 16 - 63 / 800 + lamB) * (1 + H) ^ A := by
  obtain ⟨C, Z0, hC, hZ0, hb⟩ :=
    exists_actual_large_tail_bound K S mu nu hcomplex P psi hcal hunram g hzeta
  refine ⟨C, Z0, 3, hC, hZ0, by norm_num, ?_⟩
  intro Z H hZ hH
  have hn := summable_norm_actualLargeRetainedTerm K S mu nu hcomplex P psi g
    hzeta (hZ0.trans hZ) hH
  calc
    _ ≤ ∑' u, ‖actualLargeRetainedTerm K S mu P psi g Z H zeta u‖ :=
      norm_tsum_le_tsum_norm hn
    _ = ∑' u, absoluteLargeRowTerm K Sset muS P psi
        (arithmeticHighEulerData K Sset P psi) g ∅ Z H zeta (1 + 3 / zeta) u := by
      apply tsum_congr
      intro u
      exact norm_actualLargeRetainedTerm K S mu P psi g Z H zeta u
    _ ≤ C * Z ^ (-(1 / 2 : ℝ)) * (1 + H) ^ (3 : ℕ) := hb Z H hZ hH
    _ = C * Z ^ (-(1 / 2 : ℝ)) * (1 + H) ^ (3 : ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ C * Z ^ (B - 11 / 16 - 63 / 800 + lamB) * (1 + H) ^ (3 : ℝ) :=
      retained_monomial_mono hC.le le_rfl (hZ0.trans hZ) hH (by linarith) le_rfl

include nu in
/-- One scale cutoff, one positive constant, and one nonnegative height
degree work for all three retained components, before Z and H are chosen. -/
theorem exists_actual_retained_components_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (P : ProbeData K Sset) (omega psi : HeckeCharacter K)
    (hpsi : psi ∈ HeckePacket K omega)
    (hAllowed : AllowedGeneratorInput K Sset P.arithmetic)
    (hcal : ThetaCalibrationInput K Sset P.arithmetic P.Lambda P.G)
    (hunram : ∀ p : ExteriorPrime K Sset, UnramifiedAt K psi p.val)
    (g : PrimeWindowGeometry) {B e lamB zeta : ℝ}
    (hB : 7 / 8 < B) (hB1 : B ≤ 1) (he : 0 < e) (he1 : e < 1 / 1000)
    (hlam : 0 < lamB) (hecap : e ≤ lamB / 1000) (hzeta : 0 < zeta)
    (hboundary : ∀ chi : HeckePacketIndex K omega,
      ∀ r ∈ heckePacketZeros K omega chi, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) :
    ∃ C Z0 A : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ 0 ≤ A ∧ ∀ Z H : ℝ, Z0 ≤ Z → 1 ≤ H →
      (‖actualPrincipalRetained K S mu P psi g Z H B e‖ ≤
        C * (Z ^ (B - 11 / 16 - 23 / 960 + lamB) +
          Z ^ (B - 11 / 16 - 13 / 9600 + lamB) +
          Z ^ (B - 11 / 16 - principalSlotSaving g + lamB)) * (1 + H) ^ A) ∧
      (‖actualSmallRetained K S mu P psi g Z H B e‖ ≤
        C * Z ^ (B - 11 / 16 - 1 / 50 + lamB) * (1 + H) ^ A) ∧
      (‖actualLargeRetained K S mu P psi g Z H zeta‖ ≤
        C * Z ^ (B - 11 / 16 - 63 / 800 + lamB) * (1 + H) ^ A) := by
  obtain ⟨Cp, Zp, Ap, hCp, hZp, hAp, hp⟩ :=
    exists_actual_principalRetained_bound K S mu nu hcomplex P omega psi hpsi hAllowed
      hunram g hB hB1 he he1 hlam hecap hboundary
  obtain ⟨Cs, Zs, As, hCs, hZs, hAs, hs⟩ :=
    exists_actual_smallRetained_bound K S mu nu hcomplex P omega psi hpsi hAllowed
      hcal hunram g hB hB1 he he1 hlam hecap hboundary
  obtain ⟨Cl, Zl, Al, hCl, hZl, hAl, hl⟩ :=
    exists_actual_largeRetained_bound K S mu nu hcomplex P psi hcal hunram g hB hlam hzeta
  let C : ℝ := Cp + Cs + Cl
  let A : ℝ := Ap + As + Al
  have hC : 0 < C := by dsimp [C]; linarith
  have hA : 0 ≤ A := by dsimp [A]; linarith
  refine ⟨C, max Zp (max Zs Zl), A, hC, hZp.trans (le_max_left _ _), hA, ?_⟩
  intro Z H hZ hH
  have hpZ : Zp ≤ Z := (le_max_left _ _).trans hZ
  have hsZ : Zs ≤ Z := (le_max_left Zs Zl).trans ((le_max_right _ _).trans hZ)
  have hlZ : Zl ≤ Z := (le_max_right Zs Zl).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 ≤ Z := hZp.trans hpZ
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ1
  have hH1 : 1 ≤ 1 + H := by linarith
  have hH0 : 0 ≤ 1 + H := zero_le_one.trans hH1
  refine ⟨?_, ?_, ?_⟩
  · apply (hp Z H hpZ hH).trans
    have hCpC : Cp ≤ C := by dsimp [C]; linarith
    have hApA : Ap ≤ A := by dsimp [A]; linarith
    have hsum : 0 ≤ Z ^ (B - 11 / 16 - 23 / 960 + lamB) +
        Z ^ (B - 11 / 16 - 13 / 9600 + lamB) +
        Z ^ (B - 11 / 16 - principalSlotSaving g + lamB) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCpC hsum)
      (Real.rpow_le_rpow_of_exponent_le hH1 hApA)
      (Real.rpow_nonneg hH0 _) (mul_nonneg hC.le hsum)
  · exact (hs Z H hsZ hH).trans (retained_monomial_mono hCs.le
      (by dsimp [C]; linarith) hZ1 hH le_rfl (by dsimp [A]; linarith))
  · exact (hl Z H hlZ hH).trans (retained_monomial_mono hCl.le
      (by dsimp [C]; linarith) hZ1 hH le_rfl (by dsimp [A]; linarith))

end Expansion.Project

#print axioms Expansion.Project.summable_norm_actualLargeRetainedTerm
#print axioms Expansion.Project.summable_actualLargeRetainedTerm
#print axioms Expansion.Project.exists_actual_principalRetained_bound
#print axioms Expansion.Project.exists_actual_smallRetained_bound
#print axioms Expansion.Project.exists_actual_largeRetained_bound
#print axioms Expansion.Project.exists_actual_retained_components_bound
