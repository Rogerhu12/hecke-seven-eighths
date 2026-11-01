import HeckeSkeleton.HighBinSupport.ActualPhysicalNormForm

/-!
# The norm form on the original scheduled physical recipe

This specialization reads the shell, bin, selected arithmetic rows,
physical samples and amplitudes from the existing recipe constructor.
No replacement recipe or assumed row estimate is introduced.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open Expansion.Project ExpansionInterfaces
open HeckeSkeleton.HighBinActualEuler HighBinVerified
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (mu : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (mu p).IsAddHaarMeasure]

theorem exists_physicalRecipe_normForm
    (P : ProbeData K S₀) (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsiUnram : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {B e width lam : ℝ} (hpsi : psi ∈ HeckePacket K omega)
    (hB0 : 51 / 100 ≤ B) (hB : B ≤ 1) (he : 0 < e)
    (hbound : ∀ chi r, r ∈ heckePacketZeros K omega chi →
      1 / 2 ≤ r → r ≤ 1 → r ≤ B)
    (he1 : e ≤ 1 / 10000) (hlam : 0 < lam) (heSmall : e ≤ lam / 1000)
    (hw : 0 < width) (hgap : 2 * e < width) (hwSmall : width ≤ lam / 100)
    (sourceLam zeta k : ℝ) (hzeta : 13 / 16 + zeta ≤ 1) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ 1 → ∃ Z0 : ℝ, 2 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z →
      ∀ j : Fin (shellCount Z (1 / 16) (13 / 16 + zeta)),
      ∀ c : PhysicalRecipeChoice K S₀ B e,
      let b := physicalRecipeScheduledBlock K S₀ P omega psi g
        (arithmeticHighEulerData K S₀ P psi) hpsi hB0 hB he hbound
        mu ∅ sourceLam zeta width k hw Z (Z ^ tau) j c
      let d := shellExponent Z (1 / 16) j.val
      ∀ l ∈ physicalRecipeRetainedLabels K S₀ (hB0 := hB0) (hB := hB) (he := he)
        (g := g) width hw c,
        (∑ u ∈ (b.amplitude l).rows (Z ^ d),
          ‖physicalRecipeShiftedPiece K S₀ P (arithmeticHighEulerData K S₀ P psi)
            omega psi hpsi hB0 hB he hbound g mu ∅ sourceLam zeta width k hw
            Z (Z ^ tau) j c l u‖) ≤
          C * (((b.amplitude l).rows (Z ^ d)).card : ℝ) *
            Z ^ (NormForm.rowExponent d c.1.center
              ((∑ i, (b.amplitude l).amplitude i) / g.slots) + lam / 4) *
                (1 + Z ^ tau) ^ A := by
  obtain ⟨A, C, hA, hC, hb⟩ := exists_physicalBlock_normForm K S mu P omega psi g
    hcal hpsiUnram B (physicalRecipeHeightBound B e) he he1 hlam heSmall hgap hwSmall
  refine ⟨A, C, hA, hC, ?_⟩
  intro tau htau htau1
  obtain ⟨Z0, hZ0, hnorm⟩ := hb tau htau htau1
  refine ⟨Z0, hZ0, ?_⟩
  intro Z hZ j c
  dsimp only
  have hZgt : 1 < Z := (by norm_num : (1 : ℝ) < 2).trans_le (hZ0.trans hZ)
  have hT : 0 ≤ Z ^ tau := Real.rpow_nonneg (zero_lt_one.trans hZgt).le _
  have hd := actualShell_range hZgt j
  have ha := rowBufferIndex_center_range hB0 he c.1
  have hh : c.1.1.val ≤ physicalRecipeHeightBound B e := by
    have hs := physicalRecipeChoice_height_le K S₀ B e c
    omega
  refine hnorm Z hZ (shellExponent Z (1 / 16) j.val) hd.1 (hd.2.le.trans hzeta)
    c.1.center ha.1 (ha.2.trans hB) c.1.1.val hh
    (physicalRecipeRows K S₀ P (arithmeticHighEulerData K S₀ P psi) omega psi
      hpsi hB0 hB he hbound zeta Z (Z ^ tau) j c) ?_ ?_
    (fixedAmplitudeLabelCount g.slots width)
    (physicalRecipeScheduledBlock K S₀ P omega psi g
      (arithmeticHighEulerData K S₀ P psi) hpsi hB0 hB he hbound mu ∅
      sourceLam zeta width k hw Z (Z ^ tau) j c) c.2
    (amplitudeLabels_card_le_fixed g.slots hw (physicalRecipeChoice_cap K S₀ hB0 hB he c)) ?_
  · intro u hu
    have hr := physicalRecipeRows_spec K S₀ P (arithmeticHighEulerData K S₀ P psi)
      omega psi hpsi hB0 hB he hbound zeta Z (Z ^ tau) hZgt j c u hu
    exact ⟨hr.1.le, hr.2.1⟩
  · intro u hu
    have hr := physicalRecipeRows_spec K S₀ P (arithmeticHighEulerData K S₀ P psi)
      omega psi hpsi hB0 hB he hbound zeta Z (Z ^ tau) hZgt j c u hu
    simpa only [ExpansionInterfaces.upperHeight, Nat.cast_add, Nat.cast_one,
      add_assoc, show (1 + 1 : ℝ) = 2 by norm_num] using hr.2.2.2.2
  · exact (physicalRecipeScheduledBlock_origins K S₀ P omega psi g
      (arithmeticHighEulerData K S₀ P psi) hpsi hB0 hB he hbound mu ∅
      sourceLam zeta width k hw Z (Z ^ tau) hZgt hT j c).1

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_physicalRecipe_normForm
