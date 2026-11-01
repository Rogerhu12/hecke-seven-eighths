import HeckeSkeleton.HighBinSupport.ActualPhysicalKernel
import HeckeSkeleton.HighBinSupport.ActualPhysicalPrimeLabels
import HeckeSkeleton.HighBinSupport.ActualPhysicalTransport

/-!
# The norm form for the actual physical source blocks

The constants precede the scale, shell, bin, physical point and row.  The
height degree is fixed before the positive power-height exponent; only the
finite-height prime cutoff depends on that exponent.  The estimate uses
the source's actual main-polynomial amplitude, carries every correction
error through the conductor allocation, and integrates the same moving
fiber transport used by the presentation constructor.
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

/-- The actual source data suffice for the transported norm form.  The
`PhysicalAmplitudeOrigin` premises are exact constructor provenance, not
analytic bounds or row counts.  All analytic bounds are proved internally. -/
theorem exists_physicalBlock_normForm
    (P : ProbeData K S₀) (omega psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    (B : ℝ) (heightCount : ℕ) {e width lam : ℝ}
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (hlam : 0 < lam)
    (heSmall : e ≤ lam / 1000) (hgap : 2 * e < width) (hwSmall : width ≤ lam / 100) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ 1 → ∃ Z0 : ℝ, 2 ≤ Z0 ∧
      ∀ Z : ℝ, Z0 ≤ Z → ∀ d : ℝ, 1 / 16 ≤ d → d ≤ 1 →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 → ∀ h : ℕ, h ≤ heightCount →
      ∀ rows : Finset (FrequencyRow K S₀),
        (∀ u ∈ rows, Z ^ d ≤ frequencyRowNorm K S₀ u ∧
          frequencyRowNorm K S₀ u ≤ 2 * Z ^ d) →
        (∀ u ∈ rows, rowZeroBelow K S₀ psi {1} P
          (arithmeticHighEulerData K S₀ P psi) u
          (3 * ((h : ℝ) + 2) * Z ^ tau) (a + 2 * e)) →
      ∀ N : ℕ, ∀ b : RecipeBlockData K S₀ psi g (physicalRecipeFamily K psi g B e) N,
      ∀ sector : SixthUnitClasses K S₀,
      ∀ hcard : Fintype.card (AmplitudeLabels g.slots width ((2 * a - 1) / 2)) ≤ N,
        (∀ label : AmplitudeLabels g.slots width ((2 * a - 1) / 2),
          PhysicalAmplitudeOrigin K S₀ P (arithmeticHighEulerData K S₀ P psi).rows
            omega psi g (physicalRecipeFamily K psi g B e) width ((2 * a - 1) / 2)
            Z (Z ^ tau) (Z ^ d) rows sector label
            (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width ((2 * a - 1) / 2)
              hcard label))) →
      ∀ l ∈ retainedFixedLabels hcard,
        (∑ u ∈ (b.amplitude l).rows (Z ^ d),
          ‖physicalBlockShiftedPiece (P := P)
            (R := (arithmeticHighEulerData K S₀ P psi).rows) (ω := omega)
            width ((2 * a - 1) / 2) Z (Z ^ tau) rows b hcard physicalHeightVolume
            (physicalContourKernel K S₀ mu P psi (arithmeticHighEulerData K S₀ P psi)
              g ∅ Z (a + 16 * e) (1 - a - 6 * e) (17 / 50)) l u‖) ≤
          C * (((b.amplitude l).rows (Z ^ d)).card : ℝ) *
            Z ^ (NormForm.rowExponent d a ((∑ i, (b.amplitude l).amplitude i) / g.slots) +
              lam / 4) * (1 + Z ^ tau) ^ A := by
  let eps : ℝ := lam / 1000
  let eta : ℝ := lam / (1000 * ((g.slots : ℝ) + 2))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaSmall : eta ≤ eps := by
    dsimp only [eta, eps]
    apply (div_le_iff₀ (by positivity : 0 < 1000 * ((g.slots : ℝ) + 2))).mpr
    have hn := mul_nonneg hlam.le (Nat.cast_nonneg g.slots : (0 : ℝ) ≤ g.slots)
    nlinarith
  have hetaEq : ((g.slots : ℝ) + 2) * eta = eps := by
    have hJ2 : (g.slots : ℝ) + 2 ≠ 0 := by positivity
    dsimp only [eta, eps]
    field_simp [hJ2]
  have hw : 0 < width := (mul_pos (by norm_num) he).trans hgap
  obtain ⟨A, C, ZK, hA, hC, hZK, hkernel⟩ :=
    exists_actual_physical_kernel_normForm_of_main K S mu P psi g hcal hpsi heightCount
      he he1 heps heta heps hw.le
  let normalization : ℝ := ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ + 1
  let Ctotal : ℝ := 8 * normalization * C
  have hn : 0 < normalization := by dsimp only [normalization]; positivity
  have hCt : 0 < Ctotal := by dsimp only [Ctotal]; positivity
  refine ⟨A + 3, Ctotal, by linarith, hCt, ?_⟩
  intro tau htau htau1
  obtain ⟨ZP, hZP, hprime⟩ := exists_physicalRecipe_prime_cap K S₀ P
    (arithmeticHighEulerData K S₀ P psi) omega psi g B heightCount he.le hgap htau htau1
  refine ⟨max ZK ZP, hZP.trans (le_max_right _ _), ?_⟩
  intro Z hZ d hd hd1 a ha ha1 h hh rows hrows hbelow N b sector hcard horigin l hl
  have hZZK : ZK ≤ Z := (le_max_left _ _).trans hZ
  have hZZP : ZP ≤ Z := (le_max_right _ _).trans hZ
  have hZ2 : 2 ≤ Z := hZP.trans hZZP
  have hZ1 : 1 ≤ Z := by linarith
  have hZgt : 1 < Z := by linarith
  have hZpos : 0 < Z := by linarith
  have hT1 : 1 ≤ Z ^ tau := Real.one_le_rpow hZ1 htau.le
  have hT0 : 0 ≤ Z ^ tau := Real.rpow_nonneg hZpos.le _
  have hcap : 0 ≤ (2 * a - 1) / 2 := by linarith
  rw [retainedFixedLabels_eq_physicalAmplitudeLabels] at hl
  obtain ⟨label, _, rfl⟩ := Finset.mem_map.mp hl
  let amplitude : Fin g.slots → ℝ := fun i =>
    decodeAmplitude width ((2 * a - 1) / 2) (label i)
  let q : ℝ := (∑ i, amplitude i) / g.slots
  have hamp : ∀ i, 0 ≤ amplitude i := by
    intro i
    exact le_min hcap (mul_nonneg hw.le (Nat.cast_nonneg _))
  have hmean : (∑ i, (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width
      ((2 * a - 1) / 2) hcard label)).amplitude i) / g.slots = q := by
    rw [(horigin label).2.2.1]
  have hbudget : (105 / 8 + 6 * d) * e +
      d * (2 * eps + (g.slots + 2) * eta) + ((width + eta) / 6 + eps) ≤ lam / 4 := by
    rw [hetaEq]
    have hde := mul_le_mul_of_nonneg_right hd1 he.le
    have hdeps := mul_le_mul_of_nonneg_right hd1 heps.le
    dsimp only [eps] at hetaSmall heSmall hdeps ⊢
    nlinarith
  have hpoint (p : Fin 3 → ℝ) (hp : ‖p‖ ≤ Z ^ tau)
      (u : FrequencyRow K S₀)
      (hu : u ∈ recipeAmplitudeRows K S₀ P (arithmeticHighEulerData K S₀ P psi).rows
        omega psi g (physicalRecipeFamily K psi g B e) width ((2 * a - 1) / 2) Z rows p label) :
      ‖physicalContourKernel K S₀ mu P psi (arithmeticHighEulerData K S₀ P psi)
        g ∅ Z (a + 16 * e) (1 - a - 6 * e) (17 / 50) u p‖ ≤
        normalization * C * Z ^ (NormForm.rowExponent d a q + lam / 4) * (1 + Z ^ tau) ^ A := by
    let s : ℂ := ((a + 16 * e : ℝ) : ℂ) + (p 0 : ℂ) * Complex.I
    let w : ℂ := ((1 - a - 6 * e : ℝ) : ℂ) + (p 1 : ℂ) * Complex.I
    let z : ℂ := ((17 / 50 : ℝ) : ℂ) + (p 2 : ℂ) * Complex.I
    have hz : z = (17 / 50 : ℂ) + (p 2 : ℂ) * Complex.I := by
      dsimp only [z]
      norm_num
    have hur := recipeAmplitudeRows_subset K S₀ P (arithmeticHighEulerData K S₀ P psi).rows
      omega psi g (physicalRecipeFamily K psi g B e) width ((2 * a - 1) / 2) Z rows p label hu
    have hmain (i : Fin g.slots) :
        ‖HighBinVerified.NormFormFullCorrection.actualCompensationMainSlot K S₀ P g ∅ u Z z i‖ ≤
          (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude i + width) := by
      rw [hz]
      exact physicalRecipe_mainSlot_bound_on_fiber K S₀ P
        (arithmeticHighEulerData K S₀ P psi).rows omega psi g B e hw hcap hZgt rows p
        (fun i v hv => by
          have hh := hprime Z hZZP d hd hd1 v (hrows v hv).1 (hrows v hv).2
            a (by linarith) ha1 h hh p hp (hbelow v hv) i
          convert hh using 1 <;> congr 1 <;> ring)
        label i u hu
    have hcoord (i : Fin 3) : |p i| ≤ Z ^ tau := by
      have hpi : |p i| ≤ ‖p‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm p i
      exact hpi.trans hp
    have hk := hkernel Z (Z ^ tau) hZZK hT1 d hd hd1 u
      (hrows u hur).1 (hrows u hur).2 a ha ha1 h hh (hbelow u hur) amplitude hamp
      s w z (by simp [s]) (by simp [w]) (by norm_num [z])
      (by simpa [s] using hcoord 0) (by simpa [w] using hcoord 1) hmain
    have hk' : ‖compensatedRowMellinKernel K S₀ mu P psi
        (arithmeticHighEulerData K S₀ P psi) g ∅ u Z s w z‖ ≤
        C * Z ^ (NormForm.rowExponent d a q + lam / 4) * (1 + Z ^ tau) ^ A := by
      apply hk.trans
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Z ^ tau) _)
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le hZ1
      change NormForm.rowExponent d a q + (105 / 8 + 6 * d) * e +
        d * (2 * eps + (g.slots + 2) * eta) + ((width + eta) / 6 + eps) ≤
          NormForm.rowExponent d a q + lam / 4
      linarith only [hbudget]
    change ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
      compensatedRowMellinKernel K S₀ mu P psi (arithmeticHighEulerData K S₀ P psi)
        g ∅ u Z s w z‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul
      (by dsimp only [normalization]; linarith :
        ‖(2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))‖ ≤ normalization)
      hk' (norm_nonneg _) hn.le).trans_eq (by ring)
  have hrow (u : FrequencyRow K S₀) :
      ‖physicalBlockShiftedPiece (P := P)
        (R := (arithmeticHighEulerData K S₀ P psi).rows) (ω := omega)
        width ((2 * a - 1) / 2) Z (Z ^ tau) rows b hcard physicalHeightVolume
        (physicalContourKernel K S₀ mu P psi (arithmeticHighEulerData K S₀ P psi)
          g ∅ Z (a + 16 * e) (1 - a - 6 * e) (17 / 50))
        (physicalAmplitudeLabelEmbedding g.slots width ((2 * a - 1) / 2) hcard label) u‖ ≤
          Ctotal * Z ^ (NormForm.rowExponent d a q + lam / 4) * (1 + Z ^ tau) ^ (A + 3) := by
    have hh := physicalBlockShiftedPiece_norm_le width ((2 * a - 1) / 2) Z (Z ^ tau)
      (Z ^ d) hT0 rows sector b hcard _ label (horigin label)
      (C := normalization * C * Z ^ (NormForm.rowExponent d a q + lam / 4) *
        (1 + Z ^ tau) ^ A) (by positivity) hpoint u
    have hvol : (Z ^ tau) ^ 3 ≤ (1 + Z ^ tau) ^ (3 : ℝ) := by
      rw [Real.rpow_ofNat (1 + Z ^ tau) 3]
      exact pow_le_pow_left₀ hT0 (by linarith) 3
    apply hh.trans
    calc
      _ ≤ (normalization * C * Z ^ (NormForm.rowExponent d a q + lam / 4) *
          (1 + Z ^ tau) ^ A) * (8 * (1 + Z ^ tau) ^ (3 : ℝ)) := by
        gcongr
      _ = _ := by
        rw [Real.rpow_add (by positivity : 0 < 1 + Z ^ tau)]
        dsimp only [Ctotal]
        ring
  rw [hmean]
  calc
    _ ≤ ∑ u ∈ (b.amplitude (physicalAmplitudeLabelEmbedding g.slots width
        ((2 * a - 1) / 2) hcard label)).rows (Z ^ d),
        Ctotal * Z ^ (NormForm.rowExponent d a q + lam / 4) * (1 + Z ^ tau) ^ (A + 3) :=
      Finset.sum_le_sum (fun u _ => hrow u)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_physicalBlock_normForm
