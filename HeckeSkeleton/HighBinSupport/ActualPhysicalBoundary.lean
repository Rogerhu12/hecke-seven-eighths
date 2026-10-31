import Expansion.PhysicalRecipeRemainders
import HeckeSkeleton.HighBinSupport.ActualBoundaryEstimate
import HeckeSkeleton.HighBinSupport.BoundaryHeightAbsorption

/-!
# Arbitrary height decay for the actual physical whole-bin boundary

The fixed rows, buffered choices, sectors and clipped final shell are those
of `physicalScheduledWholeBoundary`.  Each actual zero detector may be
shortened to `T + 3/2` without changing any row.  Applying the arithmetic
contour theorem at a larger decay order absorbs its fixed height degree.
The original finite shell schedule then gives scale degree 14, with no
height loss.  All constants and the scale threshold precede the external
decay order, except for the decay constant itself.

This module does not import the named HIGHBIN obligations.  In particular,
its tail estimate is available to construct their original boundary
producer and does not consume that producer as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinPhysicalBoundary

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualEstimate
open Expansion.Project ExpansionInterfaces
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))

local instance physicalBoundary_sectorFintype : Fintype (SixthUnitClasses K S₀) :=
  Fintype.ofFinite _

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (μ : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (μ p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K S₀)]
variable [BorelSpace (sLocalNormOneGroup K S₀)]
local notation "μS" => (fun p : S₀ => μ (Subtype.val p))

variable (P : ProbeData K S₀) (ω ψ : HeckeCharacter K)
variable {B e : ℝ} (hψ : ψ ∈ HeckePacket K ω)
variable (hB0 : 51 / 100 ≤ B) (hB1 : B ≤ 1) (he : 0 < e)
variable (hboundary : ∀ χ : HeckePacketIndex K ω,
  ∀ r ∈ heckePacketZeros K ω χ, 1 / 2 ≤ r → r ≤ 1 → r ≤ B)
variable (g : PrimeWindowGeometry)
local notation "E" => arithmeticHighEulerData K S₀ P ψ

/-- A count for the original EXPANSION shell schedule, uniform in every
upper exponent at most one.  This uses its literal `shellCount`. -/
theorem physicalBoundary_shellCount_le_linear {Z upper : ℝ}
    (hZ : 1 ≤ Z) (hlo : 1 / 16 ≤ upper) (hhi : upper ≤ 1) :
    (ExpansionInterfaces.shellCount Z (1 / 16) upper : ℝ) ≤
      (2 + 1 / Real.log 2) * Z := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := ExpansionInterfaces.shellCount_subpower (lower := (1 / 16 : ℝ))
    hZ hlo (by norm_num : (0 : ℝ) < 1)
  simp only [div_one, Real.rpow_one] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hZ)
  apply add_le_add_left
  exact div_le_div_of_nonneg_right (by linarith) hlog.le

/-- The actual physical whole-bin move has arbitrary external height
decay.  The same rows occur at the initial and final endpoints, and the
same arithmetic Euler provider occurs in the detector and the integral. -/
theorem exists_physicalScheduledWholeBoundary_external_tail
    (he1 : e ≤ 1 / 10000) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ ζ Z T : ℝ, 0 ≤ ζ → 13 / 16 + ζ ≤ 1 → Z₀ ≤ Z → 1 ≤ T →
      ‖physicalScheduledWholeBoundary K S μ P E ω ψ hψ hB0 hB1 he hboundary
        g ζ Z T‖ ≤ C * Z ^ 14 * T ^ (-(N : ℝ)) := by
  let q := HighBinBoundary.ActualLRatioStrip.boundaryHeightDegree K
  obtain ⟨Z₁, hZ₁, htail⟩ := exists_arithmetic_fixedRows_external_tail
    K S μS P ψ {1} (by simp) g he he1
  refine ⟨max Z₁ 2, le_max_right _ _, ?_⟩
  intro N
  obtain ⟨C, hC, hfixed⟩ := htail (N + q)
  let A : ℝ := 2 + 1 / Real.log 2
  let D : ℝ := C * (5 : ℝ) ^ q
  let M : ℝ := physicalRecipeMultiplicity K S₀ B e
  have hA : 0 < A := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [A]
    positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast physicalRecipeMultiplicity_pos K S₀ B e
  refine ⟨A * M * D, mul_pos (mul_pos hA hM) hD, ?_⟩
  intro ζ Z T hζ hupper hZ hT
  have hZbase : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hZlt : 1 < Z := by linarith
  have hZpos : 0 < Z := zero_lt_one.trans hZlt
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpiece : ∀ j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)),
      ∀ c : PhysicalRecipeChoice K S₀ B e,
      ‖∑ u ∈ physicalRecipeRows K S₀ P E ω ψ hψ hB0 hB1 he hboundary ζ Z T j c,
        (rowContourBox K S₀ μS P ψ E g ∅ u Z T
          (B + 20 * e) (1 - c.1.center - 6 * e) (17 / 50) -
          rowContourBox K S₀ μS P ψ E g ∅ u Z T
            (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))‖ ≤
        D * Z ^ 13 * T ^ (-(N : ℝ)) := by
    intro j c
    let d := shellExponent Z (1 / 16) j.val
    let rows := physicalRecipeRows K S₀ P E ω ψ hψ hB0 hB1 he hboundary ζ Z T j c
    have hshell := ExpansionInterfaces.actualShell_range hZlt j
    have ha := rowBufferIndex_center_range hB0 he c.1
    have hdata (u : FrequencyRow K S₀) (hu : u ∈ rows) :=
      physicalRecipeRows_spec K S₀ P E ω ψ hψ hB0 hB1 he hboundary
        ζ Z T hZlt j c u hu
    have hrows : rows ⊆ frequencyRows K S₀ (2 * Z ^ d) := by
      intro u hu
      exact (mem_frequencyRows_iff K S₀ _ (by positivity) u).mpr (hdata u hu).2.1
    have hlower : ∀ u ∈ rows, Z ^ d ≤ frequencyRowNorm K S₀ u :=
      fun u hu => (hdata u hu).1.le
    have hgap : T + 3 / 2 ≤ ExpansionInterfaces.upperHeight (c.1.1.val + 1) T := by
      unfold ExpansionInterfaces.upperHeight
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg c.1.1.val : (0 : ℝ) ≤ c.1.1.val) hT0]
    have hbelow : ∀ u ∈ rows, rowZeroBelow K S₀ ψ {1} P E u
        (T + 3 / 2) (c.1.center + 2 * e) := by
      intro u hu χ hχ ρ hρ hρ0 hρ1 hheight
      exact (hdata u hu).2.2.2.2 χ hχ ρ hρ hρ0 hρ1 (hheight.trans hgap)
    have hb := hfixed ∅ Z hZbase d hshell.1 (hshell.2.le.trans hupper)
      rows hrows hlower c.1.center B T (T + 3 / 2) T ha.1 ha.2 hB1
      hT le_rfl le_rfl hbelow
    rw [← Finset.sum_sub_distrib] at hb
    have habs := HighBinBoundary.height_tail_absorb T N q hT
    calc
      _ ≤ C * Z ^ 13 * (2 + (T + 3 / 2)) ^ q * T ^ (-((N + q : ℕ) : ℝ)) := hb
      _ = C * Z ^ 13 *
          ((2 + (T + 3 / 2)) ^ q * T ^ (-((N + q : ℕ) : ℝ))) := by ring
      _ ≤ C * Z ^ 13 * ((5 : ℝ) ^ q * T ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ = D * Z ^ 13 * T ^ (-(N : ℝ)) := by dsimp only [D]; ring
  have hcount : (shellCount Z (1 / 16) (13 / 16 + ζ) : ℝ) ≤ A * Z :=
    physicalBoundary_shellCount_le_linear hZlt.le (by linarith) hupper
  unfold physicalScheduledWholeBoundary
  calc
    _ ≤ ∑ j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)),
        ∑ c : PhysicalRecipeChoice K S₀ B e,
          ‖∑ u ∈ physicalRecipeRows K S₀ P E ω ψ hψ hB0 hB1 he hboundary ζ Z T j c,
            (rowContourBox K S₀ μS P ψ E g ∅ u Z T
              (B + 20 * e) (1 - c.1.center - 6 * e) (17 / 50) -
              rowContourBox K S₀ μS P ψ E g ∅ u Z T
                (c.1.center + 16 * e) (1 - c.1.center - 6 * e) (17 / 50))‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ ∑ _j : Fin (shellCount Z (1 / 16) (13 / 16 + ζ)),
        ∑ _c : PhysicalRecipeChoice K S₀ B e,
          D * Z ^ 13 * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun c _ => hpiece j c
    _ = (shellCount Z (1 / 16) (13 / 16 + ζ) : ℝ) *
        (M * (D * Z ^ 13 * T ^ (-(N : ℝ)))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        M, physicalRecipeMultiplicity]
    _ ≤ (A * Z) * (M * (D * Z ^ 13 * T ^ (-(N : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (A * M * D) * Z ^ 14 * T ^ (-(N : ℝ)) := by ring

/-- The original scheduled physical whole-bin boundary satisfies the
external tail contract with fixed scale degree 14 and height degree zero. -/
theorem physicalScheduledWholeBoundary_powerHeightTailBound
    (he1 : e ≤ 1 / 10000) {ζ : ℝ} (hζ : 0 ≤ ζ) (hupper : 13 / 16 + ζ ≤ 1) :
    PowerHeightTailBound
      (physicalScheduledWholeBoundary K S μ P E ω ψ hψ hB0 hB1 he hboundary g ζ) := by
  obtain ⟨Z₀, hZ₀, htail⟩ := exists_physicalScheduledWholeBoundary_external_tail
    K S μ P ω ψ hψ hB0 hB1 he hboundary g he1
  refine ⟨0, 14, 1, le_rfl, by norm_num, ?_⟩
  intro τ hτ _ N
  obtain ⟨C, hC, hb⟩ := htail N
  refine ⟨C, Z₀, hC, by linarith, ?_⟩
  intro Z hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hT : 1 ≤ Z ^ τ := Real.one_le_rpow hZ1 hτ.le
  simpa only [Real.rpow_zero, mul_one, Real.rpow_natCast] using
    hb ζ Z (Z ^ τ) hζ hupper hZ hT

end HeckeSkeleton.HighBinPhysicalBoundary

#print axioms HeckeSkeleton.HighBinPhysicalBoundary.physicalBoundary_shellCount_le_linear
#print axioms HeckeSkeleton.HighBinPhysicalBoundary.exists_physicalScheduledWholeBoundary_external_tail
#print axioms HeckeSkeleton.HighBinPhysicalBoundary.physicalScheduledWholeBoundary_powerHeightTailBound
