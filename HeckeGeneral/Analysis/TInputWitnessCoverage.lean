import HeckeGeneral.Analysis.TInputRanges
import HeckeGeneral.Analysis.MomentWitnessCount
import HeckeGeneral.Analysis.FiniteWitnessHeight

/-!
Actual moment witnesses cover physical arithmetic rows. This file proves
the counting consumer from MI/P; the coverage premise is a threshold on
the actual finite polynomials, not a row-count or high estimate.

The finite expansion/presentation family is fixed before constants are
selected. Projecting FrequencyRow to its ideal loses at most the ACTUAL
finite number of sixth-unit classes. No arbitrary row enumeration is
declared canonical by this combinatorial consumer.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def frequencyRowEncoding (u : FrequencyRow K S) : NonzeroIdeal K × SixthUnitClasses K S :=
  (u.ideal.val, u.sector)

omit [Fintype S] in
theorem frequencyRowEncoding_injective : Function.Injective (frequencyRowEncoding K S) := by
  intro u v h
  have hi : u.ideal = v.ideal := Subtype.ext (Prod.mk.inj h).1
  have hs : u.sector = v.sector := (Prod.mk.inj h).2
  cases u
  cases v
  cases hi
  cases hs
  rfl

theorem physicalRows_card_le_idealImage (R : Finset (FrequencyRow K S)) :
    (R.card : ℝ) ≤ (Nat.card (SixthUnitClasses K S) : ℝ) *
      ((R.image (fun u => u.ideal.val)).card : ℝ) := by
  let : Fintype (SixthUnitClasses K S) := Fintype.ofFinite _
  have hsub : R.image (frequencyRowEncoding K S) ⊆
      (R.image (fun u => u.ideal.val)).product Finset.univ := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨u, hu, rfl⟩, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective R (frequencyRowEncoding_injective K S)] at hc
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] at hc
  have hc' : (R.card : ℝ) ≤
      ((R.image (fun u => u.ideal.val)).card : ℝ) * Fintype.card (SixthUnitClasses K S) := by
    exact_mod_cast hc
  simpa only [Nat.card_eq_fintype_card, mul_comm] using hc'

theorem polynomialHeightBound_power_mono {E : ℝ → ℝ → ℝ} {p q ε : ℝ}
    (h : PolynomialHeightBound E p ε) (hpq : p ≤ q) : PolynomialHeightBound E q ε := by
  obtain ⟨C, Z₀, A, h, hC, hZ₀, hA, hh, hb⟩ := h
  refine ⟨C, Z₀, A, h, hC, hZ₀, hA, hh, ?_⟩
  intro Z t hZ ht
  apply (hb Z t hZ ht).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hZ₀.trans hZ) (by linarith)) hC.le)
    (Real.rpow_nonneg (by positivity) _)

theorem polynomialHeightBound_positive_mul {E : ℝ → ℝ → ℝ} {p ε M : ℝ}
    (h : PolynomialHeightBound E p ε) (hM : 0 < M) :
    PolynomialHeightBound (fun Z t => M * E Z t) p ε := by
  obtain ⟨C, Z₀, A, ceiling, hC, hZ₀, hA, hh, hb⟩ := h
  refine ⟨M * C, Z₀, A, ceiling, mul_pos hM hC, hZ₀, hA, hh, ?_⟩
  intro Z t hZ ht
  calc
    _ ≤ M * (C * Z ^ (p + ε) * (1 + |t|) ^ A) :=
      mul_le_mul_of_nonneg_left (hb Z t hZ ht) hM.le
    _ = _ := by ring

structure MomentWitnessFamily (ω : HeckeCharacter K) where
  packetTarget : HeckeCharacter K
  data : ℝ → MomentData K ω packetTarget
  parameters : RealParameters
  geometry : SlotGeometry K
  threshold : ℝ
  paired : Bool

variable {K} in
def MomentWitnessFamily.rows {ω : HeckeCharacter K} (f : MomentWitnessFamily K ω)
    (Z t : ℝ) : Finset (NonzeroIdeal K) :=
  if f.paired then pairedWitnessRows K (f.data Z) f.parameters Z t f.threshold
  else inverseWitnessRows K (f.data Z) f.parameters Z t f.threshold

variable {K} in
def MomentWitnessFamily.countPower {ω : HeckeCharacter K} (f : MomentWitnessFamily K ω) : ℝ :=
  (if f.paired then f.parameters.m + f.parameters.q else f.parameters.m) - f.threshold

variable {K} in
/-- All structural calibration is imposed on the ENTIRE scale family.
The fourth-moment boundary is actual meromorphic order, not an improved
boundary. This predicate contains no energy or counting estimate. -/
def MomentWitnessFamily.Calibrated {ω : HeckeCharacter K}
    (cal : CanonicalAdmissibility ω) (b : RealBox) (mesh : ℝ)
    (f : MomentWitnessFamily K ω) : Prop :=
  f.packetTarget ∈ HeckePacket K ω ∧ InBox b f.parameters ∧
    f.geometry.fitsMesh mesh ∧ f.geometry.totalLength = f.parameters.z ∧
    (∀ Z, (f.data Z).geometry = f.geometry) ∧
    if f.paired then
      PRegion f.parameters ∧ FiniteOrderBoundary (K := K) ((1 + f.parameters.κ) / 2) ∧
        cal.paired b f.parameters mesh f.packetTarget f.data ∧
        (∀ Z i, (f.data Z).slotCoefficient i ∈ (f.data Z).theta)
    else
      MIRegion f.parameters ∧ MIUniformMargins b f.parameters ∧
        cal.inverse b f.parameters mesh f.packetTarget f.data

theorem physicalRowCount_of_witness_cover {ι : Type*} (F : Finset ι)
    (R : ℝ → ℝ → Finset (FrequencyRow K S)) (W : ι → ℝ → ℝ → Finset (NonzeroIdeal K))
    {p ε : ℝ}
    (hcover : ∀ Z t, 1 ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ F, u.ideal.val ∈ W i Z t)
    (hW : ∀ i ∈ F, PolynomialHeightBound (fun Z t => ((W i Z t).card : ℝ)) p ε) :
    PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p ε := by
  have hI := polynomialHeightBound_finite_cover F
    (fun Z t => (R Z t).image (fun u => u.ideal.val)) W
    (fun Z t hZ I hI => by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
      exact hcover Z t hZ u hu) hW
  have hM : (0 : ℝ) < Nat.card (SixthUnitClasses K S) := by
    exact_mod_cast Nat.card_pos (α := SixthUnitClasses K S)
  apply polynomialHeightBound_mono (polynomialHeightBound_positive_mul hI hM)
  intro Z t _
  exact physicalRows_card_le_idealImage K S (R Z t)

/-- Full MI/P-to-physical-count consumer. The supplied cover is a genuine
large-polynomial witness assertion. The final count is proved here, not
stored as a field of T. Both meshes precede the finite witness family;
the numerical exponent comparison remains explicit. Source-polynomial
calibration and the construction of the physical cover remain obligations. -/
theorem physicalRowCount_of_calibrated_moment_cover {ω : HeckeCharacter K}
    (cal : CanonicalAdmissibility ω) (hMI : MIInput ω cal) (hP : PInput ω cal)
    (b : RealBox) (ε : ℝ) (hε : 0 < ε) :
    ∃ meshMI meshP : ℝ, 0 < meshMI ∧ 0 < meshP ∧
      ∀ {ι : Type} (F : Finset ι) (f : ι → MomentWitnessFamily K ω)
        (R : ℝ → ℝ → Finset (FrequencyRow K S)) (p : ℝ),
        (∀ i ∈ F, (f i).Calibrated cal b (if (f i).paired then meshP else meshMI)) →
        (∀ i ∈ F, (f i).countPower ≤ p) →
        (∀ Z t, 1 ≤ Z → ∀ u ∈ R Z t, ∃ i ∈ F, u.ideal.val ∈ (f i).rows Z t) →
        PolynomialHeightBound (fun Z t => ((R Z t).card : ℝ)) p ε := by
  obtain ⟨meshMI, hmeshMI, hMIbound⟩ := hMI b ε hε
  obtain ⟨meshP, hmeshP, hPbound⟩ := hP b ε hε
  refine ⟨meshMI, meshP, hmeshMI, hmeshP, ?_⟩
  intro ι F f R p hcal hp hcover
  apply physicalRowCount_of_witness_cover K S F R (fun i => (f i).rows) hcover
  intro i hi
  obtain ⟨hpacket, hbox, hmesh, hlength, hgeometry, hrest⟩ := hcal i hi
  cases he : (f i).paired with
  | false =>
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hmesh hrest
    obtain ⟨hregion, hmargins, hadmissible⟩ := hrest
    have heff := hMIbound (f i).parameters hbox hregion hmargins (f i).geometry
      hmesh hlength (f i).packetTarget hpacket (f i).data hgeometry hadmissible
    have hw := inverseWitnessRows_polynomialHeightBound K (f i).data (f i).parameters heff
      (f i).threshold
    apply polynomialHeightBound_power_mono (p := (f i).parameters.m - (f i).threshold)
    · simpa only [MomentWitnessFamily.rows, he, Bool.false_eq_true, ↓reduceIte] using hw
    · simpa only [MomentWitnessFamily.countPower, he, Bool.false_eq_true, ↓reduceIte] using hp i hi
  | true =>
    simp only [he, ↓reduceIte] at hmesh hrest
    obtain ⟨hregion, hboundary, hadmissible, hslot⟩ := hrest
    have heff := hPbound (f i).parameters hbox hregion hboundary (f i).geometry
      hmesh hlength (f i).packetTarget hpacket (f i).data hgeometry hadmissible hslot
    have hw := pairedWitnessRows_polynomialHeightBound K (f i).data (f i).parameters heff
      (f i).threshold
    apply polynomialHeightBound_power_mono (p := (f i).parameters.m + (f i).parameters.q - (f i).threshold)
    · simpa only [MomentWitnessFamily.rows, he, ↓reduceIte] using hw
    · simpa only [MomentWitnessFamily.countPower, he, ↓reduceIte] using hp i hi

end HeckeGeneral.ThetaSkeleton.Physical
