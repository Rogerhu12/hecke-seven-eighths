import ActualProbeSpectralFrequencyExpansion
import ActualProbeLogRowNormEnvelope
import ActualAdditiveGramUnitOrbits

/-!
UNCOMPILED / native 0. The finite frequency set is now kept inside the
literal translated compact logarithmic support. Two members of the same
ORIGINAL sixth-power-unit orbit have a quotient in one fixed compact ratio
set. Discreteness of the actual S-unit diagonal therefore gives a uniform
fiber bound before t, X and Y. The two literal energies are then grouped by
that same quotient, with every original sector retained.

This proves a finite geometric transport. It does not estimate the resulting
Gram or theta energy, or assert a reflected-theta identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "Γ" => sixthPowerUnits K S
local notation "OQ" => SIntegerOrbits K S Γ

/-- The literal quotient map, retaining every sector of the original group. -/
def probeSixthOrbit : NZ → OQ := Quotient.mk _

/-- Compact ratio sets meet the actual diagonal subgroup in a finite set.
No finite-index or torsion-free replacement of the given subgroup is used. -/
theorem finite_compact_diagonal_ratios (Δ : Subgroup (S.unit K))
    (C : Set G) (hC : IsCompact C) :
    Set.Finite ((Δ.map (sLocalDiagonal K S) : Set G) ∩
      ((fun p : G × G => p.1 / p.2) '' (C ×ˢ C))) := by
  exact (((hC.prod hC).image continuous_div').inter_left
    (isClosed_sLocalDiagonal_map K S Δ)).finite
      ((isDiscrete_sLocalDiagonal_map K S Δ).mono inter_subset_left)

/-- Fixed compact shape gives uniform multiplicity for the original Gamma,
independently of the translating element and the chosen finite subset. -/
theorem exists_compact_shape_orbit_fiber_bound (C : Set G) (hC : IsCompact C) :
    ∃ B : ℕ, ∀ (d : G) (M : Finset NZ),
      (∀ m ∈ M, sLocalNonzeroIntegerDiagonal K S m / d ∈ C) →
      ∀ q : OQ, (M.filter (fun m => probeSixthOrbit K S m = q)).card ≤ B := by
  have hfinite := finite_compact_diagonal_ratios K S Γ C hC
  let U : Finset G := hfinite.toFinset
  refine ⟨U.card, ?_⟩
  intro d M hM q
  let F : Finset NZ := M.filter (fun m => probeSixthOrbit K S m = q)
  by_cases hF : F.Nonempty
  · obtain ⟨b, hb⟩ := hF
    have hbM : b ∈ M := (Finset.mem_filter.mp hb).1
    have hbq : probeSixthOrbit K S b = q := (Finset.mem_filter.mp hb).2
    change F.card ≤ U.card
    apply Finset.card_le_card_of_injOn
      (fun a : NZ => sLocalNonzeroIntegerDiagonal K S a /
        sLocalNonzeroIntegerDiagonal K S b)
    · intro a ha
      have haM : a ∈ M := (Finset.mem_filter.mp ha).1
      have haq : probeSixthOrbit K S a = q := (Finset.mem_filter.mp ha).2
      have hab : MulAction.orbitRel (sIntegerUnitSubgroup K S Γ) NZ a b :=
        Quotient.exact (haq.trans hbq.symm)
      obtain ⟨u, hu⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
      have hdiag := sLocalNonzeroIntegerDiagonal_eq_of_unit_mul K S a b u.val hu
      apply hfinite.mem_toFinset.mpr
      constructor
      · change sLocalNonzeroIntegerDiagonal K S a /
          sLocalNonzeroIntegerDiagonal K S b ∈ (Subgroup.map (sLocalDiagonal K S) Γ : Set G)
        rw [hdiag, mul_div_cancel_right]
        exact Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩
      · refine ⟨(sLocalNonzeroIntegerDiagonal K S a / d,
          sLocalNonzeroIntegerDiagonal K S b / d), ⟨hM a haM, hM b hbM⟩, ?_⟩
        exact div_div_div_cancel_right _ _ _
    · intro a _ a' _ haa'
      exact sLocalNonzeroIntegerDiagonal_injective K S (div_left_inj.mp haa')
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ U.card
    simp only [he, Finset.card_empty, Nat.zero_le]

/-- The literal geometric finite set; membership in the fixed shape is
exported, rather than hidden behind a finite-support existence statement. -/
def probeGeometricFrequencyFinset (P : ProbeData K S) (d : G) : Finset NZ :=
  (finite_nonzeroSIntegerDiagonal_preimage_compact K S
    ((fun x : G => x * d) '' probeLogSpatialSupport K S P)
    ((isCompact_probeLogSpatialSupport K S P).image
      (continuous_id.mul continuous_const))).toFinset

theorem mem_probeGeometricFrequencyFinset (P : ProbeData K S) (d : G) (m : NZ) :
    m ∈ probeGeometricFrequencyFinset K S P d ↔
      sLocalNonzeroIntegerDiagonal K S m / d ∈ probeLogSpatialSupport K S P := by
  rw [probeGeometricFrequencyFinset, Set.Finite.mem_toFinset]
  change sLocalNonzeroIntegerDiagonal K S m ∈
    ((fun x : G => x * d) '' probeLogSpatialSupport K S P) ↔ _
  constructor
  · rintro ⟨x, hx, he⟩
    rw [← he, mul_div_cancel_right]
    exact hx
  · intro hm
    exact ⟨sLocalNonzeroIntegerDiagonal K S m / d, hm, div_mul_cancel _ _⟩

/-- This strengthened support theorem keeps the actual compact-shape witness,
the row norm bound, and the uniformly bounded original-Gamma fibers together.
The same M precedes every theta parameter and Fourier frequency. -/
theorem exists_probeSpectral_geometric_common_support (P : ProbeData K S) :
    ∃ Cball : ℝ, 0 < Cball ∧ ∃ B : ℕ,
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y),
      ∃ M : Finset NZ,
        (∀ m ∈ M, probeColumnBasePoint K S m t X Y hX hY ∈
          probeLogSpatialSupport K S P) ∧
        (∀ m ∈ M, (sIntegerElementNorm K S m).val ≤ Cball * (X * Y)) ∧
        (∀ q : OQ, (M.filter (fun m => probeSixthOrbit K S m = q)).card ≤ B) ∧
        (∀ q ∈ M.image (probeSixthOrbit K S),
          (sIntegerOrbitNorm K S Γ q).val ≤ Cball * (X * Y)) ∧
        ∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z ξ : ℝ)
          (m : NZ), m ∉ M →
          probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ = 0 := by
  obtain ⟨Cball, hCball, hnorm⟩ := exists_probeLogSchwartz_row_norm_envelope K S P
  obtain ⟨B, hB⟩ := exists_compact_shape_orbit_fiber_bound K S
    (probeLogSpatialSupport K S P) (isCompact_probeLogSpatialSupport K S P)
  refine ⟨Cball, hCball, B, ?_⟩
  intro t X Y hX hY
  let d : G := (t : G) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩
  let M₀ := probeGeometricFrequencyFinset K S P d
  let M := M₀.filter (fun m => (sIntegerElementNorm K S m).val ≤ Cball * (X * Y))
  have hshape (m : NZ) (hm : m ∈ M) :
      sLocalNonzeroIntegerDiagonal K S m / d ∈ probeLogSpatialSupport K S P :=
    (mem_probeGeometricFrequencyFinset K S P d m).mp (Finset.mem_filter.mp hm).1
  have hMnorm (m : NZ) (hm : m ∈ M) :
      (sIntegerElementNorm K S m).val ≤ Cball * (X * Y) :=
    (Finset.mem_filter.mp hm).2
  refine ⟨M, hshape, hMnorm, hB d M hshape, ?_, ?_⟩
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
    exact hMnorm m hm
  · intro ψ Q Z ξ m hm
    by_cases hm₀ : m ∈ M₀
    · have hlarge : Cball * (X * Y) < (sIntegerElementNorm K S m).val := by
        by_contra h
        exact hm (Finset.mem_filter.mpr ⟨hm₀, le_of_not_gt h⟩)
      have hz := (hnorm t X Y hX hY m hlarge).2
      simp only [probeAmplitudeSpectralRow, hz, SchwartzMap.zero_apply, zero_mul]
    · have hout : probeColumnBasePoint K S m t X Y hX hY ∉
          probeLogSpatialSupport K S P := by
        intro hx
        exact hm₀ ((mem_probeGeometricFrequencyFinset K S P d m).mpr hx)
      have hz := probeLogSchwartz_eq_zero_of_not_mem K S P _ hout
      simp [probeAmplitudeSpectralRow, hz]

/-- Finite grouping loses only the already proved geometric multiplicity.
This is algebra on the original quotient, not a moment estimate. -/
theorem sum_comp_probeSixthOrbit_le (C : Set G) (hC : IsCompact C) :
    ∃ B : ℕ, ∀ (d : G) (M : Finset NZ),
      (∀ m ∈ M, sLocalNonzeroIntegerDiagonal K S m / d ∈ C) →
      ∀ f : OQ → ℝ, (∀ q, 0 ≤ f q) →
      (∑ m ∈ M, f (probeSixthOrbit K S m)) ≤
        (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S), f q := by
  obtain ⟨B, hB⟩ := exists_compact_shape_orbit_fiber_bound K S C hC
  refine ⟨B, ?_⟩
  intro d M hM f hf
  have hpartition :
      (∑ q ∈ M.image (probeSixthOrbit K S),
        ∑ m ∈ M with probeSixthOrbit K S m = q, f (probeSixthOrbit K S m)) =
      ∑ m ∈ M, f (probeSixthOrbit K S m) :=
    Finset.sum_fiberwise_of_maps_to
      (fun m hm => Finset.mem_image_of_mem (probeSixthOrbit K S) hm) _
  rw [← hpartition]
  calc
    _ ≤ ∑ q ∈ M.image (probeSixthOrbit K S), (B : ℝ) * f q := by
      apply Finset.sum_le_sum
      intro q _
      calc
        _ = ∑ m ∈ M with probeSixthOrbit K S m = q, f q := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [(Finset.mem_filter.mp hm).2]
        _ = ((M.filter (fun m => probeSixthOrbit K S m = q)).card : ℝ) * f q := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (B : ℝ) * f q :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hB d M hM q) (hf q)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Existing genuine ideal-symbol invariance supplies the original subgroup
invariance for the completed theta sum, for all its original parameters. -/
theorem completedThetaSum_mul_sixthPowerUnits (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (γ : Γ) (m : S.integer K)
    (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ) :
    completedThetaSum K S D θ ((S.unitEquivUnitsInteger K γ.val).val * m) r Q V X =
      completedThetaSum K S D θ m r Q V X := by
  have hγ : γ.val ∈ (powMonoidHom 6 : S.unit K →* S.unit K).range := γ.property
  obtain ⟨u, hu⟩ := hγ
  change u ^ 6 = γ.val at hu
  rw [← hu, map_pow, Units.val_pow_eq_pow_val]
  exact completedThetaSum_mul_sixth_unit K S D θ u m r Q V X

/-- Literal completed theta values on every original sixth-unit sector. -/
def probeCompletedThetaOrbit (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (Z : ℝ) : OQ → ℂ :=
  Quotient.lift (fun m => completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ)
    m.val (primeSetIdeal K S ∅) Q logGaussianProfile Z) (by
      intro a b hab
      obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S Γ a b).mp hab
      have he : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
      have h := completedThetaSum_mul_sixthPowerUnits K S P.arithmetic
        (thetaPeriod K S P ψ) γ b.val (primeSetIdeal K S ∅) Q logGaussianProfile Z
      rw [he] at h
      exact h)

@[simp] theorem probeCompletedThetaOrbit_mk (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (Z : ℝ) (m : NZ) :
    probeCompletedThetaOrbit K S P ψ Q Z (probeSixthOrbit K S m) =
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
        (primeSetIdeal K S ∅) Q logGaussianProfile Z := rfl

/-- Both actual energies on the SAME compact-shape subset are bounded by
energies on its SAME original-Gamma image. Constants precede moving data. -/
theorem exists_probeSpectral_sameM_orbit_energy_transport (P : ProbeData K S) :
    ∃ B : ℕ, ∀ (d : G) (M : Finset NZ),
      (∀ m ∈ M, sLocalNonzeroIntegerDiagonal K S m / d ∈
        probeLogSpatialSupport K S P) →
      ∀ (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest) (Y ν : ℝ)
        (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
      (∑ m ∈ M, ‖actualAdditiveGramAmplitude K S P c W Y ν m.val‖ ^ 2) ≤
        (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S),
          ‖actualAdditiveGramOrbitAmplitude K S P c W Y ν q‖ ^ 2 ∧
      (∑ m ∈ M, ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
          (primeSetIdeal K S ∅) Q logGaussianProfile Z‖ ^ 2) ≤
        (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S),
          ‖probeCompletedThetaOrbit K S P ψ Q Z q‖ ^ 2 := by
  obtain ⟨B, hB⟩ := sum_comp_probeSixthOrbit_le K S
    (probeLogSpatialSupport K S P) (isCompact_probeLogSpatialSupport K S P)
  refine ⟨B, ?_⟩
  intro d M hM c W Y ν ψ Q Z
  constructor
  · simpa only [probeSixthOrbit, actualAdditiveGramOrbitAmplitude_mk] using
      hB d M hM (fun q => ‖actualAdditiveGramOrbitAmplitude K S P c W Y ν q‖ ^ 2)
        (fun q => sq_nonneg _)
  · simpa only [probeCompletedThetaOrbit_mk] using
      hB d M hM (fun q => ‖probeCompletedThetaOrbit K S P ψ Q Z q‖ ^ 2)
        (fun q => sq_nonneg _)

/-- Fully actual same-M sector interface. No compact-membership, invariance,
cardinality or convergence premise remains for a consumer to supply. The
orbit image lies in the original norm cutoff, with all sectors retained. -/
theorem exists_probeSpectral_sameM_sector_support (P : ProbeData K S) :
    ∃ Cball : ℝ, 0 < Cball ∧ ∃ B : ℕ,
      ∀ (t : sLocalNormOneGroup K S) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y),
      ∃ M : Finset NZ,
        (∀ m ∈ M, (sIntegerElementNorm K S m).val ≤ Cball * (X * Y)) ∧
        (∀ q ∈ M.image (probeSixthOrbit K S),
          (sIntegerOrbitNorm K S Γ q).val ≤ Cball * (X * Y)) ∧
        (∀ (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z ξ : ℝ)
          (m : NZ), m ∉ M →
          probeAmplitudeSpectralRow K S P ψ Q t X Y Z hX hY m ξ = 0) ∧
        ∀ (c : ExteriorIdeal K S → ℂ) (W : SmoothAnnularTest) (ν : ℝ)
          (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
        (∑ m ∈ M, ‖actualAdditiveGramAmplitude K S P c W Y ν m.val‖ ^ 2) ≤
          (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S),
            ‖actualAdditiveGramOrbitAmplitude K S P c W Y ν q‖ ^ 2 ∧
        (∑ m ∈ M, ‖completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) Q logGaussianProfile Z‖ ^ 2) ≤
          (B : ℝ) * ∑ q ∈ M.image (probeSixthOrbit K S),
            ‖probeCompletedThetaOrbit K S P ψ Q Z q‖ ^ 2 := by
  obtain ⟨Cball, hCball, B₀, hs⟩ := exists_probeSpectral_geometric_common_support K S P
  obtain ⟨B, hB⟩ := exists_probeSpectral_sameM_orbit_energy_transport K S P
  refine ⟨Cball, hCball, B, ?_⟩
  intro t X Y hX hY
  obtain ⟨M, hshape, hnorm, _hfiber, horbit, hsupp⟩ := hs t X Y hX hY
  refine ⟨M, hnorm, horbit, hsupp, ?_⟩
  intro c W ν ψ Q Z
  exact hB ((t : G) * sLocalNormSection K S ⟨X * Y, mul_pos hX hY⟩)
    M hshape c W Y ν ψ Q Z

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
