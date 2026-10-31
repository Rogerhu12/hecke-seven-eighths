import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialBoxes

/-!
# The actual initial frozen measure

The initial one-pass source freezes only the residual g/d. Its other
two outer ideals are literally one. The divisor-weighted mass is bounded
by the proved reconstruction measure on distinct triples, never by an
assumed fiber or source-energy estimate. The small-power exponent and
constant are chosen before every norm box and actual source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialMass

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

theorem exists_packet_mass_bound (slotCap : ℕ) (A pi : ℝ)
    (hA : 0 ≤ A) (hpi : 0 < pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ {σ : Type*} [DecidableEq σ]
      (J : Finset σ) (lists : σ → Finset (Ideal (𝓞 K)))
      (hprime : ∀ i ∈ J, ∀ p ∈ lists i, Prime p) (hcap : J.card ≤ slotCap)
      (X : ℝ) (H : ProviderInitialSource.Cutoff K S)
      (P : Finset (ProviderInitialSource.Index K S D Γ X H))
      (b : SecondMobiusGeometry.Index X) (Z h : ℝ)
      (j : ProviderInitialBoxes.BoxIndex Z A),
      1 < Z → h ∈ Set.Icc (0 : ℝ) 1 → 2 ≤ Z ^ h → 4 * X ≤ Z ^ A →
      let Q := ProviderInitialSource.packet K S D Γ X H J lists hprime slotCap hcap
        (ProviderInitialBoxes.boxed K S D Γ X H P b Z A j)
      (∑ gamma ∈ Q.triples, tripleDivisorWeight slotCap gamma) ≤
        C * Z ^ (ProviderInitialBoxes.length Z j 0 - ProviderInitialBoxes.length Z j 1 +
          2 * h + pi) := by
  let e := pi / (A + 2)
  have hden : 0 < A + 2 := by linarith
  have he : 0 < e := div_pos hpi hden
  obtain ⟨C, hC, hm⟩ := exists_sourceTriples_normalized_mass_bound
    (K := K) (Sector := Sector) slotCap e he
  refine ⟨C, hC, ?_⟩
  intro σ _ J lists hprime hcap X H P b Z h j hZ hh hwidth hbox
  let Pg := ProviderInitialBoxes.boxed K S D Γ X H P b Z A j
  let Q := ProviderInitialSource.packet K S D Γ X H J lists hprime slotCap hcap Pg
  let R := ProviderInitialBoxes.length Z j 0 - ProviderInitialBoxes.length Z j 1 + 2 * h
  change (∑ gamma ∈ Q.triples, tripleDivisorWeight slotCap gamma) ≤ C * Z ^ (R + pi)
  by_cases hne : Q.triples.Nonempty
  · have hnorm : ∀ gamma ∈ Q.triples,
        (gamma.q0.absNorm : ℝ) ≤ 1 ∧ (gamma.quotient.absNorm : ℝ) ≤ 1 ∧
          (gamma.residual.absNorm : ℝ) ≤ Z ^ R := by
      intro gamma hgamma
      obtain ⟨i, hi, rfl⟩ := ProviderInitialSource.packet_triple_member K S D Γ X H J lists
        hprime slotCap hcap Pg gamma hgamma
      refine ⟨by simp [ProviderInitialSource.outer], by simp [ProviderInitialSource.outer], ?_⟩
      exact ProviderInitialBoxes.residual_norm K S D Γ X H P b Z A h hZ hh.1 hwidth hbox
        j i (Finset.mem_filter.mp hi).1
    have hRone : 1 ≤ Z ^ R := by
      obtain ⟨gamma, hgamma⟩ := hne
      exact SourceLengths.one_le_norm_cap gamma.residual (Q.outer_nonzero gamma hgamma).2.2
        _ (hnorm gamma hgamma).2.2
    have hm' := hm Q.source Q.oldLists Q.newLists Q.keep 1 1 (Z ^ R)
      le_rfl le_rfl hRone
      (fun x hx => hnorm x.outer (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
      (fun x hx => Q.outer_nonzero x.outer (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    simp only [one_mul] at hm'
    change (∑ gamma ∈ Q.triples, tripleDivisorWeight slotCap gamma) / Z ^ R ≤
      C * (Z ^ R) ^ e at hm'
    have hRcap : R ≤ A + 2 := by
      have hg := (ProviderInitialBoxes.length_bounds Z A hZ hA j 0).2
      have hd := (ProviderInitialBoxes.length_bounds Z A hZ hA j 1).1
      dsimp only [R]
      linarith [hh.2]
    have hRe : R * e ≤ pi := by
      calc
        _ ≤ (A + 2) * e := mul_le_mul_of_nonneg_right hRcap he.le
        _ = pi := by dsimp only [e]; field_simp [hden.ne']
    have hpow : (Z ^ R) ^ e ≤ Z ^ pi := by
      rw [← Real.rpow_mul (zero_lt_one.trans hZ).le]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le hRe
    calc
      _ ≤ (C * (Z ^ R) ^ e) * Z ^ R :=
        (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) R)).mp hm'
      _ ≤ (C * Z ^ pi) * Z ^ R :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans hZ)]; congr 2; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact mul_nonneg hC.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialMass

end
