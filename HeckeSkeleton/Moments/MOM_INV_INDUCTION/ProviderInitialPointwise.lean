import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialNodes
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialMass
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialProduction

/-!
# Initial physical normalization and the actual reconstruction sum

The expression bounded here is the literal positive initial source,
with its adaptive Poisson scalar, independent overlap, original marked
coefficients and actual canonical rows. The class estimate is supplied
only by the genuine uniform node bound. All three remaining small
powers are chosen before the source, and the original normalization
cancels to the original moment exponent m.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialPointwise

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools ProviderNodes
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
variable {σ : Type u} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)
variable (W : SchwartzMap ℝ ℂ) (G : HeckeCharacter K) (hG : G ∈ Θ)
variable (hbase : 1 < C.base) (hW : tsupport W ⊆ Set.Icc (1 : ℝ) 2)
variable (m : ℝ) (H : ProviderInitialSource.Cutoff K S)
local notation "X" => C.base ^ C.length
local notation "Idx" => ProviderInitialSource.Index K S D Γ X H

def sourceSum (P : Finset Idx) (b : SecondMobiusGeometry.Index X)
    (J : Finset σ) (e t : ℝ) : ℝ :=
  X⁻¹ * ∑ i ∈ P,
    ProviderInitialProduction.positiveScalar K S D Γ C Θ ψ hν W hbase hW m H e i *
      ‖SecondColumnEnergy.overlapZero K S (ProviderInitialSource.common K S D Γ X H i)
        (FirstInversePoisson.unitIdeal K S) (ProviderInitialSource.overlap K S D Γ X H i)‖ *
      ‖divisorMark J C.primeLists C.primeWeights
        ((ProviderInitialSource.common K S D Γ X H i).val.val *
          (ProviderInitialSource.overlap K S D Γ X H i).val.val)‖ ^ 2 *
      ‖childValue K Sset D (ProviderInitialNodes.wideFamily K S C Θ ψ hν W G hG J b t)
        (CanonicalSectors.sectorUnit K Sset Γ) (ProviderInitialSource.child K S D Γ X H i)‖ ^ 2

theorem sourceSum_nonneg (P : Finset Idx) (b : SecondMobiusGeometry.Index X)
    (J : Finset σ) (e t : ℝ) :
    0 ≤ sourceSum K S D Γ C Θ ψ hν W G hG hbase hW m H P b J e t := by
  unfold sourceSum
  apply mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (zero_lt_one.trans hbase).le _))
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (mul_nonneg
      (ProviderInitialProduction.positiveScalar_nonneg K S D Γ C Θ ψ hν W hbase hW m H e i)
      (norm_nonneg _)) (sq_nonneg _)) (sq_nonneg _)

/-- Uniform initial source control from the proved node class. The
only energy premise is `UniformBound` at the canonical initial stage;
the actual source, scalar, frozen mass and finite fibers are derived. -/
theorem exists_uniform_source_bound (slotCap : ℕ) (A pi : ℝ)
    (hA : 0 ≤ A) (hpi : 0 < pi) (q : Finset (ℕ × ℕ)) :
    ∃ e : ℝ, 0 < e ∧ ∃ s : Finset (ℕ × ℕ), ∃ B : ℝ, 0 ≤ B ∧
      ∀ {σ₀ : Type u} [DecidableEq σ₀]
        (C₀ : CanonicalBlock.ColumnData K S σ₀)
        (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ : HeckeCharacter K)
        (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ C₀.background)
        (W₀ : SchwartzMap ℝ ℂ) (G₀ : HeckeCharacter K) (hG₀ : G₀ ∈ Θ₀)
        (hbase₀ : 1 < C₀.base) (hW₀ : tsupport W₀ ⊆ Set.Icc (1 : ℝ) 2)
        (m Q z c h tau lo hi eps Cih : ℝ) (markLengths : σ₀ → ℝ)
        (H₀ : ProviderInitialSource.Cutoff K S)
        (P₀ : Finset (ProviderInitialSource.Index K S D Γ (C₀.base ^ C₀.length) H₀))
        (b₀ : SecondMobiusGeometry.Index (C₀.base ^ C₀.length))
        (j₀ : ProviderInitialBoxes.BoxIndex C₀.base A)
        (J₀ : Finset σ₀) (Lambda : HeckeCharacter K),
      0 ≤ m → C₀.length ≤ A → 0 ≤ Q → 0 ≤ z → h ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau →
      2 ≤ C₀.base ^ h → 4 * C₀.base ^ C₀.length ≤ C₀.base ^ A →
      C₀.length + Q + z ≤ m - c → 2 * C₀.length + 6 * z ≤ 3 * m - c →
      100 * h + 3 * tau ≤ c / 4 →
      H₀ = SecondAdaptiveCutoff.fineCutoff K S
        (ProviderInitialProduction.parent K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m).radius
        (C₀.base ^ C₀.length) C₀.base tau →
      C₀.lambda = Lambda → ThetaCalibrationInput K Sset D C₀.lambda G₀ →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C₀.background p) →
      C₀.puncture ≠ 0 → (C₀.puncture.radical.absNorm : ℝ) ≤ C₀.base ^ Q →
      MarkConditions K S slotCap C₀.base z lo hi C₀.slots C₀.primeLists
        C₀.primeWeights markLengths → J₀ ⊆ C₀.slots →
      0 ≤ eps → 0 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ₀) (ψ := ψ₀) D Lambda G₀ slotCap C₀.base m
        (3 * c / 4) z lo hi eps m Cih q →
      ∀ t : ℝ,
      sourceSum K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ hW₀ m H₀
        (ProviderInitialBoxes.boxed K S D Γ (C₀.base ^ C₀.length) H₀ P₀ b₀ C₀.base A j₀)
        b₀ J₀ e t ≤
      B * (Cih + (Fintype.card Sector : ℝ)) *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 t)) ^ 2 *
        C₀.base ^ (m + 48 * h + 3 * pi + eps) := by
  obtain ⟨e, he, hscalar⟩ := ProviderInitialProduction.exists_uniform_scalar_bound K S D Γ A pi hA hpi
  obtain ⟨s, Braw, hBraw, hraw⟩ :=
    ProviderInitialNodes.exists_uniform_raw_bound K S D Γ slotCap A pi hA hpi q
  obtain ⟨Bmass, hBmass, hmass⟩ := ProviderInitialMass.exists_packet_mass_bound K S D Γ
    slotCap A pi hA hpi
  let B := ActualPoissonScale.fieldConstant K * Braw * Bmass
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K) hBraw.le) hBmass.le
  refine ⟨e, he, s, B, hB, ?_⟩
  intro σ₀ _ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ hW₀
    m Q z c h tau lo hi eps Cih markLengths H₀ P₀ b₀ j₀ J₀ Lambda
    hm hL hQ hz hh htau hwidth hbox hsource₁ hsource₂ hloss hcutoff
    hLambda hcal hbg hRho hRhoNorm hmarks hJ heps hCih hih t
  let Pg := ProviderInitialBoxes.boxed K S D Γ (C₀.base ^ C₀.length) H₀ P₀ b₀ C₀.base A j₀
  have hprime : ∀ i ∈ J₀, ∀ p ∈ C₀.primeLists i, Prime p :=
    fun i hi => hmarks.prime i (hJ hi)
  have hcap : J₀.card ≤ slotCap := (Finset.card_le_card hJ).trans hmarks.card_le
  let Qp := ProviderInitialSource.packet K S D Γ (C₀.base ^ C₀.length) H₀ J₀ C₀.primeLists
    hprime slotCap hcap Pg
  let F := childValue K Sset D (ProviderInitialNodes.wideFamily K S C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ J₀ b₀ t)
    (CanonicalSectors.sectorUnit K Sset Γ)
  let R := ProviderInitialBoxes.length C₀.base j₀ 0 - ProviderInitialBoxes.length C₀.base j₀ 1 + 2 * h
  let N := Real.logb C₀.base (SecondMobiusGeometry.childScale (C₀.base ^ C₀.length) b₀)
  let Vc := ProviderInitialGeometry.labelLength (ProviderInitialBoxes.length C₀.base j₀ 1)
    (ProviderInitialBoxes.length C₀.base j₀ 2) h
  let Qtest := (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 t)) ^ 2
  let Craw := Braw * (Cih + (Fintype.card Sector : ℝ)) * Qtest
  let E := 2 * (max 0 N + Vc) + 28 * h + eps + pi
  let Pscalar := ActualPoissonScale.fieldConstant K * C₀.base ^ (m - 2 * C₀.length + R + pi)
  have hCr : 0 ≤ Craw := by dsimp only [Craw, Qtest]; positivity
  have hPs : 0 ≤ Pscalar := mul_nonneg (ActualPoissonScale.fieldConstant_nonneg K)
    (Real.rpow_nonneg (zero_lt_one.trans hbase₀).le _)
  by_cases hne : Pg.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hne
    have hlen := ProviderInitialBoxes.child_length K S D Γ (C₀.base ^ C₀.length) H₀
      P₀ b₀ C₀.base A h hbase₀ hh.1 hwidth hbox j₀ C₀.length rfl i₀ hi₀
    have hpoint : ∀ gamma ∈ Qp.triples, Qp.energy F gamma ≤ Craw * C₀.base ^ E := by
      intro gamma hgamma
      exact hraw C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ H₀ J₀ hprime hcap P₀ b₀ j₀
        Lambda (ProviderInitialProduction.parent K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m).radius
        m Q z c h tau lo hi eps Cih markLengths hQ hz hh htau hwidth hbox
        hsource₁ hsource₂ hloss
        (ProviderInitialProduction.parent_radius K S C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m).le
        hcutoff hLambda hcal hbg hRho hRhoNorm hmarks heps hCih hih t gamma hgamma
    have hm0 := hmass J₀ C₀.primeLists hprime hcap (C₀.base ^ C₀.length) H₀
      P₀ b₀ C₀.base h j₀ hbase₀ hh hwidth hbox
    change (∑ gamma ∈ Qp.triples, tripleDivisorWeight slotCap gamma) ≤
      Bmass * C₀.base ^ (R + pi) at hm0
    have hpacket : (∑ gamma ∈ Qp.triples, tripleDivisorWeight slotCap gamma * Qp.energy F gamma) ≤
        (Bmass * C₀.base ^ (R + pi)) * (Craw * C₀.base ^ E) := by
      calc
        _ ≤ ∑ gamma ∈ Qp.triples, tripleDivisorWeight slotCap gamma * (Craw * C₀.base ^ E) :=
          Finset.sum_le_sum (fun gamma hgamma => mul_le_mul_of_nonneg_left
            (hpoint gamma hgamma) (tripleDivisorWeight_nonneg slotCap gamma))
        _ = (∑ gamma ∈ Qp.triples, tripleDivisorWeight slotCap gamma) *
            (Craw * C₀.base ^ E) := (Finset.sum_mul ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hm0
          (mul_nonneg hCr (Real.rpow_nonneg (zero_lt_one.trans hbase₀).le _))
    have hsource : sourceSum K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ hW₀ m H₀
        Pg b₀ J₀ e t ≤
        Pscalar * ∑ gamma ∈ Qp.triples, tripleDivisorWeight slotCap gamma * Qp.energy F gamma := by
      have hmark := ProviderInitialSource.marked_energy_le_packet K S D Γ (C₀.base ^ C₀.length)
        H₀ J₀ C₀.primeLists hprime slotCap hcap C₀.primeWeights
        (fun i hi => hmarks.weights_le i (hJ hi)) Pg F
      apply le_trans _ (mul_le_mul_of_nonneg_left hmark hPs)
      unfold sourceSum
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hiP
      have hs := hscalar C₀ Θ₀ ψ₀ hν₀ W₀ hbase₀ hW₀ m H₀ P₀ b₀ h j₀
        hm hL hh.1 hwidth hbox i hiP
      have hnonneg : 0 ≤
          ‖SecondColumnEnergy.overlapZero K S (ProviderInitialSource.common K S D Γ
            (C₀.base ^ C₀.length) H₀ i) (FirstInversePoisson.unitIdeal K S)
            (ProviderInitialSource.overlap K S D Γ (C₀.base ^ C₀.length) H₀ i)‖ *
          ‖divisorMark J₀ C₀.primeLists C₀.primeWeights
            ((ProviderInitialSource.common K S D Γ (C₀.base ^ C₀.length) H₀ i).val.val *
              (ProviderInitialSource.overlap K S D Γ (C₀.base ^ C₀.length) H₀ i).val.val)‖ ^ 2 *
          ‖F (ProviderInitialSource.child K S D Γ (C₀.base ^ C₀.length) H₀ i)‖ ^ 2 := by positivity
      convert mul_le_mul_of_nonneg_right hs hnonneg using 1 <;>
        dsimp only [Pscalar, R, F] <;> ring
    have heq : Pscalar * ((Bmass * C₀.base ^ (R + pi)) * (Craw * C₀.base ^ E)) =
        B * (Cih + (Fintype.card Sector : ℝ)) * Qtest *
          C₀.base ^ ((m - 2 * C₀.length + R + pi) + (R + pi) + E) := by
      dsimp only [Pscalar, Craw, B]
      rw [Real.rpow_add (zero_lt_one.trans hbase₀), Real.rpow_add (zero_lt_one.trans hbase₀)]
      ring
    have hpower : (m - 2 * C₀.length + R + pi) + (R + pi) + E ≤
        m + 48 * h + 3 * pi + eps := by
      have hb := ProviderInitialGeometry.closed_exponent_budget m C₀.length
        (ProviderInitialBoxes.length C₀.base j₀ 0) (ProviderInitialBoxes.length C₀.base j₀ 1)
        (ProviderInitialBoxes.length C₀.base j₀ 2) h N pi eps hh.1 hlen.2.1 hlen.2.2
      dsimp only [R, E, Vc]
      linarith
    apply (hsource.trans (mul_le_mul_of_nonneg_left hpacket hPs)).trans
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase₀.le hpower)
      (mul_nonneg (mul_nonneg hB (add_nonneg hCih (Nat.cast_nonneg _))) (sq_nonneg _))
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    change sourceSum K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ hW₀ m H₀ Pg b₀ J₀ e t ≤ _
    simp only [sourceSum, hempty, Finset.sum_empty, mul_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hB (add_nonneg hCih (Nat.cast_nonneg _))) (sq_nonneg _))
      (Real.rpow_nonneg (zero_lt_one.trans hbase₀).le _)

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialPointwise

end
