import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionPacket
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBoxes
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualBoxGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.PositivePacketBudget

/-!
# The genuine boxed second source under the smaller-child hypothesis

This module combines the actual source integral, its automatically
reconstructed packet, and the physical fixed-triple budget. The
counting constant is chosen before all source data and frequencies.
The only energy assumption is the normalized estimate for each smaller
literal canonical child. The physical scalar hypothesis concerns the
original numerical source factors, and the arithmetic norm-box
condition is proved from the original pools.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy FirstParentRows FirstToSecondData CommonKernel
  CanonicalNormPools ActualProductionBoxes ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
local notation "transport" => ActualMaskReconstruction.sectorTransport K S D Γ

/-- The fixed divisor-counting constant does not take a source,
an original prime list, a norm box, a test, or a frequency argument. -/
def massConstant (slotCap : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) : ℝ :=
  Classical.choose (PositivePacketBudget.exists_centered_positive_budget
    (K := K) transport slotCap massEps hmassEps)

theorem massConstant_pos (slotCap : ℕ) (massEps : ℝ) (hmassEps : 0 < massEps) :
    0 < massConstant K S D Γ slotCap massEps hmassEps :=
  (Classical.choose_spec (PositivePacketBudget.exists_centered_positive_budget
    (K := K) transport slotCap massEps hmassEps)).1

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T,
  ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) →
    Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ) (hmask : T.mask = ∅)
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
variable (P : Finset (ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂))
variable (Z L ell h : ℝ) (j : BoxIndex Z L)
local notation "Pbox" => SecondProductionBoxes.normBox K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask P Z L j
variable (hprime : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k, Prime p)
variable (hweights : ∀ k ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists k,
  ‖T.columns.primeWeights k p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (side₁ : Bool) (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "packet" => SecondProductionPacket.packet K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap
local notation "ALen" => extractedLength Z j side₁
local notation "BLen" => length Z j .firstCommon
local notation "RLen" => length Z j .activeConductor
local notation "JLen" => length Z j .cubeLabel
local notation "deltaLen" => length Z j .firstDivisor
local notation "tLen" => length Z j .firstOverlap
local notation "gLen" => length Z j .secondCommon
local notation "thetaLen" => length Z j .secondDivisor
local notation "vLen" => length Z j .secondOverlap

/-- The left side is the original finite-source integral with its
unchanged original marks, retained zeros and actual child columns.
All reconstruction and triple norm-box premises are discharged here.
The displayed scalar bound is a bound on actual individual numerical
factors, to be supplied by the first and second physical prefactors. -/
theorem sourceIntegral_le_smaller_children
    (M r V eta tau pi eps Nactual Cphysical massEps : ℝ)
    (hmassEps : 0 < massEps) (hZ : 1 < Z) (hh : 0 ≤ h) (hmesh : h ≤ eta / 16)
    (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hcube : ∀ b ∈ T.cubes, height K Sset b ≤ Z ^ (ell + h))
    (hCphysical : 0 ≤ Cphysical)
    (hlo : secondFormalColumn r ALen BLen tLen gLen vLen - 5 * h ≤ Nactual)
    (hhi : Nactual ≤ secondFormalColumn r ALen BLen tLen gLen vLen + 8 * h)
    (hlive : -2 * h ≤ Nactual)
    (hloss : massEps * (secondCount ell RLen JLen tLen gLen thetaLen + 11 * h / 2) ≤ pi)
    (m : ℕ) (side₂ : Bool) (b : SecondMobiusGeometry.Index X)
    (hw : ∀ i ∈ Pbox, 0 ≤ w i.1 i.2.1)
    (hphysical : ∀ i ∈ Pbox, w i.1 i.2.1 *
      SecondProductionPacket.radialWeight K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ ε i *
      FirstProductionWeight.physicalCost K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask i ≤
        Cphysical *
          (Z ^ (firstKappa M r ell V deltaLen ALen BLen RLen + (9 / 2 : ℝ) * h) *
            Z ^ (secondLambda M r ell V deltaLen ALen BLen JLen tLen gLen thetaLen +
              18 * h + tau)))
    (Cchild : LogPlane × ℝ → ℝ) (hCchild : ∀ p, 0 ≤ Cchild p)
    (htest : Integrable
      (fun p : LogPlane × ℝ => SecondProductionIntegral.jointDensity s m p * Cchild p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)))
    (hchild : ∀ p : LogPlane × ℝ, ∀ γ ∈ (packet).triples,
      normalizedChildEnergy Z (max 0 Nactual)
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
        slotCap (packet).labels (packet).rows
        (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ ≤
      Cchild p * Z ^ (max 0 Nactual + secondFormalLabel BLen thetaLen vLen JLen + 4 * h + eps)) :
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ m side₂ Pbox b J₂ ≤
      (Cphysical * massConstant K S D Γ slotCap massEps hmassEps *
        Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps)) *
          ∫ p : LogPlane × ℝ, SecondProductionIntegral.jointDensity s m p * Cchild p
            ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  let physicalPower :=
    Z ^ (firstKappa M r ell V deltaLen ALen BLen RLen + (9 / 2 : ℝ) * h) *
      Z ^ (secondLambda M r ell V deltaLen ALen BLen JLen tLen gLen thetaLen +
        18 * h + tau)
  let cost := Cphysical * physicalPower
  let targetPower := Z ^ (r + 3 * ell + V + 40 * eta + tau + pi + eps)
  let e : LogPlane × ℝ → ℝ :=
    SecondProductionPacket.packetEnergy K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap side₂ b
  have hnorm := SecondProductionBoxes.packet_source_norm_box K S D Γ T Θ ψ G
    hν hG hbase R U J₁ s H₂ hmask P Z L ell h hZ hh hwidth
    hb hfirst hsecond hcube j hprime hweights hJ₁ J₂ hJ₂ side₁ slotCap hcap
  have hbudget := (Classical.choose_spec
    (PositivePacketBudget.exists_centered_positive_budget
      (K := K) transport slotCap massEps hmassEps)).2
  have hp : ∀ p : LogPlane × ℝ,
      physicalPower * e p ≤
        massConstant K S D Γ slotCap massEps hmassEps * Cchild p * targetPower := by
    intro p
    exact hbudget packet Z M r ell V deltaLen ALen BLen RLen JLen tLen gLen thetaLen vLen
      h eta tau pi eps Nactual (Cchild p) hZ.le hh hmesh (hCchild p)
      hlo hhi hlive hloss hnorm
      (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) (hchild p)
  have hcost : 0 ≤ cost := mul_nonneg hCphysical
    (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
  have hs := SecondProductionPacket.sourceIntegral_le_packetIntegral
    K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ w ε hmask
    hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap m side₂ b
    cost hcost hw hphysical
  have hi : Integrable
      (fun p : LogPlane × ℝ => SecondProductionIntegral.jointDensity s m p * e p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) :=
    SecondProductionPacket.packetEnergy_integrable K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap m side₂ b
  have hj := htest.const_mul
    (Cphysical * massConstant K S D Γ slotCap massEps hmassEps * targetPower)
  calc
    _ ≤ cost * ∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s m p * e p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := hs
    _ = ∫ p : LogPlane × ℝ, cost *
        (SecondProductionIntegral.jointDensity s m p * e p)
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := (integral_const_mul _ _).symm
    _ ≤ ∫ p : LogPlane × ℝ,
        (Cphysical * massConstant K S D Γ slotCap massEps hmassEps * targetPower) *
          (SecondProductionIntegral.jointDensity s m p * Cchild p)
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
      apply integral_mono (hi.const_mul cost) hj
      intro p
      have hp' := mul_le_mul_of_nonneg_left (hp p)
        (mul_nonneg hCphysical (SecondProductionIntegral.jointDensity_nonneg s m p))
      convert hp' using 1 <;> dsimp only [cost] <;> ring
    _ = _ := integral_const_mul _ _

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondProductionBudget

end

