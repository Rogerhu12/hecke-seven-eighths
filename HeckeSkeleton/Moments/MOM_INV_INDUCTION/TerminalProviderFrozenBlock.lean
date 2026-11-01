import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderRectangles
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderGeometry

/-!
# A literal completed reflected block at one frozen row

The complete dual source is split into the actual retained rectangles
and a summable complementary tail. The canonical exponent is then a
conclusion of the two original norm budgets and the proved conductor
inequality. The half-powerful saving remains visible until the actual
frozen row count is inserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalFrozenBlock

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open GeneralReflectedEnergy ProviderTerminalConductor
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

def fixedData (P J f r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
    (inactive : Finset (ExteriorPrime K S))
    (haway : ∀ p ∈ inactive, ¬p.val.asIdeal ∣ (frozenIdeal K S P J f).val.val ∧
      ¬p.val.asIdeal ∣ r.val.val) : FixedData K S where
  frozen := frozenIdeal K S P J f
  puncture := r
  puncture_squarefree := hr
  rowUnit := u
  inactive := inactive
  inactive_away := haway

def fullSource (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ) (ps : Finset Ext) (k : Ext) : ℂ :=
  ∑ P ∈ ps, a P * ∑' cb : Ext × Ext, atom K S D f s F θ V X k P cb.1 cb.2

theorem fullSource_eq_rectangles_tail
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X R : ℝ) (ps : Finset Ext) (k : Ext)
    (hsum : ∀ P ∈ ps, Summable (fun cb : Ext × Ext =>
      atom K S D f s F θ V X k P cb.1 cb.2)) :
    fullSource K S D f s F θ a V X ps k =
      (∑ j ∈ TerminalRectangles.indices R,
        block K S D f s F θ a V X ps
          (TerminalRectangles.annulus K S R j.1) (TerminalRectangles.annulus K S R j.2) k) +
      TerminalSelectedTail.value K S D f s F θ a V X
        (fun cb => ¬TerminalRectangles.retained K S R cb) ps k := by
  unfold fullSource
  calc
    _ = ∑ P ∈ ps, a P *
        ((∑ j ∈ TerminalRectangles.indices R,
          ∑ c ∈ TerminalRectangles.annulus K S R j.1,
            ∑ b ∈ TerminalRectangles.annulus K S R j.2,
              atom K S D f s F θ V X k P c b) +
          ∑' cb, if ¬TerminalRectangles.retained K S R cb then
            atom K S D f s F θ V X k P cb.1 cb.2 else 0) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [TerminalRectangles.tsum_eq_rectangles_add_tail K S R _ (hsum P hP)]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      simp only [GeneralReflectedEnergy.block, Finset.mul_sum]

private theorem norm_add_sq (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The only source pieces in this Hilbert-space inequality are the
literal blocks and the literal omitted range proved above. -/
theorem fullSource_energy
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X R : ℝ) (rows ps : Finset Ext)
    (hsum : ∀ k ∈ rows, ∀ P ∈ ps, Summable (fun cb : Ext × Ext =>
      atom K S D f s F θ V X k P cb.1 cb.2))
    (B T : ℝ) (hB : 0 ≤ B)
    (hblocks : ∀ j ∈ TerminalRectangles.indices R,
      (∑ k ∈ rows, ‖block K S D f s F θ a V X ps
        (TerminalRectangles.annulus K S R j.1) (TerminalRectangles.annulus K S R j.2) k‖ ^ 2) ≤ B)
    (htail : (∑ k ∈ rows, ‖TerminalSelectedTail.value K S D f s F θ a V X
      (fun cb => ¬TerminalRectangles.retained K S R cb) ps k‖ ^ 2) ≤ T) :
    (∑ k ∈ rows, ‖fullSource K S D f s F θ a V X ps k‖ ^ 2) ≤
      2 * (((TerminalRectangles.indices R).card : ℝ) ^ 2 * B + T) := by
  let pieces (j : ℕ × ℕ) (k : Ext) := block K S D f s F θ a V X ps
    (TerminalRectangles.annulus K S R j.1) (TerminalRectangles.annulus K S R j.2) k
  have hb := finite_reconstruction_energy (TerminalRectangles.indices R) rows
    (fun _ => (1 : ℂ)) pieces (fun k => ∑ j ∈ TerminalRectangles.indices R, pieces j k)
    hB (Nat.cast_nonneg (TerminalRectangles.indices R).card)
    (fun k hk => by simp) (by simp) hblocks
  calc
    _ ≤ ∑ k ∈ rows, 2 *
        (‖∑ j ∈ TerminalRectangles.indices R, pieces j k‖ ^ 2 +
          ‖TerminalSelectedTail.value K S D f s F θ a V X
            (fun cb => ¬TerminalRectangles.retained K S R cb) ps k‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [fullSource_eq_rectangles_tail K S D f s F θ a V X R ps k (hsum k hk)]
      exact norm_add_sq _ _
    _ = 2 * ((∑ k ∈ rows, ‖∑ j ∈ TerminalRectangles.indices R, pieces j k‖ ^ 2) +
        ∑ k ∈ rows, ‖TerminalSelectedTail.value K S D f s F θ a V X
          (fun cb => ¬TerminalRectangles.retained K S R cb) ps k‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hb htail) (by norm_num)

/-- This estimate uses the actual conductor lemma, not a supplied
terminal exponent. All finite supports may retain their original zeros. -/
theorem canonical_block_energy
    (backgrounds : Finset (HeckeCharacter K))
    (F : HeckeCharacter K → FiniteMellinData K S)
    (hE : Input K S D F backgrounds)
    (L lo hi eps : ℝ) (hL : 0 < L) (hlo : 0 < lo) (hhi : lo ≤ hi) (heps : 0 < eps) :
    ∃ C Z₀ A : ℝ, ∃ Jtest : ℕ, 0 < C ∧ 1 < Z₀ ∧ 0 ≤ A ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      MarkedCoefficientReflectionInput K S D (F θ) θ →
      ∀ (P J f r : Ext) (hr : Squarefree r.val.val) (u : S.unit K)
        (inactive : Finset (ExteriorPrime K S))
        (haway : ∀ p ∈ inactive, ¬p.val.asIdeal ∣ (frozenIdeal K S P J f).val.val ∧
          ¬p.val.asIdeal ∣ r.val.val)
        (s : FrozenState K S (frozenIdeal K S P J f) r)
        (W : SmoothAnnularTest) (Z N V M Q z d c cstar O H za v ell h tau amp : ℝ),
      Z₀ ≤ Z → Powerful P.val →
      BoundedSource K S (fixedData K S P J f r hr u inactive haway) Z L (N - 3 * h) H za →
      0 ≤ O → 0 ≤ za → za ≤ z → 0 ≤ v → v ≤ L → 0 ≤ ell → ell ≤ L →
      0 ≤ h → h ≤ d → 0 ≤ amp →
      exteriorNorm K S f ≤ Z ^ V → exteriorNorm K S r ≤ Z ^ Q →
      0 ≤ M → 0 ≤ Q → V ≤ d →
      HeckePort.Moments.CanonicalMargins (N + V) M Q z c →
      0 < cstar → cstar / 2 ≤ c → d ≤ cstar / 200 →
      tau ≤ cstar / 1000 → eps ≤ cstar / 1000 →
      v + 3 * ell ≤ threshold K S
        (fixedData K S P J f r hr u inactive haway) s Z (N - 3 * h) H za + tau →
      Function.support W.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps cs bs : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, exteriorNorm K S (exteriorMul K S (exteriorMul K S P J) k) ≤ Z ^ M) →
      Z ^ O ≤ exteriorNorm K S P →
      (∀ k ∈ rows, InAnnulus K S Z H k) →
      (∀ p ∈ ps, InAnnulus K S Z za p) →
      (∀ b ∈ cs, InAnnulus K S Z v b) →
      (∀ b ∈ bs, InAnnulus K S Z ell b) →
      (∀ p ∈ ps, ‖a p‖ ≤ amp) →
      (∑ k ∈ rows, ‖block K S D (fixedData K S P J f r hr u inactive haway) s
        (F θ) θ a W.toFun (Z ^ (N - 3 * h)) ps cs bs k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm W.toFun Jtest A ^ 2 *
          ‖inactiveWeight K S (fixedData K S P J f r hr u inactive haway)‖ ^ 2 *
            Z ^ (N + V - cstar / 4 - O / 2) := by
  obtain ⟨C, Z₀, A, Jtest, hC, hZ₀, hA, hb⟩ :=
    hE.block_energy L lo hi eps hL hlo hhi heps
  refine ⟨C, Z₀, A, Jtest, hC, hZ₀, hA, ?_⟩
  intro θ hθ hreflection P J f r hr u inactive haway s W Z N V M Q z d c cstar O H za v ell h tau amp
    hZ hP hsource hO hza hz hv hvL hell hellL hh hd hamp hf hpuncture hM hQ hV hinv
    hcstar hc hdsmall htau hepssmall hretained hW rows ps cs bs a hrows hpower
    hrowsWindow hps hcs hbs ha
  have hZ' : 1 < Z := hZ₀.trans_le hZ
  have hhblock := hb θ hθ hreflection _ s W Z (N - 3 * h) H za v ell amp hZ hsource
    hv hvL hell hellL hamp hW rows ps cs bs a hrowsWindow hps hcs hbs ha
  by_cases hne : rows.Nonempty
  · obtain ⟨k, hk⟩ := hne
    let g := TerminalGeometry.actualGeometry K S hZ' P J f r k hP s (hrows k hk)
      hpower (hrowsWindow k hk).1 hf hpuncture hO hza hz hv hell
      (le_refl (0 : ℝ)) hh (by simpa using hd) hretained
    have hsaving := g.exponent_saving hinv hQ hM hV hcstar hc hdsmall
      (by linarith : (0 : ℝ) ≤ cstar / 1000) htau hepssmall
    have he : exponent K S (fixedData K S P J f r hr u inactive haway) s
        Z (N - 3 * h) H za v ell + eps ≤ N + V - cstar / 4 - O / 2 := by
      dsimp only [g, TerminalGeometry.actualGeometry, TerminalBlockGeometry.exponent] at hsaving
      unfold exponent threshold HeckePort.Moments.reflectedExponent at *
      dsimp only [fixedData] at *
      linarith
    exact hhblock.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ'.le he) (by positivity))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalFrozenBlock

end
