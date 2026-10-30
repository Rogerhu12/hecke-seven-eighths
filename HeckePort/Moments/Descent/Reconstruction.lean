import HeckePort.Moments.Descent.Decomposition
import HeckePort.Moments.Descent.Hybrid

/-!
# Reconstructing a supported hybrid row from its column data

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/Reconstruction.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

As in `Descent/Hybrid`, the cubic kernel `inverseCubicKernel` and the quadratic row
`quadraticRow · (primaryGenerator ·)` are the abstract `κ`, `q` (`CubicKernelAxioms`), and
"the primary generator is nonzero" is the predicate `Ext`.  The square-mask identity that openai
derives from admissibility of `k` (`hybrid_quadratic_square_mask`) is the hypothesis `hsq`,
exactly as in `hybrid_original_kernel_decomposition`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

def supportedHybridRow (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) : ℂ :=
  ∑ p ∈ S, ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta p.1 p.2 *
    (q k (p.1 * p.2) * κ P p.1 *
      (if IsCoprime P p.2 then 1 else 0) * (if IsCoprime k P then 1 else 0))

theorem supportedHybridRow_product (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (nset bset Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) :
    supportedHybridRow κ q (nset ×ˢ bset) Pset a beta k = hybridRow κ q Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

def reconstructedHybridTerm (κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K)) (P : Ideal (𝓞 K))
    (d : HybridColumnData K) : ℂ :=
  a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) *
    ((if IsCoprime k d.square then 1 else 0) *
      (if IsCoprime k (P * d.common) then 1 else 0) *
      q k (d.residualN * d.residualB) *
      κ P (d.common * d.residualN) *
      (if IsCoprime P (d.residualB * d.square) then 1 else 0))

theorem supportedHybridRow_reconstruct {Ext : Ideal (𝓞 K) → Prop}
    {κ q : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (S : Finset (Ideal (𝓞 K) × Ideal (𝓞 K))) (Pset : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ ⊥ ∧ Ext p.1 ∧ Ext p.2)
    (hP : ∀ P ∈ Pset, Ext P)
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K))
    (hsq : ∀ d : HybridColumnData K, d.reconstruct ∈ S →
      q k ((d.common * d.residualN) * ((d.common * d.residualB) * d.square ^ 2)) =
        (if IsCoprime k (d.common * d.square) then 1 else 0) *
          q k (d.residualN * d.residualB)) :
    supportedHybridRow κ q S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm κ q a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition hκ k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square (hP P hPP) hdprim.2.2.1 rfl rfl (hsq d hdS))

end HeckePort.Moments

end
