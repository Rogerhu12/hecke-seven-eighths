import PrimeCancellationPrimeSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Set.Finite.Basic

/-!
# Euler derivatives of normalized prime windows

The window transform associated with logarithmic differentiation in the
scale is `T W = -x * W' - W / 2`.  It preserves smoothness and topological
support.  The scale derivative identity is first proved for a fixed finite
pool.  The arbitrary finite-subset counting hypothesis then proves that
bounded norm sets are finite, giving a common pool on a neighborhood of
each positive scale and the same identity for the actual prime `tsum`.

No interchange of a derivative with an infinite series is assumed.
The common pool is local in the scale, not a single pool for all scales.
-/

set_option autoImplicit false
noncomputable section

namespace PrimeCancellationEulerDerivatives

open Function Filter Set
open scoped Classical BigOperators Topology ContDiff
open PrimeCancellationPrimeSeries

variable {α : Type*}

def eulerDerivative (W : ℝ → ℂ) (x : ℝ) : ℂ :=
  x • deriv W x

def normalizedEulerTransform (W : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(eulerDerivative W x) - (1 / 2 : ℝ) • W x

def normalizedPrimePolynomial (pool : Finset α) (ν : α → ℝ)
    (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  (P ^ (-(1 / 2 : ℝ))) • ∑ p ∈ pool, a p * W (ν p / P)

def normalizedPrimeSum (ν : α → ℝ) (a : α → ℂ)
    (W : ℝ → ℂ) (P : ℝ) : ℂ :=
  (P ^ (-(1 / 2 : ℝ))) • primeSum ν a W P

/-! ## The window transform -/

theorem contDiff_eulerDerivative {W : ℝ → ℂ}
    (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (eulerDerivative W) := by
  change ContDiff ℝ ∞ (fun x : ℝ => x • deriv W x)
  exact contDiff_id.smul (contDiff_infty_iff_deriv.mp hW).2

theorem contDiff_normalizedEulerTransform {W : ℝ → ℂ}
    (hW : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (normalizedEulerTransform W) := by
  change ContDiff ℝ ∞ (fun x : ℝ => -(eulerDerivative W x) - (1 / 2 : ℝ) • W x)
  exact (contDiff_eulerDerivative hW).neg.sub (hW.const_smul (1 / 2 : ℝ))

theorem support_normalizedEulerTransform_subset (W : ℝ → ℂ) :
    Function.support (normalizedEulerTransform W) ⊆ tsupport W := by
  intro x hx
  by_contra hxt
  have hzero : W x = 0 := by
    by_contra hne
    exact hxt (subset_closure hne)
  have hderiv : deriv W x = 0 := deriv_of_notMem_tsupport hxt
  exact hx (by simp [normalizedEulerTransform, eulerDerivative, hzero, hderiv])

theorem tsupport_normalizedEulerTransform_subset (W : ℝ → ℂ) :
    tsupport (normalizedEulerTransform W) ⊆ tsupport W :=
  closure_minimal (support_normalizedEulerTransform_subset W) isClosed_closure

theorem support_normalizedEulerTransform_subset_Icc {W : ℝ → ℂ}
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    Function.support (normalizedEulerTransform W) ⊆ Icc (1 : ℝ) 2 :=
  (support_normalizedEulerTransform_subset W).trans
    (closure_minimal hsupport isClosed_Icc)

theorem hasCompactSupport_normalizedEulerTransform {W : ℝ → ℂ}
    (hW : HasCompactSupport W) : HasCompactSupport (normalizedEulerTransform W) :=
  hW.mono' (support_normalizedEulerTransform_subset W)

theorem contDiff_normalizedEulerTransform_iterate (q : ℕ) {W : ℝ → ℂ}
    (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ ((normalizedEulerTransform^[q]) W) := by
  induction q with
  | zero => simpa using hW
  | succ q ih =>
      simpa only [Function.iterate_succ_apply'] using
        contDiff_normalizedEulerTransform ih

theorem tsupport_normalizedEulerTransform_iterate_subset (q : ℕ) (W : ℝ → ℂ) :
    tsupport ((normalizedEulerTransform^[q]) W) ⊆ tsupport W := by
  induction q with
  | zero => exact Set.Subset.rfl
  | succ q ih =>
      simpa only [Function.iterate_succ_apply'] using
        (tsupport_normalizedEulerTransform_subset ((normalizedEulerTransform^[q]) W)).trans ih

theorem support_normalizedEulerTransform_iterate_subset_Icc (q : ℕ) {W : ℝ → ℂ}
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    Function.support ((normalizedEulerTransform^[q]) W) ⊆ Icc (1 : ℝ) 2 := by
  exact subset_closure.trans
    ((tsupport_normalizedEulerTransform_iterate_subset q W).trans
      (closure_minimal hsupport isClosed_Icc))

/-! ## An exact finite scale derivative -/

theorem hasDerivAt_normalizedWindow (W : ℝ → ℂ) (v P : ℝ)
    (hP : 0 < P) (hW : DifferentiableAt ℝ W (v / P)) :
    HasDerivAt (fun Q : ℝ => (Q ^ (-(1 / 2 : ℝ))) • W (v / Q))
      ((P ^ (-(1 / 2 : ℝ)) / P) • normalizedEulerTransform W (v / P)) P := by
  have harg : HasDerivAt (fun Q : ℝ => v / Q) (-v / P ^ 2) P := by
    simpa using (hasDerivAt_const P v).fun_div (hasDerivAt_id P) hP.ne'
  have hcomp : HasDerivAt (fun Q : ℝ => W (v / Q))
      ((-v / P ^ 2) • deriv W (v / P)) P :=
    hW.hasDerivAt.scomp P harg
  have hweight : HasDerivAt (fun Q : ℝ => Q ^ (-(1 / 2 : ℝ)))
      ((-(1 / 2 : ℝ)) * (P ^ (-(1 / 2 : ℝ)) / P)) P := by
    simpa only [Real.rpow_sub_one hP.ne'] using
      (Real.hasDerivAt_rpow_const (x := P) (p := -(1 / 2 : ℝ)) (Or.inl hP.ne'))
  apply (hweight.fun_smul hcomp).congr_deriv
  simp only [normalizedEulerTransform, eulerDerivative, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hP.ne']
  ring

theorem hasDerivAt_normalizedPrimePolynomial
    (pool : Finset α) (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ)
    (hP : 0 < P) (hW : Differentiable ℝ W) :
    HasDerivAt (normalizedPrimePolynomial pool ν a W)
      ((P ^ (-(1 / 2 : ℝ)) / P) •
        ∑ p ∈ pool, a p * normalizedEulerTransform W (ν p / P)) P := by
  have hterm (p : α) :
      HasDerivAt
        (fun Q : ℝ => a p * ((Q ^ (-(1 / 2 : ℝ))) • W (ν p / Q)))
        (a p * ((P ^ (-(1 / 2 : ℝ)) / P) •
          normalizedEulerTransform W (ν p / P))) P := by
    have h := (hasDerivAt_normalizedWindow W (ν p) P hP (hW _)).const_smul (a p)
    change HasDerivAt
      (fun Q : ℝ => a p • ((Q ^ (-(1 / 2 : ℝ))) • W (ν p / Q)))
      (a p • ((P ^ (-(1 / 2 : ℝ)) / P) •
        normalizedEulerTransform W (ν p / P))) P at h
    simpa only [smul_eq_mul] using h
  have hsum := HasDerivAt.fun_sum (u := pool) (fun p _ => hterm p)
  have hfunction :
      (fun Q : ℝ => ∑ p ∈ pool, a p * ((Q ^ (-(1 / 2 : ℝ))) • W (ν p / Q))) =
        normalizedPrimePolynomial pool ν a W := by
    funext Q
    simp only [normalizedPrimePolynomial, mul_smul_comm, Finset.smul_sum]
  rw [hfunction] at hsum
  simpa only [mul_smul_comm, Finset.smul_sum] using hsum

theorem euler_deriv_normalizedPrimePolynomial
    (pool : Finset α) (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ)
    (hP : 0 < P) (hW : Differentiable ℝ W) :
    P • deriv (normalizedPrimePolynomial pool ν a W) P =
      normalizedPrimePolynomial pool ν a (normalizedEulerTransform W) P := by
  rw [(hasDerivAt_normalizedPrimePolynomial pool ν a W P hP hW).deriv]
  simp only [normalizedPrimePolynomial, smul_smul]
  congr 1
  field_simp [hP.ne']

theorem rpow_neg_half_eq_inv_sqrt {P : ℝ} (hP : 0 ≤ P) :
    P ^ (-(1 / 2 : ℝ)) = (Real.sqrt P)⁻¹ := by
  rw [Real.rpow_neg hP, Real.sqrt_eq_rpow]

theorem normalizedPrimePolynomial_eq_inv_sqrt
    (pool : Finset α) (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ)
    (hP : 0 ≤ P) :
    normalizedPrimePolynomial pool ν a W P =
      (Real.sqrt P)⁻¹ • ∑ p ∈ pool, a p * W (ν p / P) := by
  rw [normalizedPrimePolynomial, rpow_neg_half_eq_inv_sqrt hP]

/-! ## Locally finite prime sums -/

theorem finite_norm_le (ν : α → ℝ) (a : α → ℂ) (d Y : ℝ)
    (hA : PrimeArithmetic ν a d) (hY : 0 ≤ Y) :
    {p : α | ν p ≤ Y}.Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt (d * Y)
  obtain ⟨pool, hpool, hcard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf n
  have hfilter : pool.filter (fun p => ν p ≤ Y) = pool := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact hpool hp
  have hcount := hA.count pool Y hY
  rw [hfilter, hcard] at hcount
  exact (not_le_of_gt hn) hcount

theorem primeSum_eq_sum_of_cutoff
    (pool : Finset α) (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ)
    (hP : 0 < P) (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2)
    (hpool : ∀ p, ν p ≤ 2 * P → p ∈ pool) :
    primeSum ν a W P = ∑ p ∈ pool, a p * W (ν p / P) := by
  apply tsum_eq_sum
  intro p hp
  have hzero : W (ν p / P) = 0 := by
    by_contra hne
    have hupper := (hsupport hne).2
    exact hp (hpool p ((div_le_iff₀ hP).mp hupper))
  simp only [hzero, mul_zero]

theorem normalizedPrimeSum_eventually_eq_polynomial
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d P : ℝ)
    (hA : PrimeArithmetic ν a d) (hP : 0 < P)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    ∃ pool : Finset α,
      (∀ p, ν p ≤ 4 * P → p ∈ pool) ∧
      normalizedPrimeSum ν a W =ᶠ[𝓝 P] normalizedPrimePolynomial pool ν a W := by
  let hfinite := finite_norm_le ν a d (4 * P) hA (by positivity)
  let pool : Finset α := hfinite.toFinset
  have hpool : ∀ p, ν p ≤ 4 * P → p ∈ pool := by
    intro p hp
    exact hfinite.mem_toFinset.mpr hp
  refine ⟨pool, hpool, ?_⟩
  filter_upwards [Ioo_mem_nhds (show P / 2 < P by linarith)
    (show P < 2 * P by linarith)] with Q hQ
  have hQpos : 0 < Q := by linarith [hQ.1]
  have hQpool : ∀ p, ν p ≤ 2 * Q → p ∈ pool := by
    intro p hp
    exact hpool p (by linarith [hQ.2])
  change (Q ^ (-(1 / 2 : ℝ))) • primeSum ν a W Q =
    (Q ^ (-(1 / 2 : ℝ))) • ∑ p ∈ pool, a p * W (ν p / Q)
  rw [primeSum_eq_sum_of_cutoff pool ν a W Q hQpos hsupport hQpool]

theorem euler_deriv_normalizedPrimeSum
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d P : ℝ)
    (hA : PrimeArithmetic ν a d) (hP : 0 < P)
    (hW : Differentiable ℝ W)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) :
    P • deriv (normalizedPrimeSum ν a W) P =
      normalizedPrimeSum ν a (normalizedEulerTransform W) P := by
  obtain ⟨pool, hpool, hlocal⟩ :=
    normalizedPrimeSum_eventually_eq_polynomial ν a W d P hA hP hsupport
  rw [hlocal.deriv_eq, euler_deriv_normalizedPrimePolynomial pool ν a W P hP hW]
  have hPpool : ∀ p, ν p ≤ 2 * P → p ∈ pool := by
    intro p hp
    exact hpool p (by linarith)
  change (P ^ (-(1 / 2 : ℝ))) •
      (∑ p ∈ pool, a p * normalizedEulerTransform W (ν p / P)) =
    (P ^ (-(1 / 2 : ℝ))) • primeSum ν a (normalizedEulerTransform W) P
  rw [primeSum_eq_sum_of_cutoff pool ν a (normalizedEulerTransform W) P hP
    (support_normalizedEulerTransform_subset_Icc hsupport) hPpool]

theorem normalizedPrimeSum_eq_inv_sqrt
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (P : ℝ) (hP : 0 ≤ P) :
    normalizedPrimeSum ν a W P = (Real.sqrt P)⁻¹ • primeSum ν a W P := by
  rw [normalizedPrimeSum, rpow_neg_half_eq_inv_sqrt hP]

theorem iterate_eulerDerivative_normalizedPrimeSum
    (ν : α → ℝ) (a : α → ℂ) (W : ℝ → ℂ) (d : ℝ)
    (hA : PrimeArithmetic ν a d) (hW : ContDiff ℝ ∞ W)
    (hsupport : Function.support W ⊆ Icc (1 : ℝ) 2) (q : ℕ) :
    ∀ P : ℝ, 0 < P →
      ((eulerDerivative^[q]) (normalizedPrimeSum ν a W)) P =
        normalizedPrimeSum ν a ((normalizedEulerTransform^[q]) W) P := by
  induction q with
  | zero =>
      intro P _
      rfl
  | succ q ih =>
      intro P hP
      have hlocal :
          (eulerDerivative^[q]) (normalizedPrimeSum ν a W) =ᶠ[𝓝 P]
            normalizedPrimeSum ν a ((normalizedEulerTransform^[q]) W) := by
        filter_upwards [Ioi_mem_nhds hP] with Q hQ
        exact ih Q hQ
      have hdiff : Differentiable ℝ ((normalizedEulerTransform^[q]) W) :=
        (contDiff_infty_iff_deriv.mp
          (contDiff_normalizedEulerTransform_iterate q hW)).1
      simp only [Function.iterate_succ_apply']
      change P • deriv ((eulerDerivative^[q]) (normalizedPrimeSum ν a W)) P =
        normalizedPrimeSum ν a
          (normalizedEulerTransform ((normalizedEulerTransform^[q]) W)) P
      rw [hlocal.deriv_eq]
      exact euler_deriv_normalizedPrimeSum ν a ((normalizedEulerTransform^[q]) W)
        d P hA hP hdiff (support_normalizedEulerTransform_iterate_subset_Icc q hsupport)

end PrimeCancellationEulerDerivatives

#print axioms PrimeCancellationEulerDerivatives.contDiff_eulerDerivative
#print axioms PrimeCancellationEulerDerivatives.contDiff_normalizedEulerTransform
#print axioms PrimeCancellationEulerDerivatives.support_normalizedEulerTransform_subset
#print axioms PrimeCancellationEulerDerivatives.tsupport_normalizedEulerTransform_subset
#print axioms PrimeCancellationEulerDerivatives.support_normalizedEulerTransform_subset_Icc
#print axioms PrimeCancellationEulerDerivatives.hasCompactSupport_normalizedEulerTransform
#print axioms PrimeCancellationEulerDerivatives.contDiff_normalizedEulerTransform_iterate
#print axioms PrimeCancellationEulerDerivatives.tsupport_normalizedEulerTransform_iterate_subset
#print axioms PrimeCancellationEulerDerivatives.support_normalizedEulerTransform_iterate_subset_Icc
#print axioms PrimeCancellationEulerDerivatives.hasDerivAt_normalizedWindow
#print axioms PrimeCancellationEulerDerivatives.hasDerivAt_normalizedPrimePolynomial
#print axioms PrimeCancellationEulerDerivatives.euler_deriv_normalizedPrimePolynomial
#print axioms PrimeCancellationEulerDerivatives.rpow_neg_half_eq_inv_sqrt
#print axioms PrimeCancellationEulerDerivatives.normalizedPrimePolynomial_eq_inv_sqrt
#print axioms PrimeCancellationEulerDerivatives.finite_norm_le
#print axioms PrimeCancellationEulerDerivatives.primeSum_eq_sum_of_cutoff
#print axioms PrimeCancellationEulerDerivatives.normalizedPrimeSum_eventually_eq_polynomial
#print axioms PrimeCancellationEulerDerivatives.euler_deriv_normalizedPrimeSum
#print axioms PrimeCancellationEulerDerivatives.normalizedPrimeSum_eq_inv_sqrt
#print axioms PrimeCancellationEulerDerivatives.iterate_eulerDerivative_normalizedPrimeSum
