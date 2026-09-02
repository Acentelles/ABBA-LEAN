import Mathlib
import AbbaLean.Uniformity

set_option linter.style.header false

/-!
# ABBA — Lemma `gensetT0` (centralizer criterion), per factor

For a field `k` and `z₁, …, zₘ ∈ M₂(k)`, the range of the syndrome map
`𝐚 ↦ Σᵢ [aᵢ, zᵢ]` is the traceless hyperplane `𝔰𝔩₂(k)` **iff** the centralizer of
`{zᵢ}` is the scalars.  The proof is the paper's trace-form argument: the trace
form `(x, y) ↦ tr(x y)` is nondegenerate, the orthogonal of the range is exactly
the centralizer (`orthogonal_range_eq`), and `finrank_orthogonal` turns this into
`dim range = 4 − dim centralizer`.  The paper's statement over
`Λ_q ≅ ∏ M₂(k_j)` follows factorwise.
-/

namespace Abba

section Centralizer

open Matrix

variable {k : Type*} [Field k] {m : ℕ}

/-- `M₂(k)`. -/
abbrev M2 (k : Type*) [Field k] := Matrix (Fin 2) (Fin 2) k

/-- The trace form `(x, y) ↦ tr(x y)` on `M₂(k)`. -/
def traceB (k : Type*) [Field k] : LinearMap.BilinForm k (M2 k) :=
  (LinearMap.mul k (M2 k)).compr₂ (Matrix.traceLinearMap (Fin 2) k k)

@[simp] theorem traceB_apply (x y : M2 k) : traceB k x y = Matrix.trace (x * y) := rfl

/-- Nondegeneracy of the trace form, by testing against matrix units. -/
theorem traceB_separatingLeft : (traceB k).SeparatingLeft := by
  intro x hx
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hx !![1, 0; 0, 0]
  · simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hx !![0, 0; 1, 0]
  · simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hx !![0, 1; 0, 0]
  · simpa [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using hx !![0, 0; 0, 1]

theorem traceB_nondegenerate : (traceB k).Nondegenerate := by
  refine ⟨traceB_separatingLeft, ?_⟩
  intro y hy
  apply traceB_separatingLeft
  intro x
  rw [traceB_apply, Matrix.trace_mul_comm]
  exact hy x

/-- The centralizer of a family, as a subspace. -/
def centralizer (z : Fin m → M2 k) : Submodule k (M2 k) where
  carrier := {v | ∀ i, v * z i = z i * v}
  add_mem' := by
    intro a b ha hb i
    show (a + b) * z i = z i * (a + b)
    rw [add_mul, mul_add, ha i, hb i]
  zero_mem' := by
    intro i
    show (0 : M2 k) * z i = z i * 0
    rw [zero_mul, mul_zero]
  smul_mem' := by
    intro c v hv i
    show (c • v) * z i = z i * (c • v)
    rw [smul_mul_assoc, mul_smul_comm, hv i]

theorem mem_centralizer {z : Fin m → M2 k} {v : M2 k} :
    v ∈ centralizer z ↔ ∀ i, v * z i = z i * v := Iff.rfl

/-- The traceless hyperplane `𝔰𝔩₂(k)`. -/
abbrev sl2 (k : Type*) [Field k] : Submodule k (M2 k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)

/-- `im(ad_w) ⊆ C(w)^⊥` and conversely: the trace-orthogonal of the range of
`𝐚 ↦ Σᵢ [aᵢ, zᵢ]` is exactly the centralizer of `{zᵢ}`. -/
theorem orthogonal_range_eq (z : Fin m → M2 k) :
    (traceB k).orthogonal (LinearMap.range (commMapL k z)) = centralizer z := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_centralizer]
  constructor
  · intro h i
    have key : ∀ a : M2 k, Matrix.trace (a * (z i * v - v * z i)) = 0 := by
      intro a
      have hn : a * z i - z i * a ∈ LinearMap.range (commMapL k z) := by
        refine ⟨Pi.single i a, ?_⟩
        rw [commMapL_apply, Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have h1 := h _ hn
      rw [traceB_apply] at h1
      have e1 : Matrix.trace (a * (z i * v - v * z i))
          = Matrix.trace ((a * z i - z i * a) * v) := by
        simp only [mul_sub, sub_mul, Matrix.trace_sub, mul_assoc]
        rw [Matrix.trace_mul_comm (z i) (a * v), mul_assoc]
      rw [e1]
      exact h1
    have h0 : z i * v - v * z i = 0 := by
      apply traceB_separatingLeft
      intro a
      rw [traceB_apply, Matrix.trace_mul_comm]
      exact key a
    exact (sub_eq_zero.mp h0).symm
  · rintro hv _ ⟨a, rfl⟩
    rw [traceB_apply, commMapL_apply, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [sub_mul, Matrix.trace_sub, mul_assoc, ← hv i, ← mul_assoc,
      Matrix.trace_mul_comm (a i * v) (z i), ← mul_assoc, sub_self]

/-- Every commutator is traceless: the range lies in `𝔰𝔩₂(k)`. -/
theorem range_commMapL_le_sl2 (z : Fin m → M2 k) :
    LinearMap.range (commMapL k z) ≤ sl2 k := by
  rintro _ ⟨a, rfl⟩
  rw [LinearMap.mem_ker]
  show Matrix.trace (∑ i, (a i * z i - z i * a i)) = 0
  rw [Matrix.trace_sum]
  exact Finset.sum_eq_zero fun i _ => by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem finrank_sl2 : Module.finrank k (sl2 k) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 2) k k)
  have hr : LinearMap.range (Matrix.traceLinearMap (Fin 2) k k) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨!![c, 0; 0, 0], by simp [Matrix.trace_fin_two]⟩
  rw [hr, finrank_top, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self] at h
  show Module.finrank k (LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)) = 3
  omega

/-- `dim range + dim centralizer = 4`. -/
theorem finrank_range_add_finrank_centralizer (z : Fin m → M2 k) :
    Module.finrank k (LinearMap.range (commMapL k z)) + Module.finrank k (centralizer z) = 4 := by
  have h := LinearMap.BilinForm.finrank_orthogonal traceB_nondegenerate
    (LinearMap.range (commMapL k z))
  rw [orthogonal_range_eq, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self] at h
  have hle := Submodule.finrank_le (LinearMap.range (commMapL k z))
  rw [Module.finrank_matrix] at hle
  simp only [Fintype.card_fin, Module.finrank_self] at hle
  omega

/-- **Lemma `gensetT0` (centralizer criterion), per factor**: the syndrome map
`𝐚 ↦ Σᵢ [aᵢ, zᵢ]` on `M₂(k)` has range the full traceless hyperplane iff the
centralizer of `{zᵢ}` is the scalars. -/
theorem range_eq_sl2_iff (z : Fin m → M2 k) :
    LinearMap.range (commMapL k z) = sl2 k ↔
      centralizer z = Submodule.span k {(1 : M2 k)} := by
  have hsum := finrank_range_add_finrank_centralizer z
  have h1 : Module.finrank k (Submodule.span k {(1 : M2 k)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have hle1 : Submodule.span k {(1 : M2 k)} ≤ centralizer z := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_centralizer]
    intro i
    rw [one_mul, mul_one]
  constructor
  · intro hR
    rw [hR, finrank_sl2] at hsum
    exact (Submodule.eq_of_le_of_finrank_eq hle1 (by omega)).symm
  · intro hC
    rw [hC, h1] at hsum
    exact Submodule.eq_of_le_of_finrank_eq (range_commMapL_le_sl2 z) (by rw [finrank_sl2]; omega)

/-- The paper's phrasing of the failure event: the range is a proper subspace of
`𝔰𝔩₂(k)` iff some non-scalar matrix commutes with every `zᵢ`. -/
theorem range_ne_sl2_iff (z : Fin m → M2 k) :
    LinearMap.range (commMapL k z) ≠ sl2 k ↔
      ∃ v : M2 k, v ∉ Submodule.span k {(1 : M2 k)} ∧ ∀ i, v * z i = z i * v := by
  rw [Ne, range_eq_sl2_iff]
  have hle1 : Submodule.span k {(1 : M2 k)} ≤ centralizer z := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_centralizer]
    intro i
    rw [one_mul, mul_one]
  constructor
  · intro hne
    by_contra hcon
    apply hne
    refine le_antisymm ?_ hle1
    intro v hv
    by_contra hv'
    exact hcon ⟨v, hv', hv⟩
  · rintro ⟨v, hv, hcomm⟩ heq
    have hmem : v ∈ centralizer z := mem_centralizer.mpr hcomm
    rw [heq] at hmem
    exact hv hmem

end Centralizer

end Abba
