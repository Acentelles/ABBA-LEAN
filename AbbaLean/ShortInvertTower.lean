import Mathlib
import AbbaLean.ShortInvertFull

set_option linter.style.header false

/-!
# ABBA — Lemma `shortinvert` at the totally real subfield

The paper's `Lemma:shortinvert` lives in `K⁺ ⊆ ℚ(ζ_n)`, while the challenge
elements `ζ^i + ζ^{-i}` are sums of root-of-unity powers in the cyclotomic field.
This file supplies the glue: embedding bounds descend along an algebraic
extension (`embedding_le_of_isAlgebraic`, via `IsAlgClosed.lift`), giving
`shortinvert_tower` — `shortinvert_general` at `K = K⁺` with its embedding
hypothesis discharged on the cyclotomic side (`hw_of_chal_shape`, covering both
`w₀ = 1` and `wᵢ = ζ^i + ζ^{-i}`).
-/

namespace Abba

open NumberField Module

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Embedding bounds descend along an algebraic extension: if every complex
embedding of `L` bounds the image of `x`, then every complex embedding of `K`
bounds `x` (extend the embedding with `IsAlgClosed.lift`). -/
theorem embedding_le_of_isAlgebraic (x : K) (B : ℝ)
    (h : ∀ ψ : L →ₐ[ℚ] ℂ, ‖ψ (algebraMap K L x)‖ ≤ B) (φ : K →ₐ[ℚ] ℂ) :
    ‖φ x‖ ≤ B := by
  letI : Algebra K ℂ := (φ : K →+* ℂ).toAlgebra
  let ψ' : L →ₐ[K] ℂ := IsAlgClosed.lift
  have hψ : ψ' (algebraMap K L x) = φ x := ψ'.commutes x
  have h2 := h (ψ' : L →+* ℂ).toRatAlgHom
  have h3 : (ψ' : L →+* ℂ).toRatAlgHom (algebraMap K L x)
      = ψ' (algebraMap K L x) := rfl
  rw [h3, hψ] at h2
  exact h2

variable {ι : Type*} [Fintype ι]

/-- Discharge of the embedding hypothesis for the challenge family: each `wᵢ`
maps in `L` either to `1` or to a sum of two powers of a root of unity. -/
theorem hw_of_chal_shape (n : ℕ) (hn : n ≠ 0) (z : L) (hz : z ^ n = 1)
    (w : ι → 𝓞 K)
    (hshape : ∀ i, algebraMap K L (algebraMap (𝓞 K) K (w i)) = 1
      ∨ ∃ a b : ℕ, algebraMap K L (algebraMap (𝓞 K) K (w i)) = z ^ a + z ^ b) :
    ∀ (i : ι) (ψ : L →ₐ[ℚ] ℂ), ‖ψ (algebraMap K L (algebraMap (𝓞 K) K (w i)))‖ ≤ 2 := by
  intro i ψ
  rcases hshape i with h1 | ⟨a, b, hab⟩
  · rw [h1, map_one, norm_one]
    norm_num
  · rw [hab]
    exact norm_le_two_of_pow_eq_one hn hz ψ a b

/-- **Lemma `shortinvert` at the totally real subfield**: `shortinvert_general`
with the embedding bound checked in an algebraic extension `L` (the cyclotomic
field), where the challenge elements are visible as root-of-unity sums. -/
theorem shortinvert_tower (q F : ℕ) (hq : Nat.Prime q)
    (hres : ∀ M : Ideal (𝓞 K), M.IsMaximal → (q : 𝓞 K) ∈ M → Ideal.absNorm M = q ^ F)
    (w : ι → 𝓞 K)
    (hw : ∀ (i : ι) (ψ : L →ₐ[ℚ] ℂ), ‖ψ (algebraMap K L (algebraMap (𝓞 K) K (w i)))‖ ≤ 2)
    (c : ι → ℤ) (β : ℝ) (hβ : ∀ i, |(c i : ℝ)| ≤ β)
    (hα : (∑ i, c i • w i) ≠ 0)
    (hbound : (2 * Fintype.card ι * β) ^ finrank ℚ K < (q : ℝ) ^ F) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (∑ i, c i • w i)) :=
  shortinvert_general q F hq hres w
    (fun i φ => embedding_le_of_isAlgebraic (L := L) _ 2 (hw i) φ) c β hβ hα hbound

/-- The paper's form: challenge elements as in Cor `Hc`, differences of distinct
box vectors invertible mod `q`, with the embedding bound checked cyclotomically. -/
theorem Hc_diff_tower (q F : ℕ) (hq : Nat.Prime q)
    (hres : ∀ M : Ideal (𝓞 K), M.IsMaximal → (q : 𝓞 K) ∈ M → Ideal.absNorm M = q ^ F)
    (n : ℕ) (hn : n ≠ 0) (z : L) (hz : z ^ n = 1)
    (w : ι → 𝓞 K)
    (hshape : ∀ i, algebraMap K L (algebraMap (𝓞 K) K (w i)) = 1
      ∨ ∃ a b : ℕ, algebraMap K L (algebraMap (𝓞 K) K (w i)) = z ^ a + z ^ b)
    (c c' : ι → ℤ) (cb : ℕ)
    (hc : ∀ i, |c i| ≤ (cb : ℤ)) (hc' : ∀ i, |c' i| ≤ (cb : ℤ))
    (hne : (∑ i, c i • w i) ≠ (∑ i, c' i • w i))
    (hbound : (2 * Fintype.card ι * (2 * cb : ℝ)) ^ finrank ℚ K < (q : ℝ) ^ F) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)})
      ((∑ i, c i • w i) - (∑ i, c' i • w i))) :=
  Hc_diff q F hq hres w
    (fun i φ => embedding_le_of_isAlgebraic (L := L) _ 2
      (hw_of_chal_shape n hn z hz w hshape i) φ)
    c c' cb hc hc' hne hbound

end Tower

end Abba
