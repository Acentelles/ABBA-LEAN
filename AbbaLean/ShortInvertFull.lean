import Mathlib
import AbbaLean.ShortInvert

set_option linter.style.header false

/-!
# ABBA — Lemma `shortinvert`, composed form, and Cor `Hc` difference-invertibility

Composes the three steps of `AbbaLean.ShortInvert` into the paper's Lemma
`Lemma:shortinvert`, stated generically: for a number field `K` of degree `D`,
a finite family `w : ι → 𝓞 K` whose images under every complex embedding have
norm at most 2, and integer coefficients `|cᵢ| ≤ β`, if every maximal ideal above
the prime `q` has absolute norm `q^F` and `(2·|ι|·β)^D < q^F`, then any nonzero
`α = Σ cᵢ·wᵢ` is invertible modulo `q`.

The paper's statement is the instantiation `K = K⁺`, `ι = Fin d⁺`, `D = d⁺`,
`w = {1} ∪ {ζ^i + ζ^{-i}}` (embedding bound 2 by `norm_le_two_of_pow_eq_one`),
`F = f`; the hypothesis `2d⁺β < q^{f/d⁺}` is equivalent to the power form used
here.  Cor `Hc`'s invertibility clause is `Hc_diff`: differences of distinct
coefficient vectors in a box `[-cb, cb]` are invertible mod `q` whenever they are
nonzero (nonvanishing for the concrete cyclotomic family is linear independence,
handled separately).
-/

namespace Abba

open NumberField Module

section Dichotomy

variable {K : Type*} [Field K] [NumberField K]

/-- Either `α` is a unit modulo `q`, or some maximal ideal contains both. -/
theorem isUnit_mk_or_exists_maximal (α : 𝓞 K) (q : ℕ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) α) ∨
    ∃ M : Ideal (𝓞 K), M.IsMaximal ∧ α ∈ M ∧ (q : 𝓞 K) ∈ M := by
  by_cases htop : Ideal.span {α} ⊔ Ideal.span {(q : 𝓞 K)} = ⊤
  · left
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ Ideal.span {(q : 𝓞 K)} := by
      rw [htop]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hb0 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) b = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have hmk : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c * α) = 1 := by
      have h2 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (a + b) = 1 := by
        rw [hab]; exact map_one _
      rwa [map_add, hb0, add_zero, ← hc] at h2
    have hmul : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) α
        * Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) c = 1 := by
      rw [← map_mul, mul_comm α c]
      exact hmk
    exact isUnit_iff_exists.mpr ⟨_, hmul, by rwa [mul_comm] at hmul⟩
  · right
    obtain ⟨M, hM, hMle⟩ := Ideal.exists_le_maximal _ htop
    exact ⟨M, hM,
      hMle (Submodule.mem_sup_left (Ideal.mem_span_singleton_self α)),
      hMle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

end Dichotomy

section Bounds

variable {K : Type*} [Field K] [NumberField K]

/-- Any sum of two powers of a root of unity has all embeddings bounded by 2. -/
theorem norm_le_two_of_pow_eq_one {z : K} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1)
    (φ : K →ₐ[ℚ] ℂ) (i j : ℕ) : ‖φ (z ^ i + z ^ j)‖ ≤ 2 := by
  have h1 : ‖φ z‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hn
  calc ‖φ (z ^ i + z ^ j)‖ = ‖φ z ^ i + φ z ^ j‖ := by rw [map_add, map_pow, map_pow]
    _ ≤ ‖φ z ^ i‖ + ‖φ z ^ j‖ := norm_add_le _ _
    _ = 2 := by rw [norm_pow, norm_pow, h1]; norm_num

variable {ι : Type*} [Fintype ι]

/-- Triangle-inequality bound on the embeddings of `Σ cᵢ·wᵢ`. -/
theorem embedding_bound_sum (w : ι → 𝓞 K)
    (hw : ∀ (i : ι) (φ : K →ₐ[ℚ] ℂ), ‖φ (algebraMap (𝓞 K) K (w i))‖ ≤ 2)
    (c : ι → ℤ) (β : ℝ) (hβ : ∀ i, |(c i : ℝ)| ≤ β) (φ : K →ₐ[ℚ] ℂ) :
    ‖φ (algebraMap (𝓞 K) K (∑ i, c i • w i))‖ ≤ 2 * Fintype.card ι * β := by
  have key : φ (algebraMap (𝓞 K) K (∑ i, c i • w i))
      = ∑ i, (c i : ℂ) * φ (algebraMap (𝓞 K) K (w i)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul]
  calc ‖φ (algebraMap (𝓞 K) K (∑ i, c i • w i))‖
      = ‖∑ i, (c i : ℂ) * φ (algebraMap (𝓞 K) K (w i))‖ := by rw [key]
    _ ≤ ∑ i, ‖(c i : ℂ) * φ (algebraMap (𝓞 K) K (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, β * 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        have hci : ‖((c i : ℤ) : ℂ)‖ = |(c i : ℝ)| := by
          rw [Complex.norm_intCast]
        rw [hci]
        exact mul_le_mul (hβ i) (hw i φ) (norm_nonneg _)
          (le_trans (abs_nonneg _) (hβ i))
    _ = 2 * Fintype.card ι * β := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Bounds

section Main

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

/-- **Lemma `shortinvert`, composed form.**  If every maximal ideal above the
prime `q` has absolute norm `q^F`, the family `w` has all embeddings bounded by
2, the integer coefficients are bounded by `β`, and
`(2·|ι|·β)^{[K:ℚ]} < q^F`, then any nonzero `Σ cᵢ·wᵢ` is invertible mod `q`. -/
theorem shortinvert_general (q F : ℕ) (hq : Nat.Prime q)
    (hres : ∀ M : Ideal (𝓞 K), M.IsMaximal → (q : 𝓞 K) ∈ M → Ideal.absNorm M = q ^ F)
    (w : ι → 𝓞 K)
    (hw : ∀ (i : ι) (φ : K →ₐ[ℚ] ℂ), ‖φ (algebraMap (𝓞 K) K (w i))‖ ≤ 2)
    (c : ι → ℤ) (β : ℝ) (hβ : ∀ i, |(c i : ℝ)| ≤ β)
    (hα : (∑ i, c i • w i) ≠ 0)
    (hbound : (2 * Fintype.card ι * β) ^ finrank ℚ K < (q : ℝ) ^ F) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (∑ i, c i • w i)) := by
  set α : 𝓞 K := ∑ i, c i • w i with hα_def
  rcases isUnit_mk_or_exists_maximal α q with h | ⟨M, hM, hαM, hqM⟩
  · exact h
  · exfalso
    -- q^F ≤ |N(α)| from the maximal ideal
    have hNM : Ideal.absNorm M = q ^ F := hres M hM hqM
    have hdvd : Ideal.absNorm M ∣ (Algebra.norm ℤ α).natAbs := by
      have hle : Ideal.span {α} ≤ M := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hαM
      simpa [Ideal.absNorm_span_singleton] using Ideal.absNorm_dvd_absNorm_of_le hle
    have hNne : Algebra.norm ℤ α ≠ 0 := by
      rw [Algebra.norm_ne_zero_iff]
      exact hα
    have hge : (q : ℝ) ^ F ≤ |((Algebra.norm ℤ α : ℤ) : ℝ)| := by
      have h1 : q ^ F ≤ (Algebra.norm ℤ α).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hNne) (hNM ▸ hdvd)
      calc (q : ℝ) ^ F = ((q ^ F : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((Algebra.norm ℤ α).natAbs : ℝ) := by exact_mod_cast h1
        _ = |((Algebra.norm ℤ α : ℤ) : ℝ)| := by
            rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    -- |N(α)| ≤ (2·|ι|·β)^D from the embedding bounds
    have hle : |((Algebra.norm ℤ α : ℤ) : ℝ)| ≤ (2 * Fintype.card ι * β) ^ finrank ℚ K :=
      abs_norm_le_of_embeddings_le α fun φ => embedding_bound_sum w hw c β hβ φ
    linarith

/-- **Cor `Hc`, invertibility clause**: differences of distinct coefficient
vectors in the box `[-cb, cb]` give invertible elements mod `q`, provided the
difference is nonzero. -/
theorem Hc_diff (q F : ℕ) (hq : Nat.Prime q)
    (hres : ∀ M : Ideal (𝓞 K), M.IsMaximal → (q : 𝓞 K) ∈ M → Ideal.absNorm M = q ^ F)
    (w : ι → 𝓞 K)
    (hw : ∀ (i : ι) (φ : K →ₐ[ℚ] ℂ), ‖φ (algebraMap (𝓞 K) K (w i))‖ ≤ 2)
    (c c' : ι → ℤ) (cb : ℕ)
    (hc : ∀ i, |c i| ≤ (cb : ℤ)) (hc' : ∀ i, |c' i| ≤ (cb : ℤ))
    (hne : (∑ i, c i • w i) ≠ (∑ i, c' i • w i))
    (hbound : (2 * Fintype.card ι * (2 * cb : ℝ)) ^ finrank ℚ K < (q : ℝ) ^ F) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)})
      ((∑ i, c i • w i) - (∑ i, c' i • w i))) := by
  have hdiff : (∑ i, c i • w i) - (∑ i, c' i • w i) = ∑ i, (c i - c' i) • w i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
  rw [hdiff]
  refine shortinvert_general q F hq hres w hw (fun i => c i - c' i) (2 * cb)
    (fun i => ?_) (by rw [← hdiff]; exact sub_ne_zero_of_ne hne) hbound
  have h1 : |c i - c' i| ≤ 2 * (cb : ℤ) := by
    calc |c i - c' i| ≤ |c i| + |c' i| := abs_sub _ _
      _ ≤ (cb : ℤ) + (cb : ℤ) := add_le_add (hc i) (hc' i)
      _ = 2 * (cb : ℤ) := by ring
  have h2 : |((c i - c' i : ℤ) : ℝ)| ≤ ((2 * (cb : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  calc |((c i - c' i : ℤ) : ℝ)| ≤ ((2 * (cb : ℤ) : ℤ) : ℝ) := h2
    _ = 2 * (cb : ℝ) := by push_cast; ring

end Main

end Abba
