import Mathlib
import AbbaLean.ShortInvertFull

set_option linter.style.header false

/-!
# ABBA — Cor `Hc`, counting clause

Linear independence of the challenge family `{1} ∪ {z^i + z^{-i} : 1 ≤ i < d}`.

The independence argument avoids Chebyshev polynomials: multiplying a vanishing
relation `c₀ + Σ_{i≥1} cᵢ(z^i + z^{-i}) = 0` by `z^{d-1}` moves every exponent
into `[0, 2d-2]`, where each basis power occurs exactly once (the two wings
`d-1+i` and `d-1-i` are disjoint for `i ≥ 1` and meet only at `d-1` for `i = 0`),
so independence of the powers `1, z, …, z^{2d-2}` forces all coefficients to
vanish.  For `K = ℚ(ζ_n)` with `φ(n) = 2d` (e.g. `n = 2^r`), the power
independence is the cyclotomic power basis.
-/

namespace Abba

open Finset

section Indep

variable {K : Type*} [Field K] [CharZero K]

/-- Multiplying by `z^(d-1)` and reindexing: the vanishing relation forces all
coefficients to vanish, given independence of the powers `z^0, …, z^(2d-2)`. -/
theorem coeff_eq_zero_of_relation (d : ℕ) (hd : 0 < d) (z : K) (hz0 : z ≠ 0)
    (hli : LinearIndependent ℚ (fun e : Fin (2 * d - 1) => z ^ (e : ℕ)))
    (c : ℕ → ℚ)
    (h : (c 0 : K) + ∑ i ∈ Ico 1 d, (c i : K) * (z ^ i + z⁻¹ ^ i) = 0) :
    ∀ i < d, c i = 0 := by
  classical
  set a : ℕ → ℚ := fun e => if e < d - 1 then c (d - 1 - e)
    else if e = d - 1 then c 0 else c (e - (d - 1)) with ha_def
  have key : ∑ e ∈ range (2 * d - 1), (a e : K) * z ^ e = 0 := by
    have hmul := congrArg (fun x : K => x * z ^ (d - 1)) h
    simp only [add_mul, Finset.sum_mul, zero_mul] at hmul
    have hterm : ∀ i ∈ Ico 1 d,
        (c i : K) * (z ^ i + z⁻¹ ^ i) * z ^ (d - 1)
          = (c i : K) * z ^ (d - 1 + i) + (c i : K) * z ^ (d - 1 - i) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := mem_Ico.mp hi
      have hzi : z⁻¹ ^ i * z ^ (d - 1) = z ^ (d - 1 - i) := by
        rw [inv_pow, inv_mul_eq_div, div_eq_iff (pow_ne_zero i hz0), ← pow_add]
        congr 1
        omega
      calc (c i : K) * (z ^ i + z⁻¹ ^ i) * z ^ (d - 1)
          = (c i : K) * (z ^ i * z ^ (d - 1)) + (c i : K) * (z⁻¹ ^ i * z ^ (d - 1)) := by
            ring
        _ = (c i : K) * z ^ (d - 1 + i) + (c i : K) * z ^ (d - 1 - i) := by
            rw [hzi, ← pow_add]
            ring_nf
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at hmul
    have hupper : ∑ i ∈ Ico 1 d, (c i : K) * z ^ (d - 1 + i)
        = ∑ j ∈ Ico d (2 * d - 1), (a j : K) * z ^ j := by
      refine Finset.sum_nbij' (i := fun x => d - 1 + x) (j := fun x => x - (d - 1))
        ?_ ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        omega
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        omega
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        have hlt : ¬(d - 1 + x < d - 1) := by omega
        have heq : ¬(d - 1 + x = d - 1) := by omega
        have hidx : d - 1 + x - (d - 1) = x := by omega
        simp only [ha_def, hlt, heq, if_false, hidx]
    have hlower : ∑ i ∈ Ico 1 d, (c i : K) * z ^ (d - 1 - i)
        = ∑ j ∈ range (d - 1), (a j : K) * z ^ j := by
      rw [Finset.range_eq_Ico]
      refine Finset.sum_nbij' (i := fun x => d - 1 - x) (j := fun x => d - 1 - x)
        ?_ ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        omega
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        omega
      · intro x hx
        obtain ⟨h1, h2⟩ := mem_Ico.mp hx
        have hlt : d - 1 - x < d - 1 := by omega
        have hidx : d - 1 - (d - 1 - x) = x := by omega
        simp only [ha_def, hlt, if_true, hidx]
    have hcenter : (c 0 : K) * z ^ (d - 1) = (a (d - 1) : K) * z ^ (d - 1) := by
      have h0 : a (d - 1) = c 0 := by simp [ha_def]
      rw [h0]
    have hsplit : ∑ e ∈ range (2 * d - 1), (a e : K) * z ^ e
        = (∑ e ∈ range (d - 1), (a e : K) * z ^ e)
          + (a (d - 1) : K) * z ^ (d - 1)
          + ∑ e ∈ Ico d (2 * d - 1), (a e : K) * z ^ e := by
      have h1 : ∑ e ∈ range d, (a e : K) * z ^ e
          = (∑ e ∈ range (d - 1), (a e : K) * z ^ e) + (a (d - 1) : K) * z ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        rw [Finset.sum_range_succ]
      have h2 : ∑ e ∈ range (2 * d - 1), (a e : K) * z ^ e
          = (∑ e ∈ range d, (a e : K) * z ^ e)
            + ∑ e ∈ Ico d (2 * d - 1), (a e : K) * z ^ e := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le d) (by omega : d ≤ 2 * d - 1)]
      rw [h2, h1]
    rw [hsplit, ← hcenter, ← hupper, ← hlower]
    linear_combination hmul
  have hzero : ∀ e : Fin (2 * d - 1), a (e : ℕ) = 0 := by
    have hsum0 : ∑ e : Fin (2 * d - 1), a (e : ℕ) • z ^ (e : ℕ) = 0 := by
      have hconv : ∑ e : Fin (2 * d - 1), a (e : ℕ) • z ^ (e : ℕ)
          = ∑ e ∈ range (2 * d - 1), (a e : K) * z ^ e := by
        rw [Fin.sum_univ_eq_sum_range (fun e => a e • z ^ e)]
        exact Finset.sum_congr rfl fun e _ => by rw [Rat.smul_def]
      rw [hconv]
      exact key
    intro e
    exact linearIndependent_iff'.mp hli Finset.univ (fun e => a (e : ℕ)) hsum0 e
      (Finset.mem_univ e)
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have h0 := hzero ⟨d - 1, by omega⟩
    simpa [ha_def] using h0
  · have hlt : d - 1 + i < 2 * d - 1 := by omega
    have h0 := hzero ⟨d - 1 + i, hlt⟩
    have he : ¬(d - 1 + i < d - 1) := by omega
    have he2 : ¬(d - 1 + i = d - 1) := by omega
    simp only [ha_def, he, he2, if_false] at h0
    rwa [show d - 1 + i - (d - 1) = i by omega] at h0

end Indep

end Abba
