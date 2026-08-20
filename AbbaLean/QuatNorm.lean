import Mathlib

set_option linter.style.header false

/-!
# ABBA — Lemma `quatnorm` and the deterministic core of Prop `ComSIStoIComSIS`

* `quatnorm` / `quatnorm_star` — the reduced norm of a quaternion is invariant
  under conjugation by a unit: `nrd(v·x·v⁻¹) = nrd(x)`, in the paper's algebra
  `(-1,-1 / ℚ(ζ_e + ζ_e⁻¹))`, which is Mathlib's `ℍ[K]`.  Phrased with a unit
  `v` (in the paper's division algebra, `v ≠ 0` iff `v` is a unit); stated over
  any commutative ring, using that `normSq` is a monoid homomorphism.  The
  reduced-norm formula `x·x̄ = x₀² + x₁² + x₂² + x₃²` is Mathlib's
  `Quaternion.self_mul_star` + `normSq_def'`.

* Prop `ComSIStoIComSIS`, deterministic content: bilinearity
  `F_𝐚(𝐳) - F_𝐚(𝐱) = F_𝐚(𝐳 - 𝐱)` of the commutator syndrome map
  (`Fmap_sub`), nonvanishing of the output (`Fmap_output_ne_zero`), and the
  tail arithmetic `(1+ε)/(1-ε) ≤ 2` for `ε ≤ 1/10` with the assembled collision
  bound (`ratio_le_two`, `collision_tail`).  The remaining ingredients
  (uniformity of the syndrome via Cor `UnifDistrCor`, the discrete-Gaussian
  bounds of GPV) are imported in the paper and not formalized here.
-/

namespace Abba

section QuatNorm

open Quaternion

variable {K : Type*} [CommRing K]

/-- **Lemma `quatnorm`**: the reduced norm is invariant under conjugation by a
unit. -/
theorem quatnorm (x : ℍ[K]) (v : (ℍ[K])ˣ) :
    normSq ((v : ℍ[K]) * x * ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K])) = normSq x := by
  have h2 : normSq (v : ℍ[K]) * normSq ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  calc normSq ((v : ℍ[K]) * x * ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K]))
      = normSq (v : ℍ[K]) * normSq x * normSq ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K]) := by
        rw [map_mul, map_mul]
    _ = normSq x * (normSq (v : ℍ[K]) * normSq ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K])) := by ring
    _ = normSq x := by rw [h2, mul_one]

/-- The paper's phrasing: `y·ȳ = x·x̄` for `y = v·x·v⁻¹`. -/
theorem quatnorm_star (x : ℍ[K]) (v : (ℍ[K])ˣ) :
    ((v : ℍ[K]) * x * ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K]))
        * star ((v : ℍ[K]) * x * ((v⁻¹ : (ℍ[K])ˣ) : ℍ[K]))
      = x * star x := by
  rw [self_mul_star, self_mul_star, quatnorm]

end QuatNorm

section ComSISCore

variable {R : Type*} [Ring R] {m : ℕ}

/-- The commutator syndrome map `F_𝐚(𝐱) = Σᵢ [aᵢ, xᵢ]`. -/
def Fmap (a x : Fin m → R) : R := ∑ i, (a i * x i - x i * a i)

/-- **Bilinearity step of Prop `ComSIStoIComSIS`**:
`F_𝐚(𝐳 - 𝐱) = F_𝐚(𝐳) - F_𝐚(𝐱)`, so the output `𝐰 = 𝐳 - 𝐱` satisfies
`F_𝐚(𝐰) = 0` whenever `F_𝐚(𝐳) = F_𝐚(𝐱)`. -/
theorem Fmap_sub (a z x : Fin m → R) :
    Fmap a (fun i => z i - x i) = Fmap a z - Fmap a x := by
  rw [Fmap, Fmap, Fmap, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  noncomm_ring

/-- The output `𝐰 = 𝐳 - 𝐱` vanishes iff the collision `𝐳 = 𝐱` occurs. -/
theorem Fmap_output_ne_zero (z x : Fin m → R) :
    (fun i => z i - x i) ≠ 0 ↔ z ≠ x := by
  rw [Function.ne_iff, Function.ne_iff]
  simp [sub_ne_zero]

/-- The syndrome of the output vanishes: the correctness clause. -/
theorem Fmap_output_syndrome (a z x : Fin m → R) (h : Fmap a z = Fmap a x) :
    Fmap a (fun i => z i - x i) = 0 := by
  rw [Fmap_sub, h, sub_self]

/-- Tail arithmetic: `(1+ε)/(1-ε) ≤ 2` for `0 ≤ ε ≤ 1/10`. -/
theorem ratio_le_two {ε : ℝ} (h0 : 0 ≤ ε) (hε : ε ≤ 1 / 10) :
    (1 + ε) / (1 - ε) ≤ 2 := by
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The assembled collision bound of Prop `ComSIStoIComSIS`:
`q^{3n}·((1+ε)/(1-ε))^m / 2^{mN} ≤ q^{3n} / 2^{m(N-1)}`. -/
theorem collision_tail (q n m N : ℕ) (hN : 1 ≤ N) {ε : ℝ} (h0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 10) :
    (q : ℝ) ^ (3 * n) * ((1 + ε) / (1 - ε)) ^ m / 2 ^ (m * N)
      ≤ (q : ℝ) ^ (3 * n) / 2 ^ (m * (N - 1)) := by
  have hr0 : (0 : ℝ) ≤ (1 + ε) / (1 - ε) := div_nonneg (by linarith) (by linarith)
  have hexp : (2 : ℝ) ^ (m * N) = 2 ^ m * 2 ^ (m * (N - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [← pow_add]
    congr 1
    rw [Nat.add_sub_cancel]
    ring
  calc (q : ℝ) ^ (3 * n) * ((1 + ε) / (1 - ε)) ^ m / 2 ^ (m * N)
      ≤ (q : ℝ) ^ (3 * n) * 2 ^ m / 2 ^ (m * N) := by
        have h2 : ((1 + ε) / (1 - ε)) ^ m ≤ (2 : ℝ) ^ m :=
          pow_le_pow_left₀ hr0 (ratio_le_two h0 hε) m
        gcongr
    _ = (q : ℝ) ^ (3 * n) / 2 ^ (m * (N - 1)) := by
        rw [hexp]
        field_simp

end ComSISCore

end Abba
