import Mathlib
import AbbaLean.HcCount

set_option linter.style.header false

/-!
# ABBA — Cor `Hc`, cardinality `|H_c| = (2·cb+1)^d`

From the independence theorem `coeff_eq_zero_of_relation`: the coefficient map is
injective, so the challenge set (image of the box `[-cb, cb]^d`) has exactly
`(2·cb+1)^d` elements.  The power-independence input is discharged from any
`PowerBasis` via `pow_linearIndependent` (e.g. the cyclotomic power basis).
-/

namespace Abba

open Finset

section PowerIndep

variable {K : Type*} [Field K] [CharZero K]

/-- The first `m` powers of a power-basis generator are linearly independent. -/
theorem pow_linearIndependent (pb : PowerBasis ℚ K) (m : ℕ) (hm : m ≤ pb.dim) :
    LinearIndependent ℚ (fun e : Fin m => pb.gen ^ (e : ℕ)) := by
  have hb := pb.basis.linearIndependent
  have h2 := hb.comp (Fin.castLE hm) (Fin.castLE_injective hm)
  have heq : (pb.basis ∘ Fin.castLE hm) = fun e : Fin m => pb.gen ^ (e : ℕ) := by
    funext e
    simp [PowerBasis.coe_basis]
  rwa [heq] at h2

end PowerIndep

section Card

variable {K : Type*} [Field K] [CharZero K]

/-- The challenge family on the `K`-side: `v 0 = 1`, `v i = z^i + z^{-i}`. -/
def chal (z : K) : ℕ → K := fun i => if i = 0 then 1 else z ^ i + z⁻¹ ^ i

/-- The coefficient map on `Fin d`-indexed integer vectors. -/
def chalMap (z : K) (d : ℕ) (c : Fin d → ℤ) : K :=
  ∑ i : Fin d, (c i : K) * chal z (i : ℕ)

/-- Extension of a `Fin d`-vector to `ℕ` by zero. -/
def extZ (d : ℕ) (c : Fin d → ℤ) : ℕ → ℤ := fun i => if h : i < d then c ⟨i, h⟩ else 0

theorem extZ_val (d : ℕ) (c : Fin d → ℤ) (i : Fin d) : extZ d c (i : ℕ) = c i := by
  rw [extZ]
  simp only [i.isLt, dif_pos]

/-- `chalMap` written with the `i = 0` term split off. -/
theorem chalMap_eq (z : K) (d : ℕ) (hd : 0 < d) (c : Fin d → ℤ) :
    chalMap z d c = ((extZ d c 0 : ℤ) : K)
      + ∑ i ∈ Ico 1 d, ((extZ d c i : ℤ) : K) * (z ^ i + z⁻¹ ^ i) := by
  classical
  have h1 : chalMap z d c = ∑ i ∈ range d, ((extZ d c i : ℤ) : K) * chal z i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((extZ d c i : ℤ) : K) * chal z i) d]
    simp only [chalMap]
    exact Finset.sum_congr rfl fun i _ => by rw [extZ_val]
  have h2 : ∑ i ∈ range d, ((extZ d c i : ℤ) : K) * chal z i
      = ((extZ d c 0 : ℤ) : K) * chal z 0
        + ∑ i ∈ Ico 1 d, ((extZ d c i : ℤ) : K) * chal z i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (by omega : (0 : ℕ) ≤ 1) (by omega : 1 ≤ d)]
    congr 1
    rw [← Finset.range_eq_Ico, Finset.sum_range_one]
  have h3 : chal z 0 = 1 := if_pos rfl
  have h4 : ∀ i ∈ Ico 1 d, ((extZ d c i : ℤ) : K) * chal z i
      = ((extZ d c i : ℤ) : K) * (z ^ i + z⁻¹ ^ i) := by
    intro i hi
    obtain ⟨h5, _⟩ := mem_Ico.mp hi
    rw [chal]
    simp only [show i ≠ 0 by omega, if_false]
  rw [h1, h2, h3, mul_one, Finset.sum_congr rfl h4]

/-- Injectivity of the coefficient map, from power independence. -/
theorem chalMap_injective (d : ℕ) (hd : 0 < d) (z : K) (hz0 : z ≠ 0)
    (hli : LinearIndependent ℚ (fun e : Fin (2 * d - 1) => z ^ (e : ℕ))) :
    Function.Injective (chalMap z d) := by
  intro c c' heq
  set Δ : ℕ → ℚ := fun j => ((extZ d c j : ℤ) : ℚ) - ((extZ d c' j : ℤ) : ℚ) with hΔ
  have e1 := chalMap_eq z d hd c
  have e2 := chalMap_eq z d hd c'
  have hrel : ((Δ 0 : ℚ) : K) + ∑ i ∈ Ico 1 d, ((Δ i : ℚ) : K) * (z ^ i + z⁻¹ ^ i) = 0 := by
    have hsum : ∑ i ∈ Ico 1 d, ((Δ i : ℚ) : K) * (z ^ i + z⁻¹ ^ i)
        = (∑ i ∈ Ico 1 d, ((extZ d c i : ℤ) : K) * (z ^ i + z⁻¹ ^ i))
          - ∑ i ∈ Ico 1 d, ((extZ d c' i : ℤ) : K) * (z ^ i + z⁻¹ ^ i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcast : ((Δ i : ℚ) : K)
          = ((extZ d c i : ℤ) : K) - ((extZ d c' i : ℤ) : K) := by
        rw [hΔ]
        push_cast
        ring
      rw [hcast]
      ring
    have h0 : ((Δ 0 : ℚ) : K) = ((extZ d c 0 : ℤ) : K) - ((extZ d c' 0 : ℤ) : K) := by
      rw [hΔ]
      push_cast
      ring
    rw [h0, hsum]
    linear_combination -e1 + e2 + heq
  have hzero := coeff_eq_zero_of_relation d hd z hz0 hli Δ hrel
  funext i
  have h5 := hzero (i : ℕ) i.isLt
  rw [hΔ] at h5
  have h6 : ((extZ d c (i : ℕ) : ℤ) : ℚ) = ((extZ d c' (i : ℕ) : ℤ) : ℚ) :=
    sub_eq_zero.mp h5
  have h7 : extZ d c (i : ℕ) = extZ d c' (i : ℕ) := by exact_mod_cast h6
  rwa [extZ_val, extZ_val] at h7

/-- **Cor `Hc`, counting clause**: the challenge set has `(2·cb+1)^d` elements. -/
theorem card_Hc [DecidableEq K] (d cb : ℕ) (hd : 0 < d) (z : K) (hz0 : z ≠ 0)
    (hli : LinearIndependent ℚ (fun e : Fin (2 * d - 1) => z ^ (e : ℕ))) :
    ((Fintype.piFinset fun _ : Fin d => Finset.Icc (-(cb : ℤ)) (cb : ℤ)).image
      (chalMap z d)).card = (2 * cb + 1) ^ d := by
  classical
  rw [Finset.card_image_of_injective _ (chalMap_injective d hd z hz0 hli),
    Fintype.card_piFinset]
  have hIcc : (Finset.Icc (-(cb : ℤ)) (cb : ℤ)).card = 2 * cb + 1 := by
    rw [Int.card_Icc]
    omega
  simp [hIcc, Finset.prod_const, Finset.card_univ]

end Card

end Abba
