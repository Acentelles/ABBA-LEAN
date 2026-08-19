import Mathlib

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, per-factor analysis

Paper: Lemma `Lemma:structure`: `Λ_q ≅ ∏ M₂(𝔽_{q^{f_i}})` and `Z(Λ_q) = 𝓞_{K_q}`.

This file formalizes the per-factor heart of the proof.  The factor
`𝓡 = S ⊕ uS` with relations `su = uθ(s)`, `u² = ξ` is realized concretely on
`S × S` (`a + ub ↔ (a, b)`) with multiplication
`(a, b)(c, d) = (ac + ξ·θ(b)·d, θ(a)·d + bc)`:

* `Twisted d` — the ring, for `d : TwistData S`; `Ring` instance from scratch.
* `mem_center_iff` — the paper's centre computation, uniform in the case split:
  if some `θ(s₀) - s₀` is a unit, then `Z(𝓡) = {a + u·0 : θ(a) = a} = S^θ`.
* `splitEquiv` — the split case: for `S = k × k` with the swap involution and
  `ξ = (c, c)`, `c ≠ 0`, an explicit ring isomorphism `𝓡 ≃+* M₂(k)`.

The inert case is in `AbbaLean.StructureInert`.
-/

namespace Abba

/-- Twisting data on a commutative ring `S`: a ring involution `θ` and a
`θ`-fixed twist `ξ`. -/
structure TwistData (S : Type*) [CommRing S] where
  θ : S ≃+* S
  invol : ∀ s, θ (θ s) = s
  ξ : S
  fixed : θ ξ = ξ

/-- The twisted algebra `𝓡 = S ⊕ uS`, `su = uθ(s)`, `u² = ξ`, realized on `S × S`. -/
def Twisted {S : Type*} [CommRing S] (_d : TwistData S) : Type _ := S × S

namespace Twisted

variable {S : Type*} [CommRing S] {d : TwistData S}

instance instAddCommGroup : AddCommGroup (Twisted d) :=
  inferInstanceAs (AddCommGroup (S × S))

@[ext]
theorem ext {x y : Twisted d} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  Prod.ext h1 h2

instance instAddCommGroupWithOne : AddCommGroupWithOne (Twisted d) where
  __ : AddCommGroup (Twisted d) := inferInstanceAs (AddCommGroup (S × S))
  one := ((1 : S), (0 : S))
  natCast n := ((n : S), 0)
  natCast_zero := by
    refine ext ?_ ?_
    · show ((0 : ℕ) : S) = 0
      simp
    · rfl
  natCast_succ n := by
    refine ext ?_ ?_
    · show ((n + 1 : ℕ) : S) = (n : S) + 1
      push_cast
      ring
    · show (0 : S) = 0 + 0
      simp
  intCast z := ((z : S), 0)
  intCast_ofNat n := by
    refine ext ?_ ?_
    · show (((n : ℕ) : ℤ) : S) = ((n : ℕ) : S)
      push_cast
      ring
    · rfl
  intCast_negSucc n := by
    refine ext ?_ ?_
    · show ((Int.negSucc n : ℤ) : S) = -((n + 1 : ℕ) : S)
      simp [Int.cast_negSucc]
    · show (0 : S) = -0
      simp

instance instRing : Ring (Twisted d) where
  __ : AddCommGroupWithOne (Twisted d) := instAddCommGroupWithOne
  mul x y := (x.1 * y.1 + d.ξ * d.θ x.2 * y.2, d.θ x.1 * y.2 + x.2 * y.1)
  zero_mul x := by
    refine ext ?_ ?_
    · show (0 : S) * x.1 + d.ξ * d.θ 0 * x.2 = 0
      simp
    · show d.θ 0 * x.2 + (0 : S) * x.1 = 0
      simp
  mul_zero x := by
    refine ext ?_ ?_
    · show x.1 * 0 + d.ξ * d.θ x.2 * 0 = 0
      simp
    · show d.θ x.1 * 0 + x.2 * 0 = 0
      simp
  left_distrib x y z := by
    refine ext ?_ ?_
    · show x.1 * (y.1 + z.1) + d.ξ * d.θ x.2 * (y.2 + z.2)
          = (x.1 * y.1 + d.ξ * d.θ x.2 * y.2) + (x.1 * z.1 + d.ξ * d.θ x.2 * z.2)
      ring
    · show d.θ x.1 * (y.2 + z.2) + x.2 * (y.1 + z.1)
          = (d.θ x.1 * y.2 + x.2 * y.1) + (d.θ x.1 * z.2 + x.2 * z.1)
      ring
  right_distrib x y z := by
    refine ext ?_ ?_
    · show (x.1 + y.1) * z.1 + d.ξ * d.θ (x.2 + y.2) * z.2
          = (x.1 * z.1 + d.ξ * d.θ x.2 * z.2) + (y.1 * z.1 + d.ξ * d.θ y.2 * z.2)
      rw [map_add]
      ring
    · show d.θ (x.1 + y.1) * z.2 + (x.2 + y.2) * z.1
          = (d.θ x.1 * z.2 + x.2 * z.1) + (d.θ y.1 * z.2 + y.2 * z.1)
      rw [map_add]
      ring
  one_mul x := by
    refine ext ?_ ?_
    · show (1 : S) * x.1 + d.ξ * d.θ 0 * x.2 = x.1
      simp
    · show d.θ 1 * x.2 + (0 : S) * x.1 = x.2
      simp
  mul_one x := by
    refine ext ?_ ?_
    · show x.1 * 1 + d.ξ * d.θ x.2 * 0 = x.1
      simp
    · show d.θ x.1 * 0 + x.2 * 1 = x.2
      simp
  mul_assoc x y z := by
    refine ext ?_ ?_
    · show (x.1 * y.1 + d.ξ * d.θ x.2 * y.2) * z.1
            + d.ξ * d.θ (d.θ x.1 * y.2 + x.2 * y.1) * z.2
          = x.1 * (y.1 * z.1 + d.ξ * d.θ y.2 * z.2)
            + d.ξ * d.θ x.2 * (d.θ y.1 * z.2 + y.2 * z.1)
      simp only [map_add, map_mul, d.invol, d.fixed]
      ring
    · show d.θ (x.1 * y.1 + d.ξ * d.θ x.2 * y.2) * z.2
            + (d.θ x.1 * y.2 + x.2 * y.1) * z.1
          = d.θ x.1 * (d.θ y.1 * z.2 + y.2 * z.1)
            + x.2 * (y.1 * z.1 + d.ξ * d.θ y.2 * z.2)
      simp only [map_add, map_mul, d.invol, d.fixed]
      ring

/-- The distinguished element `u`. -/
def u : Twisted d := ((0 : S), (1 : S))

/-- The embedding of `S` as the subring `a + u·0`. -/
def ofS (a : S) : Twisted d := (a, (0 : S))

@[simp] theorem mul_fst (x y : Twisted d) :
    (x * y).1 = x.1 * y.1 + d.ξ * d.θ x.2 * y.2 := rfl
@[simp] theorem mul_snd (x y : Twisted d) :
    (x * y).2 = d.θ x.1 * y.2 + x.2 * y.1 := rfl
@[simp] theorem one_fst : (1 : Twisted d).1 = 1 := rfl
@[simp] theorem one_snd : (1 : Twisted d).2 = 0 := rfl
@[simp] theorem add_fst (x y : Twisted d) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem add_snd (x y : Twisted d) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem zero_fst : (0 : Twisted d).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : Twisted d).2 = 0 := rfl
@[simp] theorem u_fst : (u : Twisted d).1 = 0 := rfl
@[simp] theorem u_snd : (u : Twisted d).2 = 1 := rfl
@[simp] theorem ofS_fst (a : S) : (ofS a : Twisted d).1 = a := rfl
@[simp] theorem ofS_snd (a : S) : (ofS a : Twisted d).2 = 0 := rfl

/-- The defining relation `u² = ξ`, verified in the model. -/
theorem u_mul_u : (u : Twisted d) * u = ofS d.ξ := by
  ext <;> simp

/-- The defining relation `s·u = u·θ(s)`. -/
theorem ofS_mul_u (s : S) : (ofS s : Twisted d) * u = u * ofS (d.θ s) := by
  ext <;> simp

/-! ## Centre (paper: first part of the proof of Lemma `structure`) -/

/-- The centre of `𝓡` consists exactly of the `θ`-fixed scalars, provided some
`θ(s₀) - s₀` is a unit (true in both the split and inert étale cases). -/
theorem mem_center_iff (hs : ∃ s₀ : S, IsUnit (d.θ s₀ - s₀)) (x : Twisted d) :
    x ∈ Subring.center (Twisted d) ↔ x.2 = 0 ∧ d.θ x.1 = x.1 := by
  rw [Subring.mem_center_iff]
  constructor
  · intro h
    obtain ⟨s₀, hs₀⟩ := hs
    have h1 : (ofS s₀ * x).2 = (x * ofS s₀).2 :=
      congrArg (fun z : Twisted d => z.2) (h (ofS s₀))
    rw [mul_snd, mul_snd] at h1
    simp only [ofS_fst, ofS_snd, zero_mul, mul_zero, add_zero, zero_add] at h1
    have h2 : (d.θ s₀ - s₀) * x.2 = 0 := by linear_combination h1
    have hx2 : x.2 = 0 := (IsUnit.mul_right_eq_zero hs₀).mp h2
    refine ⟨hx2, ?_⟩
    have h3 : (u * x).2 = (x * u).2 :=
      congrArg (fun z : Twisted d => z.2) (h u)
    rw [mul_snd, mul_snd] at h3
    simp only [u_fst, u_snd, map_zero, zero_mul, mul_zero, mul_one, one_mul,
      add_zero, zero_add, hx2] at h3
    exact h3.symm
  · rintro ⟨h2, h1⟩ y
    ext
    · rw [mul_fst, mul_fst, h2]
      simp [mul_comm]
    · rw [mul_snd, mul_snd, h2, h1]
      simp [mul_comm]

/-! ## Split case (paper: second part of the proof of Lemma `structure`) -/

section Split

variable (k : Type*) [Field k]

/-- The split twisting data: `S = k × k`, `θ` = swap, `ξ = (c, c)`. -/
def swapData (c : k) : TwistData (k × k) where
  θ := RingEquiv.prodComm
  invol := fun _ => rfl
  ξ := (c, c)
  fixed := rfl

variable {k} {c : k}

@[simp] theorem swap_mul_11 (x y : Twisted (swapData k c)) :
    (x * y).1.1 = x.1.1 * y.1.1 + c * x.2.2 * y.2.1 := rfl
@[simp] theorem swap_mul_12 (x y : Twisted (swapData k c)) :
    (x * y).1.2 = x.1.2 * y.1.2 + c * x.2.1 * y.2.2 := rfl
@[simp] theorem swap_mul_21 (x y : Twisted (swapData k c)) :
    (x * y).2.1 = x.1.2 * y.2.1 + x.2.1 * y.1.1 := rfl
@[simp] theorem swap_mul_22 (x y : Twisted (swapData k c)) :
    (x * y).2.2 = x.1.1 * y.2.2 + x.2.2 * y.1.2 := rfl

variable (k)

/-- Split case of Lemma `structure`: `(k×k) ⊕ u(k×k) ≅ M₂(k)`, by
`a + ub ↦ [[a₁, b₂], [c·b₁, a₂]]` (the paper's `D(s₁,s₂)` and `U = E₁₂ + ξE₂₁`). -/
def splitEquiv (c : k) (hc : c ≠ 0) :
    Twisted (swapData k c) ≃+* Matrix (Fin 2) (Fin 2) k where
  toFun x := !![x.1.1, x.2.2; c * x.2.1, x.1.2]
  invFun M := ((M 0 0, M 1 1), (c⁻¹ * M 1 0, M 0 1))
  left_inv x := by
    ext <;> simp <;> field_simp
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  map_mul' x y := by
    have hξ1 : (swapData k c).ξ.1 = c := rfl
    have hξ2 : (swapData k c).ξ.2 = c := rfl
    have hθ1 : ∀ z : k × k, ((swapData k c).θ z).1 = z.2 := fun _ => rfl
    have hθ2 : ∀ z : k × k, ((swapData k c).θ z).2 = z.1 := fun _ => rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hξ1, hξ2, hθ1, hθ2, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

end Split

end Twisted

end Abba
