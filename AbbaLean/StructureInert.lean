import Mathlib
import AbbaLean.Structure

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, inert case

For the inert factor `𝓡 = S ⊕ uS` with `S/k` a quadratic field extension,
`θ` the nontrivial `k`-automorphism, and `ξ = c·θ(c)` a nonzero twist, we build an
explicit ring isomorphism `𝓡 ≃+* M₂(k)`.

The paper proves this via "central simple + Artin–Wedderburn + little Wedderburn".
The formal route here is constructive and Wedderburn-free: `S` itself is an
`𝓡`-module via `s·v = sv` and `u·v = c·θ(v)` (the relation `u² = ξ` is exactly
`c·θ(c) = ξ`), giving a homomorphism `𝓡 → End_k(S)`; it is injective by a two-point
evaluation argument, hence bijective by comparing `k`-dimensions (`4 = 4`), and
`End_k(S) ≅ M₂(k)` by choosing a basis.

For the ABBA application `k = 𝔽_{q^f}`, `S = 𝔽_{q^{2f}}`: `θ` is the relative
Frobenius and the hypothesis `∃ c, c·θ(c) = ξ` is surjectivity of the norm of a
finite-field extension, to be discharged separately.
-/

namespace Abba

namespace Twisted

open Module

section Inert

variable {k S : Type*} [Field k] [Field S] [Algebra k S]
variable (d : TwistData S)

instance : Module k (Twisted d) := inferInstanceAs (Module k (S × S))

@[simp] theorem smul_fst (r : k) (x : Twisted d) : (r • x).1 = r • x.1 := rfl
@[simp] theorem smul_snd (r : k) (x : Twisted d) : (r • x).2 = r • x.2 := rfl

variable (hθk : ∀ r : k, d.θ (algebraMap k S r) = algebraMap k S r)
variable (c : S)

/-- The action of `a + ub` on `V = S`: `v ↦ a·v + c·θ(b)·θ(v)`. -/
def act (x : Twisted d) : S →ₗ[k] S where
  toFun v := x.1 * v + c * d.θ x.2 * d.θ v
  map_add' v w := by
    simp only [map_add]
    ring
  map_smul' r v := by
    simp only [Algebra.smul_def, map_mul, hθk, RingHom.id_apply]
    ring

@[simp] theorem act_apply (x : Twisted d) (v : S) :
    act d hθk c x v = x.1 * v + c * d.θ x.2 * d.θ v := rfl

/-- `act` as a ring homomorphism `𝓡 → End_k(S)`; multiplicativity is exactly the
relation `c·θ(c) = ξ`. -/
def inertHom (hc : c * d.θ c = d.ξ) : Twisted d →+* Module.End k S where
  toFun := act d hθk c
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp only [Module.End.mul_apply, act_apply, mul_fst, mul_snd, map_add, map_mul,
      d.invol, ← hc]
    ring
  map_zero' := by
    ext v
    simp
  map_add' x y := by
    ext v
    simp only [act_apply, add_fst, add_snd, map_add, LinearMap.add_apply]
    ring

variable (hc : c * d.θ c = d.ξ)

@[simp] theorem inertHom_apply (x : Twisted d) (v : S) :
    inertHom d hθk c hc x v = x.1 * v + c * d.θ x.2 * d.θ v := rfl

/-- Injectivity, by evaluating the vanishing endomorphism at `1` and at a `w` with
`θ(w) ≠ w`. -/
theorem inertHom_injective (hξ0 : d.ξ ≠ 0) (hθne : ∃ w : S, d.θ w ≠ w) :
    Function.Injective (inertHom d hθk c hc) := by
  have hc0 : c ≠ 0 := by
    intro h
    exact hξ0 (by rw [← hc, h, zero_mul])
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨w, hw⟩ := hθne
  have h1 : x.1 + c * d.θ x.2 = 0 := by
    have := congrArg (fun f : Module.End k S => f 1) hx
    simpa using this
  have hw' : x.1 * w + c * d.θ x.2 * d.θ w = 0 := by
    have := congrArg (fun f : Module.End k S => f w) hx
    simpa using this
  have h2 : c * d.θ x.2 * (d.θ w - w) = 0 := by linear_combination hw' - w * h1
  have hx2 : x.2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hc0
      · exact d.θ.injective (by simpa using h')
    · exact absurd (sub_eq_zero.mp h) hw
  have hx1 : x.1 = 0 := by
    have := h1
    rw [hx2, map_zero, mul_zero, add_zero] at this
    exact this
  ext
  · exact hx1
  · exact hx2

/-- `act` as a `k`-linear map in the algebra argument (for the dimension count). -/
def actLin : Twisted d →ₗ[k] (S →ₗ[k] S) where
  toFun := act d hθk c
  map_add' x y := by
    ext v
    simp only [act_apply, add_fst, add_snd, map_add, LinearMap.add_apply]
    ring
  map_smul' r x := by
    ext v
    show act d hθk c (r • x) v = (r • act d hθk c x) v
    rw [LinearMap.smul_apply]
    simp only [act_apply, smul_fst, smul_snd, Algebra.smul_def, map_mul, hθk]
    ring

variable [FiniteDimensional k S]

theorem finrank_twisted : finrank k (Twisted d) = 2 * finrank k S := by
  have h : finrank k (Twisted d) = finrank k (S × S) := rfl
  rw [h, Module.finrank_prod, two_mul]

theorem inertHom_bijective (hξ0 : d.ξ ≠ 0) (hθne : ∃ w : S, d.θ w ≠ w)
    (hdim : finrank k S = 2) :
    Function.Bijective (inertHom d hθk c hc) := by
  have hinj := inertHom_injective d hθk c hc hξ0 hθne
  refine ⟨hinj, ?_⟩
  have hinj' : Function.Injective (actLin d hθk c) := fun a b hab => hinj hab
  have h1 : finrank k (LinearMap.range (actLin d hθk c)) = finrank k (Twisted d) :=
    LinearMap.finrank_range_of_inj hinj'
  have h2 : finrank k (Twisted d) = 4 := by rw [finrank_twisted, hdim]
  have h3 : finrank k (S →ₗ[k] S) = 4 := by
    rw [Module.finrank_linearMap, hdim]
  have htop : LinearMap.range (actLin d hθk c) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h1, h2, h3])
  intro f
  exact LinearMap.range_eq_top.mp htop f

/-- Inert case of Lemma `structure`: `𝓡 = S ⊕ uS ≅ M₂(k)` for `S/k` quadratic,
`θ ≠ id` fixing `k`, and `ξ = c·θ(c) ≠ 0`. -/
noncomputable def inertEquiv (hξ0 : d.ξ ≠ 0) (hθne : ∃ w : S, d.θ w ≠ w)
    (hdim : finrank k S = 2) :
    Twisted d ≃+* Matrix (Fin 2) (Fin 2) k :=
  (RingEquiv.ofBijective (inertHom d hθk c hc)
      (inertHom_bijective d hθk c hc hξ0 hθne hdim)).trans
    (LinearMap.toMatrixAlgEquiv
      ((Module.finBasis k S).reindex (finCongr hdim))).toRingEquiv

end Inert

end Twisted

end Abba
