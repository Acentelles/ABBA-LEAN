import Mathlib
import AbbaLean.Structure

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, uniform per-factor theorem

The split/inert case analysis of the paper is replaced by a single statement: for
`S` a commutative `k`-algebra of dimension 2 and twisting data `(θ, ξ)` fixing `k`,
if some unit `c` satisfies `c·θ(c) = ξ` and some `w` has `θ(w) - w` a unit, then
`Twisted d ≃+* M₂(k)`.

The proof is the module action `u·v = c·θ(v)` on `V = S` (as in the inert case);
field-ness of `S` was never needed — the two-point injectivity argument only uses
that `c` and `θ(w) - w` are units.  The split model discharges the hypotheses with
`c = (ξ, 1)`, `w = (0, 1)`; the inert model with norm surjectivity and any
`w ∉ k`.  In the CRT application the hypotheses become the only per-factor
arithmetic obligations.

Also here: `Twisted.congr`, transport of the twisted algebra along a ring
isomorphism respecting the data (the glue between CRT and `piEquiv`).
-/

namespace Abba

namespace Twisted

open Module

section Congr

variable {S S' : Type*} [CommRing S] [CommRing S'] {d : TwistData S} {d' : TwistData S'}

/-- Transport of the twisted algebra along a data-respecting ring isomorphism. -/
def congr (e : S ≃+* S') (hθ : ∀ s, e (d.θ s) = d'.θ (e s)) (hξ : e d.ξ = d'.ξ) :
    Twisted d ≃+* Twisted d' where
  toFun x := (e x.1, e x.2)
  invFun y := (e.symm y.1, e.symm y.2)
  left_inv x := by refine ext ?_ ?_ <;> simp
  right_inv y := by refine ext ?_ ?_ <;> simp
  map_mul' x y := by
    refine ext ?_ ?_
    · show e ((x * y).1) = _
      rw [mul_fst]
      simp only [map_add, map_mul, hθ, hξ]
      rfl
    · show e ((x * y).2) = _
      rw [mul_snd]
      simp only [map_add, map_mul, hθ]
      rfl
  map_add' x y := by
    refine ext ?_ ?_
    · show e ((x + y).1) = _
      rw [add_fst, map_add]
      rfl
    · show e ((x + y).2) = _
      rw [add_snd, map_add]
      rfl

end Congr

section Uniform

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
variable (d : TwistData S)

instance instModuleUniform : Module k (Twisted d) := inferInstanceAs (Module k (S × S))

@[simp] theorem usmul_fst (r : k) (x : Twisted d) : (r • x).1 = r • x.1 := rfl
@[simp] theorem usmul_snd (r : k) (x : Twisted d) : (r • x).2 = r • x.2 := rfl

variable (hθk : ∀ r : k, d.θ (algebraMap k S r) = algebraMap k S r)
variable (c : S)

/-- The action of `a + ub` on `V = S`: `v ↦ a·v + c·θ(b)·θ(v)`. -/
def uact (x : Twisted d) : S →ₗ[k] S where
  toFun v := x.1 * v + c * d.θ x.2 * d.θ v
  map_add' v w := by
    simp only [map_add]
    ring
  map_smul' r v := by
    simp only [Algebra.smul_def, map_mul, hθk, RingHom.id_apply]
    ring

@[simp] theorem uact_apply (x : Twisted d) (v : S) :
    uact d hθk c x v = x.1 * v + c * d.θ x.2 * d.θ v := rfl

/-- `uact` as a ring homomorphism; multiplicativity is the relation `c·θ(c) = ξ`. -/
def uniformHom (hc : c * d.θ c = d.ξ) : Twisted d →+* Module.End k S where
  toFun := uact d hθk c
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp only [Module.End.mul_apply, uact_apply, mul_fst, mul_snd, map_add, map_mul,
      d.invol, ← hc]
    ring
  map_zero' := by
    ext v
    simp
  map_add' x y := by
    ext v
    simp only [uact_apply, add_fst, add_snd, map_add, LinearMap.add_apply]
    ring

variable (hc : c * d.θ c = d.ξ)

@[simp] theorem uniformHom_apply (x : Twisted d) (v : S) :
    uniformHom d hθk c hc x v = x.1 * v + c * d.θ x.2 * d.θ v := rfl

/-- Injectivity, by evaluating at `1` and at `w` with `θ(w) - w` a unit. -/
theorem uniformHom_injective (hcu : IsUnit c) (hwu : ∃ w : S, IsUnit (d.θ w - w)) :
    Function.Injective (uniformHom d hθk c hc) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨w, hw⟩ := hwu
  have h1 : x.1 + c * d.θ x.2 = 0 := by
    have := congrArg (fun f : Module.End k S => f 1) hx
    simpa using this
  have hw' : x.1 * w + c * d.θ x.2 * d.θ w = 0 := by
    have := congrArg (fun f : Module.End k S => f w) hx
    simpa using this
  have h2 : c * d.θ x.2 * (d.θ w - w) = 0 := by linear_combination hw' - w * h1
  have h3 : c * d.θ x.2 = 0 := (IsUnit.mul_left_eq_zero hw).mp h2
  have h4 : d.θ x.2 = 0 := (IsUnit.mul_right_eq_zero hcu).mp h3
  have hx2 : x.2 = 0 := by
    have h5 := congrArg d.θ h4
    rwa [d.invol, map_zero] at h5
  have hx1 : x.1 = 0 := by
    rw [hx2, map_zero, mul_zero, add_zero] at h1
    exact h1
  refine ext hx1 hx2

/-- `uact` as a `k`-linear map in the algebra argument. -/
def uactLin : Twisted d →ₗ[k] (S →ₗ[k] S) where
  toFun := uact d hθk c
  map_add' x y := by
    ext v
    simp only [uact_apply, add_fst, add_snd, map_add, LinearMap.add_apply]
    ring
  map_smul' r x := by
    ext v
    show uact d hθk c (r • x) v = (r • uact d hθk c x) v
    rw [LinearMap.smul_apply]
    simp only [uact_apply, usmul_fst, usmul_snd, Algebra.smul_def, map_mul, hθk]
    ring

variable [FiniteDimensional k S]

theorem ufinrank_twisted : finrank k (Twisted d) = 2 * finrank k S := by
  have h : finrank k (Twisted d) = finrank k (S × S) := rfl
  rw [h, Module.finrank_prod, two_mul]

theorem uniformHom_bijective (hcu : IsUnit c) (hwu : ∃ w : S, IsUnit (d.θ w - w))
    (hdim : finrank k S = 2) :
    Function.Bijective (uniformHom d hθk c hc) := by
  have hinj := uniformHom_injective d hθk c hc hcu hwu
  refine ⟨hinj, ?_⟩
  have hinj' : Function.Injective (uactLin d hθk c) := fun a b hab => hinj hab
  have h1 : finrank k (LinearMap.range (uactLin d hθk c)) = finrank k (Twisted d) :=
    LinearMap.finrank_range_of_inj hinj'
  have h2 : finrank k (Twisted d) = 4 := by rw [ufinrank_twisted, hdim]
  have h3 : finrank k (S →ₗ[k] S) = 4 := by
    rw [Module.finrank_linearMap, hdim]
  have htop : LinearMap.range (uactLin d hθk c) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h1, h2, h3])
  intro f
  exact LinearMap.range_eq_top.mp htop f

/-- **Uniform per-factor theorem**: for `S` a commutative 2-dimensional
`k`-algebra with data fixing `k`, a unit `c` with `c·θ(c) = ξ`, and some
`θ(w) - w` a unit, the twisted algebra is a 2×2 matrix ring over `k`.
Subsumes both the split and inert cases of Lemma `structure`. -/
noncomputable def uniformEquiv (hcu : IsUnit c) (hwu : ∃ w : S, IsUnit (d.θ w - w))
    (hdim : finrank k S = 2) :
    Twisted d ≃+* Matrix (Fin 2) (Fin 2) k :=
  (RingEquiv.ofBijective (uniformHom d hθk c hc)
      (uniformHom_bijective d hθk c hc hcu hwu hdim)).trans
    (LinearMap.toMatrixAlgEquiv
      ((Module.finBasis k S).reindex (finCongr hdim))).toRingEquiv

end Uniform

end Twisted

end Abba
