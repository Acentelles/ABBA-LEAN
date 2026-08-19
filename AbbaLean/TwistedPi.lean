import Mathlib
import AbbaLean.Structure

set_option linter.style.header false

/-!
# ABBA — Lemma `crt`, quaternion case: product decomposition of the twisted algebra

If the base ring decomposes as a product `S = ∏ Sᵢ` with the involution and twist
acting componentwise, then the twisted algebra decomposes accordingly:
`Twisted (piData) ≃+* ∀ i, Twisted (dataᵢ)`.

Combined with CRT for `𝓞_L/q𝓞_L ≅ ∏ 𝓞_L/𝔮ᵢ𝓞_L` (Mathlib's
`Ideal.quotientInfRingEquivPiQuotient`) and conjugation-stability of the factors,
this is the quaternion case of the paper's Lemma `crt`; the remaining arithmetic
input (the étale identification of each factor with the split or inert model) is
future work.
-/

namespace Abba

namespace Twisted

variable {ι : Type*} {S : ι → Type*} [∀ i, CommRing (S i)]

/-- Componentwise twisting data on a product ring. -/
def piData (data : ∀ i, TwistData (S i)) : TwistData (∀ i, S i) where
  θ := RingEquiv.piCongrRight fun i => (data i).θ
  invol := fun s => by
    funext i
    exact (data i).invol (s i)
  ξ := fun i => (data i).ξ
  fixed := by
    funext i
    exact (data i).fixed

@[simp] theorem piData_θ_apply (data : ∀ i, TwistData (S i)) (s : ∀ i, S i) (i : ι) :
    (piData data).θ s i = (data i).θ (s i) := rfl

@[simp] theorem piData_ξ_apply (data : ∀ i, TwistData (S i)) (i : ι) :
    (piData data).ξ i = (data i).ξ := rfl

/-- The twisted algebra of a product decomposes as the product of the twisted
algebras (Lemma `crt`, quaternion case, algebraic part). -/
def piEquiv (data : ∀ i, TwistData (S i)) :
    Twisted (piData data) ≃+* ∀ i, Twisted (data i) where
  toFun x := fun i => (x.1 i, x.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := by
    funext i
    refine Twisted.ext ?_ ?_
    · show (x * y).1 i = (x.1 i) * (y.1 i) + (data i).ξ * (data i).θ (x.2 i) * (y.2 i)
      rw [mul_fst]
      rfl
    · show (x * y).2 i = (data i).θ (x.1 i) * (y.2 i) + (x.2 i) * (y.1 i)
      rw [mul_snd]
      rfl
  map_add' x y := by
    funext i
    refine Twisted.ext ?_ ?_
    · rfl
    · rfl

end Twisted

end Abba
