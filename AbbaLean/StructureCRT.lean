import Mathlib
import AbbaLean.StructureQuot

set_option linter.style.header false

/-!
# ABBA — Lemma `crt` for the quaternion order, equivariant form

For an involution `σ : B ≃ₐ[A] B`, a twist `ξ₀ ∈ A`, ideals `J i` of `A` whose
extensions to `B` are pairwise coprime, and a global ideal `Q` with
`Q·B = ⨅ Jᵢ·B`, the twisted algebra over `B ⧸ Q·B` decomposes as the product of
the twisted algebras over the factors:

`crtTwisted : Twisted (quotData σ hσ ξ₀ Q) ≃+* ∀ i, Twisted (quotData σ hσ ξ₀ (J i))`.

This is the paper's Lemma `crt` in the quaternion case, with the involution kept
through the decomposition (the point that lets each factor be handled by the
uniform theorem).  `isCoprime_map` discharges the coprimality hypothesis from
coprimality in `A`.
-/

namespace Abba

namespace Twisted

open Function

section CRT

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Coprimality of ideals is preserved by extension. -/
theorem isCoprime_map {I I' : Ideal A} (h : IsCoprime I I') :
    IsCoprime (I.map (algebraMap A B)) (I'.map (algebraMap A B)) := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  rw [← Ideal.map_sup, h, Ideal.map_top]

variable (σ : B ≃ₐ[A] B) (hσ : ∀ x, σ (σ x) = x) (ξ₀ : A)
variable {ι : Type*} [Finite ι]
variable (J : ι → Ideal A) (Q : Ideal A)
variable (hcop : Pairwise (IsCoprime on fun i => (J i).map (algebraMap A B)))
variable (hglob : Q.map (algebraMap A B) = ⨅ i, (J i).map (algebraMap A B))

/-- The base-ring CRT isomorphism. -/
noncomputable def crtRing :
    (B ⧸ Q.map (algebraMap A B)) ≃+* ∀ i, B ⧸ (J i).map (algebraMap A B) :=
  (Ideal.quotEquivOfEq hglob).trans (Ideal.quotientInfRingEquivPiQuotient _ hcop)

@[simp] theorem crtRing_mk (x : B) :
    crtRing J Q hcop hglob (Ideal.Quotient.mk (Q.map (algebraMap A B)) x)
      = fun i => Ideal.Quotient.mk ((J i).map (algebraMap A B)) x := by
  rw [crtRing, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

/-- **Lemma `crt`, quaternion case, equivariant form**: the twisted algebra over
`B ⧸ Q·B` decomposes along the CRT factors, carrying the involution and twist. -/
noncomputable def crtTwisted :
    Twisted (quotData σ hσ ξ₀ Q) ≃+* ∀ i, Twisted (quotData σ hσ ξ₀ (J i)) :=
  (Twisted.congr (d := quotData σ hσ ξ₀ Q) (d' := piData fun i => quotData σ hσ ξ₀ (J i))
      (crtRing J Q hcop hglob)
      (by
        intro s
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
        rw [quotData_θ_mk, crtRing_mk, crtRing_mk]
        funext i
        exact (quotData_θ_mk σ hσ ξ₀ (J i) x).symm)
      (by
        rw [quotData_ξ, crtRing_mk]
        funext i
        rfl)).trans
    (piEquiv fun i => quotData σ hσ ξ₀ (J i))

end CRT

end Twisted

end Abba
