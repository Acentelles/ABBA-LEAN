import Mathlib
import AbbaLean.StructureInert

set_option linter.style.header false

/-!
# ABBA — Lemma `structure`, inert case at finite fields

Instantiates `AbbaLean.StructureInert` at a quadratic extension `S/k` of finite
fields: `θ` is the relative Frobenius `x ↦ x^{|k|}` and, for any `ξ₀ ≠ 0` in `k`,
norm surjectivity of finite-field extensions produces `c` with `c·θ(c) = ξ₀`
(via `FiniteField.algebraMap_norm_eq_pow`: the norm is `c ↦ c^{(q²-1)/(q-1)} = c^{q+1}`).

Main result: `finite_inert_case`: for finite fields `k ⊆ S` with `[S:k] = 2` and
`ξ₀ ∈ k^×`, the twisted algebra `S ⊕ uS` with `u² = ξ₀`, `su = u·s^{|k|}` is
isomorphic to `M₂(k)`.  This is the inert factor of the paper's Lemma `structure`
in its concrete arithmetic form (`k = 𝔽_{q^f}`, `S = 𝔽_{q^{2f}}`).
-/

namespace Abba

namespace Twisted

open FiniteField Module

section FiniteInert

variable (k S : Type*) [Field k] [Field S] [Algebra k S] [Fintype k] [Fintype S]

local notation "q" => Fintype.card k

theorem card_S (hdim : finrank k S = 2) : Fintype.card S = q ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := k) (V := S), hdim]

/-- The Frobenius fixes at most `q < q² = |S|` elements, so it is not the identity. -/
theorem exists_pow_card_ne (hdim : finrank k S = 2) : ∃ w : S, w ^ q ≠ w := by
  classical
  by_contra hcon
  push_neg at hcon
  have hq : 1 < q := Fintype.one_lt_card
  have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial S) ≠ 0 := by
    intro heq
    have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial S).natDegree = q := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
        simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, hq]
    rw [heq, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset S)
      ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial S).roots.toFinset := by
    intro w _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hcon w]
  have hcard := Finset.card_le_card hsub
  have h1 : (Polynomial.X ^ q - Polynomial.X : Polynomial S).roots.toFinset.card
      ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial S).roots.card :=
    Multiset.toFinset_card_le _
  have h2 : Multiset.card (Polynomial.X ^ q - Polynomial.X : Polynomial S).roots
      ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial S).natDegree :=
    Polynomial.card_roots' _
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial S).natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, hq]
  have : Fintype.card S ≤ q := by
    calc Fintype.card S = (Finset.univ : Finset S).card := (Finset.card_univ).symm
      _ ≤ _ := hcard
      _ ≤ _ := h1
      _ ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial S).natDegree := h2
      _ = q := hdeg
  rw [card_S k S hdim] at this
  nlinarith

/-- The twisting data at finite fields: `θ` = relative Frobenius, `ξ = ξ₀ ∈ k`. -/
noncomputable def frobData (hdim : finrank k S = 2) (ξ₀ : k) : TwistData S where
  θ := (frobeniusAlgEquivOfAlgebraic k S).toRingEquiv
  invol s := by
    show frobeniusAlgEquivOfAlgebraic k S (frobeniusAlgEquivOfAlgebraic k S s) = s
    rw [show ⇑(frobeniusAlgEquivOfAlgebraic k S) = (· ^ q) from
      coe_frobeniusAlgEquivOfAlgebraic k S]
    show (s ^ q) ^ q = s
    rw [← pow_mul, ← sq, ← card_S k S hdim]
    exact FiniteField.pow_card s
  ξ := algebraMap k S ξ₀
  fixed := (frobeniusAlgEquivOfAlgebraic k S).commutes ξ₀

@[simp] theorem frobData_θ_apply (hdim : finrank k S = 2) (ξ₀ : k) (s : S) :
    (frobData k S hdim ξ₀).θ s = s ^ q := rfl

/-- Norm surjectivity in the form needed: some `c` satisfies `c·θ(c) = ξ₀`. -/
theorem exists_norm_eq (hdim : finrank k S = 2) (ξ₀ : k) :
    ∃ c : S, c * (frobData k S hdim ξ₀).θ c = (frobData k S hdim ξ₀).ξ := by
  obtain ⟨c, hc⟩ := FiniteField.norm_surjective k S ξ₀
  refine ⟨c, ?_⟩
  have hq : 1 < q := Fintype.one_lt_card
  have hpow : algebraMap k S ξ₀ = c ^ ((Nat.card S - 1) / (Nat.card k - 1)) := by
    rw [← hc]
    exact FiniteField.algebraMap_norm_eq_pow
  have hexp : (Nat.card S - 1) / (Nat.card k - 1) = q + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_S k S hdim]
    have hq1 : 1 < q := Fintype.one_lt_card
    obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have hm1 : 0 < m := by omega
    rw [hm]
    simp only [Nat.add_sub_cancel]
    apply Nat.div_eq_of_eq_mul_left hm1
    apply Nat.sub_eq_of_eq_add
    ring
  show c * c ^ q = algebraMap k S ξ₀
  rw [hpow, hexp]
  ring

/-- **Inert case of Lemma `structure`, finite-field form**: for finite fields
`k ⊆ S` with `[S:k] = 2` and `ξ₀ ≠ 0`, the twisted algebra `S ⊕ uS` with
`u² = ξ₀` and `su = u·s^{|k|}` is isomorphic to `M₂(k)`. -/
theorem finite_inert_case (hdim : finrank k S = 2) (ξ₀ : k) (hξ₀ : ξ₀ ≠ 0) :
    Nonempty (Twisted (frobData k S hdim ξ₀) ≃+* Matrix (Fin 2) (Fin 2) k) := by
  obtain ⟨c, hc⟩ := exists_norm_eq k S hdim ξ₀
  have hξ : (frobData k S hdim ξ₀).ξ ≠ 0 := by
    show algebraMap k S ξ₀ ≠ 0
    simpa using hξ₀
  have hθne : ∃ w : S, (frobData k S hdim ξ₀).θ w ≠ w := by
    obtain ⟨w, hw⟩ := exists_pow_card_ne k S hdim
    exact ⟨w, by simpa using hw⟩
  have hθk : ∀ r : k, (frobData k S hdim ξ₀).θ (algebraMap k S r) = algebraMap k S r :=
    fun r => (frobeniusAlgEquivOfAlgebraic k S).commutes r
  exact ⟨inertEquiv (frobData k S hdim ξ₀) hθk c hc hξ hθne hdim⟩

end FiniteInert

end Twisted

end Abba
