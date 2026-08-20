import Mathlib
import AbbaLean.AbbaInstance
import AbbaLean.UnitDensity
import AbbaLean.Cap

set_option linter.style.header false

/-!
# ABBA — `unitdensity` and `cap` transported onto `Λ_Q`

Using `abba_structure`, the unit count of `Λ_Q` is `∏ᵢ (qᵢ² - 1)(qᵢ² - qᵢ)`
(`abba_card_units`, Lemma `unitdensity`'s counting core on the actual global
object), and any central set with pairwise-invertible differences has at most
`|𝓞_K/𝔮ᵢ|` elements (`abba_cap`, Lemma `cap` on the actual global object).

Helper facts: components of central elements of a product are central; central
2×2 matrices are scalar; ring isomorphisms preserve centrality.
-/

namespace Abba

namespace Twisted

open Function Module NumberField

section CenterHelpers

/-- Components of central elements of a product ring are central. -/
theorem pi_center_component {ι : Type*} [DecidableEq ι] {R : ι → Type*}
    [∀ i, Ring (R i)] (x : ∀ i, R i) (hx : x ∈ Set.center (∀ i, R i)) (i : ι) :
    x i ∈ Set.center (R i) := by
  rw [Semigroup.mem_center_iff] at hx ⊢
  intro g
  have h1 := congrFun (hx (Function.update (1 : ∀ i, R i) i g)) i
  simpa using h1

/-- Ring isomorphisms preserve centrality. -/
theorem center_map {R R' : Type*} [Ring R] [Ring R'] (e : R ≃+* R') (z : R)
    (hz : z ∈ Set.center R) : e z ∈ Set.center R' := by
  rw [Semigroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, hz]

/-- Central 2×2 matrices are scalar. -/
theorem matrix_center_scalar {F : Type*} [CommRing F]
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M ∈ Set.center (Matrix (Fin 2) (Fin 2) F)) :
    M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h := Semigroup.mem_center_iff.mp hM
  have h1 := h !![0,1;0,0]
  have h2 := h !![0,0;1,0]
  have e1 : M 1 0 = 0 := by
    have h3 := congrFun (congrFun h1 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h3
  have e2 : M 1 1 = M 0 0 := by
    have h3 := congrFun (congrFun h1 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, e1] using h3
  have e3 : M 0 1 = 0 := by
    have h3 := congrFun (congrFun h2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h3.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply, e1, e2, e3]

end CenterHelpers

section Transport

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]
variable (σL : L ≃ₐ[K] L) (hσL : ∀ x, σL (σL x) = x)
variable (ζ : 𝓞 L) (hσζ : ζ * intConj σL ζ = 1)
variable (m : ℕ) (hhalf : ζ ^ (2 * m) = -1)
variable (hrank : finrank K L = 2)
variable {ι : Type*} [Fintype ι]
variable (J : ι → Ideal (𝓞 K)) [∀ i, (J i).IsMaximal]
variable (hJne : Pairwise (fun i j => J i ≠ J j))
variable (Q : Ideal (𝓞 K)) (hQ : Q = ∏ i, J i)
variable (h2 : ∀ i, (2 : 𝓞 K) ∉ J i)

/-- Residue fields are finite. -/
theorem finite_residue (i : ι) : Finite ((𝓞 K) ⧸ J i) := by
  have hbot : J i ≠ ⊥ := by
    have h4 := Ideal.bot_lt_of_maximal (J i) (RingOfIntegers.not_isField K)
    exact h4.ne'
  exact Ring.HasFiniteQuotients.finiteQuotient hbot

include hσL ζ hσζ m hhalf hrank hJne hQ h2 in
/-- **Lemma `unitdensity` on `Λ_Q`**: the unit count of the global twisted
algebra is `∏ᵢ (qᵢ² - 1)(qᵢ² - qᵢ)` with `qᵢ = |𝓞_K/𝔮ᵢ|`. -/
theorem abba_card_units :
    Nat.card (Twisted (quotData (intConj σL) (intConj_invol σL hσL) (-1) Q))ˣ
      = ∏ i, (Nat.card ((𝓞 K) ⧸ J i) ^ 2 - 1)
          * (Nat.card ((𝓞 K) ⧸ J i) ^ 2 - Nat.card ((𝓞 K) ⧸ J i)) := by
  classical
  obtain ⟨e⟩ := abba_structure σL hσL ζ hσζ m hhalf hrank J hJne Q hQ h2
  rw [Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
    Nat.card_congr (MulEquiv.piUnits).toEquiv, Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  letI : Field ((𝓞 K) ⧸ J i) := Ideal.Quotient.field (J i)
  haveI : Finite ((𝓞 K) ⧸ J i) := finite_residue J i
  letI : Fintype ((𝓞 K) ⧸ J i) := Fintype.ofFinite _
  have hgl := card_GL2 ((𝓞 K) ⧸ J i)
  rw [Nat.card_eq_fintype_card (α := (𝓞 K) ⧸ J i)]
  exact hgl

include hσL ζ hσζ m hhalf hrank hJne hQ h2 in
/-- **Lemma `cap` on `Λ_Q`**: any central set with pairwise-invertible
differences has at most `|𝓞_K/𝔮ᵢ|` elements, for every factor `i₀`. -/
theorem abba_cap
    (C : Set (Twisted (quotData (intConj σL) (intConj_invol σL hσL) (-1) Q)))
    (hC : ∀ x ∈ C, x ∈ Set.center (Twisted (quotData (intConj σL) (intConj_invol σL hσL) (-1) Q)))
    (hdiff : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → IsUnit (x - y)) (i₀ : ι) :
    Nat.card C ≤ Nat.card ((𝓞 K) ⧸ J i₀) := by
  classical
  obtain ⟨e⟩ := abba_structure σL hσL ζ hσζ m hhalf hrank J hJne Q hQ h2
  haveI : Finite ((𝓞 K) ⧸ J i₀) := finite_residue J i₀
  letI : Field ((𝓞 K) ⧸ J i₀) := Ideal.Quotient.field (J i₀)
  -- the scalar of the i₀-component
  have hscalar : ∀ x ∈ C, (e x) i₀ = ((e x) i₀ 0 0) • (1 : Matrix (Fin 2) (Fin 2) ((𝓞 K) ⧸ J i₀)) := by
    intro x hx
    exact matrix_center_scalar _ (pi_center_component (e x) (center_map e x (hC x hx)) i₀)
  -- injectivity of x ↦ (e x) i₀ 0 0 on C
  have hinj : Set.InjOn (fun x => (e x) i₀ 0 0) C := by
    intro x hx y hy hxy
    -- pairwise-unit differences transport through e
    have hdiff' : ∀ u, u ∈ e '' C → ∀ v, v ∈ e '' C → u ≠ v → IsUnit (u - v) := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
      have hne : u ≠ v := fun h => huv (by rw [h])
      have := (hdiff u hu v hv hne).map e
      rwa [map_sub] at this
    have hproj := injOn_proj_of_pairwise_unit_sub (e '' C) hdiff' i₀
    have hxy' : (e x) i₀ 0 0 = (e y) i₀ 0 0 := hxy
    have hcomp : (e x) i₀ = (e y) i₀ := by
      rw [hscalar x hx, hscalar y hy, hxy']
    have hxy2 : e x = e y :=
      hproj (Set.mem_image_of_mem e hx) (Set.mem_image_of_mem e hy) hcomp
    exact e.injective hxy2
  have hfinal : Function.Injective (fun x : C => (e (x : _)) i₀ 0 0) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only at hxy
    exact Subtype.ext (hinj hx hy hxy)
  exact Nat.card_le_card_of_injective _ hfinal

end Transport

end Twisted

end Abba
