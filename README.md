# ABBA-LEAN

Machine-checked proofs (Lean 4 / Mathlib) for the core results of the paper
*ABBA: Lattice-based Commitments from Commutators*.

## Scope

The formalization covers the paper's own algebraic contribution end to end:

- **Lemma `structure`** (`Λ_q ≅ ∏ᵢ M₂(𝔽_{q^{f_i}})`, `Z(Λ_q) = 𝓞_{K_q}`), fully:
  the twisted algebra `𝓡 = S ⊕ uS` built from scratch (`Structure.lean`), a
  uniform per-factor theorem subsuming the split/inert dichotomy
  (`StructureUniform.lean`), Hilbert 90 and norm surjectivity for quadratic
  algebras with no étale case analysis (`Hilbert90.lean`), the equivariant CRT
  (`StructureCRT.lean`), global assembly and center (`StructureGlobal.lean`,
  `StructureFixed.lean`), and the ABBA instantiation with all arithmetic
  hypotheses discharged (`AbbaInstance.lean`, `AbbaTransport.lean`).
- **Lemma `shortinvert`** in all forms, including at the totally real subfield
  (`ShortInvert.lean`, `ShortInvertFull.lean`, `ShortInvertTower.lean`).
- **Cor `Hc`**: invertibility of challenge differences and the count
  `|H_c| = (2c+1)^d` (`HcCount.lean`, `HcCard.lean`).
- **Lemma `cap`**, **Lemma `unitdensity`**, **Lemma `centrality`**, the AM-GM
  norm floor, the deterministic core of the CSIS → I-CSIS reduction, and the
  statistical-distance identity of Rem `syndromegap`
  (`Cap.lean`, `UnitDensity.lean`, `Polish.lean`, `CsisToIcsis.lean`).

Out of scope by design: the PPT wrappers of the probabilistic reductions (no
complexity theory in Mathlib; their distributional cores are verified
exhaustively in a companion Sage battery) and Cor `Hc`'s expansion-factor
clause (defined in Neo's external framework). See `STATUS.md` for the full
result-by-result table.

## Building

```
lake exe cache get
lake build
```

Lean `v4.33.0`, Mathlib pinned to the matching release. The build is green with
zero `sorry`; every commit in the history is a verified checkpoint.

## Caveat

Lean verifies the statements as transcribed into `AbbaLean/*.lean`; the
correspondence with the paper's LaTeX statements is by inspection.
