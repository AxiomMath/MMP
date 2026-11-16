[![](logo.svg)](https://axiommath.ai/)

# The Minimal Model Program in Lean

A Lean 4 (v4.35.0) formalization of the minimal model program for log canonical pairs in dimension at most four, built on [Mathlib](https://github.com/leanprover-community/mathlib4) and on [the Stacks Project in Lean](https://github.com/AxiomMath/Stacks). The four-dimensional theorem follows OpenAI, *Termination for projective log canonical fourfolds with rational boundary* (2026); the classical background follows J. Kollár and S. Mori, *Birational Geometry of Algebraic Varieties* (Cambridge University Press, 1998), and *Flips and Abundance for Algebraic Threefolds* (J. Kollár et al., Astérisque 211, 1992). Lean's kernel checks every proof. There is no `sorry`, no `native_decide` and no added axiom.

## The minimal model program for fourfolds

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective log canonical pair of dimension four over `k` with rational boundary `B`. A program from `(X, B)` runs the minimal model program: at each stage it contracts a `(K + B)`-negative extremal ray, and continues with the flip or divisorial contraction, or stops at a Mori fibre space. If the program is maximal, it has finitely many birational steps and ends either with a model `(Xₙ, Bₙ)` on which `K_{Xₙ} + Bₙ` is nef, or with a Mori fibre space:

```lean
theorem MMP.Fourfold.Program.IsMaximal.isNefOnCurves_or_isMoriFibreSpace {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) {P : Program sX K B} (hP : P.IsMaximal) :
    P.n ≠ ⊤ ∧
      ((MMP.Mori.IsProjectiveVariety k (modelStr sX P.sY P.n.toNat) ∧
          MMP.Intersection.IsLogCanonicalPair (modelStr sX P.sY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) ∧
          (∃ m : ℕ, Divisor.IsCanonicalDivisor (modelStr sX P.sY P.n.toNat) m
            (divisorSeq K P.KY P.n.toNat)) ∧
          QDivisor.IsNefOnCurves (modelStr sX P.sY P.n.toNat)
            (Divisor.toQDivisor (divisorSeq K P.KY P.n.toNat) + divisorSeq B P.BY P.n.toNat)) ∨
        (P.hasFinal ∧
          IsMoriFibreSpace (modelStr sX P.sY P.n.toNat) P.sT (divisorSeq K P.KY P.n.toNat)
            (divisorSeq B P.BY P.n.toNat) P.g))
```

([MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/ProgramEndpoints.lean](MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/ProgramEndpoints.lean).) It combines two theorems:

- **Continuation** (`MMP.Fourfold.Program.isContinuableRay`, [MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/RayContinuable.lean](MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/RayContinuable.lean)): at every stage of a program, every `(K + B)`-negative extremal ray of the cone of curves has a contraction, and, when that contraction is birational, a permitted next step (a divisorial contraction or a flip).
- **Termination** (`MMP.Fourfold.Program.n_ne_top_of_isAlgClosed`, [MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/Termination.lean](MMP/AlgebraicGeometry/MMP/Fourfold/AlgClosed/Termination.lean)): every program has finitely many birational steps.

Neither `ℚ`-factoriality nor pseudo-effectivity of `K + B` is assumed.

## Dimension at most three

The proof runs through the relative minimal model program for `ℚ`-factorial dlt pairs of dimension at most three over `ℂ`, a theorem in its own right:

```lean
theorem MMP.Fourfold.projectiveLowerLogMMP_three : ProjectiveLowerLogMMP 3
```

([MMP/AlgebraicGeometry/MMP/Threefold/LogMMP.lean](MMP/AlgebraicGeometry/MMP/Threefold/LogMMP.lean).) `ProjectiveLowerLogMMP n` ([MMP/AlgebraicGeometry/MMP/Fourfold/DltProgram.lean](MMP/AlgebraicGeometry/MMP/Fourfold/DltProgram.lean)) says: for every projective morphism `π : X → S` of complex projective varieties with `dim X ≤ n` and every projective `ℚ`-factorial dlt pair `(X, B)` with rational boundary, every `(K_X + B)`-negative extremal ray over `S` has a contraction and, when the contraction is small, a flip; every projective dlt program over `S` terminates; and some program ends with `K + B` nef over `S` or with a Mori fibre space.

## Structure

`import MMP` brings in the whole library, [MMP](MMP/), about 2,270 modules written by AI agents. Every proof is kernel-checked; the code has not yet been reviewed by humans.

A declaration that formalizes an item of the minimal model program or of the background it uses carries the attribute `@[mmp "label"]` (defined in [MMP/Attr.lean](MMP/Attr.lean)), where the label names the item, for example `thm_main` for the theorem above.

The library uses the Stacks Project in Lean for schemes, sheaf cohomology, Chow groups and divisors, and builds on it, among others: the cone and contraction theorems, Kawamata–Viehweg vanishing and the basepoint-free theorem, resolution of singularities in characteristic zero, singularities of pairs (klt, plt, dlt, lc), the construction of flips, termination, and, for the comparison with complex geometry, Borel–Moore homology, the cycle class map and GAGA for projective schemes.

## Axioms

Proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. After `import MMP`, `#print axioms` on any declaration lists exactly what it rests on, for example

```lean
#print axioms MMP.Fourfold.Program.IsMaximal.isNefOnCurves_or_isMoriFibreSpace
-- 'MMP.Fourfold.Program.IsMaximal.isNefOnCurves_or_isMoriFibreSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Building

```
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's compiled files. The Stacks Project modules this library uses are compiled locally, so the first build takes a long time and a lot of memory.

## License

[Apache 2.0](LICENSE).
