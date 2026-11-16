module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.ComplexTransfer
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.LcTermination

/-!
# Termination of programs for projective lc fourfolds

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective lc
fourfold pair over `k` with rational boundary; no `ℚ`-factoriality or pseudo-effectivity is
assumed. Every program from `(X, B)` has finitely many birational steps, whatever the extremal
rays, contractions and permitted steps chosen along the way.

## Main results

* `MMP.Fourfold.Program.n_ne_top_of_isAlgClosed`: a program from a projective lc fourfold pair
  has finitely many birational steps.

## Implementation notes

A program `P : MMP.Fourfold.Program sX K B` carries the projectivity of `X`, the log canonicity
of `(X, B)` and the canonical divisor `K`, together with all of its choices (rays, contractions,
permitted steps). Its number of birational steps is `P.n : ℕ∞`, so "finitely many" is
`P.n ≠ ⊤`, and quantifying over every `P` is quantifying over every sequence of permitted
choices. The boundary is a `ℚ`-divisor, so it is rational, and "fourfold" is
`topologicalKrullDim X = 4`.
-/

@[expose] public section

section

namespace Proof_thm_oai4_main

open CategoryTheory AlgebraicGeometry MMP.Fourfold

private theorem solution {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : MMP.Mori.Divisor X} {B : MMP.Mori.QDivisor X}
    (hdim : topologicalKrullDim X = 4) (P : Program sX K B) : P.n ≠ ⊤ := by
  intro hP
  obtain ⟨X', sX', _, _, _, _, K', B', hdim', P', hP'⟩ :=
    Program.exists_complex_of_n_eq_top hdim P hP
  exact Program.n_ne_top hdim' P' hP'

end Proof_thm_oai4_main

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Termination.** Let `(X, B)` be a projective lc fourfold pair over an algebraically closed
field of characteristic zero, with rational boundary. Every program `P` from `(X, B)` has finitely
many birational steps. -/
@[mmp "thm_oai4_main"]
public theorem Program.n_ne_top_of_isAlgClosed {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) (P : Program sX K B) : P.n ≠ ⊤ :=
      by revert k X sX K B hdim P; first | exact Proof_thm_oai4_main.solution | exact Proof_thm_oai4_main.solution _ | exact Proof_thm_oai4_main.solution _ _ | exact Proof_thm_oai4_main.solution _ _ _ | exact Proof_thm_oai4_main.solution _ _ _ _

end MMP.Fourfold

