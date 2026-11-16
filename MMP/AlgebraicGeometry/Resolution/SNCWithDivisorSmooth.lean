/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityOneSmoothness

/-!
# Closed subschemes having simple normal crossings with a divisor are smooth

Let `k` be a field of characteristic zero and `X` a smooth scheme of finite type over `k`. If a
closed subscheme `Z ⊆ X` has simple normal crossings with a simple normal crossing divisor `E`,
then `Z` is smooth over `k`.

At a point `x ∈ Z` there are local coordinates `z_1, …, z_n` at `x` with
`𝒪_{Z,x} = 𝒪_{X,x} / (z_j : j ∈ J)`. Since `𝒪_{X,x}` is regular and the `z_j` are part of a
regular system of parameters, the quotient is a regular local ring. As `k` is perfect, a scheme
locally of finite type over `k` all of whose local rings are regular is smooth over `k`.

## Main results

* `MMP.Resolution.isSmoothScheme_subscheme_of_hasSNCWith`: a closed subscheme having simple
  normal crossings with an snc divisor is smooth over `k`.

## Implementation notes

The statement is proved over any perfect field, characteristic zero being the case of the source.
The argument uses only the regular system of parameters at each point of `Z` and the description
of the stalk of the ideal of `Z`; neither the clauses of `MMP.Resolution.HasSNCWith` concerning
the components of `E`, nor the hypothesis that `E` is an snc divisor, are needed. The latter is
kept as a hypothesis so that the statement is the source's.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.24–3.25]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace MMP.Resolution

/-- **A closed subscheme having simple normal crossings with an snc divisor is smooth.** Let `k`
be a perfect field (for instance of characteristic zero) and `X` a scheme smooth and locally of
finite type over `k`. If a closed subscheme `Z ⊆ X` has simple normal crossings with a simple
normal crossing divisor `E`, then `Z` is smooth over `k`. The hypothesis that `E` is an snc
divisor is not used by the proof. -/
@[mmp "lem_kr3b_snc_with_divisor_smooth"]
theorem isSmoothScheme_subscheme_of_hasSNCWith {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : MMP.Mori.IsSmoothScheme sX)
    {Λ : Type*} {E : Λ → X.IdealSheafData} (_hE : IsSNCFamily sX E) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E Z) : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have : LocallyOfFiniteType (Z.subschemeι ≫ sX) := inferInstance
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have : LocallyOfFinitePresentation (Z.subschemeι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Z.subschemeι ≫ sX)).mpr
      inferInstance
  rw [MMP.Mori.isSmoothScheme_iff] at hX ⊢
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).1 hX
  rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro y
  have hy : Z.subschemeι y ∈ (Z.support : Set X) := by
    rw [← Z.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨n, z, -, J, hz, -, -, hstalk⟩ := hZ _ hy
  apply isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient
  rw [hstalk]
  have := hreg (Z.subschemeι y)
  obtain ⟨h, -, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  exact h

end MMP.Resolution
