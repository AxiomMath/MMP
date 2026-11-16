module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem

/-!
# Compactly supported cohomology

Compactly supported cohomology is the definition `MMP.Fourfold.compactSupportCohomology`:
the `q`-th cohomology of the right derived functor of the functor
`MMP.Fourfold.compactSupportSectionsFunctor` of global sections with compact support.

The definition is stated for sheaves of modules over any commutative ring `R`, rational
coefficients being the case `R = ℚ`. A section has compact support when its germs vanish off a
compact set; for a locally compact Hausdorff `X` this is the same as the support being compact,
because the support is closed. Extension by zero `j_!` along an open `j : U → X` is notation for
the lemmas that use it.
-/

@[expose] public section

attribute [mmp "def_mmp_compact_support_cohomology"] MMP.Fourfold.compactSupportCohomology

end
