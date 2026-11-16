module

public import MMP.AlgebraicGeometry.Morphisms.FiniteCodimOnePoints
public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Construction

/-!
# Components of the reduced inverse image through a point of a cover

A prime divisor containing the generic point of another is that divisor
(`MMP.FourfoldProofs.FractionalLogComplexProof.eq_of_genericPoint_mem_support`). For a finite
dominant `g : Y ⟶ X` and the reduced inverse image `S'` of a divisor `S`,
a point `y` over the generic point of a prime divisor `E` of `X` is the generic point of a prime
divisor `E'` of `Y`; it lies on a component of `S'` exactly when `E` is a component of `S`, and
that component is then `E'`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_primeDivisor_genericPoint_eq_of_map_eq`: under a
  finite dominant morphism, a point over the generic point of a prime divisor is the generic point
  of a prime divisor.
* `MMP.FourfoldProofs.FractionalLogComplexProof.mem_support_of_map_genericPoint_eq`: a prime divisor
  over a component of `S` is a component of `S'`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.notMem_support_of_map_genericPoint_eq`: a generic point
  over a prime divisor that is not a component of `S` lies on no component of `S'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Order

namespace MMP.FourfoldProofs.FractionalLogComplexProof

open _root_.Topology

universe u

/-- For a finite dominant `f : Y ⟶ X`, a point of `Y` mapping to the generic point of a prime
divisor of `X` is the generic point of a prime divisor of `Y`. -/
theorem exists_primeDivisor_genericPoint_eq_of_map_eq {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsNormal X] (f : Y ⟶ X)
    [IsFinite f] [IsDominant f] (E : MMP.Mori.PrimeDivisor X) {y : Y}
    (hy : f y = E.genericPoint) :
    ∃ E' : MMP.Mori.PrimeDivisor Y, E'.genericPoint = y :=
  ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y (coheight_eq_one_of_map_eq_genericPoint f E hy),
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _⟩

open scoped Classical in
/-- If `S'` has coefficient `1` exactly at the prime divisors over a component of `S`, then a prime
divisor whose generic point maps to that of a component of `S` is a component of `S'`. -/
theorem mem_support_of_map_genericPoint_eq {X Y : Scheme.{u}} (g : Y ⟶ X)
    {S : MMP.Mori.Divisor X} {S' : MMP.Mori.Divisor Y}
    (hS' : ∀ E' : MMP.Mori.PrimeDivisor Y, S' E' =
      if ∃ E ∈ S.support, g E'.genericPoint = E.genericPoint then 1 else 0)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S.support)
    {E' : MMP.Mori.PrimeDivisor Y} (hE' : g E'.genericPoint = E.genericPoint) :
    E' ∈ S'.support := by
  rw [Finsupp.mem_support_iff, hS']
  split_ifs with h
  · exact one_ne_zero
  · exact absurd ⟨E, hE, hE'⟩ h

open scoped Classical in
/-- If `S'` has coefficient `1` exactly at the prime divisors over a component of `S`, and the
generic point of `E'` maps to that of a prime divisor `E` that is not a component of `S`, then the
generic point of `E'` lies on no component of `S'`. -/
theorem notMem_support_of_map_genericPoint_eq {X Y : Scheme.{u}} (g : Y ⟶ X) {S : MMP.Mori.Divisor X} {S' : MMP.Mori.Divisor Y}
    (hS' : ∀ E' : MMP.Mori.PrimeDivisor Y, S' E' =
      if ∃ E ∈ S.support, g E'.genericPoint = E.genericPoint then 1 else 0)
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∉ S.support) {E' : MMP.Mori.PrimeDivisor Y}
    (hE' : g E'.genericPoint = E.genericPoint) {F : MMP.Mori.PrimeDivisor Y}
    (hF : F ∈ S'.support) : E'.genericPoint ∉ F.support := by
  intro h
  obtain rfl := (eq_of_genericPoint_mem_support h).symm
  rw [Finsupp.mem_support_iff, hS'] at hF
  split_ifs at hF with hex
  · obtain ⟨E₀, hE₀, h₀⟩ := hex
    exact hE (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h₀.symm.trans hE') ▸ hE₀)
  · exact hF rfl

end MMP.FourfoldProofs.FractionalLogComplexProof
