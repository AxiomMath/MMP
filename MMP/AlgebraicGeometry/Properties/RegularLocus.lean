module

public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses

/-!
# The regular locus along open immersions and fibre products over a field

For a scheme `X` locally of finite type over a field `K`, the regular locus of `X` is open
(`X` is J-2, Stacks 07R5), and the open subscheme it supports is regular. Over a perfect field
the fibre product of two regular schemes locally of finite type is regular (Stacks 038F), so a
point of `V ×_K W` lying over regular points of `V` and `W` is a regular point of `V ×_K W`.

## Main definitions

* `MMP.regularLocusOpens`: the regular locus of a scheme locally of finite type over a field,
  as an open subset.

## Main results

* `MMP.mem_regularLocus_iff_of_isOpenImmersion`: an open immersion preserves and reflects
  regular points.
* `MMP.isRegular_regularLocusOpens`: the open subscheme on the regular locus is regular.
* `MMP.mem_regularLocus_pullback`: over a perfect field, a point of `V ×_K W` lying over points
  of the regular loci of `V` and `W` is in the regular locus of `V ×_K W`.

## References

* [Stacks Project, Tag 07R5](https://stacks.math.columbia.edu/tag/07R5),
  [Tag 038F](https://stacks.math.columbia.edu/tag/038F).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace MMP

/-- For an open immersion `i : X ⟶ Y`, the point `i x` is in the regular locus of `Y` iff `x` is
in the regular locus of `X`. -/
theorem mem_regularLocus_iff_of_isOpenImmersion {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsOpenImmersion i] (x : X) : i x ∈ regularLocus Y ↔ x ∈ regularLocus X := by
  let e := (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨fun h ↦ @IsRegularLocalRing.of_ringEquiv _ _ h _ _ e,
    fun h ↦ @IsRegularLocalRing.of_ringEquiv _ _ h _ _ e.symm⟩

/-- The regular locus of a scheme locally of finite type over a field, as an open subset. -/
def regularLocusOpens (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : X.Opens :=
  ⟨regularLocus X, by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    exact (Scheme.isJ2_of_locallyOfFiniteType_over_field K f).isOpen_regularLocus (𝟙 X)⟩

/-- The open subscheme of a scheme locally of finite type over a field supported on its regular
locus is regular. -/
theorem isRegular_regularLocusOpens (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : IsRegular (regularLocusOpens K f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := (isRegular_tfae (regularLocusOpens K f).toScheme).out 1 2
  exact this.mpr ⟨inferInstance, fun x ↦
    (mem_regularLocus_iff_of_isOpenImmersion (regularLocusOpens K f).ι x).mp x.2⟩

/-- Over a perfect field `K`, a point of `V ×_K W` lying over points of the regular loci of `V`
and `W` is in the regular locus of `V ×_K W`. -/
theorem mem_regularLocus_pullback (K : Type u) [Field K] [PerfectField K] {V W : Scheme.{u}}
    (f : V ⟶ Spec (.of K)) (g : W ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (z : (pullback f g : Scheme.{u}))
    (hV : pullback.fst f g z ∈ regularLocus V)
    (hW : pullback.snd f g z ∈ regularLocus W) : z ∈ regularLocus (pullback f g) := by
  set U := regularLocusOpens K f
  set U' := regularLocusOpens K g
  let j := pullback.map (U.ι ≫ f) (U'.ι ≫ g) f g U.ι U'.ι (𝟙 _) (by simp) (by simp)
  obtain ⟨z', rfl⟩ : z ∈ Set.range j := by
    rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact ⟨hV, hW⟩
  have := (isRegular_tfae (pullback (U.ι ≫ f) (U'.ι ≫ g))).out 1 2
  exact (mem_regularLocus_iff_of_isOpenImmersion j z').mpr
    ((this.mp (isRegular_pullback_of_isRegular (U.ι ≫ f) (U'.ι ≫ g)
      (isRegular_regularLocusOpens K f) (isRegular_regularLocusOpens K g))).2 z')

end MMP
