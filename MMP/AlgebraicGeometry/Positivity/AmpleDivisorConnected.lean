module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Connected
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ComponentsVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.GenericProjection

/-!
# The support of an effective ample divisor is connected

Let `X` be a normal projective variety of dimension at least two over an algebraically closed
field `k` of characteristic zero, and let `A` be an effective ample Cartier divisor on `X`.
Then the support `Supp A` is connected.

The proof applies [Stacks, Tag 0FD9] to the canonical section `1` of `𝒪_X(A)`: normality gives
Serre's condition `(S₂)`, so with `dim X ≥ 2` every closed point has depth at least two, and the
zero scheme of this regular section of an ample invertible sheaf is connected; its support is
`Supp A`.

## Main results

* `MMP.Fourfold.isConnected_supp_of_isAmple`: `Supp A` is connected.

## Implementation notes

* The source works over `ℂ`; the statement keeps an algebraically closed field of
  characteristic zero, although the proof uses neither hypothesis.
* The dimension hypothesis `n ≥ 2` is `2 ≤ topologicalKrullDim X`.
* Connectedness is `IsConnected`, which includes nonemptiness: an ample divisor on a projective
  variety of positive dimension is nonzero.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15.
-/

@[expose] public section

/-!
## Proof: The support of an effective ample divisor on a normal projective variety is connected

Let `X` be a normal projective variety of dimension at least two over a field `k` and `A` an
effective ample Cartier divisor on `X`. The canonical section `1` of `𝒪_X(A)` is a nonzero, hence
regular, section of an ample invertible sheaf whose zero scheme has support `Supp A`. A normal
scheme satisfies Serre's condition `(S₂)`, and every closed point of the irreducible variety `X`
has a local ring of dimension `dim X ≥ 2`, so these local rings have depth at least two. The
zero scheme of a regular section of an ample invertible sheaf on a connected proper scheme whose
closed points have depth at least two is connected [Stacks, Tag 0FD9], and so is its support.

## Implementation notes

The source proves the vanishing `H¹(W, 𝒪_W(-p^*A)) = 0` on a resolution `p : W → X` and deduces
connectedness of `Supp p^*A`, hence of its image `Supp A`. The argument here replaces the
resolution and Kawamata–Viehweg vanishing by Serre's condition `(S₂)` on `X` itself and Enriques–
Severi–Zariski vanishing, which is what [Stacks, Tag 0FD9] rests on; it uses neither that `k` is
algebraically closed nor that it has characteristic zero.

## References

* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15.
-/

namespace MMP.FourfoldProofs.FourfoldFa15NormalAmpleDivisorConnectedProof

open CategoryTheory AlgebraicGeometry MMP.Mori Opposite

universe u

/-- On a normal scheme, irreducible and locally of finite type over a field, of dimension at
least two, the local ring at every closed point has depth at least two: it satisfies `(S₂)` and
has dimension `dim X`. -/
private theorem two_le_depth_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IrreducibleSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (hdim : 2 ≤ topologicalKrullDim X)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := by
  have h := (hasPropertySk_iff X 2).mp (hasPropertySk_two_of_isNormal X) x
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX x hx,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k X sX
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) x, Nat.cast_ofNat,
    min_eq_left hdim] at h
  exact WithBot.coe_le_coe.1 h

/-- The canonical section `1` of `𝒪_X(A)` for an effective Cartier divisor `A` on a normal
integral scheme is nonzero, and its zero scheme has support `Supp A`. -/
private theorem supportSet_zeroScheme_oneSection {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {A : Divisor X} (hA : 0 ≤ A) (hAc : A.IsCartier)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A.divisorialSheaf]
    [Stacks.Ample.IsInvertibleModule X A.divisorialSheaf] :
    MMP.Threefold.Mori.oneSection hA ≠ 0 ∧
      (zeroScheme X A.divisorialSheaf (MMP.Threefold.Mori.oneSection hA)).supportSet =
        A.supp := by
  have hnv := MMP.Threefold.Mori.nonvanishingLocus_oneSection hA hAc
  have hs0 : MMP.Threefold.Mori.oneSection hA ≠ 0 := fun h => by
    rw [h, Stacks.Ample.nonvanishingLocus_zero] at hnv
    exact hnv.symm.subset (MMP.Fourfold.genericPoint_notMem_supp A)
  refine ⟨hs0, ?_⟩
  set s := Stacks.Divisors.sectionsOfTop A.divisorialSheaf (MMP.Threefold.Mori.oneSection hA)
  have hs : s.eval (op ⊤) = MMP.Threefold.Mori.oneSection hA :=
    Stacks.Divisors.sectionsOfTop_eval_top _ _
  have hc := nonvanishingLocus_eq_compl_supportSet_zeroScheme A.divisorialSheaf s (hs ▸ hs0)
  rw [show Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) A.divisorialSheaf s =
      Stacks.Ample.nonvanishingLocus A.divisorialSheaf (s.eval (op ⊤)) from
    Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval X _ s, hs, hnv, compl_inj_iff] at hc
  exact hc.symm

private theorem solution {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hdim : 2 ≤ topologicalKrullDim X) (A : Divisor X) (hA : 0 ≤ A)
    (hAc : A.IsCartier) (hAa : A.IsAmple hAc) : _root_.IsConnected (A.supp : Set X) := by
  haveI : IsIntegral X := inferInstance
  haveI : IsProper sX := inferInstance
  haveI := hAc.isInvertibleModule_divisorialSheaf
  haveI := InvertibleSheafGeneral.isInvertible_of_isInvertibleModule A.divisorialSheaf
  obtain ⟨hs0, hsupp⟩ := supportSet_zeroScheme_oneSection hA hAc
  let s := Stacks.Divisors.sectionsOfTop A.divisorialSheaf (MMP.Threefold.Mori.oneSection hA)
  have hs : s.eval (op ⊤) = MMP.Threefold.Mori.oneSection hA :=
    Stacks.Divisors.sectionsOfTop_eval_top _ _
  have := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple k sX
    A.divisorialSheaf ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).2 hAa) s
    (isRegularSection_of_eval_top_ne_zero A.divisorialSheaf s (hs ▸ hs0))
    (two_le_depth_stalk sX hdim)
  rw [← hsupp, ← hs]
  change _root_.IsConnected ((zeroScheme X A.divisorialSheaf (s.eval (op ⊤))).support : Set X)
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact isConnected_range (Scheme.IdealSheafData.subschemeι _).continuous

end MMP.FourfoldProofs.FourfoldFa15NormalAmpleDivisorConnectedProof

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

universe u

namespace MMP.Fourfold

/-- Let `X` be a normal projective variety of dimension at least two over an algebraically
closed field `k` of characteristic zero, and let `A` be an effective ample Cartier divisor on `X`.
Then the support `Supp A` is connected. -/
@[mmp "lem_fourfold_fa15_normal_ample_divisor_connected"]
public theorem isConnected_supp_of_isAmple {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hdim : 2 ≤ topologicalKrullDim X)
    (A : Divisor X) (hA : 0 ≤ A) (hAc : A.IsCartier) (hAa : A.IsAmple hAc) :
    _root_.IsConnected (A.supp : Set X) :=
  MMP.FourfoldProofs.FourfoldFa15NormalAmpleDivisorConnectedProof.solution sX hdim A hA hAc hAa

end MMP.Fourfold

end

end
