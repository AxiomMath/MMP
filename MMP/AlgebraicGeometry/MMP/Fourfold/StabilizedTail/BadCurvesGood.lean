module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.CurveMldFinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
import MMP.AlgebraicGeometry.Singularities.Surface.MldDenominatorBound
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolutionExists
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.BridgeLabels
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight

/-!
# Bad curves and varying labels along a stabilized tail

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized tail, with step diagrams
`X_i⁻ = X_i → Z_i ← X_i⁺ = X_{i+1}` and bad loci `W_i⁻ ⊆ X_i`, `W_i⁺ ⊆ X_{i+1}`.

**Bad curves are eventually good.** From some index `i₁` on, every irreducible curve `V` in
`W_i⁻` (resp. `W_i⁺`) has generic minimal log discrepancy `mld_{η_V}(X_i^σ, B_i^σ) > 1` on the
corresponding model, and that model is smooth over `ℂ` at the generic point `η_V`. Only finitely
many indices carry a bad curve with `mld_{η_V} ≤ 1`
(`MMP.Fourfold.StabilizedTail.finite_setOf_exists_minimalLogDiscrepancy_le_one`); past all of
them every bad curve has `mld_{η_V} > 1`. The point `η_V` has codimension two on a threefold, and
at a singular point of codimension two of an effective pair over an algebraically closed field of
characteristic zero the minimal log discrepancy is at most one [KM98, 4.1]; hence `X_i^σ` is
smooth at `η_V`.

That codimension-two bound is proved in two steps. Over a singular closed point `p` of a normal
quasi-projective surface pair `(S, Δ)` in characteristic zero, the negativity of the intersection
form on the exceptional curves of the minimal resolution, together with the relative nefness of
its canonical divisor, gives an exceptional curve of log discrepancy at most one over `p`. A
singular codimension-two point `x` of `(X, B)` has the local ring of such a singular point on the
generic surface through `x`, and that curve spreads out to a divisor over `X` with centre
`closure {x}` and the same log discrepancy.

**Varying labels have point centres downstairs.** Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`,
be a terminal chain over the tail, with common low-discrepancy set `I_∞` and exceptional divisors
`E_{i,s} = c_{Y_i}(s)`. From some `i₁` on, every varying label `S_h` is one of the divisors
`E_{0,s}`, `s ∈ I_∞`; its centre `S_h^{Y_i}` on the `i`-th junction is `E_{i,s}`; and
`p_i(E_{i,s}) = c_{X_i}(s)` is a closed point of `X_i`. A label coming from a component of `B_0`
is fixed, so `S_h = E_{0,s}`. The centre `c_{X_i}(s)` has codimension at least two, since `s` is
exceptional over `X_i`; it is not a curve, for then (bad curves being good) `S_h` would be fixed.
So it is a closed point, and it is the image of `E_{i,s}` because `p_i` is a closed map.

## Main results

* `MMP.Fourfold.StabilizedTail.exists_forall_ge_one_lt_minimalLogDiscrepancy_and_mem_smoothLocus`:
  bad curves are eventually good, for both sides at once.
* `MMP.Fourfold.StabilizedTail.TerminalChain.exists_isCentre_closedPoint_of_isVaryingLabel`:
  from some stage on, every varying label is an extracted divisor whose centre downstairs is a
  closed point.

## Implementation notes

An irreducible curve of `X` is an irreducible closed subset `V` of `X` of dimension one, and
`η_V` is its generic point; the generic mld is `MMP.Fourfold.minimalLogDiscrepancy` at `η_V`,
valued in `EReal`. Smoothness at `η_V` is membership in `MMP.Mori.smoothLocus` of the structure
morphism to `Spec ℂ`. On the positive side the model is `X_i⁺ = X_{i+1}` with boundary
`B_{i+1}`.

The valuation `s ∈ I_∞ = I(X_0, B_0)` is an element of the finite set `I_0` extracted by the
first junction; on `X_i` it is the valuation `s'` of `k(X_i)` corresponding to it under the
identifications `k(X_j) ≅ k(Z_j) ≅ k(X_{j+1})`, `j < i`
(`MMP.Fourfold.StabilizedTail.IsTransportedValuationFrom`), which is an element of the set `I_i`
extracted by the `i`-th junction, so that `E_{i,s}` is the divisor `E_{s'}` of that junction. The
centre `S_h^{Y_i}` is `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`, and the centre
`c_{X_i}(s)` is `MMP.Intersection.IsCentre`.

## References

* [KM98] Kollár, Mori, *Birational geometry of algebraic varieties*, 2.25, 4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedTail

/-! ### Bad curves are eventually good -/

/-- The generic point of an irreducible curve on a model of a stabilized tail has
codimension two. -/
private theorem coheight_genericPoint_eq_two (T : StabilizedTail) {j : ℕ}
    (V : IrreducibleCloseds (T.X j)) (hV : topologicalKrullDim (V : Set (T.X j)) = 1) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  have : LocallyOfFiniteType (T.sX j) := (T.isKltPair j).1.isPair.1.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (T.sX j)
    V.isIrreducible.genericPoint
  rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, T.dim_eq j] at h
  exact ENat.add_right_injective_of_ne_top ENat.one_ne_top
    (WithBot.coe_injective (by push_cast; rw [h]; rfl) : (1 : ℕ∞) + _ = 1 + 2)

/-- On a model of a stabilized tail, an irreducible curve whose generic mld exceeds one has a
smooth generic point. -/
private theorem mem_smoothLocus_of_one_lt_minimalLogDiscrepancy (T : StabilizedTail) {j : ℕ}
    (V : IrreducibleCloseds (T.X j)) (hV : topologicalKrullDim (V : Set (T.X j)) = 1)
    (hlt : 1 < minimalLogDiscrepancy (T.sX j) (T.B j) V.isIrreducible.genericPoint) :
    V.isIrreducible.genericPoint ∈ smoothLocus (T.sX j) := by
  by_contra hsing
  exact (MMP.Threefold.minimalLogDiscrepancy_le_one_of_coheight_eq_two (T.sX j)
    (T.isKltPair j).1 (coheight_genericPoint_eq_two T V hV) hsing).not_gt hlt

/-- **Bad curves are eventually good.** For a stabilized tail `T` there is `i₁` such that for
every `i ≥ i₁`: every irreducible curve `V ⊆ W_i⁻ ⊆ X_i` has `mld_{η_V}(X_i, B_i) > 1` and `X_i`
is smooth at `η_V`; and every irreducible curve `V ⊆ W_i⁺ ⊆ X_{i+1}` has
`mld_{η_V}(X_{i+1}, B_{i+1}) > 1` and `X_{i+1}` is smooth at `η_V`. -/
@[mmp "prop_mmp_indexc_bad_curves_good"]
public theorem exists_forall_ge_one_lt_minimalLogDiscrepancy_and_mem_smoothLocus
    (T : StabilizedTail) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁,
      (∀ V : IrreducibleCloseds (T.X i),
        topologicalKrullDim (V : Set (T.X i)) = 1 →
        (V : Set (T.X i)) ⊆ (T.badLocusMinusAt i : Set (T.X i)) →
        1 < minimalLogDiscrepancy (T.sX i) (T.B i) V.isIrreducible.genericPoint ∧
          V.isIrreducible.genericPoint ∈ smoothLocus (T.sX i)) ∧
      (∀ V : IrreducibleCloseds (T.X (i + 1)),
        topologicalKrullDim (V : Set (T.X (i + 1))) = 1 →
        (V : Set (T.X (i + 1))) ⊆ (T.badLocusPlusAt i : Set (T.X (i + 1))) →
        1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint ∧
          V.isIrreducible.genericPoint ∈ smoothLocus (T.sX (i + 1))) := by
  obtain ⟨hm, hp⟩ := T.finite_setOf_exists_minimalLogDiscrepancy_le_one
  obtain ⟨i₁, hi₁⟩ := (hm.union hp).bddAbove
  refine ⟨i₁ + 1, fun i hi => ⟨fun V hV hW => ?_, fun V hV hW => ?_⟩⟩
  · have hlt : 1 < minimalLogDiscrepancy (T.sX i) (T.B i) V.isIrreducible.genericPoint :=
      lt_of_not_ge fun h => by
        have := hi₁ (Or.inl ⟨V, hV, hW, h⟩); omega
    exact ⟨hlt, mem_smoothLocus_of_one_lt_minimalLogDiscrepancy T V hV hlt⟩
  · have hlt : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1))
        V.isIrreducible.genericPoint :=
      lt_of_not_ge fun h => by
        have := hi₁ (Or.inr ⟨V, hV, hW, h⟩); omega
    exact ⟨hlt, mem_smoothLocus_of_one_lt_minimalLogDiscrepancy T V hV hlt⟩

namespace TerminalChain

/-! ### Varying labels have point centres downstairs -/

section Threefold

variable {X : Scheme.{0}} [IsIntegral X]

/-- On a threefold every point has coheight at most `3`. -/
private theorem coheight_le_three {Y : Scheme.{0}} (hdim : topologicalKrullDim Y = 3) (y : Y) :
    Order.coheight y ≤ 3 := by
  have h := Order.coheight_le_krullDim y
  rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (Y : Type))),
    ← topologicalKrullDim, hdim] at h
  exact WithBot.coe_le_coe.mp h

/-- On a threefold, the closure of a point of coheight `2` is a curve. -/
private theorem topologicalKrullDim_closure_eq_one_of_coheight_eq_two (s : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType s] (hdim : topologicalKrullDim X = 3) {x : X} (hx : Order.coheight x = 2) :
    topologicalKrullDim (closure {x} : Set X) = 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s x
  rw [hdim, hx] at h
  generalize topologicalKrullDim (closure {x} : Set X) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have : ((d + 2 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) := WithBot.coe_injective (by push_cast; exact h)
      obtain rfl : d = 1 := by have := Nat.cast_injective this; omega
      rfl

/-- On a threefold, a point of codimension at least `2` whose closure is not a curve is a closed
point. -/
private theorem closure_singleton_eq_of_two_le_coheight (s : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType s] (hdim : topologicalKrullDim X = 3) {x : X}
    (hx : 2 ≤ Order.coheight x) (hcurve : topologicalKrullDim (closure {x} : Set X) ≠ 1) :
    closure {x} = ({x} : Set X) := by
  have h3 : 2 + 1 ≤ Order.coheight x := Order.add_one_le_of_lt <| hx.lt_of_ne
    fun h => hcurve (topologicalKrullDim_closure_eq_one_of_coheight_eq_two s hdim h.symm)
  refine subset_antisymm (fun y hy => ?_) subset_closure
  by_contra hne
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  have hlt : y < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxy)
    fun h => hne (hxy.antisymm (Scheme.le_iff_specializes.mp h)).symm.eq
  have h4 := (coheight_le_three hdim y).trans' <|
    (by gcongr : 2 + 1 + 1 ≤ Order.coheight x + 1).trans (Order.coheight_add_one_le hlt)
  exact absurd h4 (by decide)

end Threefold

/-- **Varying labels have point centres downstairs.** Let `C` be a terminal chain over a
stabilized tail `T`. There is `i₁` such that for every `i ≥ i₁` and every varying label `S` of
`C`: `S` is the divisor `E_{0,s}` for some `s ∈ I_∞`; the valuation `s'` of `k(X_i)`
corresponding to `s` belongs to the set extracted by the `i`-th junction, and the centre of `S`
on `Y_i` is the divisor `E_{i,s} = E_{s'}` of that junction; and the image `p_i(E_{i,s})` is a
closed point `x` of `X_i`, whose closure `{x}` is the centre `c_{X_i}(s')`. -/
@[mmp "prop_mmp_indexc_varying_point_centres"]
public theorem exists_isCentre_closedPoint_of_isVaryingLabel {T : StabilizedTail}
    (C : TerminalChain T) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁, ∀ S : C.Label, C.IsVaryingLabel S →
      ∃ s : C.I 0, S.1 = (C.junction 0).E s ∧
        ∃ s' : C.I i, T.IsTransportedValuationFrom i s.1 s'.1 ∧
          C.IsLabelCentre S ⟨i, none⟩ ((C.junction i).E s') ∧
          ∃ x : T.X i, IsClosed ({x} : Set (T.X i)) ∧
            (C.junction i).p '' ((C.junction i).E s').support = {x} ∧
            MMP.Intersection.IsCentre ℂ (T.sX i) s'.1 (IrreducibleCloseds.closureSingleton x) := by
  obtain ⟨i₁, hi₁⟩ := exists_forall_ge_one_lt_minimalLogDiscrepancy_and_mem_smoothLocus T
  refine ⟨i₁, fun i hi S hS => ?_⟩
  obtain ⟨S, hSl⟩ := S
  obtain ⟨Γ, hΓ, hSΓ⟩ | ⟨s, rfl⟩ := id hSl
  · exact absurd (isLabelCoefficient_coeff_and_isFixedLabel C (S := ⟨S, hSl⟩) hΓ hSΓ).2 hS
  obtain ⟨s', hs'w, hs'v⟩ := (exists_equiv_primeDivisor C).2.2 i s
  have hvar : MMP.Mori.IsVariety ℂ (T.sX i) := (T.isProjectiveVariety i).toIsVariety
  have : LocallyOfFiniteType (T.sX i) := hvar.toLocallyOfFiniteType
  set J := C.junction i
  have : IsProper J.p := isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism
  let D : MMP.Mori.DivisorOver ℂ (T.sX i) :=
    ⟨J.Y, J.p, J.isQFactorial.1, J.isBirationalMorphism, J.E s'⟩
  have hDv : D.valuation = s'.1 := J.valuation_eq s'
  have hcentre : MMP.Intersection.IsCentre ℂ (T.sX i) s'.1 D.center :=
    ⟨D, inferInstanceAs (IsProper J.p), hDv.symm, rfl⟩
  have hDc : D.center = IrreducibleCloseds.closureSingleton (J.p (J.E s').genericPoint) :=
    MMP.Positivity.DivisorOver.center_eq_closureSingleton D
  obtain ⟨D₁, -, hD₁, hc⟩ := (show s'.1 ∈ lowDiscrepancySet (T.sX i) (T.B i) from
    (C.coe_I i) ▸ s'.2).1
  rw [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hvar (hD₁.symm.trans hDv.symm),
    MMP.Positivity.DivisorOver.codimension_center] at hc
  have hclosure := closure_singleton_eq_of_two_le_coheight (T.sX i) (T.dim_eq i) hc fun hdim1 =>
    hS (isFixedLabel_and_isJunctionLabelCoefficient C
      (fun j hj V h1 h2 => ((hi₁ j hj).1 V h1 h2).1) s hi hs'w (hDc ▸ hcentre) hdim1
      (J.Θ_eq.choose_spec.1 s')).1
  have himage : J.p '' (J.E s').support = closure (J.p '' (J.E s').support) :=
    (J.p.isClosedMap _ (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isClosed_closure)).closure_eq.symm
  refine ⟨s, rfl, s', hs'w, ⟨s'.1, (labelValuation_E s).symm ▸ hs'w, hs'v⟩,
    J.p (J.E s').genericPoint, hclosure ▸ isClosed_closure, ?_, hDc ▸ hcentre⟩
  rw [himage, ← hclosure]
  exact congrArg SetLike.coe hDc

end TerminalChain

end StabilizedTail

end MMP.Fourfold
