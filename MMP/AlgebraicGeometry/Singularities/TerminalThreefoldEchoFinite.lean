module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.MonomialValuationWeight
import MMP.AlgebraicGeometry.MMP.Fourfold.EchoMonomialValuation
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Finitely many non-echoes below log discrepancy two

Let `(Y, Θ)` be a terminal pair on a projective `ℚ`-factorial complex threefold `Y`, and let
`L = {S_1, …, S_m}` be distinct prime divisors with `Supp Θ ⊆ ⋃_h S_h`, so `Θ = ∑_h b_h S_h`
with `b_h ≥ 0`. Then only finitely many normalized divisorial valuations `ξ` of `ℂ(Y)`,
exceptional over `Y` with `a(ξ; Y, Θ) < 2`, are not echoes: of any order `j ≥ 1` of any label
`S_h` at any curve `V ⊆ S_h` whose generic point lies in the one-label smooth locus `Y°`.

Let `π : W ⟶ Y` be a log resolution of `(Y, L)` which is an isomorphism over the snc locus of
`(Y, L)`, and `T` the reduced snc divisor with support `Ex(π) ∪ π⁻¹(Supp L)`; `(π, T)` is a
log-smooth datum of `(Y, Θ)`. With `a_j = a(ord_{T_j}; Y, Θ) > 0` (and `a_j > 1` for the
exceptional components, by terminality) the log-smooth formula reads
`a(ξ; Y, Θ) = ∑_{j ∈ J(ξ)} ξ(T_j) a_j + e_T(ξ)`.

* If `e_T(ξ) = 0`, then `ξ(T_j) < 2 / a_j` and `ξ` lies in the finite set of zero-error
  valuations of bounded order.
* If `e_T(ξ) ≥ 1`, then `∑_{J(ξ)} ξ(T_j) a_j < 1`; no exceptional component passes through the
  centre `Z = c_W(ξ)`, whose generic point is therefore off `Ex(π)`. If `J(ξ) = ∅`, then
  `a(ξ; Y, Θ) = e_T(ξ) ≥ codim Z ≥ 2`. If `|J(ξ)| ≥ 2`, the monomial valuation of weight
  `(1, …, 1)` at the stratum through `Z` is exceptional over `Y` with log discrepancy
  `∑_{J(ξ)} a_j`, which is `> 1` by terminality. If `J(ξ)` is a single component, the bound forces
  `e_T(ξ) = 1` and `codim Z = 2`: the centre on `Y` is a curve `V ⊆ S_h` whose generic point
  lies in `Y°`. A local equation `x` of `S_h` there is completed to a regular system of
  parameters `(x, t)`, `t` a local equation of a prime divisor `L'`, and on a log resolution of
  `(Y, L + L')` which is an isomorphism over `η_V` the formula becomes
  `a(ξ; Y, Θ) = (1 - b_h) ξ(x) + ξ(t) + e(ξ)`; hence `ξ(t) = 1`, `e(ξ) = 0`, and `ξ` is monomial
  of weight `(ξ(x), 1)`, i.e. an echo of order `ξ(x)` of `S_h` at `V`.

## Main results

* `MMP.Fourfold.finite_setOf_not_isEcho`: the finiteness statement.
* `MMP.Mori.DivisorOver.isExceptional_iff_two_le_codimension`: a divisor over a normal variety
  is exceptional exactly when its centre has codimension at least two.

## Implementation notes

* The labels are a finite set `L` of prime divisors, so they are distinct, and
  `Supp Θ ⊆ ⋃_h S_h` is `Θ.support ⊆ L`; the coefficients `b_h ≥ 0` are part of the pair
  `MMP.Fourfold.IsPair`, carried by the terminal pair `MMP.Fourfold.IsKltTerminalPair`.
* "`ξ` is an echo of order `j` of `S_h` at `V`" is `MMP.Fourfold.IsEcho`, which also records
  `S_h ∈ L`, `V ⊆ S_h` a curve, `η_V ∈ Y°` and `j ≥ 1`.
* `a(ξ; Y, Θ) < 2` reads: `ξ` has some log discrepancy `a < 2`
  (`MMP.Fourfold.HasLogDiscrepancy`).
* A complex threefold is a scheme over `ℂ` of dimension `3`.
* The source principalizes the ideal of `Y ∖ Y°` to make every centre inside `Y ∖ Y°` lie on an
  exceptional divisor of `W`. Here the log resolution is only required to be an isomorphism over
  the snc locus of `(Y, L)`; a centre off `Ex(π)` through two labels is excluded instead by
  terminality, applied to the monomial valuation of weight `(1, …, 1)` at the stratum of `T`
  through it, whose reduced snc discrepancy is zero. The curve case is computed on a second log
  resolution of `(Y, L + L')`, an isomorphism over a neighbourhood of `η_V` in `Y°`, rather than
  on an open subset of `Y°`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.Mori.DivisorOver

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
public theorem isExceptional_iff_two_le_codimension {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) from
      Subsingleton.elim _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ :=
    Closeds.ext <| by
      rw [Closeds.coe_closure]
      exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩ ↔ _
  rw [closedsCodimension_coe]

end MMP.Mori.DivisorOver

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Preliminaries -/

/-- In a scheme of dimension three, an irreducible closed subset of codimension two is a
curve. -/
private theorem topologicalKrullDim_eq_one_of_codimension_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 3) (V : IrreducibleCloseds Y) (hV : codimension V = 2) :
    topologicalKrullDim (V : Set Y) = 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at hV
  rw [hV] at h
  generalize topologicalKrullDim (V : Set Y) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h' : (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast
        exact h
      have h'' : d + 2 = 3 := by exact_mod_cast WithBot.coe_inj.mp h'
      obtain rfl : d = 1 := by omega
      rfl

/-! ### Components of an snc closed subset -/

/-- An irreducible closed subset maximal in a closed set of pure codimension one of a scheme is
the support of a prime divisor. -/
private theorem exists_primeDivisor_support_eq_of_maximal {Y : Scheme.{u}} {T : Closeds Y}
    (hT : IsPureCodimOne T) {W : IrreducibleCloseds Y}
    (hW : Maximal (fun V : IrreducibleCloseds Y => (V : Set Y) ⊆ T) W) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W := by
  have h1 := hT W hW
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq

/-- An irreducible component of a closed set of pure codimension one of a scheme is the support of
a prime divisor. -/
private theorem exists_primeDivisor_support_eq {Y : Scheme.{u}} {T : Set Y} (hTc : IsClosed T)
    (hpure : IsPureCodimOne (⟨T, hTc⟩ : Closeds Y)) {W : Set Y} (hW : W ∈ componentsOf T) :
    ∃ P : MMP.Mori.PrimeDivisor Y, (P.support : Set Y) = W :=
  exists_primeDivisor_support_eq_of_maximal hpure
    (W := ⟨W, hW.1.1, Aux.isClosed_of_mem_componentsOf hTc hW⟩)
    ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩

/-- A point of a closed set of pure codimension one of a Noetherian scheme lies on a prime divisor
contained in it. -/
private theorem exists_primeDivisor_mem_support_subset {Y : Scheme.{u}} [NoetherianSpace Y]
    {T : Closeds Y} (hT : IsPureCodimOne T) {y : Y} (hy : y ∈ (T : Set Y)) :
    ∃ P : MMP.Mori.PrimeDivisor Y, y ∈ P.support ∧ (P.support : Set Y) ⊆ T := by
  obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf T.isClosed).2 hy)
  obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq T.isClosed hT hW
  exact ⟨P, hP ▸ hyW, hP ▸ hW.1.2⟩

/-- **The components of an snc closed subset.** The prime divisors whose generic points lie on a
divisor `T` with simple normal crossings on a smooth scheme form a finite set whose reduced sum is
an snc divisor. -/
private theorem exists_finset_isSNC_of_isSNCClosedSubset {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [NoetherianSpace Y] (hsm : IsSmoothScheme sY)
    {T : Set Y} (hT : IsSNCClosedSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      (⋃ F ∈ S, (F.support : Set Y)) = T := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
  have hT' := hT
  obtain ⟨hTc, hT0 | ⟨hpure, hfin, -⟩⟩ := hT'
  · refine ⟨∅, ?_, by simp [hT0]⟩
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
  have hinj : Set.InjOn (fun P : MMP.Mori.PrimeDivisor Y => (P.support : Set Y))
      {P | (P.support : Set Y) ∈ componentsOf T} := fun P _ Q _ hPQ =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ.le
  have hfinS : {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ∈ componentsOf T}.Finite :=
    Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 fun _ hP => hP)) hinj
  set S := hfinS.toFinset
  have hmemS : ∀ P, P ∈ S ↔ (P.support : Set Y) ∈ componentsOf T := fun _ =>
    hfinS.mem_toFinset
  have hU : (⋃ F ∈ S, (F.support : Set Y)) = T := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun F hF => ((hmemS F).1 hF).1.2)
      fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hTc).2 hx)
    obtain ⟨P, hP⟩ := exists_primeDivisor_support_eq hTc hpure hW
    exact Set.mem_iUnion₂.2 ⟨P, (hmemS P).2 (hP ▸ hW), hP ▸ hxW⟩
  have hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y),
      IsRegularSystemOfParameters z := fun y => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    exact MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk y)
  exact ⟨S, MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset
    sY hreg S (hU ▸ hT), hU⟩

/-! ### The support of the crepant boundary -/

section Crepant

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
  {f : Y ⟶ X}

/-- **The support of the crepant boundary.** For a proper birational morphism `f : Y ⟶ X` from a
normal variety, every prime divisor in the support of the crepant boundary `Δ_Y` is
`f`-exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_exceptionalSet_or_mem_of_mem_support (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : G ∈ ΔY.support) :
    G.genericPoint ∈ (exceptionalSet f : Set Y) ∨
      f G.genericPoint ∈ (Δ.support.sup fun E => (E.idealSheaf.support : Set X)) := by
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hGe
    have hη : f G.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hc' : ΔY.coeff G = Δ.coeff P := neg_injective ((hΔY G).eq hd)
    refine Or.inr ?_
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc',
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

end Crepant

/-! ### Log-smooth data with prescribed labels -/

/-- **Log-smooth data with labels.** Let `(X, B)` be a klt pair and `D` a finite set of prime
divisors containing `Supp B`. A log resolution `π : W ⟶ X` of `(X, D)` which is an isomorphism
over the snc locus of `(X, D)`, with `T` the reduced sum of the components of
`Ex(π) ∪ π⁻¹(Supp D)`, is a log-smooth datum of `(X, B)`. -/
private theorem exists_isLogSmoothDatum {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltPair sX B) (D : Finset (MMP.Mori.PrimeDivisor X))
    (hD : B.support ⊆ D) :
    ∃ (W : Scheme.{u}) (π : W ⟶ X) (T : Divisor W), IsLogSmoothDatum sX B π T ∧
      IsPureCodimOne (exceptionalSet π) ∧
      (⋃ E ∈ T.support, (E.support : Set W)) =
        (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) ∧
      ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
        IsSNCClosedSubset (U.ι ≫ sX) (U.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X))) →
        IsIso (π ∣_ U) := by
  classical
  haveI : IsAlgClosed k := hB.1.isAlgClosed
  haveI : CharZero k := hB.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.isPair
  obtain ⟨Y, f, hres, hpure, hS, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D
  haveI : IsProper f := IsProjective.isProper hres.isProjective
  have hfres : IsSmoothResolution sX f :=
    ⟨inferInstance, hres.isBirationalMorphism, hres.isSmoothScheme⟩
  obtain ⟨hY, -, -⟩ := hfres.isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := (hY.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  obtain ⟨⟨BY, hBY, -⟩, -⟩ :=
    IsPair.existsUnique_isCrepantBoundary hB.1.isPair hK f hY hfres.isBirationalMorphism
  obtain ⟨S, hsncS, hU⟩ :=
    exists_finset_isSNC_of_isSNCClosedSubset (f ≫ sX) hfres.isSmoothScheme hS
  have hsupp : (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support = S :=
    Finset.ext fun G => by
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
      simp [Finsupp.single_apply]
  have hmem : ∀ G : MMP.Mori.PrimeDivisor Y, G.genericPoint ∈ (⋃ F ∈ S, (F.support : Set Y)) →
      G ∈ S := fun G hG => by
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hG
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE
  have hBD : (B.support.sup fun E => (E.idealSheaf.support : Set X)) ⊆
      (D.sup fun E => (E.idealSheaf.support : Set X)) := Finset.sup_mono hD
  refine ⟨Y, f, ∑ E ∈ S, Finsupp.single E (1 : ℤ), ⟨hB, hres.isProjective,
    hfres.isBirationalMorphism, hY, hfres.isSmoothScheme, fun P => ?_, hsncS, fun y hy => ?_,
    n, K, BY, hBY, fun G hG => ?_⟩, hpure, by rw [hsupp, hU], hiso⟩
  · rw [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply]
    by_cases hP : P ∈ S <;> simp [Finsupp.single_apply, hP]
  · rw [hsupp, hU]
    exact Or.inl hy
  · rw [hsupp]
    apply hmem
    rw [hU]
    exact (genericPoint_mem_exceptionalSet_or_mem_of_mem_support ⟨hX, hK, hq⟩ hY
      hfres.isBirationalMorphism hBY hG).imp_right (hBD ·)

/-! ### Exceptional divisors and the log discrepancies of the components -/

/-- **The log discrepancies of the prime divisors of a log-smooth datum.** Let `(π, T)` be a
log-smooth datum of a terminal pair `(X, B)`. Every prime divisor `G` of `W` has a log
discrepancy `a_G > 0`; it is `> 1` when the generic point of `G` lies in `Ex(π)`, and it is
`1 - b_P` when `π` maps the generic point of `G` to that of a prime divisor `P` of `X`. -/
private theorem exists_logDiscrepancy_primeDivisor {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltTerminalPair sX B) {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) :
    ∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
      ∃ aT : MMP.Mori.PrimeDivisor W → ℝ,
        (∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
          ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j)) ∧
        (∀ j, 0 < aT j) ∧
        (∀ j, j.genericPoint ∈ (exceptionalSet π : Set W) → 1 < aT j) ∧
        ∀ j (P : MMP.Mori.PrimeDivisor X), π j.genericPoint = P.genericPoint →
          aT j = 1 - (B.coeff P : ℝ) := by
  haveI : IsAlgClosed k := hB.1.1.isAlgClosed
  haveI : CharZero k := hB.1.1.charZero
  obtain ⟨hX, n, K, hK, hq⟩ := hB.1.1.isPair
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : IsIntegral W := hW.1.toIsIntegral
  let DT : MMP.Mori.PrimeDivisor W → DivisorOver k sX :=
    fun j => ⟨W, π, hW, hπ.isBirationalMorphism, j⟩
  have hex : ∀ j, ∃ a : ℝ,
      MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) (DT j) a := fun j => by
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.1.isPair hK (DT j)
    exact ⟨_, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
      (inferInstance : IsProper π)⟩
  choose aT haT using hex
  refine ⟨n, K, hK, aT, haT, fun j => hB.1.2 n (DT j) (aT j) (haT j),
    fun j hj => hB.2 n (DT j) (aT j) ?_ (haT j), fun j P hP => ?_⟩
  · rw [DivisorOver.isExceptional_iff_two_le_codimension hX,
      MMP.Positivity.DivisorOver.codimension_center]
    have hcod := MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sX π
      (hY := hX.1) (hX := hW.1) hπ.isBirationalMorphism
    exact (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hcod) _
      (MMP.Mori.mem_exceptionalSet.1 hj)
  · have hc1 : codimension (DT j).center = 1 := by
      rw [MMP.Positivity.DivisorOver.codimension_center]
      change Order.coheight (π j.genericPoint) = 1
      rw [hP]
      exact P.coheight_genericPoint
    have hne : ¬ (DT j).IsExceptional := by
      rw [DivisorOver.isExceptional_iff_two_le_codimension hX, hc1]
      decide
    obtain ⟨P', hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff ⟨hX, hK, hq⟩ _ hne
    have hPP : P' = P := by
      refine MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset ?_
      rw [← hc, DivisorOver.center_eq_closure_genericPoint,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      change closure {π j.genericPoint} ⊆ _
      rw [hP]
    subst hPP
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.unique (haT j)
      (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd inferInstance)]
    push_cast
    ring

/-! ### Lifting prime divisors over the biregular locus -/

/-- **Prime divisors lift over the biregular locus.** If `π : W ⟶ X` is an isomorphism over a
neighbourhood of `π(w)` and `S` is a prime divisor of `X` through `π(w)`, there is a prime divisor
`G` of `W` through `w` with `π(η_G) = η_S`, whose ideal at `w` is the image of that of `S` under
the isomorphism `𝒪_{X,π(w)} ≅ 𝒪_{W,w}`. -/
private theorem exists_primeDivisor_lift {X W : Scheme.{u}} (π : W ⟶ X) {w : W}
    (hw : π w ∈ MMP.Mori.biregularLocus π) (S : MMP.Mori.PrimeDivisor X)
    (hS : π w ∈ S.support) :
    ∃ G : MMP.Mori.PrimeDivisor W, w ∈ G.support ∧ π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf w =
        Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk S.idealSheaf (π w)) := by
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus π hw
  let e : X.presheaf.stalk (π w) ≃+* W.presheaf.stalk w :=
    (asIso (π.stalkMap w)).commRingCatIsoToRingEquiv
  obtain ⟨q, hq, hqI, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
  set q' : PrimeSpectrum (W.presheaf.stalk w) := PrimeSpectrum.comap e.symm.toRingHom q
  have hmap : π (W.fromSpecStalk w q') = S.genericPoint := by
    have h : π (W.fromSpecStalk w q') =
        X.fromSpecStalk (π w) (PrimeSpectrum.comap (π.stalkMap w).hom q') := by
      have := congrArg (fun g : Spec (W.presheaf.stalk w) ⟶ X => g q')
        (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := w))
      simp only [Scheme.Hom.comp_apply] at this
      exact this.symm
    rw [h, ← hq]
    congr 1
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change a ∈ Ideal.comap (π.stalkMap w).hom (Ideal.comap e.symm.toRingHom q.asIdeal) ↔ _
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change e.symm (e a) ∈ q.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  have hgen : π (W.fromSpecStalk w q') ∈ MMP.Mori.biregularLocus π := by
    rw [hmap]
    refine (Specializes.mem_open ?_ (MMP.Mori.biregularLocus π).isOpen hw)
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hS
  have h1 : Order.coheight (W.fromSpecStalk w q') = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus π hgen, hmap]
    exact S.coheight_genericPoint
  set G := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hsupp : (G.support : Set W) = closure {W.fromSpecStalk w q'} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [hsupp]
    exact specializes_iff_mem_closure.1 (MMP.Resolution.specializes_fromSpecStalk w q')
  · change π (AlgebraicGeometry.PrimeDivisor.genericPoint G) = _
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hmap
  · have hcl : G.idealSheaf.support = Closeds.closure {W.fromSpecStalk w q'} :=
      Closeds.ext (by rwa [Closeds.coe_closure])
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf G, hcl,
      Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk w q', hqI]
    exact Ideal.comap_symm e

/-! ### Centres over a birational morphism -/

/-- The generic point of the centre of a divisor `D` over `X` is the image of the generic point
of `D`. -/
private theorem genericPoint_center_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) :
    D.center.isIrreducible.genericPoint = D.f D.E.genericPoint :=
  (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).eq
    D.center_eq_closure_genericPoint.symm

section Centres

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsIntegral W] [IsSeparated sX] {π : W ⟶ X} [IsDominant π]

/-- If `π_* v_{D'} = v_{D₀}` for a divisor `D'` over `W` and a divisor `D₀` over `X`, then `π`
maps the generic point of the centre of `D'` to that of the centre of `D₀`. -/
private theorem map_genericPoint_eq_of_comap_eq (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation) :
    π (D'.f D'.E.genericPoint) = D₀.f D₀.E.genericPoint := by
  open MMP.Positivity.DivisorOver in
  refine eq_of_dominates sX D₀.valuation (fun x => ?_) (fun x hx => ?_)
    (valuation_algebraMap_le_one D₀ _ rfl) (valuation_algebraMap_lt_one D₀ _ rfl)
  · rw [← hξ]
    change D'.valuation (functionFieldMap π _) ≤ 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact valuation_algebraMap_le_one D' _ rfl _
  · rw [← hξ]
    change D'.valuation (functionFieldMap π _) < 1
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact valuation_algebraMap_lt_one D' _ rfl _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit _ _ hu))

/-- If `π_* v_{D'} = v_{D₀}`, then `π` maps the generic point of `c_W(D')` to that of
`c_X(D₀)`. -/
private theorem map_genericPoint_center_eq_of_comap_eq (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation) :
    π D'.center.isIrreducible.genericPoint = D₀.center.isIrreducible.genericPoint := by
  rw [genericPoint_center_eq, genericPoint_center_eq]
  exact map_genericPoint_eq_of_comap_eq D' D₀ hξ

/-- **A centre off the exceptional locus has the same codimension downstairs.** -/
private theorem codimension_center_eq_of_notMem_exceptionalSet (D' : DivisorOver k (π ≫ sX))
    (D₀ : DivisorOver k sX) (hξ : D'.valuation.comap (functionFieldMap π) = D₀.valuation)
    (hη : D'.f D'.E.genericPoint ∉ (exceptionalSet π : Set W)) :
    codimension D₀.center = codimension D'.center := by
  rw [MMP.Positivity.DivisorOver.codimension_center, MMP.Positivity.DivisorOver.codimension_center,
    ← map_genericPoint_eq_of_comap_eq D' D₀ hξ]
  exact MMP.Positivity.coheight_map_of_mem_biregularLocus π
    (by_contra fun h => hη (MMP.Mori.mem_exceptionalSet.2 h))

end Centres

/-- A nonzero element of the maximal ideal of the local ring at the centre of a divisor `D` has
`v_D`-order a positive integer. -/
private theorem exists_valuation_eq_exp_neg {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] (D : DivisorOver k sW) {η : W}
    (hη : η = D.f D.E.genericPoint) {z : W.presheaf.stalk η} (hz0 : z ≠ 0)
    (hz : z ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk η)) :
    ∃ m : ℤ, 1 ≤ m ∧ D.valuation (algebraMap _ W.functionField z) = WithZero.exp (-m) := by
  have hne : D.valuation (algebraMap _ W.functionField z) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0))
  refine ⟨-WithZero.log (D.valuation (algebraMap _ W.functionField z)), ?_, by
    rw [neg_neg, WithZero.exp_log hne]⟩
  have h := MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D η hη z hz
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  omega

/-! ### The log-smooth formula at the centre -/

/-- **The log-smooth formula at the centre.** Let `(π, T)` be a log-smooth datum of `(X, B)`,
with log discrepancies `a_G` of the prime divisors of `W`, and `D` a divisor over `X` with log
discrepancy `a`. Then `v_D = π_* v_{D'}` for a divisor `D'` over `W`, the reduced snc
discrepancy `e_T(v_{D'})` is a natural number `e`, and for local equations `z_j` of the
components `T_j` through the centre of `D'` the orders `m_j = v_{D'}(z_j) ≥ 1` satisfy
`a = ∑_j m_j a_j + e`. -/
private theorem exists_logSmoothFormula_at_center {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {B : QDivisor X}
    {π : W ⟶ X} {T : Divisor W} (hπ : IsLogSmoothDatum sX B π T) {n : ℕ}
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    {D : DivisorOver k sX} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a) :
    haveI := hπ.isBirationalMorphism.isDominant
    ∃ D' : DivisorOver k (π ≫ sX),
      MMP.Intersection.IsCentre k (π ≫ sX) D'.valuation D'.center ∧
      D'.valuation.comap (functionFieldMap π) = D.valuation ∧
      ∃ e : ℕ, IsReducedSNCDiscrepancy (π ≫ sX) T D'.valuation e ∧
      ∃ (z : sncIndexSet T (D'.center : Set W) →
          W.presheaf.stalk D'.center.isIrreducible.genericPoint)
        (m : sncIndexSet T (D'.center : Set W) → ℤ),
        (∀ j, IdealSheafData.stalk j.1.idealSheaf D'.center.isIrreducible.genericPoint =
          Ideal.span {z j}) ∧
        (∀ j, 1 ≤ m j) ∧
        (∀ j, D'.valuation (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) ∧
        a = ∑ j, (m j : ℝ) * aT j + e := by
  classical
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : LocallyOfFiniteType (π ≫ sX) := hπ.isNormalVariety.1.toLocallyOfFiniteType
  let φ := RingEquiv.ofBijective (functionFieldMap π)
    hπ.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨Z, hZ, e, he, hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D ha.2.1 ha (D.valuation.comap φ.symm.toRingHom)
      (by
        ext f
        exact congrArg D.valuation (φ.symm_apply_apply f))
  obtain ⟨D', hD'p, hξD', rfl⟩ := hZ
  have hηj : ∀ j : sncIndexSet T (D'.center : Set W),
      D'.center.isIrreducible.genericPoint ∈ (j.1.support : Set W) := fun j =>
    (Finset.mem_filter.1 j.2).2
      (D'.center.isIrreducible.isGenericPoint_genericPoint D'.center.isClosed).mem
  choose z hzp hz using fun j : sncIndexSet T (D'.center : Set W) =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sX) hπ.isSmoothScheme j.1 (hηj j)
  choose m hm1 hm using fun j => exists_valuation_eq_exp_neg D' (genericPoint_center_eq D')
    (hzp j).ne_zero ((IsLocalRing.mem_maximalIdeal _).2 (hzp j).not_unit)
  obtain ⟨e, rfl⟩ := he.exists_eq_natCast
  refine ⟨D', ⟨D', hD'p, rfl, rfl⟩, ?_, e, hξD' ▸ he, z, m, hz, hm1, hm,
    hform z m hz (hξD' ▸ hm)⟩
  rw [← hξD']
  ext f
  exact congrArg D.valuation (φ.symm_apply_apply f)

/-! ### Uniqueness of the reduced snc discrepancy -/

/-- Pulling valuations back along the inclusion of a nonempty open subscheme is injective. -/
private theorem comap_functionFieldMap_ι_injective {X : Scheme.{u}} [IsIntegral X]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (U : X.Opens) [Nonempty U] :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
    Function.Injective (Valuation.comap (Γ₀ := Γ₀) (functionFieldMap U.ι)) := by
  haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hsurj := (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩).2
  intro v w hvw
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun v => v y) hvw

/-- **The reduced snc discrepancy is unique.** -/
private theorem IsReducedSNCDiscrepancy.unique {k : Type u} [Field k] [PerfectField k]
    {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {T : Divisor W} {ξ : Valuation W.functionField ℤᵐ⁰} {e e' : ℝ}
    (h : IsReducedSNCDiscrepancy sW T ξ e) (h' : IsReducedSNCDiscrepancy sW T ξ e') :
    e = e' := by
  obtain ⟨hWv, -, -, -, Z, hZ, hne, n, D, -, hξD, ha⟩ := h
  obtain ⟨-, -, -, -, Z', hZ', hne', n', D', -, hξD', ha'⟩ := h'
  obtain rfl : Z = Z' := by
    obtain ⟨D₀, -, hv₀, rfl⟩ := hZ
    obtain ⟨D₁, -, hv₁, rfl⟩ := hZ'
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv (hv₀.symm.trans hv₁)
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha'
    (comap_functionFieldMap_ι_injective _ (hξD.symm.trans hξD'))

/-! ### Two components through a centre off the exceptional locus -/

/-- A member of a regular system of parameters of a regular local ring is not in `𝔪²`. -/
private theorem notMem_sq_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {n : ℕ} {z : Fin n → R} (hz : IsRegularSystemOfParameters z)
    (m : Fin n) : z m ∉ IsLocalRing.maximalIdeal R ^ 2 := fun h => by
  haveI := IsRegularLocalRing.isDomain R
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero (MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m)) h
    (MMP.Resolution.isRegularLocalRing_quotient_span_singleton_of_isRegularSystemOfParameters hz m)

/-- A generator of the ideal of a component of an snc divisor at a point is not in `𝔪²`. -/
private theorem notMem_sq_of_isSNC {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} {T : Divisor W} (hT : T.IsSNC sW) (hsm : IsSmoothScheme sW)
    [LocallyOfFiniteType sW] {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ T.support) {w : W}
    (hw : w ∈ E.support) {z : W.presheaf.stalk w}
    (hz : IdealSheafData.stalk E.idealSheaf w = Ideal.span {z}) :
    z ∉ IsLocalRing.maximalIdeal (W.presheaf.stalk w) ^ 2 := by
  haveI : Smooth sW := Aux.smooth_of_isSmoothScheme' sW hsm
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sW w
  haveI := IsRegularLocalRing.isDomain (W.presheaf.stalk w)
  obtain ⟨n, c, j, hc, -, hI⟩ := hT.2 w
  have h1 := notMem_sq_of_isRegularSystemOfParameters hc (j ⟨E, hE, hw⟩)
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz.symm.trans (hI ⟨E, hE, hw⟩))
  intro h
  exact h1 (hu ▸ Ideal.mul_mem_right _ _ h)

/-- In a weighted monomial ideal of weight `1`, a generator `z_j` of the maximal ideal outside
`𝔪²` has order exactly one. -/
private theorem isGreatest_weightedMonomialIdeal_one {R : Type*} [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ι → R}
    (hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal R) (j : ι)
    (hj : z j ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsGreatest {m : ℕ | z j ∈ weightedMonomialIdeal z (fun _ => 1) m} 1 := by
  refine ⟨Ideal.subset_span ⟨Pi.single j 1, by simp, by simp [Pi.single_apply]⟩, fun m hm => ?_⟩
  by_contra h2
  refine hj (weightedMonomialIdeal_antitone z _ (show 2 ≤ m by simp at h2 ⊢; omega) hm |>
    fun h => (Ideal.span_le.2 ?_) h)
  rintro r ⟨β, hβ, rfl⟩
  have hmem : ∏ i, z i ^ β i ∈ ∏ i, IsLocalRing.maximalIdeal R ^ β i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hzm i) _
  rw [Finset.prod_pow_eq_pow_sum] at hmem
  exact Ideal.pow_le_pow_right (by simpa using hβ) hmem

/-- A point of a prime divisor other than its generic point has coheight at least two. -/
private theorem two_le_coheight_of_mem_support_of_ne {X : Scheme.{u}}
    (S : MMP.Mori.PrimeDivisor X) {p : X} (hp : p ∈ S.support) (hne : p ≠ S.genericPoint) :
    2 ≤ Order.coheight p := by
  have hle : p ≤ S.genericPoint := specializes_iff_mem_closure.mpr
    (by rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
  have hlt : p < S.genericPoint := lt_of_le_not_ge hle fun h => hne
    (Specializes.antisymm (show p ⤳ S.genericPoint from h)
      (show S.genericPoint ⤳ p from hle)).eq
  have h := Order.coheight_add_one_le hlt
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h
  exact h

/-- A point on two distinct prime divisors has coheight at least two. -/
private theorem two_le_coheight_of_mem_support_of_mem_support {X : Scheme.{u}} {p : X}
    {E₁ E₂ : MMP.Mori.PrimeDivisor X} (h₁ : p ∈ E₁.support) (h₂ : p ∈ E₂.support)
    (hne : E₁ ≠ E₂) : 2 ≤ Order.coheight p := by
  by_cases h : p = E₁.genericPoint
  · exact two_le_coheight_of_mem_support_of_ne E₂ h₂ fun h' =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h.symm.trans h'))
  · exact two_le_coheight_of_mem_support_of_ne E₁ h₁ h

/-- A centre `Z` lies in an irreducible component `Z₀` of the intersection of the components of
`T` through `Z`, and the components of `T` through `Z₀` are those through `Z`. -/
private theorem exists_maximal_subset_sncIndexSet_eq {W : Scheme.{u}} [NoetherianSpace W]
    (T : Divisor W) (Z : IrreducibleCloseds W) :
    ∃ Z₀ : IrreducibleCloseds W,
      Maximal (fun S : Set W => IsIrreducible S ∧
        S ⊆ ⋂ E ∈ sncIndexSet T (Z : Set W), (E.support : Set W)) (Z₀ : Set W) ∧
      (Z : Set W) ⊆ Z₀ ∧ sncIndexSet T (Z₀ : Set W) = sncIndexSet T (Z : Set W) := by
  classical
  have hηZ := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hcl : IsClosed (⋂ E ∈ sncIndexSet T (Z : Set W), (E.support : Set W)) :=
    isClosed_biInter fun E _ => SNCWeight.PrimeDivisorUnion.isClosed_support E
  obtain ⟨C, hC, hηC⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hcl).2
    (Set.mem_iInter₂.2 fun E hE => (Finset.mem_filter.1 hE).2 hηZ))
  let Z₀ : IrreducibleCloseds W := ⟨C, hC.1.1, Aux.isClosed_of_mem_componentsOf hcl hC⟩
  have hZZ₀ : (Z : Set W) ⊆ Z₀ := by
    rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
    exact closure_minimal (Set.singleton_subset_iff.2 hηC) Z₀.isClosed
  refine ⟨Z₀, hC, hZZ₀, ?_⟩
  ext E
  simp only [sncIndexSet, Finset.mem_filter]
  refine ⟨fun ⟨hE, h⟩ => ⟨hE, hZZ₀.trans h⟩, fun ⟨hE, h⟩ => ⟨hE, fun x hx => ?_⟩⟩
  exact Set.mem_iInter₂.1 (hC.1.2 hx) E (Finset.mem_filter.2 ⟨hE, h⟩)

/-- **A centre of codimension two off `Ex(π)` gives an exceptional divisor.** A divisor `D'` over
`W` whose centre has codimension at least two and generic point off `Ex(π)` is, through `π`, an
exceptional divisor `D₀` over `X` with `π_* v_{D'} = v_{D₀}`. -/
private theorem exists_isExceptional_of_two_le_codimension {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsSeparated sX] {π : W ⟶ X}
    [IsDominant π] [IsProper π]
    (hX : IsNormalVariety k sX) (hπ : IsBirationalMorphism π) (D' : DivisorOver k (π ≫ sX))
    (hD' : IsProper D'.f) (hp : D'.f D'.E.genericPoint ∉ (exceptionalSet π : Set W))
    (h2 : 2 ≤ codimension D'.center) :
    ∃ D₀ : DivisorOver k sX, IsProper D₀.f ∧
      D'.valuation.comap (functionFieldMap π) = D₀.valuation ∧ D₀.IsExceptional := by
  haveI := D'.isIntegral
  haveI := D'.isDominant
  haveI := D'.isNormal
  haveI := D'.isLocallyNoetherian
  have hbir : IsBirationalMorphism (D'.f ≫ π) :=
    MMP.Mori.isBirationalMorphism_comp_of_isBirational π D'.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hπ)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D'.isBirationalMorphism)
  haveI := hbir.isDominant
  let D₀ : DivisorOver k sX :=
    ⟨D'.Y, D'.f ≫ π, by
      rw [Category.assoc]
      exact D'.isNormalVariety, hbir, D'.E⟩
  have hv₀ : D'.valuation.comap (functionFieldMap π) = D₀.valuation := by
    ext t
    change D'.E.divisorialValuation (functionFieldMap D'.f (functionFieldMap π t)) =
      D'.E.divisorialValuation (functionFieldMap (D'.f ≫ π) t)
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  exact ⟨D₀, (inferInstance : IsProper (D'.f ≫ π)), hv₀,
    (DivisorOver.isExceptional_iff_two_le_codimension hX D₀).2
      (codimension_center_eq_of_notMem_exceptionalSet D' D₀ hv₀ hp ▸ h2)⟩

/-- **The weight-one monomial valuation at a stratum off `Ex(π)`.** Let `(π, T)` be a log-smooth
datum of a terminal pair `(X, B)`, with log discrepancies `a_G` of the prime divisors of `W`, and
let `Z ⊆ Z₀` with the generic point of `Z` off `Ex(π)`, where `Z₀` lies on the components `J` of
`T` through it, at least two of them. Then the monomial valuation of weight `(1, …, 1)` at `Z₀`
is exceptional over `X` with log discrepancy `∑_{j ∈ J} a_j`, so `∑_{j ∈ J} a_j > 1`. -/
private theorem one_lt_sum_of_isMonomialValuationOfWeight {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {B : QDivisor X} (hB : IsKltTerminalPair sX B) {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    {Z Z₀ : IrreducibleCloseds W}
    (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W)) (hZZ₀ : (Z : Set W) ⊆ Z₀)
    {J : Finset (MMP.Mori.PrimeDivisor W)} (hZ₀I : (Z₀ : Set W) ⊆ ⋂ E ∈ J, (E.support : Set W))
    (hJ₀ : sncIndexSet T (Z₀ : Set W) = J) (hJT : J ⊆ T.support)
    {j₁ j₂ : MMP.Mori.PrimeDivisor W} (hj₁ : j₁ ∈ J) (hj₂ : j₂ ∈ J) (hj₁₂ : j₁ ≠ j₂)
    {ν : Valuation W.functionField ℤᵐ⁰}
    (hν : ∀ z : J → W.presheaf.stalk Z₀.isIrreducible.genericPoint,
      (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z₀.isIrreducible.genericPoint =
        Ideal.span {z j}) →
      IsMonomialValuationOfWeight (π ≫ sX) T J Z₀ z (fun _ => 1) ν) :
    1 < ∑ j ∈ J, aT j := by
  classical
  haveI : IsAlgClosed k := hB.1.1.isAlgClosed
  haveI : CharZero k := hB.1.1.charZero
  obtain ⟨hX, -⟩ := hB.1.1.isPair
  haveI : IsProper π := IsProjective.isProper hπ.isProjective
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI := hπ.isBirationalMorphism.isDominant
  haveI : IsSeparated sX := hX.1.toIsSeparated
  set η₀ := Z₀.isIrreducible.genericPoint
  have hη₀ : ∀ E : J, η₀ ∈ E.1.support := fun E => Set.mem_iInter₂.1
    (hZ₀I (Z₀.isIrreducible.isGenericPoint_genericPoint Z₀.isClosed).mem) E.1 E.2
  choose z hzp hz using fun E : J =>
    MMP.Resolution.Aux.exists_prime_stalk_idealSheaf (π ≫ sX) hπ.isSmoothScheme E.1 (hη₀ E)
  have hνm := hν z hz
  have he₀ := isReducedSNCDiscrepancy_zero_of_isMonomialValuationOfWeight (π ≫ sX) hνm
    fun d hd => Nat.dvd_one.1 (hd ⟨j₁, hj₁⟩)
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨D', hD'p, hνD', hZ₀D'⟩, hval⟩ := hνm
  set p := D'.f D'.E.genericPoint
  have hpZ₀ : p ∈ (Z₀ : Set W) := by
    rw [hZ₀D', D'.center_eq_closure_genericPoint]
    exact subset_closure rfl
  have hpη : p ⤳ Z.isIrreducible.genericPoint := by
    have : Z.isIrreducible.genericPoint ∈ (D'.center : Set W) :=
      hZ₀D' ▸ hZZ₀ (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
    rwa [D'.center_eq_closure_genericPoint, ← specializes_iff_mem_closure] at this
  have h2 : 2 ≤ codimension D'.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact two_le_coheight_of_mem_support_of_mem_support (Set.mem_iInter₂.1 (hZ₀I hpZ₀) j₁ hj₁)
      (Set.mem_iInter₂.1 (hZ₀I hpZ₀) j₂ hj₂) hj₁₂
  obtain ⟨D₀, hD₀p, hv₀, hex⟩ := exists_isExceptional_of_two_le_codimension hX
    hπ.isBirationalMorphism D' hD'p (fun h => hZ (hpη.mem_closed (exceptionalSet π).isClosed h)) h2
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.1.1.isPair hK D₀
  have haν := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hD₀p
  obtain ⟨Z', hZ', e', he', hform⟩ :=
    IsLogSmoothDatum.logDiscrepancy_eq_sum_add_reducedSNCDiscrepancy sX hπ aT
      (fun j _ => haT j) D₀ hD₀p haν ν (hνD' ▸ hv₀)
  have hZ'₀ : Z' = Z₀ := by
    obtain ⟨D'', -, hνD'', rfl⟩ := hZ'
    rw [hZ₀D']
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hW.1 (hνD''.symm.trans hνD')
  subst Z'
  obtain rfl : e' = 0 := IsReducedSNCDiscrepancy.unique he' he₀
  have hmem : ∀ j : sncIndexSet T (Z₀ : Set W), j.1 ∈ J := fun j => hJ₀ ▸ j.2
  have hval1 : ∀ j : J, ν (algebraMap _ W.functionField (z j)) = WithZero.exp (-(1 : ℤ)) := by
    intro j
    obtain ⟨M, hM, hνM⟩ := hval (z j) (hzp j).ne_zero
    have h1 := isGreatest_weightedMonomialIdeal_one
      (fun i => (IsLocalRing.mem_maximalIdeal _).2 (hzp i).not_unit) j
      (notMem_sq_of_isSNC hπ.isSNC hπ.isSmoothScheme (hJT j.2) (hη₀ j) (hz j))
    rw [hνM, hM.unique h1]
    rfl
  have hsum := hform (fun j => z ⟨j.1, hmem j⟩) (fun _ => 1) (fun j => hz ⟨j.1, hmem j⟩)
    (fun j => hval1 ⟨j.1, hmem j⟩)
  simp only [Int.cast_one, one_mul, add_zero] at hsum
  rw [Finset.sum_coe_sort (sncIndexSet T (Z₀ : Set W)) aT, hJ₀] at hsum
  rw [← hsum]
  exact hB.2 n D₀ _ hex haν

/-- **Two components through a centre off the exceptional locus.** Let `(π, T)` be a log-smooth
datum of a terminal pair `(X, B)`, with log discrepancies `a_G` of the prime divisors of `W`, and
let `Z ⊆ W` be irreducible closed with generic point outside `Ex(π)`, contained in at least two
components of `T`. Then the components through `Z` have `∑ a_j > 1`: the monomial valuation of
weight `(1, …, 1)` at a component of their intersection is exceptional over `X`, with log
discrepancy `∑ a_j`. -/
private theorem one_lt_sum_of_two_le_card {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : IsKltTerminalPair sX B) {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    {Z : IrreducibleCloseds W}
    (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    (hJ : 2 ≤ (sncIndexSet T (Z : Set W)).card) :
    1 < ∑ j ∈ sncIndexSet T (Z : Set W), aT j := by
  classical
  haveI : CharZero k := hB.1.1.charZero
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : CompactSpace W := (hW.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  obtain ⟨Z₀, hC, hZZ₀, hJ₀⟩ := exists_maximal_subset_sncIndexSet_eq T Z
  obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := Finset.one_lt_card.1 hJ
  obtain ⟨ν, hν⟩ := exists_isMonomialValuationOfWeight (π ≫ sX) hW.1 hπ.isSmoothScheme T
    hπ.isReducedEffective hπ.isSNC _ ⟨j₁, hj₁⟩ (Finset.filter_subset _ _) Z₀ hC (fun _ => 1)
    (fun _ => one_pos) fun d hd => Nat.dvd_one.1 (hd ⟨j₁, hj₁⟩)
  exact one_lt_sum_of_isMonomialValuationOfWeight hB hπ hK aT haT hZ hZZ₀ hC.1.2 hJ₀
    (Finset.filter_subset _ _) hj₁ hj₂ hj₁₂ hν

/-! ### Components of `T` through a centre off the exceptional locus -/

/-- A morphism is injective on the points over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X W : Scheme.{u}} (π : W ⟶ X) {a b : W}
    (ha : π a ∈ MMP.Mori.biregularLocus π) (hab : π a = π b) : a = b := by
  haveI : IsIso (π ∣_ MMP.Mori.biregularLocus π) := MMP.Mori.isBiregular_biregularLocus π
  have ha' : a ∈ π ⁻¹ᵁ MMP.Mori.biregularLocus π := ha
  have hb' : b ∈ π ⁻¹ᵁ MMP.Mori.biregularLocus π := show π b ∈ _ from hab ▸ ha
  let pa : (π ⁻¹ᵁ MMP.Mori.biregularLocus π).toScheme := ⟨a, ha'⟩
  let pb : (π ⁻¹ᵁ MMP.Mori.biregularLocus π).toScheme := ⟨b, hb'⟩
  have h := (π ∣_ MMP.Mori.biregularLocus π).isOpenEmbedding.injective
    (a₁ := pa) (a₂ := pb) (Subtype.ext (by
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact hab))
  exact congrArg Subtype.val h

/-- A point of coheight one on a prime divisor is its generic point. -/
private theorem eq_genericPoint_of_coheight_eq_one {X : Scheme.{u}} (S : MMP.Mori.PrimeDivisor X)
    {p : X} (hp : p ∈ S.support) (h1 : Order.coheight p = 1) : p = S.genericPoint := by
  by_contra hne
  have h := two_le_coheight_of_mem_support_of_ne S hp hne
  rw [h1] at h
  exact absurd h (by decide)

section Components

variable {k : Type u} [Field k] {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {π : W ⟶ X} {T : Divisor W}
  {D : Finset (MMP.Mori.PrimeDivisor X)}

/-- A prime divisor `S ∈ D` through `π(η)`, for `η` the generic point of `Z` off `Ex(π)`, lifts
to a component of `T` through `Z`, when `T` has support `Ex(π) ∪ π⁻¹(Supp D)`. -/
private theorem exists_mem_sncIndexSet_lift
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {S : MMP.Mori.PrimeDivisor X} (hSD : S ∈ D) (hS : π Z.isIrreducible.genericPoint ∈ S.support) :
    ∃ G ∈ sncIndexSet T (Z : Set W), π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf Z.isIrreducible.genericPoint =
        Ideal.map (π.stalkMap Z.isIrreducible.genericPoint).hom
          (IdealSheafData.stalk S.idealSheaf (π Z.isIrreducible.genericPoint)) := by
  classical
  have hηB : π Z.isIrreducible.genericPoint ∈ MMP.Mori.biregularLocus π :=
    by_contra fun h => hZ (MMP.Mori.mem_exceptionalSet.2 h)
  obtain ⟨G, hηG, hGS, hGI⟩ := exists_primeDivisor_lift π hηB S hS
  have hGT : G.genericPoint ∈ ⋃ E ∈ T.support, (E.support : Set W) := by
    rw [hT]
    refine Or.inr ?_
    rw [Set.mem_preimage, hGS, Finset.sup_set_eq_biUnion]
    exact Set.mem_iUnion₂.2 ⟨S, hSD, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
  obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.1 hGT
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen
  refine ⟨E, Finset.mem_filter.2 ⟨hE, ?_⟩, hGS, hGI⟩
  rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
  exact closure_minimal (Set.singleton_subset_iff.2 hηG)
    (SNCWeight.PrimeDivisorUnion.isClosed_support E)

/-- A component of `T` through `Z`, for `Z` with generic point `η` off `Ex(π)`, lies over a prime
divisor `S ∈ D` through `π(η)`, its generic point going to that of `S`. -/
private theorem exists_genericPoint_eq_of_mem_sncIndexSet
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {E : MMP.Mori.PrimeDivisor W} (hE : E ∈ sncIndexSet T (Z : Set W)) :
    E.genericPoint ∉ (exceptionalSet π : Set W) ∧ ∃ S ∈ D,
      π Z.isIrreducible.genericPoint ∈ S.support ∧ π E.genericPoint = S.genericPoint := by
  classical
  have hηZ := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hEgen : E.genericPoint ⤳ Z.isIrreducible.genericPoint := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (Finset.mem_filter.1 hE).2 hηZ
  have hEEx : E.genericPoint ∉ (exceptionalSet π : Set W) := fun h =>
    hZ (hEgen.mem_closed (exceptionalSet π).isClosed h)
  have hET : E.genericPoint ∈ ⋃ E ∈ T.support, (E.support : Set W) :=
    Set.mem_iUnion₂.2 ⟨E, (Finset.mem_filter.1 hE).1,
      MMP.Flips.primeDivisor_genericPoint_mem_support E⟩
  rw [hT] at hET
  rcases hET with hET | hET
  · exact absurd hET hEEx
  rw [Set.mem_preimage, Finset.sup_set_eq_biUnion] at hET
  obtain ⟨S, hSD, hES⟩ := Set.mem_iUnion₂.1 hET
  have hEB : π E.genericPoint ∈ MMP.Mori.biregularLocus π :=
    by_contra fun h => hEEx (MMP.Mori.mem_exceptionalSet.2 h)
  have h1 : Order.coheight (π E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus π hEB]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  have hES' := eq_genericPoint_of_coheight_eq_one S hES h1
  refine ⟨hEEx, S, hSD, ?_, hES'⟩
  exact (hEgen.map π.continuous).mem_closed
    (SNCWeight.PrimeDivisorUnion.isClosed_support S) hES

/-- If every prime divisor `S ∈ D` through `π(η)`, for `η` the generic point of `Z` off `Ex(π)`,
is `P` or `L'`, and `G_P`, `G_L` are components of `T` through `Z` over `P`, `L'`, then they are
the only components of `T` through `Z`. -/
private theorem sncIndexSet_eq_pair [DecidableEq (MMP.Mori.PrimeDivisor W)]
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {P L' : MMP.Mori.PrimeDivisor X}
    (hD : ∀ S ∈ D, π Z.isIrreducible.genericPoint ∈ S.support → S = P ∨ S = L')
    {Gx Gt : MMP.Mori.PrimeDivisor W} (hGxJ : Gx ∈ sncIndexSet T (Z : Set W))
    (hGtJ : Gt ∈ sncIndexSet T (Z : Set W)) (hGx : π Gx.genericPoint = P.genericPoint)
    (hGt : π Gt.genericPoint = L'.genericPoint) :
    sncIndexSet T (Z : Set W) = {Gx, Gt} := by
  ext E
  rw [Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun hE => ?_, fun h => h.elim (fun h => h ▸ hGxJ) (fun h => h ▸ hGtJ)⟩
  obtain ⟨hEEx, S, hSD, hηS, hES⟩ := exists_genericPoint_eq_of_mem_sncIndexSet hT hZ hE
  have hEB : π E.genericPoint ∈ MMP.Mori.biregularLocus π :=
    by_contra fun h => hEEx (MMP.Mori.mem_exceptionalSet.2 h)
  rcases hD S hSD hηS with rfl | rfl
  · exact Or.inl (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus π hEB (hES.trans hGx.symm)))
  · exact Or.inr (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_map_eq_of_mem_biregularLocus π hEB (hES.trans hGt.symm)))

end Components

/-! ### The one-label smooth locus below a centre off the exceptional locus -/

/-- At a point where `𝒪_{Y,y} ⧸ I_{S,y}` is regular, the prime divisor `S` is regular. -/
private theorem notMem_image_singularLocus_of_isRegularLocalRing_quotient {Y : Scheme.{u}}
    (S : MMP.Mori.PrimeDivisor Y) {y : Y}
    (h : IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk S.idealSheaf y)) :
    y ∉ S.idealSheaf.subschemeι '' singularLocus S.idealSheaf.subscheme := by
  rintro ⟨z, hz, rfl⟩
  exact hz (IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z))

/-- At a point of a smooth prime divisor `G`, the ring `𝒪_{W,w} ⧸ I_{G,w}` is regular. -/
private theorem isRegularLocalRing_quotient_of_isSmoothScheme {k : Type u} [Field k]
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [LocallyOfFiniteType sW]
    (G : MMP.Mori.PrimeDivisor W) (hG : IsSmoothScheme (G.idealSheaf.subschemeι ≫ sW)) {w : W}
    (hw : w ∈ G.support) :
    IsRegularLocalRing (W.presheaf.stalk w ⧸ IdealSheafData.stalk G.idealSheaf w) := by
  obtain ⟨z, rfl⟩ : w ∈ Set.range G.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  haveI : Smooth (G.idealSheaf.subschemeι ≫ sW) := Aux.smooth_of_isSmoothScheme' _ hG
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (G.idealSheaf.subschemeι ≫ sW) z
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z).symm

/-- **A centre on exactly one component and off the exceptional locus lies over `Y°`.** Let
`(π, T)` be a log-smooth datum whose divisor `T` has support `Ex(π) ∪ π⁻¹(Supp L)`, and let the
generic point `η` of `Z ⊆ W` lie off `Ex(π)` on exactly one component `G` of `T`. Then `π(η)`
lies in the one-label smooth locus of `(X, L)`, on a label `P`, the only label through `π(η)`. -/
private theorem mem_oneLabelSmoothLocus_of_sncIndexSet_eq_singleton {k : Type u} [Field k]
    {X W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} {π : W ⟶ X} {T : Divisor W}
    (hπ : IsLogSmoothDatum sX B π T) {L : Finset (MMP.Mori.PrimeDivisor X)}
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (L.sup fun E => (E.idealSheaf.support : Set X)))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W))
    {G : MMP.Mori.PrimeDivisor W} (hJ : sncIndexSet T (Z : Set W) = {G}) :
    π Z.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧
      ∃ P ∈ L, π Z.isIrreducible.genericPoint ∈ P.support ∧
        ∀ S ∈ L, π Z.isIrreducible.genericPoint ∈ S.support → S = P := by
  classical
  have hW : IsNormalVariety k (π ≫ sX) := hπ.isNormalVariety
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : Smooth (π ≫ sX) := Aux.smooth_of_isSmoothScheme' _ hπ.isSmoothScheme
  set η := Z.isIrreducible.genericPoint
  have hηZ : η ∈ (Z : Set W) := (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem
  have hηB : π η ∈ MMP.Mori.biregularLocus π :=
    by_contra fun h => hZ (MMP.Mori.mem_exceptionalSet.2 h)
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus π hηB
  let e : X.presheaf.stalk (π η) ≃+* W.presheaf.stalk η :=
    (asIso (π.stalkMap η)).commRingCatIsoToRingEquiv
  have hGT : G ∈ sncIndexSet T (Z : Set W) := hJ ▸ Finset.mem_singleton_self G
  -- a label through `π(η)` lifts to `G`
  have hlift : ∀ S ∈ L, π η ∈ S.support → π G.genericPoint = S.genericPoint ∧
      IdealSheafData.stalk G.idealSheaf η =
        Ideal.map (π.stalkMap η).hom (IdealSheafData.stalk S.idealSheaf (π η)) := by
    intro S hSL hS
    obtain ⟨G', hG'J, hG'⟩ := exists_mem_sncIndexSet_lift hT hZ hSL hS
    rw [hJ, Finset.mem_singleton] at hG'J
    exact hG'J ▸ hG'
  obtain ⟨-, P, hPL, hηP, -⟩ := exists_genericPoint_eq_of_mem_sncIndexSet hT hZ hGT
  have huniq : ∀ S ∈ L, π η ∈ S.support → S = P := fun S hSL hS =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hlift S hSL hS).1.symm.trans (hlift P hPL hηP).1)
  refine ⟨?_, P, hPL, hηP, huniq⟩
  rw [mem_oneLabelSmoothLocus_iff]
  refine ⟨?_, fun S hSL => ?_, fun S hSL S' hS'L hne h => hne ?_⟩
  · haveI := isRegularLocalRing_stalk_of_smooth_over_field (π ≫ sX) η
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · by_cases hS : π η ∈ S.support
    · refine notMem_image_singularLocus_of_isRegularLocalRing_quotient S ?_
      haveI := isRegularLocalRing_quotient_of_isSmoothScheme G
        (hπ.isSNC.1 G (Finset.mem_filter.1 hGT).1) ((Finset.mem_filter.1 hGT).2 hηZ)
      exact IsRegularLocalRing.of_ringEquiv
        (Ideal.quotientEquiv _ _ e (hlift S hSL hS).2).symm
    · rintro ⟨z, -, hz⟩
      refine hS ?_
      have : S.idealSheaf.subschemeι z ∈ Set.range S.idealSheaf.subschemeι := ⟨z, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι, hz] at this
      exact this
  · exact (huniq S hSL h.1).trans (huniq S' hS'L h.2).symm

/-- A centre whose generic point lies in `Ex(π)`, of pure codimension one and covered by `T`, lies
on a component of `T` whose generic point is in `Ex(π)`. -/
private theorem exists_mem_sncIndexSet_of_mem_exceptionalSet {X W : Scheme.{u}} [NoetherianSpace W]
    {π : W ⟶ X} {T : Divisor W} (hpure : IsPureCodimOne (exceptionalSet π))
    (hT : (exceptionalSet π : Set W) ⊆ ⋃ E ∈ T.support, (E.support : Set W))
    {Z : IrreducibleCloseds W} (hZ : Z.isIrreducible.genericPoint ∈ (exceptionalSet π : Set W)) :
    ∃ E ∈ sncIndexSet T (Z : Set W), E.genericPoint ∈ (exceptionalSet π : Set W) := by
  classical
  obtain ⟨E, hηE, hEsub⟩ := exists_primeDivisor_mem_support_subset hpure hZ
  have hEgen := hEsub (MMP.Flips.primeDivisor_genericPoint_mem_support E)
  obtain ⟨E', hE', hgen⟩ := Set.mem_iUnion₂.1 (hT hEgen)
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen
  refine ⟨E', Finset.mem_filter.2 ⟨hE', ?_⟩, hEgen⟩
  rw [← (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).def]
  exact closure_minimal (Set.singleton_subset_iff.2 hηE)
    (SNCWeight.PrimeDivisorUnion.isClosed_support E')

/-- A component through a centre met by exactly two components `G₀, G₁` is one of them. -/
private theorem eq_or_eq_of_sncIndexSet_eq_pair {W : Scheme.{u}} {T : Divisor W} {Z : Set W}
    [DecidableEq (MMP.Mori.PrimeDivisor W)] {G₀ G₁ : MMP.Mori.PrimeDivisor W}
    (hJ : sncIndexSet T Z = {G₀, G₁})
    (i : sncIndexSet T Z) : i.1 = G₀ ∨ i.1 = G₁ := by
  simpa [hJ] using i.2

/-! ### Echo ideals as monomial ideals -/

section EchoAlgebra

variable {R : Type*} [CommRing R]

/-- The ideal generated by the monomials `t^a x^b` of weight `a + j b ≥ n`. -/
private def pairMonomialIdeal (t x : R) (j n : ℕ) : Ideal R :=
  Ideal.span {r | ∃ a b : ℕ, n ≤ a + j * b ∧ r = t ^ a * x ^ b}

/-- Powers of `𝔪 = (x, t)` are generated by the monomials of degree at least the exponent. -/
private theorem pow_le_pairMonomialIdeal_one {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) (c : ℕ) : 𝔪 ^ c ≤ pairMonomialIdeal t x 1 c := by
  induction c with
  | zero =>
    intro r _
    have h1 : (1 : R) ∈ pairMonomialIdeal t x 1 0 := by
      rw [pairMonomialIdeal]
      exact Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩
    simpa using Ideal.mul_mem_left (pairMonomialIdeal t x 1 0) r h1
  | succ c ih =>
    calc 𝔪 ^ (c + 1) = 𝔪 ^ c * 𝔪 := pow_succ _ _
      _ ≤ pairMonomialIdeal t x 1 c * Ideal.span {x, t} := Ideal.mul_mono ih h𝔪.ge
      _ ≤ pairMonomialIdeal t x 1 (c + 1) := ?_
    rw [pairMonomialIdeal, pairMonomialIdeal, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨a, b, hab, rfl⟩, s, hs, rfl⟩
    rcases hs with rfl | rfl
    · exact Ideal.subset_span ⟨a, b + 1, by omega, by ring⟩
    · exact Ideal.subset_span ⟨a + 1, b, by omega, by ring⟩

/-- If `𝔪 = (x, t)` and `j ≥ 1`, the echo ideal `∑_b x^b 𝔪^{n - jb}` is generated by the
monomials `t^a x^b` with `a + j b ≥ n`. -/
private theorem echoIdeal_eq_pairMonomialIdeal {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    echoIdeal x 𝔪 j n = pairMonomialIdeal t x j n := by
  refine le_antisymm (iSup_le fun b => ?_) ?_
  · refine (Ideal.mul_mono_right (pow_le_pairMonomialIdeal_one h𝔪 _)).trans ?_
    rw [pairMonomialIdeal, pairMonomialIdeal, Ideal.span_mul_span']
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, rfl, _, ⟨a', b', h, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨a', b + b', ?_, by ring⟩
    have : b' ≤ j * b' := Nat.le_mul_of_pos_left b' hj
    rw [Nat.mul_add]
    omega
  · rw [pairMonomialIdeal]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.mem_iSup_of_mem b ?_
    rw [mul_comm (t ^ a)]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (Ideal.pow_le_pow_right (show n - j * b ≤ a by omega) (Ideal.pow_mem_pow ?_ a))
    exact h𝔪 ▸ Ideal.subset_span (by simp)

/-- A weighted monomial ideal on two variables `z i₀, z i₁` is generated by the monomials
`z i₁^a z i₀^b` of weight `a α_{i₁} + b α_{i₀} ≥ n`. -/
private theorem weightedMonomialIdeal_eq_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i₀ i₁ : ι} (h01 : i₀ ≠ i₁) (huniv : ∀ i, i = i₀ ∨ i = i₁) (z : ι → R) (α : ι → ℕ)
    (n : ℕ) :
    weightedMonomialIdeal z α n =
      Ideal.span {r | ∃ a b : ℕ, n ≤ α i₁ * a + α i₀ * b ∧ r = z i₁ ^ a * z i₀ ^ b} := by
  have huniv' : (Finset.univ : Finset ι) = {i₀, i₁} := by
    ext i
    simpa using huniv i
  have hsum : ∀ β : ι → ℕ, ∑ i, α i * β i = α i₀ * β i₀ + α i₁ * β i₁ := fun β => by
    rw [huniv', Finset.sum_pair h01]
  have hprod : ∀ β : ι → ℕ, ∏ i, z i ^ β i = z i₀ ^ β i₀ * z i₁ ^ β i₁ := fun β => by
    rw [huniv', Finset.prod_pair h01]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨β, hβ, rfl⟩
    refine Ideal.subset_span ⟨β i₁, β i₀, by rw [hsum] at hβ; omega, by rw [hprod]; ring⟩
  · rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.subset_span ⟨fun i => if i = i₀ then b else a, ?_, ?_⟩
    · have e := hsum (fun i => if i = i₀ then b else a)
      beta_reduce at e
      rw [if_pos rfl, if_neg h01.symm] at e
      rw [e]; omega
    · have e := hprod (fun i => if i = i₀ then b else a)
      beta_reduce at e
      rw [if_pos rfl, if_neg h01.symm] at e
      rw [e]; ring

/-- The image of `pairMonomialIdeal t x j n` under a ring homomorphism. -/
private theorem map_pairMonomialIdeal {S : Type*} [CommRing S] (φ : R →+* S) (t x : R)
    (j n : ℕ) :
    (pairMonomialIdeal t x j n).map φ = pairMonomialIdeal (φ t) (φ x) j n := by
  rw [pairMonomialIdeal, pairMonomialIdeal, Ideal.map_span]
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨a, b, h, rfl⟩, rfl⟩
    exact ⟨a, b, h, by simp⟩
  · rintro ⟨a, b, h, rfl⟩
    exact ⟨_, ⟨a, b, h, rfl⟩, by simp⟩

end EchoAlgebra

/-! ### Echo values from a monomial valuation over the biregular locus -/

open Classical in
/-- **Echo values from a monomial valuation.** Let `π : W ⟶ Y` induce an isomorphism
`𝒪_{Y,y} ≅ 𝒪_{W,w}` with `π(w) = y`, where `w` is the generic point of `Z ⊆ W` and exactly two
components `G_P ≠ G_L` of `T` pass through `Z`, their ideals at `w` the images of those of the
prime divisors `P`, `L'` of `Y`. Let `x`, `t` be local equations of `P`, `L'` at `y` with
`𝔪_y = (x, t)`. If `ξ_W` is monomial of weight `(j, 1)` at `Z` for `G_P + G_L`, then
`ξ = π_* ξ_W` satisfies the echo formula `ξ(f) = max {n : f ∈ ∑_b x^b 𝔪^{n - jb}}` on
`𝒪_{Y,y}`. -/
private theorem isEchoValue_of_isMonomialValuationOfWeight {k : Type u} [Field k]
    {Y W : Scheme.{u}} [IsIntegral Y] [IsIntegral W] {sW : W ⟶ Spec (.of k)} (π : W ⟶ Y)
    [IsDominant π] {T : Divisor W} {Z : IrreducibleCloseds W} (w : W)
    (hw : Z.isIrreducible.genericPoint = w) (y : Y) (hy : π w = y) (hiso : IsIso (π.stalkMap w))
    {Gx Gt : MMP.Mori.PrimeDivisor W} (hne : Gx ≠ Gt)
    (hJ : sncIndexSet T (Z : Set W) = {Gx, Gt}) {P L' : MMP.Mori.PrimeDivisor Y}
    (hGx : IdealSheafData.stalk Gx.idealSheaf w =
      Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk P.idealSheaf (π w)))
    (hGt : IdealSheafData.stalk Gt.idealSheaf w =
      Ideal.map (π.stalkMap w).hom (IdealSheafData.stalk L'.idealSheaf (π w)))
    {x t : Y.presheaf.stalk y} (hx : IdealSheafData.stalk P.idealSheaf y = Ideal.span {x})
    (ht : IdealSheafData.stalk L'.idealSheaf y = Ideal.span {t})
    (hxt : Ideal.span {x, t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) {j : ℕ}
    (hj : 1 ≤ j) {ξW : Valuation W.functionField ℤᵐ⁰} {α : sncIndexSet T (Z : Set W) → ℕ}
    (hαP : ∀ i, i.1 = Gx → α i = j) (hαL : ∀ i, i.1 = Gt → α i = 1)
    (hmono : ∀ z : sncIndexSet T (Z : Set W) → W.presheaf.stalk Z.isIrreducible.genericPoint,
      (∀ i, IdealSheafData.stalk i.1.idealSheaf Z.isIrreducible.genericPoint =
        Ideal.span {z i}) →
        IsMonomialValuationOfWeight sW T (sncIndexSet T (Z : Set W)) Z z α ξW) :
    ∀ f : Y.presheaf.stalk y, f ≠ 0 → ∃ M : ℕ,
      IsGreatest {n : ℕ | f ∈ echoIdeal x (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) j n}
        M ∧
      ξW.comap (functionFieldMap π) (algebraMap _ Y.functionField f) =
        WithZero.exp (-(M : ℤ)) := by
  classical
  subst hw
  subst hy
  let φ := (π.stalkMap Z.isIrreducible.genericPoint).hom
  have hbij : Function.Bijective φ :=
    (asIso (π.stalkMap Z.isIrreducible.genericPoint)).commRingCatIsoToRingEquiv.bijective
  have hGxJ : Gx ∈ sncIndexSet T (Z : Set W) := by simp [hJ]
  have hGtJ : Gt ∈ sncIndexSet T (Z : Set W) := by simp [hJ]
  let i₀ : sncIndexSet T (Z : Set W) := ⟨Gx, hGxJ⟩
  let i₁ : sncIndexSet T (Z : Set W) := ⟨Gt, hGtJ⟩
  have h01 : i₀ ≠ i₁ := fun h => hne (congrArg Subtype.val h)
  have huniv : ∀ i, i = i₀ ∨ i = i₁ := fun i =>
    (eq_or_eq_of_sncIndexSet_eq_pair hJ i).imp Subtype.ext Subtype.ext
  let z : sncIndexSet T (Z : Set W) → W.presheaf.stalk Z.isIrreducible.genericPoint :=
    fun i => if i = i₀ then φ x else φ t
  have hz₀ : z i₀ = φ x := if_pos rfl
  have hz₁ : z i₁ = φ t := if_neg h01.symm
  have hz : ∀ i,
      IdealSheafData.stalk i.1.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z i} := by
    intro i
    rcases huniv i with rfl | rfl
    · rw [hz₀]
      change IdealSheafData.stalk Gx.idealSheaf Z.isIrreducible.genericPoint = _
      rw [hGx, hx, Ideal.map_span, Set.image_singleton]
    · rw [hz₁]
      change IdealSheafData.stalk Gt.idealSheaf Z.isIrreducible.genericPoint = _
      rw [hGt, ht, Ideal.map_span, Set.image_singleton]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hval⟩ := hmono z hz
  have hα₀ : α i₀ = j := hαP i₀ rfl
  have hα₁ : α i₁ = 1 := hαL i₁ rfl
  have hideal : ∀ n, weightedMonomialIdeal z α n =
      (echoIdeal x (IsLocalRing.maximalIdeal _) j n).map φ := by
    intro n
    rw [weightedMonomialIdeal_eq_of_pair h01 huniv, echoIdeal_eq_pairMonomialIdeal hxt hj,
      map_pairMonomialIdeal, pairMonomialIdeal, hz₀, hz₁, hα₀, hα₁]
    congr 1
    ext r
    simp only [Set.mem_setOf_eq, one_mul]
  intro f hf
  have hφf : φ f ≠ 0 := fun h => hf (hbij.1 (h.trans (map_zero φ).symm))
  obtain ⟨M, hM, hξM⟩ := hval (φ f) hφf
  refine ⟨M, ?_, ?_⟩
  · have hset : {n : ℕ | f ∈ echoIdeal x (IsLocalRing.maximalIdeal _) j n} =
        {n : ℕ | φ f ∈ weightedMonomialIdeal z α n} := by
      ext n
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hideal, ← Ideal.mem_comap,
        Ideal.comap_map_of_bijective _ hbij]
    rwa [hset]
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact hξM

/-! ### Valuations of small log discrepancy at a curve of the one-label smooth locus -/

/-- Under a bijective ring map `φ`, an ideal whose image is generated by `φ t` is generated by
`t`. -/
private theorem eq_span_singleton_of_map_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {I : Ideal R} {t : R} (h : Ideal.span {φ t} = Ideal.map φ I) :
    I = Ideal.span {t} := by
  have h' : Ideal.map φ (Ideal.span {t}) = Ideal.map φ I := by
    rwa [Ideal.map_span, Set.image_singleton]
  have h'' := congrArg (Ideal.comap φ) h'
  rw [Ideal.comap_map_of_bijective _ hφ, Ideal.comap_map_of_bijective _ hφ] at h''
  exact h''.symm

/-- An open subscheme of a scheme locally of finite type over a perfect field, with regular local
rings, is smooth. -/
private theorem isSmoothScheme_ι_of_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (U : Y.Opens)
    (hU : ∀ v : U.toScheme, IsRegularLocalRing (Y.presheaf.stalk (U.ι v))) :
    IsSmoothScheme (U.ι ≫ sY) := by
  haveI : LocallyOfFinitePresentation (U.ι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sY)).mpr inferInstance
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, eq_top_iff]
  intro v _
  refine ((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField (U.ι ≫ sY)).1 v).2 ?_
  haveI := hU v
  exact IsRegularLocalRing.of_ringEquiv (asIso (U.ι.stalkMap v)).commRingCatIsoToRingEquiv

open Classical in
/-- On an open `U` meeting no label of `L` other than `P`, with `S_U = P ∩ U` and `L_U = L' ∩ U`,
the labels `L' + L` restrict to `S_U + L_U`. -/
private theorem preimage_sup_insert_eq {Y : Scheme.{u}} {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {P L' : MMP.Mori.PrimeDivisor Y} (hP : P ∈ L) {U : Y.Opens}
    (hUS : ∀ S' ∈ L, S' ≠ P → Disjoint (U : Set Y) S'.support)
    {SU LU : MMP.Mori.PrimeDivisor U.toScheme} (hSU : SU.support = U.ι ⁻¹' P.support)
    (hL' : ∀ v : U.toScheme, U.ι v ∈ L'.support ↔ v ∈ LU.support) :
    U.ι ⁻¹' ((insert L' L).sup fun E => (E.idealSheaf.support : Set Y)) =
      ⋃ F ∈ (MMP.Intersection.reducedDivisorOf {SU, LU}).support,
        (F.support : Set U.toScheme) := by
  rw [MMP.Intersection.support_reducedDivisorOf]
  ext v
  simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂, Finset.mem_insert,
    Finset.mem_singleton, exists_prop]
  constructor
  · rintro ⟨S, hS, hvS⟩
    rcases hS with rfl | hSL
    · exact ⟨LU, Or.inr rfl, (hL' v).1 hvS⟩
    · by_cases hSP : S = P
      · subst hSP
        exact ⟨SU, Or.inl rfl, by rwa [hSU]⟩
      · exact absurd hvS (Set.disjoint_left.1 (hUS S hSL hSP) v.2)
  · rintro ⟨F, hF, hvF⟩
    rcases hF with rfl | rfl
    · exact ⟨P, Or.inr hP, by rwa [hSU] at hvF⟩
    · exact ⟨L', Or.inl rfl, (hL' v).2 hvF⟩

/-- If `a = m₀ a₀ + m₁ + e < 2` with `m₀, m₁ ≥ 1` and `a₀ > 0`, then `m₁ = 1` and `e = 0`. -/
private theorem eq_one_and_eq_zero_of_lt_two {m₀ m₁ : ℤ} {e : ℕ} {a a₀ : ℝ} (h₀ : 1 ≤ m₀)
    (h₁ : 1 ≤ m₁) (ha₀ : 0 < a₀) (ha : a = (m₀ : ℝ) * a₀ + (m₁ : ℝ) * 1 + (e : ℝ))
    (ha2 : a < 2) : m₁ = 1 ∧ e = 0 := by
  have h₀' : (1 : ℝ) ≤ m₀ := by exact_mod_cast h₀
  have hlt : (m₁ : ℝ) + e < 2 := by nlinarith
  have hm : m₁ = 1 := by
    have : (m₁ : ℝ) < 2 := by linarith [(e.cast_nonneg : (0 : ℝ) ≤ e)]
    have : m₁ < 2 := by exact_mod_cast this
    omega
  refine ⟨hm, ?_⟩
  rw [hm, Int.cast_one] at hlt
  have : e < 1 := by exact_mod_cast (by linarith : (e : ℝ) < 1)
  omega

/-- **A zero-error valuation is monomial of weight its orders.** If `e_T(v_D) = 0` for a divisor
`D` over `W`, and `z_j` are local equations of the components of `T` through the centre of `D`
with `v_D(z_j) = exp(-m_j)`, then `v_D` is monomial of weight `m` at the centre. -/
private theorem exists_isMonomialValuationOfWeight_of_eq_zero {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k] {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hW : IsNormalVariety k sW) {T : Divisor W}
    (D : DivisorOver k sW) (he : IsReducedSNCDiscrepancy sW T D.valuation 0)
    {z : sncIndexSet T (D.center : Set W) → W.presheaf.stalk D.center.isIrreducible.genericPoint}
    (hz : ∀ j, IdealSheafData.stalk j.1.idealSheaf D.center.isIrreducible.genericPoint =
      Ideal.span {z j})
    {m : sncIndexSet T (D.center : Set W) → ℤ}
    (hm : ∀ j, D.valuation (algebraMap _ W.functionField (z j)) = WithZero.exp (-m j)) :
    ∃ α : sncIndexSet T (D.center : Set W) → ℕ, (∀ j, (α j : ℤ) = m j) ∧
      ∀ z' : sncIndexSet T (D.center : Set W) →
          W.presheaf.stalk D.center.isIrreducible.genericPoint,
        (∀ j, IdealSheafData.stalk j.1.idealSheaf D.center.isIrreducible.genericPoint =
          Ideal.span {z' j}) →
        IsMonomialValuationOfWeight sW T (sncIndexSet T (D.center : Set W)) D.center z' α
          D.valuation := by
  obtain ⟨Z₃, hZ₃, -, α, -, hall⟩ :=
    IsReducedSNCDiscrepancy.isMonomialValuationOfWeight_of_eq_zero he
  obtain rfl : Z₃ = D.center := by
    obtain ⟨D'', -, hv'', rfl⟩ := hZ₃
    exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hW.1 hv''.symm
  refine ⟨α, fun j => ?_, fun z' hz' => (hall z' hz').2⟩
  have h1 := (hall z hz).1 j
  rw [hm j] at h1
  have h2 := WithZero.exp_injective h1
  omega

open Classical in
/-- **The echo on a log resolution over `η_V`.** Let `(Y, Θ)` be a terminal pair, `ξ = v_D` with
`a(ξ; Y, Θ) < 2` centred at a curve `V ⊆ P` with generic point `y ∈ Y°`, and `(x, t)` a regular
system of parameters at `y`, with `x`, `t` local equations of `P ∈ L` and of a prime divisor
`L' ∉ L` with `b_{L'} = 0`. On a log-smooth datum `(π, T)` with `T` supported on
`Ex(π) ∪ π⁻¹(L + L')` and `π` an isomorphism over `y`, the log-smooth formula forces `ξ` to be an
echo of `P` at `V`. -/
private theorem exists_isEcho_of_isLogSmoothDatum {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ) {L : Finset (MMP.Mori.PrimeDivisor Y)}
    (hdim : topologicalKrullDim Y = 3) {D : DivisorOver k sY} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) D a) (ha2 : a < 2)
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∈ L) (hVP : (D.center : Set Y) ⊆ P.support)
    (hV : topologicalKrullDim (D.center : Set Y) = 1)
    (hη : D.center.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L)
    {x t : Y.presheaf.stalk D.center.isIrreducible.genericPoint}
    (hx : IdealSheafData.stalk P.idealSheaf D.center.isIrreducible.genericPoint = Ideal.span {x})
    {L' : MMP.Mori.PrimeDivisor Y}
    (ht : IdealSheafData.stalk L'.idealSheaf D.center.isIrreducible.genericPoint =
      Ideal.span {t})
    (hxt : Ideal.span {x, t} =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk D.center.isIrreducible.genericPoint))
    (hyL' : D.center.isIrreducible.genericPoint ∈ L'.support) (hL'L : L' ∉ L)
    (hcoeff : Θ.coeff L' = 0) {W : Scheme.{u}} {π : W ⟶ Y} {T : Divisor W}
    (hπ : IsLogSmoothDatum sY Θ π T)
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) = (exceptionalSet π : Set W) ∪
      π ⁻¹' ((insert L' L).sup fun E => (E.idealSheaf.support : Set Y)))
    (hyB : D.center.isIrreducible.genericPoint ∈ MMP.Mori.biregularLocus π) :
    ∃ j, IsEcho sY L P D.center j D.valuation := by
  classical
  haveI : IsAlgClosed k := hΘ.1.1.isAlgClosed
  haveI : CharZero k := hΘ.1.1.charZero
  have hY : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  have hyP : D.center.isIrreducible.genericPoint ∈ P.support :=
    hVP (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).mem
  obtain ⟨n₂, K₂, hK₂, aT, haT, hpos, -, hval⟩ := exists_logDiscrepancy_primeDivisor hΘ hπ
  obtain rfl : n = n₂ := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK₂.topologicalKrullDim_eq
  have hWv : IsNormalVariety k (π ≫ sY) := hπ.isNormalVariety
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hWv.2
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨D', -, hΦ, e0, he, z, m, hz, hm1, hm, hform'⟩ :=
    exists_logSmoothFormula_at_center hπ aT haT ha
  set η := D'.center.isIrreducible.genericPoint
  have hπη : π η = D.center.isIrreducible.genericPoint :=
    map_genericPoint_center_eq_of_comap_eq D' D hΦ
  have hηB : π η ∈ MMP.Mori.biregularLocus π := by rwa [hπη]
  have hηEx : η ∉ (exceptionalSet π : Set W) := fun h => (MMP.Mori.mem_exceptionalSet.1 h) hηB
  -- the components of `T` through the centre are the lifts of `P` and `L'`
  obtain ⟨Gx, hGxJ, hGxgen, hGxI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_of_mem hP) (by rwa [hπη])
  obtain ⟨Gt, hGtJ, hGtgen, hGtI⟩ := exists_mem_sncIndexSet_lift hT hηEx
    (Finset.mem_insert_self L' L) (by rwa [hπη])
  have hGxGt : Gx ≠ Gt := fun h => hL'L (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hGxgen.symm.trans ((congrArg (fun G => π G.genericPoint) h).trans hGtgen)) ▸ hP)
  have hJ := sncIndexSet_eq_pair hT hηEx (fun S hS hηS => (Finset.mem_insert.1 hS).symm.imp
    (fun hSL => eq_of_mem_oneLabelSmoothLocus hη hSL hP (by rwa [← hπη]) hyP) id)
    hGxJ hGtJ hGxgen hGtgen
  -- the formula has the two terms `ξ(x) (1 - b_P)` and `ξ(t)`
  let i₀ : sncIndexSet T (D'.center : Set W) := ⟨Gx, hGxJ⟩
  let i₁ : sncIndexSet T (D'.center : Set W) := ⟨Gt, hGtJ⟩
  have h01 : i₀ ≠ i₁ := fun h => hGxGt (congrArg Subtype.val h)
  have huniv : ∀ i, i = i₀ ∨ i = i₁ := fun i =>
    (eq_or_eq_of_sncIndexSet_eq_pair hJ i).imp Subtype.ext Subtype.ext
  have hsum : ∑ j, (m j : ℝ) * aT j = m i₀ * aT Gx + m i₁ * aT Gt :=
    Fintype.sum_eq_add i₀ i₁ h01 fun i hi => ((huniv i).elim hi.1 hi.2).elim
  have haGt : aT Gt = 1 := by
    rw [hval Gt L' hGtgen, hcoeff]
    simp
  rw [hsum, haGt] at hform'
  obtain ⟨hm₁, rfl⟩ := eq_one_and_eq_zero_of_lt_two (hm1 i₀) (hm1 i₁) (hpos Gx) hform' ha2
  -- the zero-error valuation is monomial of weight `(ξ(x), 1)`
  obtain ⟨α, hαm, hall⟩ := exists_isMonomialValuationOfWeight_of_eq_zero hWv D'
    (by simpa using he) hz hm
  have hα₁ : α i₁ = 1 := by exact_mod_cast (hαm i₁).trans hm₁
  have hjj : 1 ≤ α i₀ := by exact_mod_cast (hm1 i₀).trans_eq (hαm i₀).symm
  have hecho := isEchoValue_of_isMonomialValuationOfWeight π η rfl _ hπη
    (MMP.isIso_stalkMap_of_mem_biregularLocus π hηB) hGxGt hJ hGxI hGtI hx ht hxt hjj
    (fun i hi => by rw [show i = i₀ from Subtype.ext hi])
    (fun i hi => by rw [show i = i₁ from Subtype.ext hi, hα₁]) hall
  refine ⟨α i₀, hY, hdim, hP, hVP, hV, hη, hjj, ⟨D, ha.2.1, rfl, rfl⟩, x, hx, fun f hf => ?_⟩
  obtain ⟨M, hM, hξM⟩ := hecho f hf
  exact ⟨M, hM, hΦ ▸ hξM⟩

/-- **Below log discrepancy two, a valuation centred at a curve of `Y°` is an echo.** Let `(Y, Θ)`
be a terminal pair on a normal threefold, `L ⊇ Supp Θ` a finite set of labels, and `ξ = v_D` a
normalized divisorial valuation with `a(ξ; Y, Θ) < 2` whose centre is a curve `V ⊆ P`, `P ∈ L`,
with generic point in `Y°`. Complete a local equation `x` of `P` at `η_V` to a regular system of
parameters `(x, t)`, with `t` a local equation of a prime divisor `L'`, and take a log resolution
`π : W ⟶ Y` of `(Y, L + L')` which is an isomorphism over `η_V`. The two components of the
log-smooth formula give `a(ξ; Y, Θ) = ξ(x)(1 - b_P) + ξ(t) + e_T(ξ)`, so `ξ(t) = 1`,
`e_T(ξ) = 0`, and `ξ` is monomial of weight `(ξ(x), 1)`: an echo of order `ξ(x)` of `P` at
`V`. -/
private theorem exists_isEcho_of_mem_oneLabelSmoothLocus {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ) {L : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsupp : Θ.support ⊆ L) (hdim : topologicalKrullDim Y = 3)
    {D : DivisorOver k sY} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) D a) (ha2 : a < 2)
    {P : MMP.Mori.PrimeDivisor Y} (hP : P ∈ L) (hVP : (D.center : Set Y) ⊆ P.support)
    (hV : topologicalKrullDim (D.center : Set Y) = 1)
    (hη : D.center.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) :
    ∃ j, IsEcho sY L P D.center j D.valuation := by
  classical
  haveI : IsAlgClosed k := hΘ.1.1.isAlgClosed
  haveI : CharZero k := hΘ.1.1.charZero
  have hY : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  set V := D.center
  set y := V.isIrreducible.genericPoint
  have hyV : y ∈ (V : Set Y) := (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hyP : y ∈ P.support := hVP hyV
  haveI hreg : IsRegularLocalRing (Y.presheaf.stalk y) := (mem_oneLabelSmoothLocus_iff.mp hη).1
  -- a local equation `x` of `P` at `η_V`, and its completion `t`
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hyP
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk y)
  obtain ⟨x, hxq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
  have hx : IdealSheafData.stalk P.idealSheaf y = Ideal.span {x} := hq.trans hxq
  obtain ⟨⟨t, ht, U, hyU, hUL, hUS, xU, tU, hxU, htU, SU, LU, Zu, hSU, hSUx, hLUt, hne, hsnc,
    hZu, hZmax⟩, -⟩ := isEcho_tfae_isMonomialValuationOfWeight_isWeightedMonomialValuation sY L P
      V 1 hY hdim hP hVP hV hη le_rfl x hx
  have hxt : Ideal.span {x, t} = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    have := ht.1
    rwa [Matrix.range_cons_cons_empty] at this
  set u : U.toScheme := ⟨y, hyU⟩
  have huZ : u ∈ (Zu : Set U.toScheme) := by rwa [hZu]
  have huLU : u ∈ LU.support := (hZmax.1.2 huZ).2
  -- the prime divisor `L' = {t = 0}` of `Y`
  set L' := OpenWeilRestriction.primeDivisorMap U.ι LU
  have hL'supp : ∀ v : U.toScheme, U.ι v ∈ L'.support ↔ v ∈ LU.support :=
    MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι LU
  have hyL' : y ∈ L'.support := (hL'supp u).2 huLU
  have ht' : IdealSheafData.stalk L'.idealSheaf y = Ideal.span {t} := by
    have h1 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map U.ι L'.idealSheaf u
    rw [MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap, hLUt u, ← htU] at h1
    exact eq_span_singleton_of_map_eq (U.ι.stalkMap u).hom
      (asIso (U.ι.stalkMap u)).commRingCatIsoToRingEquiv.bijective h1
  have hL'L : L' ∉ L := fun h => hne (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support (by
    rw [hSU, ← eq_of_mem_oneLabelSmoothLocus hη h hP hyL' hyP]
    exact (hL'supp _).2 (MMP.Flips.primeDivisor_genericPoint_mem_support LU)))
  have hcoeff : Θ.coeff L' = 0 := by
    by_contra h
    exact hL'L (hsupp (by rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]))
  -- a log resolution of `(Y, L + L')`, an isomorphism over `U`
  obtain ⟨W, π, T, hπ, -, hT, hiso⟩ :=
    exists_isLogSmoothDatum hΘ.1 (insert L' L) (hsupp.trans (Finset.subset_insert _ _))
  have hUsnc : IsSNCClosedSubset (U.ι ≫ sY)
      (U.ι ⁻¹' ((insert L' L).sup fun E => (E.idealSheaf.support : Set Y))) := by
    rw [preimage_sup_insert_eq hP hUS hSU hL'supp]
    exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hsnc
  have hUsm : IsSmoothScheme (U.ι ≫ sY) := isSmoothScheme_ι_of_isRegularLocalRing U fun v =>
    (mem_oneLabelSmoothLocus_iff.mp (hUL v.2)).1
  exact exists_isEcho_of_isLogSmoothDatum hΘ hdim ha ha2 hP hVP hV hη hx ht' hxt hyL' hL'L hcoeff
    hπ hT (MMP.Mori.le_biregularLocus (hiso U hUsm hUsnc) hyU)

/-- If the components of `T` through the centre of `D'` all have log discrepancy `< 1`, then
that centre is off `Ex(π)`, and the centres of `D'` on `W` and of `D = π_* D'` on `Y` have the
same finite codimension `c ≥ 2`. -/
private theorem codimension_center_of_forall_lt_one {k : Type u} [Field k]
    {Y W : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ) (hdim : topologicalKrullDim Y = 3)
    {π : W ⟶ Y} {T : Divisor W} (hπ : IsLogSmoothDatum sY Θ π T)
    (hpure : IsPureCodimOne (exceptionalSet π)) (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (hexc : ∀ j, j.genericPoint ∈ (exceptionalSet π : Set W) → 1 < aT j)
    {D₀ D : DivisorOver k sY} (hD₀ : D.valuation = D₀.valuation)
    (hcod : 2 ≤ codimension D₀.center) :
    haveI := hπ.isBirationalMorphism.isDominant
    ∀ D' : DivisorOver k (π ≫ sY), D'.valuation.comap (functionFieldMap π) = D.valuation →
      (∀ j : sncIndexSet T (D'.center : Set W), aT j < 1) →
      D'.center.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W) ∧
        ∃ c : ℕ, codimension D'.center = c ∧ codimension D.center = c ∧ 2 ≤ c := by
  intro D' hΦ hlt1
  have hYn : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  have hWv : IsNormalVariety k (π ≫ sY) := hπ.isNormalVariety
  haveI : CompactSpace W := (hWv.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  haveI := hπ.isBirationalMorphism.isDominant
  have hgen := genericPoint_center_eq D'
  have hηEx : D'.center.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W) := fun h => by
    obtain ⟨E, hE, hEex⟩ := exists_mem_sncIndexSet_of_mem_exceptionalSet hpure
      hπ.exceptionalSet_subset h
    exact absurd (hexc E hEex) (not_lt.2 (hlt1 ⟨E, hE⟩).le)
  have hcodW : codimension D₀.center = codimension D'.center :=
    codimension_center_eq_of_notMem_exceptionalSet D' D₀ (hΦ.trans hD₀) (hgen ▸ hηEx)
  have hne : codimension D'.center ≠ ⊤ := by
    intro htop
    have h1 : ((Order.coheight D'.center : ℕ∞) : WithBot ℕ∞) ≤
        Order.krullDim (IrreducibleCloseds W) := Order.coheight_le_krullDim _
    rw [← codimension_eq_coheight, htop] at h1
    change _ ≤ topologicalKrullDim W at h1
    haveI := hYn.1
    haveI := hWv.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (π ≫ sY)
      hπ.isBirationalMorphism, hdim] at h1
    exact absurd h1 (by decide)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hne
  refine ⟨hηEx, c, hc.symm, ?_, ?_⟩
  · rw [codimension_center_eq_of_notMem_exceptionalSet D' D hΦ (hgen ▸ hηEx), hc]
  · rw [hcodW, ← hc] at hcod
    exact_mod_cast hcod

/-- If exactly one component `G` of `T` passes through the centre of `D'`, off `Ex(π)`, and the
centre of `D = π_* D'` has codimension two, then `v_D` is an echo. -/
private theorem exists_isEcho_of_sncIndexSet_eq_singleton {k : Type u} [Field k]
    {Y W : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    (hdim : topologicalKrullDim Y = 3) {π : W ⟶ Y} {T : Divisor W}
    (hπ : IsLogSmoothDatum sY Θ π T)
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (L.sup fun E => (E.idealSheaf.support : Set Y)))
    {D : DivisorOver k sY} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) D a) (ha2 : a < 2)
    (hcD : codimension D.center = 2) :
    haveI := hπ.isBirationalMorphism.isDominant
    ∀ D' : DivisorOver k (π ≫ sY), D'.valuation.comap (functionFieldMap π) = D.valuation →
      D'.center.isIrreducible.genericPoint ∉ (exceptionalSet π : Set W) →
      ∀ G : MMP.Mori.PrimeDivisor W, sncIndexSet T (D'.center : Set W) = {G} →
      ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
        IsEcho sY L S V j D.valuation := by
  intro D' hΦ hηEx G hG
  have hYn : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  haveI := hπ.isBirationalMorphism.isDominant
  obtain ⟨hηY, P, hPL, hηP, -⟩ :=
    mem_oneLabelSmoothLocus_of_sncIndexSet_eq_singleton hπ hT hηEx hG
  have hπη : π D'.center.isIrreducible.genericPoint = D.center.isIrreducible.genericPoint :=
    map_genericPoint_center_eq_of_comap_eq D' D hΦ
  have hVP : (D.center : Set Y) ⊆ P.support := by
    rw [← (D.center.isIrreducible.isGenericPoint_genericPoint D.center.isClosed).def, ← hπη]
    exact closure_minimal (Set.singleton_subset_iff.2 hηP)
      (SNCWeight.PrimeDivisorUnion.isClosed_support P)
  obtain ⟨j, hj⟩ := exists_isEcho_of_mem_oneLabelSmoothLocus hΘ hsupp hdim ha ha2 hPL hVP
    (topologicalKrullDim_eq_one_of_codimension_eq_two sY hdim D.center hcD) (hπη ▸ hηY)
  exact ⟨P, D.center, j, hj⟩

/-- **A positive reduced snc discrepancy below two gives an echo.** Let `(π, T)` be a
log-smooth datum of a terminal pair `(Y, Θ)` on a threefold, and `D` a divisor over `Y` with log
discrepancy `a < 2` whose centre has codimension `≥ 2`. If `v_D = π_* v_{D'}` and the log-smooth
formula `a = ∑_j m_j a_j + e` at the centre of `D'` has `e ≥ 1`, then `v_D` is an echo. -/
private theorem exists_isEcho_of_isReducedSNCDiscrepancy_ne_zero {k : Type u} [Field k]
    {Y W : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {Θ : QDivisor Y} (hΘ : IsKltTerminalPair sY Θ) {L : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsupp : Θ.support ⊆ L) (hdim : topologicalKrullDim Y = 3) {π : W ⟶ Y} {T : Divisor W}
    (hπ : IsLogSmoothDatum sY Θ π T) (hpure : IsPureCodimOne (exceptionalSet π))
    (hT : (⋃ E ∈ T.support, (E.support : Set W)) =
      (exceptionalSet π : Set W) ∪ π ⁻¹' (L.sup fun E => (E.idealSheaf.support : Set Y)))
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) (aT : MMP.Mori.PrimeDivisor W → ℝ)
    (haT : ∀ j, MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ)
      ⟨W, π, hπ.isNormalVariety, hπ.isBirationalMorphism, j⟩ (aT j))
    (hpos : ∀ j, 0 < aT j) (hexc : ∀ j, j.genericPoint ∈ (exceptionalSet π : Set W) → 1 < aT j)
    {D₀ D : DivisorOver k sY} (hD₀ : D.valuation = D₀.valuation)
    (hcod : 2 ≤ codimension D₀.center) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n (QDivisor.toRDivisor Θ) D a) (ha2 : a < 2) :
    haveI := hπ.isBirationalMorphism.isDominant
    ∀ D' : DivisorOver k (π ≫ sY), MMP.Intersection.IsCentre k (π ≫ sY) D'.valuation D'.center →
      D'.valuation.comap (functionFieldMap π) = D.valuation → ∀ e0 : ℕ,
      IsReducedSNCDiscrepancy (π ≫ sY) T D'.valuation e0 → e0 ≠ 0 →
      ∀ m : sncIndexSet T (D'.center : Set W) → ℤ, (∀ j, 1 ≤ m j) →
      a = ∑ j, (m j : ℝ) * aT j + e0 →
      ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
        IsEcho sY L S V j D.valuation := by
  classical
  intro D' hZ₀ hΦ e0 he he0 m hm1 hform'
  haveI : IsAlgClosed k := hΘ.1.1.isAlgClosed
  haveI : CharZero k := hΘ.1.1.charZero
  have hYn : IsNormalVariety k sY := hΘ.1.1.isPair.1
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have hWv : IsNormalVariety k (π ≫ sY) := hπ.isNormalVariety
  haveI : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  haveI : CompactSpace W := (hWv.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  haveI := hπ.isBirationalMorphism.isDominant
  have hterm : ∀ j : sncIndexSet T (D'.center : Set W), 0 ≤ (m j : ℝ) * aT j := fun j =>
    mul_nonneg (by exact_mod_cast (zero_le_one.trans (hm1 j))) (hpos j).le
  have hle1 : ∀ j : sncIndexSet T (D'.center : Set W), aT j ≤ (m j : ℝ) * aT j := fun j =>
    le_mul_of_one_le_left (hpos j).le (by exact_mod_cast hm1 j)
  have he1 : (1 : ℝ) ≤ e0 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 he0
  have hsum1 : ∑ j, (m j : ℝ) * aT j < 1 := by linarith
  obtain ⟨hηEx, c, hc, hcD, hc2⟩ := codimension_center_of_forall_lt_one hΘ hdim hπ hpure aT hexc
    hD₀ hcod D' hΦ fun j => (hle1 j).trans_lt
      ((Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)).trans_lt hsum1)
  have hce := he.sub_card_sncIndexSet_le hZ₀ hc
  push_cast at hform'
  rcases (by omega : (sncIndexSet T (D'.center : Set W)).card = 0 ∨
      (sncIndexSet T (D'.center : Set W)).card = 1 ∨
      2 ≤ (sncIndexSet T (D'.center : Set W)).card) with hcard0 | hcard1 | hcard
  · -- no component through the centre: `a = e_T(ξ) ≥ codim ≥ 2`
    exfalso
    rw [hcard0] at hce
    have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    have hs0 : ∑ j, (m j : ℝ) * aT j = 0 := by
      haveI : IsEmpty (sncIndexSet T (D'.center : Set W)) :=
        ⟨fun j => (Finset.card_pos.2 ⟨j.1, j.2⟩).ne' hcard0⟩
      exact Finset.sum_of_isEmpty _
    push_cast at hce
    linarith
  · -- exactly one component through the centre: an echo
    obtain ⟨G, hG⟩ := Finset.card_eq_one.1 hcard1
    rw [hcard1] at hce
    have hGJ : G ∈ sncIndexSet T (D'.center : Set W) := hG ▸ Finset.mem_singleton_self G
    have hpos' : 0 < ∑ j, (m j : ℝ) * aT j :=
      lt_of_lt_of_le (mul_pos (by exact_mod_cast (zero_lt_one.trans_le (hm1 ⟨G, hGJ⟩)))
        (hpos G)) (Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ ⟨G, hGJ⟩))
    have hc2' : c = 2 := by
      have : (c : ℝ) < 3 := by push_cast at hce; linarith
      have : c < 3 := by exact_mod_cast this
      omega
    exact exists_isEcho_of_sncIndexSet_eq_singleton hΘ hsupp hdim hπ hT ha ha2
      (by rw [hcD, hc2']; rfl) D' hΦ hηEx G hG
  · -- two components through the centre: excluded by terminality
    exfalso
    have h := one_lt_sum_of_two_le_card hΘ hπ hK aT haT hηEx hcard
    have : ∑ j ∈ sncIndexSet T (D'.center : Set W), aT j ≤ ∑ j, (m j : ℝ) * aT j := by
      rw [← Finset.sum_coe_sort]
      exact Finset.sum_le_sum fun j _ => hle1 j
    linarith

/-! ### Finiteness -/

/-- If `m a_j < 2` with all `a_i > 0`, then `m ≤ ⌈∑_{i ∈ s} 2 / a_i⌉ + 1` for any `s ∋ j`. -/
private theorem le_ceil_sum_add_one_of_mul_lt_two {ι : Type*} {s : Finset ι} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {j : ι} (hj : j ∈ s) {m : ℝ} (h : m * a j < 2) :
    m ≤ ((⌈∑ i ∈ s, 2 / a i⌉₊ + 1 : ℕ) : ℝ) := by
  have h2 : m < 2 / a j := by rwa [lt_div_iff₀ (ha j)]
  have h3 : 2 / a j ≤ ∑ i ∈ s, 2 / a i :=
    Finset.single_le_sum (fun i _ => (div_pos two_pos (ha i)).le) hj
  have h4 := Nat.le_ceil (∑ i ∈ s, 2 / a i)
  push_cast
  linarith

/-- **Finitely many non-echoes below log discrepancy two.** Let `(Y, Θ)` be a terminal pair on a
projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors containing
the support of `Θ`. Then the normalized divisorial valuations `ξ` of `ℂ(Y)`, exceptional over
`Y`, with `a(ξ; Y, Θ) < 2`, which are not an echo (`MMP.Fourfold.IsEcho`) of any order of any
label `S ∈ L` at any curve, form a finite set. -/
@[mmp "lem_mmp_indexd_echoes"]
public theorem finite_setOf_not_isEcho
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField ℤᵐ⁰ |
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sY ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ sY ξ ∧
        (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          IsEcho sY L S V j ξ}.Finite := by
  classical
  have hYn : IsNormalVariety ℂ sY := hΘ.1.1.isPair.1
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  obtain ⟨W, π, T, hπ, hpure, hT, -⟩ := exists_isLogSmoothDatum hΘ.1 L hsupp
  obtain ⟨n, K, hK, aT, haT, hpos, hexc, -⟩ := exists_logDiscrepancy_primeDivisor hΘ hπ
  have hWv : IsNormalVariety ℂ (π ≫ sY) := hπ.isNormalVariety
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sY) := hWv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sY)
  haveI : IsNormal W := hWv.2
  haveI : CompactSpace W := (hWv.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian W := {}
  haveI := hπ.isBirationalMorphism.isDominant
  set M : ℕ := ⌈∑ j ∈ T.support, 2 / aT j⌉₊ + 1 with hM
  refine ((finite_setOf_isReducedSNCDiscrepancy_zero (π ≫ sY) T (M := M)
    (Nat.le_add_left 1 _)).image fun ξ => ξ.comap (functionFieldMap π)).subset ?_
  rintro ξ ⟨-, ⟨D₀, -, hξD₀, hcod⟩, ⟨a, ha2, n', D, hDξ, ha⟩, hnot⟩
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK.topologicalKrullDim_eq
  -- the log-smooth formula at the centre `c_W(ξ)`, with `ξ(Tⱼ) = mⱼ ≥ 1`
  obtain ⟨D', hZ₀, hΦ, e0, he, hrest⟩ := exists_logSmoothFormula_at_center hπ aT haT ha
  refine ⟨D'.valuation, ?_, hΦ.trans hDξ⟩
  set η := D'.center.isIrreducible.genericPoint
  obtain ⟨z, m, hz, hm1, hm, hform'⟩ := hrest
  have hgen : η = D'.f D'.E.genericPoint := genericPoint_center_eq D'
  have hterm : ∀ j : sncIndexSet T (D'.center : Set W), 0 ≤ (m j : ℝ) * aT j := fun j =>
    mul_nonneg (by exact_mod_cast (zero_le_one.trans (hm1 j))) (hpos j).le
  by_cases he0 : e0 = 0
  · -- `e_T(ξ) = 0`: `ξ` lies in the finite set of zero-error valuations of bounded order
    subst he0
    refine ⟨by simpa using he, fun Z' hZ' j hj z' hz' => ?_⟩
    obtain rfl : Z' = D'.center := by
      obtain ⟨D'', -, hξD'', rfl⟩ := hZ'
      exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hWv.1 hξD''.symm
    have hval : D'.valuation (algebraMap _ W.functionField z') =
        WithZero.exp (-m ⟨j, hj⟩) := by
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 (hz'.symm.trans (hz ⟨j, hj⟩))
      rw [← hm, ← hu, map_mul, map_mul, MMP.Positivity.DivisorOver.valuation_algebraMap_unit_eq_one
        _ (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' η hgen) u, mul_one]
    rw [hval, WithZero.exp_le_exp, neg_le_neg_iff]
    have h1 : (m ⟨j, hj⟩ : ℝ) * aT j < 2 := by
      have := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ ⟨j, hj⟩)
      push_cast at hform'
      linarith
    exact_mod_cast (show (m ⟨j, hj⟩ : ℝ) ≤ M from
      hM ▸ le_ceil_sum_add_one_of_mul_lt_two hpos (Finset.mem_filter.1 hj).1 h1)
  · exact (hnot (hDξ ▸ exists_isEcho_of_isReducedSNCDiscrepancy_ne_zero hΘ hsupp hdim hπ hpure
      hT hK aT haT hpos hexc (hDξ.trans hξD₀) hcod ha ha2 D' hZ₀ hΦ e0 he he0 m hm1
      hform')).elim

end MMP.Fourfold

end
