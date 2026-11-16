module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierCoheight
import MMP.AlgebraicGeometry.Resolution.Principalization.CanonicalFunctor
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.AntiAmpleExceptional
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.ProjectiveSpace.ZeroLocusFactorization
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.OrderPullback
import MMP.AlgebraicGeometry.Divisor.EffectiveCartierDivisorSupport
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization

/-!
# A dominating snc model with an antiample exceptional divisor

Let `p : Y ⟶ X` be a projective birational morphism of normal projective complex fourfolds and
`C ⊆ X` a closed subset of dimension at most one. There is a projective `r : Z ⟶ Y` with `Z`
smooth and projective such that `Ex(p ∘ r)` and `(p ∘ r)⁻¹(C)` are supports of reduced snc
divisors, some `D = ∑ mᵢ Eᵢ` over the components of `Ex(p ∘ r)`, all `mᵢ > 0`, has `-D`
Cartier and relatively ample, and `p ∘ r` is an isomorphism over the points off `C` over which
`p` is an isomorphism onto the smooth locus of `Y`.

The construction resolves `Y` by `q : Y₀ ⟶ Y`, blows up `X` along the product of the colon
ideal of the coordinate ratios of `Y₀ ⊆ ℙⁿ_X` with the ideals of the non-biregular locus and of
`C`, so that the blow-up dominates `Y₀`, and principalizes the pulled-back ideal on the smooth
`Y₀` (Kollár's canonical principalization). Kollár's Lemma 2.9 and [Stacks, Tag 0C4K] give the
antiample exceptional divisor; Krull's principal ideal theorem identifies `(p ∘ r)⁻¹(C)` with a
union of the exceptional components.

## Main results

* `MMP.Fourfold.exists_isResolution_comp_isSNC_isRelativelyAmple_neg_and_mem_biregularLocus`:
  the dominating model, an isomorphism over the points off `C` over which `p` is an isomorphism
  onto the smooth locus of `Y`.
* `MMP.Fourfold.exists_isResolution_comp_isSNC_isRelativelyAmple_neg`: the dominating model.
* `MMP.Fourfold.exists_principalization_isRelativelyAmple_neg`: for a projective resolution
  `f₀ : W₀ ⟶ S`, an ideal `K` on `S`, a further ideal `M` and an ordered snc divisor `E` on `W₀`,
  the canonical principalization of `(W₀, I 𝒪_{W₀} · M, E)` for a multiple `I` of `K` whose
  blow-up dominates `W₀`, with an antiample divisor over `S` on its exceptional components.

## Implementation notes

The source blows up the first Fitting ideal of `f₀_* L` for a relatively very ample `L` and then
normalizes; here the dominating blow-up is that of the colon
ideal of the coordinate ratios, and no normalization is needed because the principalization is
carried out on the smooth `Y₀`. The resolution `q` is
`MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap`, an isomorphism
over the smooth locus of `Y`. In `exists_principalization_isRelativelyAmple_neg` the divisor `D`
is assembled in two steps of [Stacks, Tag 0C4K], first over the blow-up of `I 𝒪_{W₀} · M` (which
makes `D` positive on the components over `V(I 𝒪_{W₀} M)`) and then over the blow-up of `I`;
the components of `D` over the double locus of `E` and off `V(I 𝒪_{W₀} M)` are not controlled.
The instance `AlgebraicGeometry.IsVariety.toIsIntegral` stays enabled for the main result: its
proof infers integrality of the model from that instance, and no binder of the statement is an
`IsVariety` instance, so the statement does not depend on it.

## References

* [J. Kollár, *Lectures on resolution of singularities*][Kollar2007], 2.9, 3.16, 3.72
* [R. Hartshorne, *Algebraic geometry*, II.7.17]
* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 07ZV](https://stacks.math.columbia.edu/tag/07ZV)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Resolution Limits Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.ProjectiveSpaceChartRatio

/-! ### Colon ideals -/

section Colon

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] {ι : Type*} (f : ι → K)

/-- The multipliers `(R : M)` of the fractional ideal `M` generated by the `f k`. -/
private def colonSet : Set K := {c | ∀ k, c * f k ∈ (algebraMap R K).range}

/-- The fractional ideal `M·(R : M)`, which lies in `R`. -/
private def colonSubmodule : Submodule R K :=
  Submodule.span R {x | ∃ c ∈ colonSet R f, ∃ k, x = c * f k}

/-- The colon ideal `M·(R : M)`, as an ideal of `R`. -/
private def colonIdeal : Ideal R := (colonSubmodule R f).comap (Algebra.linearMap R K)

variable {R f}

private theorem mem_colonIdeal {a : R} :
    a ∈ colonIdeal R f ↔ algebraMap R K a ∈ colonSubmodule R f :=
  Iff.rfl

private theorem colonSubmodule_le_range :
    colonSubmodule R f ≤ LinearMap.range (Algebra.linearMap R K) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨c, hc, k, rfl⟩
  obtain ⟨a, ha⟩ := hc k
  exact ⟨a, ha⟩

private theorem map_colonIdeal [Finite ι] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization M S] [Algebra S K] [IsScalarTower R S K]
    (hS : Function.Injective (algebraMap S K)) :
    (colonIdeal R f).map (algebraMap R S) = colonIdeal S f := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap S K (algebraMap R S a) ∈ colonSubmodule S f
    rw [← IsScalarTower.algebraMap_apply]
    have hle : (colonSubmodule R f).restrictScalars R ≤ (colonSubmodule S f).restrictScalars R := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨c, hc, k, rfl⟩
      refine Submodule.subset_span ⟨c, fun k' => ?_, k, rfl⟩
      obtain ⟨b, hb⟩ := hc k'
      exact ⟨algebraMap R S b, by rw [← hb, ← IsScalarTower.algebraMap_apply]⟩
    exact hle ha
  · intro a ha
    have key : ∀ v ∈ colonSubmodule S f, ∃ m ∈ M, (m : R) • v ∈ colonSubmodule R f := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, k, rfl⟩ := hx
        have : ∀ k', ∃ m ∈ M, ((m : R) • c) * f k' ∈ (algebraMap R K).range := by
          intro k'
          obtain ⟨s, hs⟩ := hc k'
          obtain ⟨⟨x, m⟩, hxm⟩ := IsLocalization.surj M s
          refine ⟨m, m.2, x, ?_⟩
          rw [smul_mul_assoc, ← hs, Algebra.smul_def, IsScalarTower.algebraMap_apply R S K,
            IsScalarTower.algebraMap_apply R S K, ← map_mul, mul_comm, ← hxm]
        choose m hm hm' using this
        cases nonempty_fintype ι
        refine ⟨∏ k', m k', prod_mem fun k' _ => hm k', Submodule.subset_span
          ⟨(∏ k', m k' : R) • c, fun k' => ?_, k, by rw [smul_mul_assoc]⟩⟩
        obtain ⟨y, hy⟩ := hm' k'
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k'), mul_smul, smul_mul_assoc, ← hy]
        exact ⟨_ * y, by rw [map_mul, Algebra.smul_def]⟩
      | zero => exact ⟨1, one_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨m', hm', hmy⟩ := hy
        refine ⟨m * m', mul_mem hm hm', ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]
          exact Submodule.smul_mem _ _ hmx
        · rw [mul_smul]
          exact Submodule.smul_mem _ _ hmy
      | smul s x _ hx =>
        obtain ⟨m, hm, hmx⟩ := hx
        obtain ⟨⟨y, m'⟩, hym⟩ := IsLocalization.surj M s
        refine ⟨m' * m, mul_mem m'.2 hm, ?_⟩
        have : ((m' * m : R)) • (s • x) = y • ((m : R) • x) := by
          rw [← algebraMap_smul (A := S) (R := R), smul_smul, ← algebraMap_smul (A := S) (R := R) y,
            ← algebraMap_smul (A := S) (R := R) (m : R), smul_smul]
          congr 1
          simp only at hym
          rw [map_mul]
          linear_combination (algebraMap R S m) * hym
        rw [this]
        exact Submodule.smul_mem _ _ hmx
    obtain ⟨m, hm, hmv⟩ := key _ ha
    obtain ⟨x, hx⟩ := colonSubmodule_le_range hmv
    have hx' : algebraMap R S x = algebraMap R S m * a := by
      apply hS
      rw [← IsScalarTower.algebraMap_apply, map_mul, ← IsScalarTower.algebraMap_apply]
      simpa [Algebra.smul_def] using hx
    have hxI : x ∈ colonIdeal R f := by
      rw [mem_colonIdeal]
      have : algebraMap R K x = (m : R) • algebraMap S K a := by simpa using hx
      rwa [this]
    have hu : IsUnit (algebraMap R S m) := IsLocalization.map_units S ⟨m, hm⟩
    have : a = hu.unit⁻¹ * algebraMap R S x := by
      rw [hx', ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hxI)

end Colon

/-! ### The colon ideal sheaf -/

section Sheaf

variable {Y : Scheme.{u}} [IsIntegral Y] {ι : Type} [Finite ι] (f : ι → Y.functionField)

open Classical in
/-- The colon ideal sheaf `M·(𝒪 : M)` of the fractional ideal generated by the `f k`. -/
private noncomputable def colonIdealSheaf : Y.IdealSheafData where
  ideal U := if h : Nonempty U.1 then (haveI := h; colonIdeal Γ(Y, U.1) f) else ⊤
  map_ideal_basicOpen U g := by
    by_cases hU : Nonempty U.1
    · by_cases hg : Nonempty (Y.basicOpen g)
      · have hg' : Nonempty (Y.affineBasicOpen g).1 := hg
        rw [dif_pos hU, dif_pos hg']
        have hloc := U.2.isLocalization_basicOpen g
        refine @map_colonIdeal Γ(Y, U.1) Y.functionField _ _ _ ι f _ (Submonoid.powers g)
          Γ(Y, Y.basicOpen g) _ _ hloc _ ?_ (Y.germToFunctionField_injective _)
        apply IsScalarTower.of_algebraMap_eq'
        ext a
        exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le g)) _ _ a).symm
      · have hbot : Y.basicOpen g = ⊥ := by
          ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hg ⟨⟨x, hx⟩⟩
        haveI : Subsingleton Γ(Y, Y.basicOpen g) := hbot ▸ inferInstance
        exact Subsingleton.elim _ _
    · have : ¬ Nonempty (Y.affineBasicOpen g).1 := fun ⟨x⟩ => hU ⟨⟨x.1, Y.basicOpen_le g x.2⟩⟩
      rw [dif_neg hU, dif_neg this]
      exact Ideal.map_top _

private theorem colonIdealSheaf_ideal (U : Y.affineOpens) [h : Nonempty U.1] :
    (colonIdealSheaf f).ideal U = colonIdeal Γ(Y, U.1) f := by
  classical
  exact dif_pos h

private theorem stalk_colonIdealSheaf (y : Y) :
    IdealSheafData.stalk (colonIdealSheaf f) y = colonIdeal (Y.presheaf.stalk y) f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨U, hU⟩ hyU]
  rw [colonIdealSheaf_ideal]
  have hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  letI := Y.presheaf.algebra_section_stalk ⟨y, hyU⟩
  exact @map_colonIdeal Γ(Y, U) Y.functionField _ _ _ ι f _
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (Y.presheaf.stalk y) _ _ hloc _
    (functionField_isScalarTower Y U ⟨y, hyU⟩) (IsFractionRing.injective _ _)

end Sheaf

/-! ### The standard charts of `ℙⁿ_ℤ` -/

attribute [local instance] MvPolynomial.gradedAlgebra

section Charts

variable {n : ℕ}

/-- The integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`. -/
private noncomputable abbrev PZ (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n)

/-- The standard chart `D₊(T_j)`. -/
private noncomputable abbrev chartOpen (n : ℕ) (j : Fin (n + 1)) : (PZ.{u} n).Opens :=
  Proj.basicOpen (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j)

/-- The ratio `T_k / T_j` as a germ at a point of the chart `D₊(T_j)`. -/
private noncomputable def ratio {x : PZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (PZ.{u} n).presheaf.stalk x :=
  (PZ.{u} n).presheaf.germ _ x hx
    (Proj.awayToSection _ _ (coordFracAt (ULift.{u} ℤ) n j k))

private theorem val_stalkIso'_ratio {x : PZ.{u} n} {j : Fin (n + 1)}
    (hx : x ∈ chartOpen n j) (k : Fin (n + 1)) :
    (Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x (ratio hx k)).val =
      Localization.mk (MvPolynomial.X k)
        ⟨MvPolynomial.X j, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hx)⟩ := by
  rw [ratio]
  erw [Proj.stalkIso'_germ]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [coordFracAt, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk',
    ← Localization.mk_eq_mk']
  simp

private theorem ratio_mul {x : PZ.{u} n} {j m : Fin (n + 1)} (hj : x ∈ chartOpen n j)
    (hm : x ∈ chartOpen n m) (k : Fin (n + 1)) :
    ratio hm k = ratio hj k * ratio hm j := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [map_mul, HomogeneousLocalization.val_mul, val_stalkIso'_ratio, val_stalkIso'_ratio,
    val_stalkIso'_ratio]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]; ring⟩

private theorem ratio_self {x : PZ.{u} n} {j : Fin (n + 1)} (hj : x ∈ chartOpen n j) :
    ratio hj j = 1 := by
  apply (Proj.stalkIso' _ x).injective
  apply HomogeneousLocalization.val_injective
  erw [(Proj.stalkIso' (polyGrading (ULift.{u} ℤ) n) x).map_one, HomogeneousLocalization.val_one,
    val_stalkIso'_ratio]
  exact Localization.mk_self ⟨_, (show MvPolynomial.X j ∉ x.asHomogeneousIdeal from hj)⟩

private theorem germ_mem_closure_ratio {x : PZ.{u} n} {j : Fin (n + 1)} (hx : x ∈ chartOpen n j)
    (b : Γ(PZ.{u} n, chartOpen n j)) :
    (PZ.{u} n).presheaf.germ _ x hx b ∈ Subring.closure (Set.range (ratio hx)) := by
  obtain ⟨s, rfl⟩ : ∃ s, Proj.awayToSection _ _ s = b :=
    ⟨(Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv b, by
      rw [← CommRingCat.comp_apply]
      exact congrArg (fun φ => φ b)
        (congrArg CommRingCat.Hom.hom
          (Proj.basicOpenIsoAway _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos).inv_hom_id)⟩
  obtain ⟨p, rfl⟩ := chartHom_surjective (ULift.{u} ℤ) n j s
  set ψ : HomogeneousLocalization.Away (polyGrading (ULift.{u} ℤ) n) (MvPolynomial.X j) →+*
      (PZ.{u} n).presheaf.stalk x :=
    ((PZ.{u} n).presheaf.germ _ x hx).hom.comp (Proj.awayToSection _ _).hom
  change ψ (chartHom _ n j p) ∈ _
  have : ψ.comp (chartHom (ULift.{u} ℤ) n j) =
      MvPolynomial.eval₂Hom (ψ.comp (coeffToAway _ n j)) (fun k => ψ (chartCoord _ n j k)) := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  rw [← RingHom.comp_apply, this]
  have hc : ∀ c : ULift.{u} ℤ, (ψ.comp (coeffToAway _ n j)) c ∈
      Subring.closure (Set.range (ratio hx)) := fun c => by
    rw [show c = ((c.down : ℤ) : ULift.{u} ℤ) from by ext; simp, map_intCast]
    exact intCast_mem _ _
  exact MvPolynomial.eval₂_mem (fun c _ => hc _) (fun k => Subring.subset_closure ⟨k.1, rfl⟩)

end Charts

/-! ### The coordinate ratios on a closed subscheme of `ℙⁿ_Y` -/

section Ratios

variable {Y Z : Scheme.{u}} {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y)

/-- The projection of `Z ⊆ ℙⁿ_Y` to the integral model `ℙⁿ_ℤ`. -/
private noncomputable abbrev toPZ : Z ⟶ PZ.{u} n :=
  i ≫ (pullback.snd (terminal.from Y) (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
    projectiveSpaceOver n Y ⟶ PZ.{u} n)

/-- The germ at `z` of the pulled-back ratio `T_k / T_j`, for `z` on the chart `T_j ≠ 0`. -/
private noncomputable def gRatio (z : Z) {j : Fin (n + 1)} (hz : toPZ i z ∈ chartOpen n j)
    (k : Fin (n + 1)) : Z.presheaf.stalk z :=
  (toPZ i).stalkMap z (ratio hz k)

private theorem gRatio_mul (z : Z) {j m : Fin (n + 1)} (hj : toPZ i z ∈ chartOpen n j)
    (hm : toPZ i z ∈ chartOpen n m) (k : Fin (n + 1)) :
    gRatio i z hm k = gRatio i z hj k * gRatio i z hm j := by
  rw [gRatio, gRatio, gRatio, ratio_mul hj hm k, map_mul]

private theorem gRatio_self (z : Z) {j : Fin (n + 1)} (hj : toPZ i z ∈ chartOpen n j) :
    gRatio i z hj j = 1 := by
  rw [gRatio, ratio_self, map_one]

private theorem algebraMap_gRatio [IsIntegral Z] (z : Z) {j : Fin (n + 1)}
    (hz : toPZ i z ∈ chartOpen n j) (hη : toPZ i (genericPoint Z) ∈ chartOpen n j)
    (k : Fin (n + 1)) :
    algebraMap (Z.presheaf.stalk z) Z.functionField (gRatio i z hz k) =
      gRatio i (genericPoint Z) hη k := by
  have h : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  change (Z.presheaf.stalkSpecializes h).hom ((toPZ i).stalkMap z (ratio hz k)) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, gRatio, ratio, ratio]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply (PZ.{u} n).presheaf hz _ _

end Ratios

/-! ### Generic points -/

section GenericPoint

variable {X Y : Scheme.{u}}

/-- A morphism to an irreducible scheme which hits the generic point is dominant. -/
private theorem isDominant_of_map_eq_genericPoint [IrreducibleSpace Y] (φ : X ⟶ Y) {x : X}
    (hx : φ x = genericPoint Y) : IsDominant φ := ⟨by
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact closure_mono (by rintro _ rfl; exact ⟨_, hx⟩)⟩

/-- An ideal sheaf on an irreducible scheme which is a unit at the generic point is nonzero. -/
private theorem ne_bot_of_genericPoint_notMem_support [IrreducibleSpace X]
    {I : X.IdealSheafData} (h : genericPoint X ∉ I.support) : I ≠ ⊥ := by
  rintro rfl
  exact h (by rw [Scheme.IdealSheafData.support_bot]; trivial)

/-- The pull-back of an ideal sheaf along a dominant morphism of irreducible schemes is a unit at
the generic point if the ideal sheaf is. -/
private theorem genericPoint_notMem_support_comap [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsDominant f] {I : Y.IdealSheafData} (h : genericPoint Y ∉ I.support) :
    genericPoint X ∉ (I.comap f).support := by
  rw [Scheme.IdealSheafData.support_comap]
  change f (genericPoint X) ∉ I.support
  rwa [map_genericPoint_of_isDominant f]

end GenericPoint

/-! ### Blow-ups of integral schemes -/

section BlowUp

variable {S : Scheme.{u}} [IsIntegral S]

/-- The blow-up of an ideal sheaf whose cosupport misses the generic point is dominant: it is an
isomorphism over the dense open complement of the cosupport. -/
private theorem isDominant_blowUpToBase (I : S.IdealSheafData)
    (hgen : genericPoint S ∉ I.support) : IsDominant (blowUpToBase I) := by
  haveI := isIso_blowUp_restrict_compl_support I
  have hsub : (I.support.compl : Set S) ⊆ Set.range (blowUpToBase I) := by
    intro y hy
    obtain ⟨z, hz⟩ := (blowUpToBase I ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
    exact ⟨(blowUpToBase I ⁻¹ᵁ I.support.compl).ι z,
      (morphismRestrict_base_coe (blowUpToBase I) I.support.compl z).symm.trans
        (congrArg Subtype.val hz)⟩
  exact ⟨Dense.mono hsub (I.support.compl.isOpen.dense ⟨_, hgen⟩)⟩

/-- On the blow-up of an ideal sheaf whose cosupport misses the generic point, the only point over
the generic point is the generic point. -/
private theorem eq_genericPoint_of_blowUpToBase_eq (I : S.IdealSheafData)
    (hgen : genericPoint S ∉ I.support) [IsIntegral (blowUp I)] (t : blowUp I)
    (ht : blowUpToBase I t = genericPoint S) : t = genericPoint (blowUp I) := by
  haveI := isDominant_blowUpToBase I hgen
  haveI := isIso_blowUp_restrict_compl_support I
  have h1 : blowUpToBase I (genericPoint (blowUp I)) = genericPoint S :=
    map_genericPoint_of_isDominant (blowUpToBase I)
  have hV : t ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
    change blowUpToBase I t ∈ I.support.compl
    rwa [ht]
  have hV' : genericPoint (blowUp I) ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := by
    change blowUpToBase I _ ∈ I.support.compl
    rwa [h1]
  have := (blowUpToBase I ∣_ I.support.compl).homeomorph.injective
    (a₁ := ⟨_, hV⟩) (a₂ := ⟨_, hV'⟩) (Subtype.ext
      (((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV⟩).trans ht).trans
        ((morphismRestrict_base_coe (blowUpToBase I) I.support.compl ⟨_, hV'⟩).trans h1).symm))
  exact congrArg Subtype.val this

end BlowUp

/-! ### The ideal sheaf -/

section Core

/-- If `ρ(b_k) = g_k ρ(b_j)` for all `k`, the image of the ideal generated by the `b_k` is
generated by `ρ(b_j)`. -/
private theorem map_span_range_eq_span_singleton {A B : Type*} [CommRing A] [CommRing B]
    {ι : Type*} (ρ : A →+* B) (b : ι → A) (g : ι → B) (j : ι)
    (h : ∀ k, ρ (b k) = g k * ρ (b j)) :
    (Ideal.span (Set.range b)).map ρ = Ideal.span {ρ (b j)} := by
  rw [Ideal.map_span, ← Set.range_comp]
  refine le_antisymm (Ideal.span_le.2 ?_)
    ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨j, rfl⟩))
  rintro _ ⟨k, rfl⟩
  rw [Function.comp_apply, h k]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- If `ρ(b_k) = g_k ρ(b_j)` with `ρ(b_j) ≠ 0`, `ρ` local into a domain, and the `b_k` generate a
principal ideal, then every `g_k` lies in the image of `ρ`. -/
private theorem mem_range_of_span_singleton_eq {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    {ι : Type*} (ρ : A →+* B) [IsLocalHom ρ] (b : ι → A) (g : ι → B) (j : ι) (t : A)
    (ht : Ideal.span {t} = Ideal.span (Set.range b)) (h : ∀ k, ρ (b k) = g k * ρ (b j))
    (hne : ρ (b j) ≠ 0) (k : ι) : g k ∈ Set.range ρ := by
  have hspan := map_span_range_eq_span_singleton ρ b g j h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1
    (show b j ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨j, rfl⟩)
  have htm : ρ t ∈ Ideal.span {ρ (b j)} :=
    hspan ▸ Ideal.mem_map_of_mem ρ (ht ▸ Ideal.mem_span_singleton_self t)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 htm
  have hav : ρ a * v = 1 :=
    mul_right_cancel₀ hne (by rw [mul_assoc, hv, ← map_mul, ha, one_mul])
  have hau : IsUnit a := (isUnit_map_iff ρ a).1 (isUnit_iff_exists_inv.2 ⟨v, hav⟩)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1
    (show b k ∈ Ideal.span {t} from ht ▸ Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨c * ↑hau.unit⁻¹, mul_right_cancel₀ hne ?_⟩
  have hinv : ρ ↑hau.unit⁻¹ * ρ a = 1 := by
    rw [← map_mul, hau.val_inv_mul, map_one]
  rw [← h k, ← hc, ← ha, map_mul, map_mul, map_mul]
  linear_combination (ρ c * ρ t) * hinv

/-- The stalk of an effective Cartier divisor is principal. -/
private theorem exists_stalk_eq_span_singleton {X : Scheme.{u}} (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ t, IdealSheafData.stalk J x = Ideal.span {t} := by
  obtain ⟨U, hU, hxU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hf, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

/-- **The stalks of `ℙⁿ_Y` on a standard chart.** At a point `x` of `ℙⁿ_Y = Y ×_ℤ ℙⁿ_ℤ` on the
chart `T_j ≠ 0`, a subring of the stalk which contains the functions from `Y`, the ratios
`T_k / T_j` and the inverses of its units is the whole stalk. -/
private theorem eq_top_of_subring_stalk_pullback {Y : Scheme.{u}} {n : ℕ} (f : Y ⟶ ⊤_ Scheme)
    (g : PZ.{u} n ⟶ ⊤_ Scheme) (x : ↥(pullback f g)) {j : Fin (n + 1)}
    (hx : pullback.snd f g x ∈ chartOpen n j) (T : Subring ((pullback f g).presheaf.stalk x))
    (h1 : ∀ a, (pullback.fst f g).stalkMap x a ∈ T)
    (h2 : ∀ k, (pullback.snd f g).stalkMap x (ratio hx k) ∈ T)
    (h3 : ∀ v : ((pullback f g).presheaf.stalk x)ˣ, v.1 ∈ T → (v⁻¹).1 ∈ T) :
    T = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (pullback.fst f g x)) isOpen_univ
  have hV : IsAffineOpen (chartOpen n j) :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_one (ULift.{u} ℤ) n j) Nat.one_pos
  have hW := Stacks.AlgebraicGeometry.isAffineOpen_pullback_inf f g hU hV
  have hxW : x ∈ pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j := ⟨hyU, hx⟩
  have hgerm : ∀ s, ((pullback f g).presheaf.germ _ x hxW).hom s ∈ T := by
    have htop := Stacks.AlgebraicGeometry.subring_eq_top_of_pullback_inf f g hU hV rfl
      inf_le_left inf_le_right (T.comap ((pullback f g).presheaf.germ _ x hxW).hom)
      (fun a => ?_) (fun b => ?_)
    · exact fun s =>
        (htop ▸ Subring.mem_top s : s ∈ T.comap ((pullback f g).presheaf.germ _ x hxW).hom)
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.fst f g) U x hyU a
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      exact h1 _
    · have := Scheme.Hom.germ_stalkMap_apply (pullback.snd f g) (chartOpen n j) x hx b
      rw [Subring.mem_comap, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply]
      erw [← this]
      have hle : Subring.closure (Set.range (ratio hx)) ≤
          T.comap ((pullback.snd f g).stalkMap x).hom :=
        Subring.closure_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k)
      exact hle (germ_mem_closure_ratio hx b)
  letI := (pullback f g).presheaf.algebra_section_stalk (U := pullback.fst f g ⁻¹ᵁ U ⊓
    pullback.snd f g ⁻¹ᵁ chartOpen n j) ⟨x, hxW⟩
  haveI := hW.isLocalization_stalk ⟨x, hxW⟩
  refine top_unique fun s _ => ?_
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl s
  dsimp only
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  have hu := IsLocalization.map_units ((pullback f g).presheaf.stalk x) t
  have hinv : IsLocalization.mk' ((pullback f g).presheaf.stalk x)
      (1 : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ chartOpen n j)) t =
      (hu.unit⁻¹).1 := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [IsUnit.unit_spec, mul_comm, IsLocalization.mk'_spec, map_one]
  rw [hinv]
  exact T.mul_mem (hgerm a) (h3 _ (hgerm t))

/-- A valuation subring dominating the image of a local ring `A` in its fraction field sends the
maximal ideal of `A` into its nonunits. -/
theorem algebraMap_mem_nonunits_of_range_le {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] {V : ValuationSubring K}
    (hV : LocalSubring.range (algebraMap A K) ≤ V.toLocalSubring) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : algebraMap A K a ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hV.1 ⟨a, rfl⟩, (IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_⟩
  haveI := hV.2
  obtain ⟨⟨b, ⟨a', rfl⟩⟩, hb⟩ :=
    isUnit_iff_exists_inv.1 (isUnit_of_map_unit (Subring.inclusion hV.1) ⟨_, ⟨a, rfl⟩⟩ hu)
  have hb' : algebraMap A K (a * a') = algebraMap A K 1 := by
    rw [map_mul, map_one]
    exact congrArg Subtype.val hb
  exact (IsLocalRing.mem_maximalIdeal _).1 ha
    (isUnit_iff_exists_inv.2 ⟨a', IsFractionRing.injective _ _ hb'⟩)

/-- A ring homomorphism from a local ring into a field, landing in a valuation subring and
sending the maximal ideal to nonunits, restricts to a local homomorphism into that subring. -/
theorem isLocalHom_codRestrict_of_mem_nonunits {A K : Type*} [CommRing A] [IsLocalRing A]
    [Field K] {V : ValuationSubring K} (f : A →+* K) (h₁ : ∀ a, f a ∈ V)
    (h₂ : ∀ a ∈ IsLocalRing.maximalIdeal A, f a ∈ V.nonunits) :
    IsLocalHom (f.codRestrict V h₁) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨_, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1
    (h₂ a ((IsLocalRing.mem_maximalIdeal _).2 hna))
  exact (IsLocalRing.mem_maximalIdeal _).1 hm ha

/-- For a valuation subring `V` of the function field of an integral scheme `Z` containing the
local ring at `p`, the induced map `Spec V ⟶ Z` restricts on the generic point of `Spec V` to the
generic point of `Z`. -/
theorem specMap_algebraMap_comp_fromSpecStalk {Z : Scheme.{u}} [IsIntegral Z] (p : Z)
    {V : ValuationSubring Z.functionField}
    (h : ∀ a : Z.presheaf.stalk p, algebraMap _ Z.functionField a ∈ V) :
    Spec.map (CommRingCat.ofHom (algebraMap V Z.functionField)) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap _ Z.functionField).codRestrict V h)) ≫
          Z.fromSpecStalk p = Z.fromSpecStalk (genericPoint Z) := by
  have hc : CommRingCat.ofHom ((algebraMap _ Z.functionField).codRestrict V h) ≫
      CommRingCat.ofHom (algebraMap V Z.functionField) =
        Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) := by
    ext a; rfl
  rw [← Spec.map_comp_assoc, hc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- If the local ring of an integral scheme `Z` at `p` is dominated by a valuation subring `V` of
its function field, the induced map `Spec V ⟶ Z` sends the closed point to `p`. -/
theorem specMap_codRestrict_fromSpecStalk_closedPoint {Z : Scheme.{u}} [IsIntegral Z] (p : Z)
    {V : ValuationSubring Z.functionField}
    (h : ∀ a : Z.presheaf.stalk p, algebraMap _ Z.functionField a ∈ V)
    (hloc : IsLocalHom ((algebraMap _ Z.functionField).codRestrict V h)) :
    (Spec.map (CommRingCat.ofHom ((algebraMap _ Z.functionField).codRestrict V h)) ≫
      Z.fromSpecStalk p) (IsLocalRing.closedPoint V) = p := by
  haveI : IsLocalHom (CommRingCat.ofHom ((algebraMap _ Z.functionField).codRestrict V h)).hom :=
    hloc
  change Z.fromSpecStalk p (Spec.map (CommRingCat.ofHom
    ((algebraMap _ Z.functionField).codRestrict V h)) (IsLocalRing.closedPoint V)) = p
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- **Valuative uniqueness for points.** Let `φ : Z ⟶ X` be a separated dominant morphism of
integral schemes all of whose maps on local rings are surjective. Then `φ` is injective: two
points over the same point of `X` have the same local ring inside the function field of `Z`, so
a valuation ring dominating it gives two lifts in one valuative square for `φ`. -/
private theorem injective_of_surjective_stalkMap {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (φ : Z ⟶ X) [IsSeparated φ] [IsDominant φ]
    (hsurj : ∀ z, Function.Surjective (φ.stalkMap z)) : Function.Injective φ := by
  intro z z' hzz
  obtain ⟨V, hV⟩ :=
    (LocalSubring.range
      (algebraMap (Z.presheaf.stalk z) Z.functionField)).exists_le_valuationSubring
  -- domination of the local rings of `X`, read in the function field of `Z`
  let HX : X → Prop := fun w => ∀ c : X.presheaf.stalk w,
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V
  let HX' : X → Prop := fun w => ∀ c ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk w),
    functionFieldMap φ (algebraMap _ X.functionField c) ∈ V.nonunits
  let D : Z → Prop := fun p => (∀ a : Z.presheaf.stalk p, algebraMap _ Z.functionField a ∈ V) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk p), algebraMap _ Z.functionField a ∈ V.nonunits
  have hDX : ∀ p, D p → HX (φ p) ∧ HX' (φ p) := by
    intro p hp
    refine ⟨fun c => ?_, fun c hc => ?_⟩
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact hp.1 _
    · rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine hp.2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 hc (isUnit_of_map_unit _ _ hu)
  have hXD : ∀ p, HX (φ p) → HX' (φ p) → D p := by
    intro p h1 h2
    refine ⟨fun a => ?_, fun a ha => ?_⟩
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
      exact h1 c
    · obtain ⟨c, rfl⟩ := hsurj p a
      rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]
      refine h2 c ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (hu.map _)
  have hDz : D z := ⟨fun a => hV.1 ⟨a, rfl⟩, fun _ ha => algebraMap_mem_nonunits_of_range_le hV ha⟩
  have hDz' : D z' := by
    obtain ⟨h1, h2⟩ := hDX z hDz
    exact hXD z' (hzz ▸ h1) (hzz ▸ h2)
  -- the lift `Spec V ⟶ Z` through a dominated point
  let ψ : ∀ p, D p → Z.presheaf.stalk p →+* V := fun p hp =>
    (algebraMap _ Z.functionField).codRestrict V hp.1
  let l : ∀ p, D p → (Spec (.of V) ⟶ Z) := fun p hp =>
    Spec.map (CommRingCat.ofHom (ψ p hp)) ≫ Z.fromSpecStalk p
  have hl : ∀ p (hp : D p),
      Spec.map (CommRingCat.ofHom (algebraMap V Z.functionField)) ≫ l p hp =
        Z.fromSpecStalk (genericPoint Z) := fun p hp =>
    specMap_algebraMap_comp_fromSpecStalk p hp.1
  have hlp : ∀ p (hp : D p), l p hp (IsLocalRing.closedPoint V) = p := fun p hp =>
    specMap_codRestrict_fromSpecStalk_closedPoint p hp.1
      (isLocalHom_codRestrict_of_mem_nonunits _ hp.1 hp.2)
  -- the composite `Spec V ⟶ X` only depends on the image point
  let χ : ∀ w, HX w → X.presheaf.stalk w →+* V := fun w hw =>
    ((functionFieldMap φ).comp (algebraMap _ X.functionField)).codRestrict V hw
  have hlφ : ∀ p (hp : D p), l p hp ≫ φ =
      Spec.map (CommRingCat.ofHom (χ (φ p) (hDX p hp).1)) ≫ X.fromSpecStalk (φ p) := by
    intro p hp
    simp only [l]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext c
    change algebraMap _ Z.functionField ((φ.stalkMap p).hom c) =
      functionFieldMap φ (algebraMap _ X.functionField c)
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hχ : ∀ w w' (_ : w = w') (hw : HX w) (hw' : HX w'),
      Spec.map (CommRingCat.ofHom (χ w hw)) ≫ X.fromSpecStalk w =
        Spec.map (CommRingCat.ofHom (χ w' hw')) ≫ X.fromSpecStalk w' := by
    rintro w _ rfl hw hw'
    rfl
  let S : ValuativeCommSq φ :=
    { R := V
      K := Z.functionField
      i₁ := Z.fromSpecStalk (genericPoint Z)
      i₂ := l z hDz ≫ φ
      commSq := ⟨by rw [← hl z hDz, Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion φ S
  let L : S.commSq.LiftStruct := ⟨l z hDz, hl z hDz, rfl⟩
  let L' : S.commSq.LiftStruct := ⟨l z' hDz', hl z' hDz', by
    change l z' hDz' ≫ φ = l z hDz ≫ φ
    rw [hlφ z' hDz', hlφ z hDz]
    exact hχ _ _ hzz.symm _ _⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim L L')
  rw [← hlp z hDz, ← hlp z' hDz']
  exact congrArg (fun m : Spec (.of V) ⟶ Z => m (IsLocalRing.closedPoint V)) hLL

/-- If `φ` is a local ring homomorphism and `ι v ∈ φ.range` for a unit `v`, then
`ι v⁻¹ ∈ φ.range`. -/
theorem mem_range_inv_of_mem_range {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {φ : A →+* C} [IsLocalHom φ] {ι : B →+* C} {v : Bˣ} (hv : ι v ∈ φ.range) :
    ι ↑v⁻¹ ∈ φ.range := by
  obtain ⟨c, hc⟩ := hv
  have hcu : IsUnit c := isUnit_of_map_unit φ c (hc ▸ v.isUnit.map _)
  refine ⟨↑hcu.unit⁻¹, ?_⟩
  have h1 : ι v.1 * ι (v⁻¹).1 = 1 :=
    (map_mul ι v.1 (v⁻¹).1).symm.trans ((congrArg ι v.mul_inv).trans (map_one _))
  have h2 : φ c * φ ↑hcu.unit⁻¹ = 1 :=
    (map_mul φ c _).symm.trans ((congrArg φ hcu.mul_val_inv).trans (map_one _))
  linear_combination (-φ ↑hcu.unit⁻¹) * h1 - (φ ↑hcu.unit⁻¹ * ι (v⁻¹).1) * hc + ι (v⁻¹).1 * h2

/-- The stalk maps of a morphism `φ : Z ⟶ Bl_I Y` over `Y` are surjective under the chart
hypotheses of `isIso_of_comp_blowUpToBase`. -/
private theorem surjective_stalkMap_of_comp_blowUpToBase {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r)
    (I : Y.IdealSheafData) (φ : Z ⟶ blowUp I) (hφ : φ ≫ blowUpToBase I = r)
    (hloc : ∀ z : Z, ∃ (j : Fin (n + 1)) (hz : toPZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0) (z : Z) :
    Function.Surjective (φ.stalkMap z) := by
  subst hφ
  obtain ⟨j, hz, b, hspan, hrel, hne⟩ := hloc z
  have hcomp : ∀ a, (φ ≫ blowUpToBase I).stalkMap z a =
      φ.stalkMap z ((blowUpToBase I).stalkMap (φ z) a) := fun a => by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  -- the inverse image of `I` is principal at `φ z`
  obtain ⟨t, ht⟩ := exists_stalk_eq_span_singleton (I.comap (blowUpToBase I))
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) (φ z)
  have ht' : Ideal.span {t} =
      Ideal.span (Set.range fun k => (blowUpToBase I).stalkMap (φ z) (b k)) := by
    rw [← ht, idealStalk_comap_eq_map]
    exact ((congrArg (Ideal.map ((blowUpToBase I).stalkMap (φ z)).hom) hspan).trans
      (Ideal.map_span _ _)).trans (congrArg Ideal.span (Set.range_comp _ _).symm)
  -- the coordinate ratios come from the blow-up
  have hg : ∀ k, gRatio i z hz k ∈ Set.range (φ.stalkMap z) :=
    mem_range_of_span_singleton_eq (φ.stalkMap z).hom
      (fun k => (blowUpToBase I).stalkMap (φ z) (b k)) (gRatio i z hz) j t ht'
      (fun k => by rw [← hcomp, ← hcomp]; exact hrel k) (by rw [← hcomp]; exact hne)
  -- the functions from `Y` come from the blow-up
  have hY : ∀ a, ∃ c, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a = φ.stalkMap z c := by
    intro a
    rw [Scheme.Hom.stalkMap_congr_hom _ _ hir z, CommRingCat.comp_apply, hcomp]
    exact ⟨_, rfl⟩
  have e1 : ∀ a, (i ≫ (projectiveSpaceOver n Y ↘ Y)).stalkMap z a =
      i.stalkMap z ((pullback.fst (terminal.from Y)
        (terminal.from (projectiveSpaceAtUniverse.{u} n))).stalkMap (i z) a) := by
    intro a; rw [Scheme.Hom.stalkMap_comp]; rfl
  have e2 : ∀ k, gRatio i z hz k = i.stalkMap z ((pullback.snd (terminal.from Y)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) :
        projectiveSpaceOver n Y ⟶ PZ.{u} n).stalkMap (i z) (ratio hz k)) := by
    intro k; rw [gRatio]; erw [Scheme.Hom.stalkMap_comp]; rfl
  -- the image of `φ` pulled back to the stalk of `ℙⁿ_Y` is everything
  have hT := eq_top_of_subring_stalk_pullback (terminal.from Y) (terminal.from (PZ.{u} n))
    (i z) hz (((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom) (fun a => ?_) (fun k => ?_)
    (fun v hv => ?_)
  · intro a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z a
    have : c ∈ ((φ.stalkMap z).hom.range).comap (i.stalkMap z).hom := hT ▸ Subring.mem_top c
    exact this
  · obtain ⟨c, hc⟩ := hY a
    exact ⟨c, hc.symm.trans (e1 a)⟩
  · obtain ⟨c, hc⟩ := hg k
    exact ⟨c, hc.trans (e2 k)⟩
  · exact mem_range_inv_of_mem_range hv

/-- **The comparison morphism is an isomorphism.** Let `Z ⊆ ℙⁿ_Y` be closed and integral over an
integral `Y`, `I` an ideal sheaf on `Y` vanishing nowhere near the generic point, and
`φ : Z ⟶ Bl_I Y` a morphism over `Y`. Suppose that at every `z`, on a chart `T_j ≠ 0`, the stalk of
`I` at the image of `z` is generated by elements `b_k` with `r^♯ b_k = (T_k / T_j) · r^♯ b_j` and
`r^♯ b_j ≠ 0`. Then `φ` is an isomorphism. -/
private theorem isIso_of_comp_blowUpToBase {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y]
    (r : Z ⟶ Y) {n : ℕ} (i : Z ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
    (hir : i ≫ (projectiveSpaceOver n Y ↘ Y) = r) [IsDominant r]
    (I : Y.IdealSheafData) (hgenY : genericPoint Y ∉ I.support)
    (φ : Z ⟶ blowUp I) (hφ : φ ≫ blowUpToBase I = r)
    (hloc : ∀ z : Z, ∃ (j : Fin (n + 1)) (hz : toPZ i z ∈ chartOpen n j)
      (b : Fin (n + 1) → Y.presheaf.stalk (r z)),
      IdealSheafData.stalk I (r z) = Ideal.span (Set.range b) ∧
        (∀ k, r.stalkMap z (b k) = gRatio i z hz k * r.stalkMap z (b j)) ∧
        r.stalkMap z (b j) ≠ 0) :
    IsIso φ := by
  subst hφ
  haveI : IsIntegral (blowUp I) := isIntegral_blowUp I (ne_bot_of_genericPoint_notMem_support hgenY)
  haveI : IsDominant φ := isDominant_of_map_eq_genericPoint φ
    (eq_genericPoint_of_blowUpToBase_eq I hgenY _
      (map_genericPoint_of_isDominant (φ ≫ blowUpToBase I)))
  -- the stalk maps are injective
  have hinj : ∀ z, Function.Injective (φ.stalkMap z) := fun z => by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h := MMP.Mori.functionFieldMap_algebraMap_stalk φ z a
    rw [ha, map_zero] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1
      ((map_eq_zero_iff _ (functionFieldMap φ).injective).1 h)
  have hsurj : ∀ z, Function.Surjective (φ.stalkMap z) :=
    surjective_stalkMap_of_comp_blowUpToBase _ i hir I φ rfl hloc
  -- `φ` is closed and separated
  haveI : IsProper (φ ≫ blowUpToBase I) := by
    rw [← hir]
    haveI := isProper_projectiveSpaceOver n Y
    infer_instance
  haveI : IsSeparated φ := IsSeparated.of_comp φ (blowUpToBase I)
  haveI : UniversallyClosed φ := UniversallyClosed.of_comp_of_isSeparated φ (blowUpToBase I)
  -- `φ` is injective
  have hφinj : Function.Injective φ := injective_of_surjective_stalkMap φ hsurj
  have hclosed : IsClosedMap φ := φ.isClosedMap
  have hφsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← hclosed.isClosed_range.closure_eq]
    exact (IsDominant.denseRange (f := φ)).closure_range
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨TopCat.isIso_of_bijective_of_isClosedMap _ ⟨hφinj, hφsurj⟩ hclosed, fun z => ?_⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj z, hsurj z⟩

end Core

/-! ### Generators of colon ideals, and principal ideals in local domains -/

section ColonGenerators

variable {R : Type*} {K : Type*} [CommRing R] [Field K] [Algebra R K] {ι : Type*} {f : ι → K}

/-- The colon ideal `M·(R : M) ∩ R` is generated by the elements of `R` whose image in `K` is a
product `c f_k` of a multiplier `c ∈ (R : M)` with a generator `f_k` of `M`. -/
private theorem colonIdeal_eq_span (hinj : Function.Injective (algebraMap R K)) :
    colonIdeal R f = Ideal.span {a | ∃ c ∈ colonSet R f, ∃ k, algebraMap R K a = c * f k} := by
  have h : colonSubmodule R f = Submodule.map (Algebra.linearMap R K)
      (Submodule.span R {a | ∃ c ∈ colonSet R f, ∃ k, algebraMap R K a = c * f k}) := by
    rw [Submodule.map_span]
    unfold colonSubmodule
    congr 1
    ext x
    constructor
    · rintro ⟨c, hc, k, rfl⟩
      obtain ⟨a, ha⟩ := hc k
      exact ⟨a, ⟨c, hc, k, ha⟩, ha⟩
    · rintro ⟨a, ⟨c, hc, k, ha⟩, rfl⟩
      exact ⟨c, hc, k, ha⟩
  change (colonSubmodule R f).comap (Algebra.linearMap R K) = _
  rw [h, Submodule.comap_map_eq_of_injective (f := Algebra.linearMap R K) hinj]

/-- If some `f_j` is nonzero and every ratio `f_k / f_j` comes from `R`, the colon ideal is the
unit ideal: `f_j⁻¹` is a multiplier and `f_j⁻¹ f_j = 1`. -/
private theorem colonIdeal_eq_top {j : ι} (hj : f j ≠ 0)
    (h : ∀ k, f k / f j ∈ (algebraMap R K).range) : colonIdeal R f = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_colonIdeal, map_one]
  refine Submodule.subset_span ⟨(f j)⁻¹, fun k => ?_, j, (inv_mul_cancel₀ hj).symm⟩
  rw [inv_mul_eq_div]
  exact h k

end ColonGenerators

/-- In a local ring, if a set `G` generates a nonzero principal ideal, then one element of `G`
already generates it. -/
private theorem exists_mem_span_eq_span_singleton {A : Type*} [CommRing A] [IsLocalRing A]
    {G : Set A} {t : A} (ht : t ≠ 0) (h : Ideal.span G = Ideal.span {t}) :
    ∃ g ∈ G, Ideal.span G = Ideal.span {g} := by
  by_contra hne
  push Not at hne
  have hG : G ⊆ (IsLocalRing.maximalIdeal A * Ideal.span {t} : Ideal A) := by
    intro g hg
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span hg : g ∈ Ideal.span {t})
    by_cases hs : IsUnit s
    · exact absurd (h.trans (Ideal.span_singleton_mul_left_unit hs t).symm) (hne _ hg)
    · exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 hs)
        (Ideal.mem_span_singleton_self t)
  have hle : Ideal.span {t} ≤ IsLocalRing.maximalIdeal A * Ideal.span {t} :=
    h.symm.le.trans (Ideal.span_le.2 hG)
  obtain ⟨z, hz, hzt⟩ := (Ideal.mem_mul_span_singleton).1 (hle (Ideal.mem_span_singleton_self t))
  have hu : IsUnit (1 - z) := by
    by_contra hnu
    have h1 : (1 - z) + z ∈ IsLocalRing.maximalIdeal A :=
      add_mem ((IsLocalRing.mem_maximalIdeal _).2 hnu) hz
    rw [sub_add_cancel] at h1
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one
  have h0 : (1 - z) * t = 0 := by rw [sub_mul, one_mul, hzt, sub_self]
  exact ht ((hu.mul_right_eq_zero).1 h0)

/-! ### The coordinate ratios are regular on the blow-up of the colon ideal -/

section RatioData

open scoped Pointwise

variable {S : Scheme.{u}} [IsIntegral S] {ι : Type} [Finite ι] (f : ι → S.functionField)
  (K : S.IdealSheafData)

/-- **The cofactor chart.** Let `I = C·K` with `C` the colon ideal sheaf of `f`. At every point
`t` of the blow-up `Bl_I S` the invertible ideal `I·𝒪_{T,t}` is generated by one of the
products `c f_{k₀} κ`, hence every ratio `f_l / f_{k₀}` is a regular function at `t`. -/
private theorem exists_ratio_data (I : S.IdealSheafData)
    (hIstalk : ∀ s, IdealSheafData.stalk I s =
      colonIdeal (S.presheaf.stalk s) f * IdealSheafData.stalk K s)
    (hI : genericPoint S ∉ I.support) [IsIntegral (blowUp I)] (t : blowUp I) :
    haveI := isDominant_blowUpToBase _ hI
    ∃ (k₀ : ι) (β : ι → (blowUp I).presheaf.stalk t),
      β k₀ = 1 ∧ functionFieldMap (blowUpToBase I) (f k₀) ≠ 0 ∧
      ∀ l, algebraMap _ (blowUp I).functionField (β l) =
        functionFieldMap (blowUpToBase I) (f l) / functionFieldMap (blowUpToBase I) (f k₀) := by
  classical
  haveI : IsDominant (blowUpToBase I) := isDominant_blowUpToBase _ hI
  -- a regular generator of `I·𝒪_T` at `t`
  obtain ⟨U, hU, htU, g₀, hg₀reg, hg₀⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      (I.comap (blowUpToBase I)) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) t
  haveI : Nonempty U := ⟨⟨t, htU⟩⟩
  have ht₀ : (blowUp I).presheaf.germ U t htU g₀ ≠ 0 := by
    intro h0
    have := germ_injective_of_isIntegral (blowUp I) t htU (h0.trans (map_zero _).symm)
    exact hg₀reg.ne_zero this
  have hstalkT : IdealSheafData.stalk (I.comap (blowUpToBase I)) t =
      Ideal.span {(blowUp I).presheaf.germ U t htU g₀} := by
    rw [IdealSheafData.stalk_eq_map_germ _ t ⟨U, hU⟩ htU, hg₀, Ideal.map_span,
      Set.image_singleton]
  -- generators of `I` at the image point
  have hinj : Function.Injective
      (algebraMap (S.presheaf.stalk (blowUpToBase I t)) S.functionField) :=
    IsFractionRing.injective _ _
  have hspan : Ideal.span ((blowUpToBase I).stalkMap t ''
      ({a | ∃ c ∈ colonSet (S.presheaf.stalk (blowUpToBase I t)) f, ∃ k,
          algebraMap _ S.functionField a = c * f k} *
        (IdealSheafData.stalk K (blowUpToBase I t) : Set _))) =
      Ideal.span {(blowUp I).presheaf.germ U t htU g₀} := by
    have e : ∀ (G : Set (S.presheaf.stalk (blowUpToBase I t))),
        Ideal.span G * IdealSheafData.stalk K (blowUpToBase I t) =
          Ideal.span (G * (IdealSheafData.stalk K (blowUpToBase I t) : Set _)) := fun G => by
      conv_lhs => rw [← Ideal.span_eq (IdealSheafData.stalk K (blowUpToBase I t))]
      exact Ideal.span_mul_span' _ _
    rw [← hstalkT, idealStalk_comap_eq_map, hIstalk, colonIdeal_eq_span hinj, e, Ideal.map_span]
  obtain ⟨g, hgmem, hgspan⟩ := exists_mem_span_eq_span_singleton ht₀ hspan
  obtain ⟨y, ⟨a, ha, κ, hκ, rfl⟩, rfl⟩ := hgmem
  obtain ⟨c₀, hc₀, k₀, hak₀⟩ := ha
  have hg0 : (blowUpToBase I).stalkMap t (a * κ) ≠ 0 := by
    intro h0
    have h := hspan.symm.trans hgspan
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h
    exact ht₀ (Ideal.span_singleton_eq_bot.1 h)
  choose a' ha' using fun l => hc₀ l
  have hmem : ∀ l, (blowUpToBase I).stalkMap t (a' l * κ) ∈
      Ideal.span {(blowUpToBase I).stalkMap t (a * κ)} := fun l => by
    rw [← hgspan]
    exact Ideal.subset_span ⟨_, ⟨a' l, ⟨c₀, hc₀, l, ha' l⟩, κ, hκ, rfl⟩, rfl⟩
  choose β hβ using fun l => Ideal.mem_span_singleton'.1 (hmem l)
  -- the images in the function field
  have himg : ∀ x, algebraMap _ (blowUp I).functionField ((blowUpToBase I).stalkMap t x) =
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField x) := fun x =>
    (MMP.Mori.functionFieldMap_algebraMap_stalk (blowUpToBase I) t x).symm
  have hden : functionFieldMap (blowUpToBase I) c₀ * functionFieldMap (blowUpToBase I) (f k₀) *
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField κ) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← hak₀, ← map_mul, ← himg]
    exact fun h => hg0 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have hc₀κ : functionFieldMap (blowUpToBase I) c₀ *
      functionFieldMap (blowUpToBase I) (algebraMap _ S.functionField κ) ≠ 0 := fun h =>
    hden (by rw [mul_right_comm, h, zero_mul])
  have hfk₀ : functionFieldMap (blowUpToBase I) (f k₀) ≠ 0 := fun h =>
    hden (by rw [h, mul_zero, zero_mul])
  have hβK : ∀ l, algebraMap _ (blowUp I).functionField (β l) =
      functionFieldMap (blowUpToBase I) (f l) / functionFieldMap (blowUpToBase I) (f k₀) := by
    intro l
    have h1 := congrArg (algebraMap _ (blowUp I).functionField) (hβ l)
    simp only [map_mul, himg, ha', hak₀] at h1
    rw [eq_div_iff hfk₀]
    apply mul_right_cancel₀ hc₀κ
    linear_combination h1
  refine ⟨k₀, β, ?_, hfk₀, hβK⟩
  have h1 := hβK k₀
  rw [div_self hfk₀] at h1
  exact IsFractionRing.injective _ (blowUp I).functionField (h1.trans (map_one _).symm)

end RatioData

/-! ### Coordinate ratios along a morphism -/

/-- Germs of the pull-back of a section along equal morphisms agree. -/
private theorem germ_app_congr {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (x : X)
    (hφ : φ x ∈ U) (hψ : ψ x ∈ U) (s : Γ(Y, U)) :
    X.presheaf.germ (φ ⁻¹ᵁ U) x hφ (φ.app U s) = X.presheaf.germ (ψ ⁻¹ᵁ U) x hψ (ψ.app U s) := by
  subst h
  rfl

/-- If `Z' ⊆ ℙⁿ_{Y'}` maps to `ℙⁿ_ℤ` through `q : Z' ⟶ Z` and `Z ⊆ ℙⁿ_Y`, the coordinate ratios
of `Z'` are the pull-backs along `q` of those of `Z`. -/
private theorem gRatio_eq_stalkMap {Y Y' Z Z' : Scheme.{u}} {n : ℕ}
    (i : Z ⟶ projectiveSpaceOver n Y) (i' : Z' ⟶ projectiveSpaceOver n Y') (q : Z' ⟶ Z)
    (hq : toPZ i' = q ≫ toPZ i) (z : Z') {j : Fin (n + 1)} (hz : toPZ i' z ∈ chartOpen n j)
    (hz' : toPZ i (q z) ∈ chartOpen n j) (k : Fin (n + 1)) :
    gRatio i' z hz k = q.stalkMap z (gRatio i (q z) hz' k) := by
  simp only [gRatio, ratio, Scheme.Hom.germ_stalkMap_apply]
  rw [germ_app_congr hq _ z hz hz']
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- The base change of a closed subscheme `W₀ ⊆ ℙⁿ_S` along `b : T ⟶ S` is a closed subscheme of
`ℙⁿ_T`, compatibly with the projections to `T` and to `ℙⁿ_ℤ`. -/
private theorem exists_isClosedImmersion_projectiveSpaceOver {S T W₀ Γ : Scheme.{u}} {n : ℕ}
    (b : T ⟶ S) (i : W₀ ⟶ projectiveSpaceOver n S) [IsClosedImmersion i]
    (g : Γ ⟶ pullback b (i ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)))) (hg : IsClosedImmersion g) :
    ∃ iΓ : Γ ⟶ projectiveSpaceOver n T, IsClosedImmersion iΓ ∧
      iΓ ≫ pullback.fst _ _ = g ≫ pullback.fst _ _ ∧
      iΓ ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ ≫ i ≫ pullback.snd _ _ := by
  let e₁ := pullbackLeftPullbackSndIso b
    (pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))) i
  let e₂ := pullbackRightPullbackFstIso (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n)) b
  let e₃ : pullback (b ≫ terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) ≅ projectiveSpaceOver n T :=
    pullback.congrHom (Subsingleton.elim _ _) rfl
  refine ⟨g ≫ e₁.inv ≫ pullback.fst _ _ ≫ e₂.hom ≫ e₃.hom, inferInstance, ?_, ?_⟩
  · simp only [e₃, e₂, e₁, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
      Category.comp_id, pullbackRightPullbackFstIso_hom_fst, pullbackLeftPullbackSndIso_inv_fst]
  · simp only [e₃, e₂, e₁, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackRightPullbackFstIso_hom_snd,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc]

/-! ### The blow-up of the colon ideal dominates `W₀` -/

section Domination

variable {S W₀ : Scheme.{u}}

/-- Over its biregular locus a morphism has a point over every point, with bijective map on
local rings. -/
private theorem exists_bijective_stalkMap_of_mem_biregularLocus (f₀ : W₀ ⟶ S) {y : S}
    (hy : y ∈ MMP.Mori.biregularLocus f₀) :
    ∃ w, f₀ w = y ∧ Function.Bijective (f₀.stalkMap w) := by
  haveI : IsIso (f₀ ∣_ MMP.Mori.biregularLocus f₀) := MMP.Mori.isBiregular_biregularLocus f₀
  obtain ⟨x₀, hx₀⟩ := (f₀ ∣_ MMP.Mori.biregularLocus f₀).homeomorph.surjective ⟨y, hy⟩
  have hw : f₀ ((f₀ ⁻¹ᵁ MMP.Mori.biregularLocus f₀).ι x₀) = y :=
    (morphismRestrict_base_coe f₀ _ x₀).symm.trans (congrArg Subtype.val hx₀)
  refine ⟨_, hw, ?_⟩
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus f₀ (x := (f₀ ⁻¹ᵁ _).ι x₀) (hw ▸ hy)
  exact ConcreteCategory.bijective_of_isIso _

variable [IsIntegral S] [IsIntegral W₀] [IsLocallyNoetherian S]

/-- **A blow-up of `S` dominating `W₀`.** Let `f₀ : W₀ ⟶ S` be a projective birational morphism
of integral schemes, isomorphic over the generic point, and `K` an ideal sheaf on `S` nonzero at
the generic point. There is an ideal sheaf `I`, a multiple of `K`, whose cosupport contains that
of `K` and misses the points of the biregular locus of `f₀` outside the cosupport of `K`, such
that `Bl_I S ⟶ S` factors through `f₀`. The ideal is `C·K`, with `C = M·(𝒪_S : M)` the colon
ideal of the fractional ideal `M` generated by the coordinate ratios of the generic point of
`W₀ ⊆ ℙⁿ_S`. -/
private theorem exists_blowUp_dominating (f₀ : W₀ ⟶ S) (hf₀ : IsProjectiveMorphism f₀)
    (hb : MMP.Mori.IsBirationalMorphism f₀)
    (hgenbir : genericPoint S ∈ MMP.Mori.biregularLocus f₀) (K : S.IdealSheafData)
    (hK : genericPoint S ∉ K.support) :
    ∃ I : S.IdealSheafData, (∃ A : S.IdealSheafData, I = A * K) ∧
      genericPoint S ∉ I.support ∧ K.support ≤ I.support ∧
      (∀ y ∈ MMP.Mori.biregularLocus f₀, y ∉ K.support → y ∉ I.support) ∧
      ∃ r : blowUp I ⟶ W₀, r ≫ f₀ = blowUpToBase I := by
  classical
  haveI : IsDominant f₀ := MMP.Mori.IsBirationalMorphism.isDominant hb
  obtain ⟨n, i, hi, rfl⟩ := hf₀
  set f₀ := i ≫ (projectiveSpaceOver n S ↘ S) with hf₀def
  -- the chart of the generic point and the coordinate ratios there
  have hcover : ∀ x : PZ.{u} n, ∃ j, x ∈ chartOpen n j := fun x => by
    have hx : x ∈ (⊤ : (PZ.{u} n).Opens) := trivial
    rw [← iSup_basicOpen_X_eq_top (ULift.{u} ℤ) n] at hx
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  have hgen : ∀ (z : W₀) {j : Fin (n + 1)}, toPZ i z ∈ chartOpen n j →
      toPZ i (genericPoint W₀) ∈ chartOpen n j := fun z j hz =>
    ((genericPoint_spec W₀).mem_open_set_iff (toPZ i ⁻¹ᵁ chartOpen n j).isOpen).2 ⟨z, trivial, hz⟩
  obtain ⟨j₀, hj₀⟩ := hcover (toPZ i (genericPoint W₀))
  set c : Fin (n + 1) → W₀.functionField := fun k => gRatio i (genericPoint W₀) hj₀ k with hcdef
  have hc₀ : c j₀ = 1 := gRatio_self i _ hj₀
  have hcrel : ∀ (z : W₀) {j : Fin (n + 1)} (hz : toPZ i z ∈ chartOpen n j) (k : Fin (n + 1)),
      c k = algebraMap _ W₀.functionField (gRatio i z hz k) * c j := by
    intro z j hz k
    rw [algebraMap_gRatio i z hz (hgen z hz)]
    exact gRatio_mul i _ (hgen z hz) hj₀ k
  have hcj : ∀ (z : W₀) {j : Fin (n + 1)} (_ : toPZ i z ∈ chartOpen n j), c j ≠ 0 := by
    intro z j hz h
    have := hcrel z hz j₀
    rw [h, mul_zero, hc₀] at this
    exact one_ne_zero this
  have hbij := MMP.Mori.IsBirationalMorphism.functionFieldMap_bijective hb
  set f : Fin (n + 1) → S.functionField := fun k => Function.surjInv hbij.2 (c k) with hfdef
  have hf : ∀ k, functionFieldMap f₀ (f k) = c k := fun k => Function.surjInv_eq hbij.2 _
  have hfj : ∀ (z : W₀) {j : Fin (n + 1)} (_ : toPZ i z ∈ chartOpen n j), f j ≠ 0 := by
    intro z j hz h
    apply hcj z hz
    rw [← hf, h, map_zero]
  -- the colon ideal is the unit ideal on the biregular locus
  have hCbir : ∀ y ∈ MMP.Mori.biregularLocus f₀, y ∉ (colonIdealSheaf f).support := by
    intro y hy
    obtain ⟨w, rfl, hwbij⟩ := exists_bijective_stalkMap_of_mem_biregularLocus f₀ hy
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, stalk_colonIdealSheaf]
    obtain ⟨j, hz⟩ := hcover (toPZ i w)
    refine colonIdeal_eq_top (hfj w hz) fun k => ?_
    obtain ⟨a, ha⟩ := hwbij.2 (gRatio i w hz k)
    refine ⟨a, (functionFieldMap f₀).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk, map_div₀, hf, hf, eq_div_iff (hcj w hz)]
    exact ((congrArg (algebraMap _ W₀.functionField) ha).trans rfl) ▸ (hcrel w hz k).symm
  set I := colonIdealSheaf f * K with hIdef
  have hIsupp : I.support = (colonIdealSheaf f).support ⊔ K.support :=
    Scheme.IdealSheafData.support_mul _ _
  have hIgen : genericPoint S ∉ I.support := by
    rw [hIsupp]
    rintro (h | h)
    · exact hCbir _ hgenbir h
    · exact hK h
  refine ⟨I, ⟨_, rfl⟩, hIgen, hIsupp ▸ le_sup_right, fun y hy hyK => ?_, ?_⟩
  · rw [hIsupp]
    rintro (h | h)
    · exact hCbir y hy h
    · exact hyK h
  -- the blow-ups `T = Bl_I S` and `Γ = Bl_{I 𝒪_{W₀}} W₀`
  haveI : IsIntegral (blowUp I) :=
    isIntegral_blowUp I (ne_bot_of_genericPoint_notMem_support hIgen)
  haveI : IsLocallyNoetherian (blowUp I) :=
    TwoStepTower.isLocallyNoetherian_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI : IsDominant (blowUpToBase I) := isDominant_blowUpToBase I hIgen
  have hJgen := genericPoint_notMem_support_comap f₀ hIgen
  haveI : IsIntegral (blowUp (I.comap f₀)) :=
    isIntegral_blowUp _ (ne_bot_of_genericPoint_notMem_support hJgen)
  haveI : IsDominant (blowUpToBase (I.comap f₀)) := isDominant_blowUpToBase _ hJgen
  have hlamb : canonicalLift f₀ I ≫ blowUpToBase I = blowUpToBase (I.comap f₀) ≫ f₀ :=
    canonicalLift_comp_blowUpToBase f₀ I
  have hlamgen : canonicalLift f₀ I (genericPoint (blowUp (I.comap f₀))) =
      genericPoint (blowUp I) := by
    apply eq_genericPoint_of_blowUpToBase_eq I hIgen
    have h1 : (blowUpToBase (I.comap f₀) ≫ f₀) (genericPoint (blowUp (I.comap f₀))) =
        genericPoint S := map_genericPoint_of_isDominant _
    rw [← hlamb] at h1
    exact h1
  haveI : IsDominant (canonicalLift f₀ I) := isDominant_of_map_eq_genericPoint _ hlamgen
  -- `Γ` is a closed subscheme of `ℙⁿ_T`
  obtain ⟨g, hg, hgsnd, hgfst⟩ := exists_isClosedImmersion_canonicalLift_factor f₀ I
  haveI := hg
  obtain ⟨iΓ, hiΓ, hiΓfst, hiΓsnd⟩ := exists_isClosedImmersion_projectiveSpaceOver
    (blowUpToBase I) i g hg
  haveI := hiΓ
  have hiΓ1 : iΓ ≫ (projectiveSpaceOver n (blowUp I) ↘ blowUp I) = canonicalLift f₀ I :=
    hiΓfst.trans hgfst
  have hiΓ2 : toPZ iΓ = blowUpToBase (I.comap f₀) ≫ toPZ i := by
    have h := congrArg (fun φ => φ ≫ i ≫ pullback.snd (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))) hgsnd
    simp only [Category.assoc] at h
    exact hiΓsnd.trans h
  -- the local data on `Γ`
  have hloc : ∀ z : blowUp (I.comap f₀), ∃ (j : Fin (n + 1)) (hz : toPZ iΓ z ∈ chartOpen n j)
      (b : Fin (n + 1) → (blowUp I).presheaf.stalk (canonicalLift f₀ I z)),
      IdealSheafData.stalk (⊤ : (blowUp I).IdealSheafData) (canonicalLift f₀ I z) =
          Ideal.span (Set.range b) ∧
        (∀ k, (canonicalLift f₀ I).stalkMap z (b k) =
          gRatio iΓ z hz k * (canonicalLift f₀ I).stalkMap z (b j)) ∧
        (canonicalLift f₀ I).stalkMap z (b j) ≠ 0 := by
    intro z
    obtain ⟨j, hz⟩ := hcover (toPZ iΓ z)
    have hz' : toPZ i (blowUpToBase (I.comap f₀) z) ∈ chartOpen n j := by
      have := congrArg (fun φ => φ z) hiΓ2
      simp only [Scheme.Hom.comp_apply] at this
      exact this ▸ hz
    obtain ⟨k₀, β, hβ1, hfk₀, hβ⟩ := exists_ratio_data f K I
      (fun s => by rw [IdealSheafData.stalk_mul, stalk_colonIdealSheaf]) hIgen
      (canonicalLift f₀ I z)
    have hΨ : ∀ t : S.functionField, functionFieldMap (canonicalLift f₀ I)
        (functionFieldMap (blowUpToBase I) t) =
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ t) := fun t => by
      rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_congr hlamb]
    have hfj0 : f j ≠ 0 := hfj _ hz'
    have himgΓ : ∀ x, algebraMap _ (blowUp (I.comap f₀)).functionField
        ((canonicalLift f₀ I).stalkMap z x) =
        functionFieldMap (canonicalLift f₀ I) (algebraMap _ (blowUp I).functionField x) :=
      fun x => (MMP.Mori.functionFieldMap_algebraMap_stalk _ z x).symm
    have hgR : ∀ k, algebraMap _ (blowUp (I.comap f₀)).functionField (gRatio iΓ z hz k) =
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ (f k / f j)) := by
      intro k
      rw [gRatio_eq_stalkMap i iΓ _ hiΓ2 z hz hz' k,
        ← MMP.Mori.functionFieldMap_algebraMap_stalk, map_div₀, hf, hf]
      congr 1
      rw [eq_div_iff (hcj _ hz')]
      exact (hcrel _ hz' k).symm
    have hA : ∀ l, f l ≠ 0 →
        functionFieldMap (blowUpToBase (I.comap f₀)) (functionFieldMap f₀ (f l)) ≠ 0 :=
      fun l hl h => hl ((map_eq_zero_iff _ (functionFieldMap f₀).injective).1
        ((map_eq_zero_iff _ (functionFieldMap (blowUpToBase (I.comap f₀))).injective).1 h))
    have hfk₀' : f k₀ ≠ 0 := fun h => hfk₀ (by rw [h, map_zero])
    refine ⟨j, hz, β, ?_, fun k => ?_, ?_⟩
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 (by
        rw [Scheme.IdealSheafData.support_top]; exact id)]
      exact (Ideal.eq_top_of_isUnit_mem (Ideal.span (Set.range β))
        (Ideal.subset_span (⟨k₀, hβ1⟩ : (1 : _) ∈ Set.range β)) isUnit_one).symm
    · apply IsFractionRing.injective ((blowUp (I.comap f₀)).presheaf.stalk z)
        (blowUp (I.comap f₀)).functionField
      rw [map_mul, himgΓ, himgΓ, hβ, hβ, hgR]
      simp only [map_div₀, hΨ]
      have h1 := hA j hfj0
      have h2 := hA k₀ hfk₀'
      field_simp
    · intro h0
      have h1 := congrArg (algebraMap _ (blowUp (I.comap f₀)).functionField) h0
      rw [himgΓ, hβ, map_zero, map_div₀, hΨ, hΨ] at h1
      exact div_ne_zero (hA j hfj0) (hA k₀ hfk₀') h1
  -- `Γ ⟶ T` is an isomorphism
  haveI := ClosedBlowupSequence.isIso_blowUpToBase_top (blowUp I)
  have hgentop : genericPoint (blowUp I) ∉ (⊤ : (blowUp I).IdealSheafData).support := by
    rw [Scheme.IdealSheafData.support_top]
    exact id
  haveI := isIso_of_comp_blowUpToBase (canonicalLift f₀ I) iΓ hiΓ1 ⊤ hgentop
    (canonicalLift f₀ I ≫ inv (blowUpToBase ⊤)) (by simp) hloc
  haveI : IsIso (canonicalLift f₀ I) := by
    have e : canonicalLift f₀ I = (canonicalLift f₀ I ≫ inv (blowUpToBase ⊤)) ≫ blowUpToBase ⊤ := by
      simp
    rw [e]
    infer_instance
  refine ⟨inv (canonicalLift f₀ I) ≫ blowUpToBase (I.comap f₀), ?_⟩
  rw [Category.assoc, ← hlamb, IsIso.inv_hom_id_assoc]

end Domination

/-! ### A relatively antiample divisor supported over the exceptional locus -/

section Exceptional

/-- **Coefficients of a pull-back where the morphism is a local isomorphism.** If the stalk map
of `f` at the generic point of `H` is an isomorphism and `f(η_H) = η_P`, then
`coeff_H(f^*C) = coeff_P(C)`. -/
private theorem coeff_isPullback_eq_of_isIso {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {f : Y ⟶ X} [IsDominant f] {C : Divisor X} (hCc : C.IsCartier)
    {hC : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ C.supp}
    {C' : Divisor Y} (h : C.IsPullback f hC C') (H : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (hHP : f H.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap H.genericPoint)] : C'.coeff H = C.coeff P := by
  obtain ⟨V, hV, φ, hφ⟩ := hCc (f H.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ H hV P.component,
    MMP.Positivity.ord_functionFieldMap_of_isIso f H P hHP,
    ← MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
    hφ P ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P, hHP ▸ hV⟩]

variable {X Y : Scheme.{u}}

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_mem_biregularLocus (π : X ⟶ Y) {a b : X}
    (ha : π a ∈ MMP.Mori.biregularLocus π) (hab : π a = π b) : a = b := by
  set V := MMP.Mori.biregularLocus π
  haveI : IsIso (π ∣_ V) := MMP.Mori.isBiregular_biregularLocus π
  have hb : π b ∈ V := hab ▸ ha
  have := (π ∣_ V).homeomorph.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext
    (((morphismRestrict_base_coe π V ⟨a, ha⟩).trans hab).trans
      (morphismRestrict_base_coe π V ⟨b, hb⟩).symm))
  exact congrArg Subtype.val this

/-- The prime divisor of `Y` through the image of the generic point of a prime divisor `P` of `X`,
when that image lies in the biregular locus. -/
private noncomputable def imagePrimeDivisor (π : X ⟶ Y) (P : MMP.Mori.PrimeDivisor X)
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π) : MMP.Mori.PrimeDivisor Y :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (π P.genericPoint)
    ((MMP.Positivity.coheight_map_of_mem_biregularLocus π h).trans
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P))

private theorem genericPoint_imagePrimeDivisor (π : X ⟶ Y) (P : MMP.Mori.PrimeDivisor X)
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π) :
    (imagePrimeDivisor π P h).genericPoint = π P.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

private theorem imagePrimeDivisor_injective (π : X ⟶ Y) {P P' : MMP.Mori.PrimeDivisor X}
    (h : π P.genericPoint ∈ MMP.Mori.biregularLocus π)
    (h' : π P'.genericPoint ∈ MMP.Mori.biregularLocus π)
    (e : imagePrimeDivisor π P h = imagePrimeDivisor π P' h') : P = P' := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  apply eq_of_mem_biregularLocus π h
  rw [← genericPoint_imagePrimeDivisor π P h, ← genericPoint_imagePrimeDivisor π P' h', e]

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- **A relatively antiample divisor supported over the exceptional locus.** Let `π : X ⟶ Y` be
a projective morphism of varieties over `k` which is an isomorphism over a nonempty open `O`,
with `Y` smooth and quasi-projective. There is a divisor `G` on `X`, with `-G` Cartier and
`π`-ample, all of whose components lie over the complement of `O`: Kollár's divisor `W`
(Lemma 2.9), minus the pull-back of its image on `Y`, which is Cartier because `Y` is smooth. -/
private theorem exists_isRelativelyAmple_neg_of_isIso {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} (π : X ⟶ Y) (hX : MMP.Mori.IsVariety k (π ≫ sY))
    (hY : MMP.Mori.IsVariety k sY) (hYqp : Stacks.HProjective.IsHQuasiProjective sY)
    (hYsm : IsSmoothScheme sY) (hπ : IsProjectiveMorphism π) [IsDominant π] (O : Y.Opens)
    [IsIso (π ∣_ O)] (hO : (O : Set Y).Nonempty) :
    ∃ G : Divisor X, ∃ hGc : (-G).IsCartier, (-G).IsRelativelyAmple π hGc ∧
      ∀ P : MMP.Mori.PrimeDivisor X, G.coeff P ≠ 0 → π P.genericPoint ∉ O := by
  classical
  haveI : QuasiCompact sY := hY.toQuasiCompact
  have hOb : O ≤ MMP.Mori.biregularLocus π :=
    MMP.Mori.le_biregularLocus (show MMP.Mori.IsBiregular π O from ‹IsIso (π ∣_ O)›)
  have hOr : ((O : Set Y) ∩ Set.range π).Nonempty := by
    obtain ⟨y, hy⟩ := hO
    obtain ⟨z, hz⟩ := (π ∣_ O).surjective ⟨y, hy⟩
    exact ⟨y, hy, (π ⁻¹ᵁ O).ι z,
      (morphismRestrict_base_coe π O z).symm.trans (congrArg Subtype.val hz)⟩
  -- Kollár's divisor
  obtain ⟨W, -, hWc, hWamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism hX
      hY hYqp hπ ⟨O, hOr, inferInstance⟩
  -- the image of `W` on `Y`
  let B : Divisor Y := ∑ P ∈ W.support,
    if h : π P.genericPoint ∈ O then W.coeff P • Finsupp.single (imagePrimeDivisor π P (hOb h)) 1
    else 0
  have hBcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (h : π P.genericPoint ∈ O),
      B.coeff (imagePrimeDivisor π P (hOb h)) = W.coeff P := by
    intro P h
    change B (imagePrimeDivisor π P (hOb h)) = W P
    rw [Finsupp.finset_sum_apply]
    by_cases hPW : P ∈ W.support
    · rw [Finset.sum_eq_single P]
      · rw [dif_pos h, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
        rfl
      · intro P' _ hP'
        split_ifs with h'
        · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
          exact fun e => hP' (imagePrimeDivisor_injective π _ _ e)
        · rfl
      · exact fun hP => absurd hPW hP
    · rw [Finsupp.notMem_support_iff.1 hPW]
      refine Finset.sum_eq_zero fun P' hP' => ?_
      split_ifs with h'
      · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero]
        rintro e
        exact hPW (imagePrimeDivisor_injective π _ _ e ▸ hP')
      · rfl
  have hBc : B.IsCartier := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hYsm B
  have hBgen : ∀ Z : irreducibleComponents X, π (componentGenericPoint X Z) ∉ B.supp := by
    intro Z
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp B
  obtain ⟨B', hB'⟩ : ∃ B' : Divisor X, B.IsPullback π hBgen B' :=
    hBc.exists_isPullback (f := π) hBgen
  have hB'c : B'.IsCartier := Divisor.IsPullback.isCartier hB' hBc
  refine ⟨W - B', ?_, ?_, fun P hP hPO => hP ?_⟩
  · rw [neg_sub]
    exact hB'c.sub hWc
  · have := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback π hWc.neg hWamp hBc hB'
      hB'c
    convert this using 1
    rw [neg_sub, sub_eq_neg_add]
  · rw [DivisorWithCoeffs.coeff_sub, sub_eq_zero]
    haveI : IsIso (π.stalkMap P.genericPoint) :=
      MMP.isIso_stalkMap_of_mem_biregularLocus π (hOb hPO)
    rw [coeff_isPullback_eq_of_isIso hBc hB' P (imagePrimeDivisor π P (hOb hPO))
      (genericPoint_imagePrimeDivisor π P (hOb hPO)).symm, hBcoeff P hPO]

end Exceptional

/-! ### The divisor of a monomial ideal -/

section MonomialDivisor

open MMP.Intersection

variable {X : Scheme.{u}}

/-- The closed subscheme of the zero Cartier divisor is empty. -/
private theorem subscheme_zero :
    MMP.CartierDivisor.subscheme (0 : X.CartierDivisor)
      MMP.CartierDivisor.isEffective_zero = ⊤ := by
  have h1 : ∀ U : X.Opens, MMP.CartierDivisor.IsRegularLocalEquation
      (0 : X.CartierDivisor) (1 : Γ(X, U)) := by
    intro U
    have hu : IsUnit (MMP.CartierDivisorSheaf.toK U (1 : Γ(X, U))) := by
      rw [map_one]
      exact isUnit_one
    refine ⟨hu, ?_⟩
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, map_one]; rfl)
    rw [this, IsLocalEquationOn, cartierClass_one, restrictDivisor, map_zero]
  refine ((MMP.CartierDivisor.eq_subscheme_iff _ ⊤).2 fun U g hg => ?_).symm
  obtain ⟨u, hu⟩ := hg.exists_unit_mul (h1 U)
  rw [mul_one] at hu
  rw [hu, Ideal.span_singleton_eq_top.2 u.isUnit]
  rfl

variable [IsIntegral X] [IsLocallyNoetherian X] {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))

/-- Multiples of an effective Cartier divisor cutting out a prime divisor `E` cut out the powers
of the ideal of `E`, and have Weil divisor the multiples of `E`. -/
private theorem exists_nsmul (A : X.CartierDivisor)
    (E : MMP.Mori.PrimeDivisor X) (hA : MMP.Intersection.IsEffective A)
    (hAs : MMP.CartierDivisor.subscheme A hA = E.idealSheaf)
    (hAw : IsWeilDivisorOfCartier A (Finsupp.single E 1)) (n : ℕ) :
    ∃ hn : MMP.Intersection.IsEffective (n • A),
      MMP.CartierDivisor.subscheme (n • A) hn = E.idealSheaf ^ n ∧
      IsWeilDivisorOfCartier (n • A) ((n : ℤ) • Finsupp.single E 1) := by
  induction n with
  | zero =>
    refine ⟨by rw [zero_smul]; exact MMP.CartierDivisor.isEffective_zero, ?_, ?_⟩
    · simp only [zero_smul, pow_zero, Scheme.IdealSheafData.one_eq_top]
      exact subscheme_zero
    · intro P
      simp only [zero_smul, Nat.cast_zero, DivisorWithCoeffs.coeff_zero]
      exact isOrderAlong_zero _
  | succ n ih =>
    obtain ⟨hn, hns, hnw⟩ := ih
    have hn' : MMP.Intersection.IsEffective (n • A + A) := hn.add hA
    refine ⟨by rw [succ_nsmul]; exact hn', ?_, ?_⟩
    · have e := MMP.CartierDivisor.subscheme_add hn hA hn'
      simp only [succ_nsmul, pow_succ]
      rw [e, hns, hAs]
    · intro P
      have := (hnw P).add (hAw P)
      simpa only [succ_nsmul, Nat.cast_succ, add_smul, one_smul, DivisorWithCoeffs.coeff_add]
        using this

/-- **The divisor of a monomial ideal.** On a smooth variety, the ideal `∏_E I_E^{c_E}` over a
finite set of prime divisors is the ideal sheaf of an effective Cartier divisor whose Weil divisor
is `∑ c_E E`. -/
private theorem exists_isWeilDivisorOfCartier_prod [AlgebraicGeometry.IsVariety k sX]
    (hsm : IsSmoothScheme sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℕ) :
    ∃ (A : X.CartierDivisor)
      (hA : MMP.Intersection.IsEffective A),
      MMP.CartierDivisor.subscheme A hA = ∏ E ∈ s, E.idealSheaf ^ c E ∧
      IsWeilDivisorOfCartier A (∑ E ∈ s, (c E : ℤ) • Finsupp.single E 1) := by
  classical
  have hreg : IsRegular X := MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, MMP.CartierDivisor.isEffective_zero, ?_, fun P => ?_⟩
    · rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
      exact subscheme_zero
    · rw [Finset.sum_empty, DivisorWithCoeffs.coeff_zero]
      exact isOrderAlong_zero _
  | insert E s hE ih =>
    obtain ⟨A, hA, hAs, hAw⟩ := ih
    obtain ⟨AE, hAEw⟩ :=
      (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2 X hreg
        (Finsupp.single E 1)
    obtain ⟨hAEe, hAEs⟩ :=
      IsWeilDivisorOfCartier.isEffective_and_subscheme_eq_of_isSmoothScheme sX hsm hAEw
    obtain ⟨hn, hns, hnw⟩ := exists_nsmul AE E hAEe hAEs hAEw (c E)
    refine ⟨c E • AE + A, hn.add hA, ?_, fun P => ?_⟩
    · rw [MMP.CartierDivisor.subscheme_add hn hA (hn.add hA), hns, hAs,
        Finset.prod_insert hE]
    · rw [Finset.sum_insert hE, DivisorWithCoeffs.coeff_add]
      exact (hnw P).add (hAw P)

end MonomialDivisor

/-! ### Composing with the blow-up of `S` -/

section Compose

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple MMP.Intersection

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- `𝒪_Y(mA) ≅ 𝒪_Y(A)^{⊗ m}` for a Cartier divisor `A`. -/
private noncomputable def divisorialSheafNsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

/-- The Weil divisor of `-A` is minus the Weil divisor of `A`. -/
private theorem isWeilDivisorOfCartier_neg {X : Scheme.{u}} {A : X.CartierDivisor}
    {w : Divisor X} (h : IsWeilDivisorOfCartier A w) :
    IsWeilDivisorOfCartier (-A) (-w) := by
  intro P
  obtain ⟨a, b, ha, hb, ⟨g, ⟨U, hxU, g', hg', hgg⟩, hbu, hbg⟩, la, lb, hla, hlb, hN⟩ := h P
  have hgu : IsUnit g := hgg ▸ g'.isUnit.map _
  refine ⟨b, a, hb, ha, ⟨_, ⟨U, hxU, g'⁻¹, hg'.inv, rfl⟩, ?_, ?_⟩, lb, la, hlb, hla, ?_⟩
  · rw [← hbg]
    exact hbu.mul hgu
  · rw [← hbg, ← hgg, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rw [DivisorWithCoeffs.coeff_neg, hN]; ring

/-- **[Stacks, Tag 0C4K] against a module on the target.** Let `h : W ⟶ T`, `b : T ⟶ S` be
quasi-compact, `S` quasi-compact, `L` an `h`-ample Cartier divisor on the normal scheme `W` and
`M` a `b`-ample invertible sheaf on `T` whose pull-back is `𝒪_W(N)`. Then `L + nN` is
`(h ≫ b)`-ample for all large `n`. -/
private theorem exists_isRelativelyAmple_add_nsmul_of_iso {W T S : Scheme.{u}}
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace S]
    (h : W ⟶ T) (b : T ⟶ S) [QuasiCompact h] [QuasiCompact b] (M : T.Modules)
    [IsInvertibleModule T M] (hM : MMP.Mori.IsRelativelyAmple b M)
    {L : Divisor W} (hLc : L.IsCartier) (hL : L.IsRelativelyAmple h hLc)
    {N : Divisor W} (hNc : N.IsCartier)
    (eN : (modulePullback h.toLRSHom.toShHom).obj M ≅ N.divisorialSheaf) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (L + n • N).IsRelativelyAmple (h ≫ b) (hLc.add (hNc.nsmul n)) := by
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hNc.isInvertibleModule_divisorialSheaf
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp h b _ _
    (stacks_of_isRelativelyAmple h _ hL) (stacks_of_isRelativelyAmple b _ hM)
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := (hLc.add (hNc.nsmul n)).isInvertibleModule_divisorialSheaf
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule h L.divisorialSheaf M n ≅
      (L + n • N).divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso W (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso h _ n ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso W _ _ eN n ≪≫
          (divisorialSheafNsmulIso hNc n).symm) ≪≫
      hLc.divisorialSheafTensorIso (hNc.nsmul n)
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ n hn))

/-- **The pull-back of the exceptional ideal.** If `h : W ⟶ Bl_I S` pulls `I` back to the closed
subscheme of an effective Cartier divisor `A` on the normal scheme `W` with Weil divisor `K`, the
pull-back of the exceptional ideal sheaf `I·𝒪_{Bl}` is `𝒪_W(-K)`. -/
private theorem nonempty_modulePullback_exceptionalIdealModule_iso {W S : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (I : S.IdealSheafData)
    (h : W ⟶ blowUp I) (A : W.CartierDivisor)
    (hA : MMP.Intersection.IsEffective A)
    (hAs : MMP.CartierDivisor.subscheme A hA = I.comap (h ≫ blowUpToBase I))
    {K : Divisor W} (hAw : IsWeilDivisorOfCartier A K) :
    Nonempty ((modulePullback h.toLRSHom.toShHom).obj (exceptionalIdealModule I) ≅
      (-K).divisorialSheaf) := by
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalIdeal I) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I
  have heq : (exceptionalIdeal I).comap h = MMP.CartierDivisor.subscheme A hA := by
    rw [hAs, Scheme.IdealSheafData.comap_comp]
  have hdef : Stacks.Divisors.IsPullbackDefined h (exceptionalIdeal I) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor ((exceptionalIdeal I).comap h)
    rw [heq]
    exact MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hA
  exact ⟨Stacks.Divisors.pullbackIdealSheafComapIso h (exceptionalIdeal I) hdef ≪≫
    eqToIso (congrArg (fun J : W.IdealSheafData =>
      Stacks.ClosedImmersion.idealSheaf J.subschemeι.toLRSHom.toShHom) heq) ≪≫
    MMP.CartierDivisor.idealSheafIsoSheafNeg A hA ≪≫
      (isWeilDivisorOfCartier_neg hAw).sheafIsoDivisorialSheaf⟩

/-- **Twisting by the exceptional divisor of a blow-up.** Let `W` be a smooth variety and
`h : W ⟶ Bl_J X` pull `J` back to `∏ I_E^{c_E}`. If `-G` is Cartier and `h`-ample, then
`-(G + n ∑ c_E E)` is `(h ≫ Bl_J X ⟶ X)`-ample for all large `n`. -/
theorem exists_isRelativelyAmple_neg_add_nsmul_of_blowUp {W X : Scheme.{u}} {k : Type u}
    [Field k] [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian X] (sW : W ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sW] (hsm : IsSmoothScheme sW) (J : X.IdealSheafData)
    (h : W ⟶ blowUp J) [QuasiCompact h] (s : Finset (MMP.Mori.PrimeDivisor W))
    (c : MMP.Mori.PrimeDivisor W → ℕ)
    (hJ : J.comap (h ≫ blowUpToBase J) = ∏ E ∈ s, E.idealSheaf ^ c E)
    {G : Divisor W} (hGc : (-G).IsCartier) (hG : (-G).IsRelativelyAmple h hGc) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ hc : (-(G + n •
      (∑ E ∈ s, (c E : ℤ) • Finsupp.single E (1 : ℤ)))).IsCartier,
      (-(G + n • (∑ E ∈ s, (c E : ℤ) • Finsupp.single E (1 : ℤ)))).IsRelativelyAmple
        (h ≫ blowUpToBase J) hc := by
  obtain ⟨A, hA, hAs, hAw⟩ := exists_isWeilDivisorOfCartier_prod sW hsm s c
  obtain ⟨eK⟩ := nonempty_modulePullback_exceptionalIdealModule_iso J h A hA
    (hAs.trans hJ.symm) hAw
  obtain ⟨-, hMinv, hMamp, -⟩ := MMP.Foundations.isRelativelyAmple_exceptionalIdealModule J
    (TwoStepTower.isFiniteType_of_isLocallyNoetherian J)
  haveI := hMinv
  haveI : IsProper (blowUpToBase J) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian J)
  have hKc := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
    (∑ E ∈ s, (c E : ℤ) • Finsupp.single E (1 : ℤ))
  obtain ⟨n₀, hn₀⟩ := exists_isRelativelyAmple_add_nsmul_of_iso h (blowUpToBase J) _ hMamp
    hGc hG hKc.neg eK
  refine ⟨n₀, fun n hn => ⟨MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _, ?_⟩⟩
  convert hn₀ n hn using 2
  rw [neg_add, smul_neg]

end Compose

/-! ### Cosupports of monomial ideals -/

section MonomialSupport

/-- The cosupport of a product of positive powers is the union of the cosupports. -/
private theorem coe_support_prod_pow {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (n : ι → ℕ) (hn : ∀ i ∈ s, n i ≠ 0) :
    ((∏ i ∈ s, I i ^ n i).support : Set X) = ⋃ i ∈ s, ((I i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.IdealSheafData.support_mul,
      Scheme.IdealSheafData.support_pow _ _ (hn i (Finset.mem_insert_self i s)),
      Finset.set_biUnion_insert,
      ← ih fun j hj => hn j (Finset.mem_insert_of_mem hj)]
    rfl

/-- For `J = ∏_{E ∈ Supp D} I_E^{D E}`, a prime divisor is a component of `D` exactly when its
generic point lies in the cosupport of `J`. -/
private theorem mem_support_iff_genericPoint_mem {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : DivisorWithCoeffs ℕ X) {J : X.IdealSheafData}
    (hJ : J = ∏ E ∈ D.support, E.idealSheaf ^ D E) (P : MMP.Mori.PrimeDivisor X) :
    P ∈ D.support ↔ P.genericPoint ∈ J.support := by
  subst hJ
  change P ∈ D.support ↔
    P.genericPoint ∈ ((∏ E ∈ D.support, E.idealSheaf ^ D E).support : Set X)
  rw [coe_support_prod_pow _ _ _ fun E hE => Finsupp.mem_support_iff.1 hE]
  refine ⟨fun hP => Set.mem_biUnion hP (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P),
    fun hP => ?_⟩
  obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.1 hP
  by_contra hne
  exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support_of_ne
    (fun (h : P = E) => hne (by rw [h]; exact hE)) hPE

/-- A divisor whose components form a simple normal crossing family is an snc divisor. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (D : DivisorWithCoeffs ℕ X)
    (h : IsSNCFamily sX fun E : D.support => E.1.idealSheaf) : D.IsSNC sX := by
  refine ⟨fun E hE => (h.1 ⟨E, hE⟩).2.2, fun x => ?_⟩
  obtain ⟨n, z, c, hz, hstalk, hinj⟩ := h.2 x
  refine ⟨n, z, fun E => c ⟨⟨E.1, E.2.1⟩, E.2.2⟩, hz, fun E E' hEE' => ?_,
    fun E => hstalk ⟨⟨E.1, E.2.1⟩, E.2.2⟩⟩
  exact Subtype.ext (by simpa only [Subtype.mk.injEq] using hinj hEE')

end MonomialSupport

/-! ### Morphisms and blow-up sequences -/

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- Two morphisms into `W₀` which agree after `f₀ : W₀ ⟶ S` agree on the preimage of the
biregular locus of `f₀`, hence everywhere when the source is reduced and `f₀` separated. -/
private theorem eq_of_comp_eq_of_isSeparated {X W₀ S : Scheme.{u}} [IsReduced X]
    [IrreducibleSpace X] (f₀ : W₀ ⟶ S) [IsSeparated f₀] {a b : X ⟶ W₀} (h : a ≫ f₀ = b ≫ f₀)
    (hne : ((a ≫ f₀) ⁻¹ᵁ MMP.Mori.biregularLocus f₀ : Set X).Nonempty) : a = b := by
  set V := MMP.Mori.biregularLocus f₀
  haveI : IsIso (f₀ ∣_ V) := MMP.Mori.isBiregular_biregularLocus f₀
  set O := (a ≫ f₀) ⁻¹ᵁ V
  haveI : IsDominant O.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact O.isOpen.dense hne⟩
  refine ext_of_isDominant_of_isSeparated f₀ h O.ι ?_
  have hra : Set.range (O.ι ≫ a) ⊆ Set.range (f₀ ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2
  have hrb : Set.range (O.ι ≫ b) ⊆ Set.range (f₀ ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (b ≫ f₀) z.1 ∈ V
    rw [← h]
    exact z.2
  haveI : Mono ((f₀ ⁻¹ᵁ V).ι ≫ f₀) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hab : IsOpenImmersion.lift _ _ hra = IsOpenImmersion.lift _ _ hrb := by
    rw [← cancel_mono ((f₀ ⁻¹ᵁ V).ι ≫ f₀), ← Category.assoc, ← Category.assoc,
      IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, h]
  rw [← IsOpenImmersion.lift_fac _ _ hra, ← IsOpenImmersion.lift_fac _ _ hrb, hab]

/-- A point of coheight one specialized from a point of coheight one is that point. -/
private theorem eq_of_specializes_of_coheight_eq_one {X : Scheme.{u}} {a b : X} (h : a ⤳ b)
    (ha : Order.coheight a = 1) (hb : Order.coheight b = 1) : a = b := by
  by_contra hne
  have hlt : b < a := lt_of_le_not_ge (Scheme.le_iff_specializes.2 h)
    fun h' => hne (h.antisymm (Scheme.le_iff_specializes.1 h')).eq
  have := Order.coheight_strictAnti hlt (by rw [ha]; exact ENat.one_lt_top)
  rw [ha, hb] at this
  exact lt_irrefl _ this

/-- **Components of an effective Cartier divisor are prime divisors.** On an integral noetherian
scheme, let `J` be an effective Cartier divisor not containing the generic point whose cosupport
is covered by a finite family `s` of prime divisors. Then every point of `V(J)` lies on a member
of `s` whose generic point lies in `V(J)`: by Krull's principal ideal theorem the generic point of
each irreducible component of `V(J)` has coheight one, so it is the generic point of the member
of `s` through it. -/
private theorem exists_primeDivisor_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (J : X.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (s : Finset (MMP.Mori.PrimeDivisor X))
    (hs : (J.support : Set X) ⊆ ⋃ P ∈ s, (P.idealSheaf.support : Set X)) {w : X}
    (hw : w ∈ (J.support : Set X)) :
    ∃ P ∈ s, P.genericPoint ∈ (J.support : Set X) ∧ w ∈ (P.idealSheaf.support : Set X) := by
  haveI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf J.support.isClosed
  obtain ⟨Z, hZ, hwZ⟩ := Set.mem_sUnion.1 (hcov hw)
  set η := hZ.1.1.genericPoint
  have hηZ : closure {η} = Z := by
    have := hZ.1.1.isGenericPoint_genericPoint_closure
    rwa [(MMP.Resolution.Aux.isClosed_of_mem_componentsOf J.support.isClosed hZ).closure_eq]
      at this
  have hmax : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (J.support : Set X))
      (closure {η}) := hηZ ▸ hZ
  have hηJ : η ∈ (J.support : Set X) := hmax.prop.2 (subset_closure rfl)
  obtain ⟨P, hP, hηP⟩ := Set.mem_iUnion₂.1 (hs hηJ)
  have hPη : P.genericPoint = η := eq_of_specializes_of_coheight_eq_one
    (Aux.genericPoint_specializes_of_mem_support P hηP)
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
    (MMP.coheight_eq_one_of_isEffectiveCartierDivisor_of_isLocallyNoetherian hJ hηJ
      fun y hy hyη => (hyη.antisymm (specializes_iff_closure_subset.mpr
        (hmax.2 ⟨isIrreducible_singleton.closure,
          (J.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hy)⟩
          (specializes_iff_closure_subset.mp hyη)))).eq)
  refine ⟨P, hP, hPη ▸ hηJ, ?_⟩
  have e : (P.idealSheaf.support : Set X) = closure {P.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  rw [e, hPη, hηZ]
  exact hwZ

/-! ### Reduced divisors on a finite set of prime divisors -/

section ReducedSum

variable {X : Scheme.{u}} (s : Finset (MMP.Mori.PrimeDivisor X))

open scoped Classical in
private theorem coeff_sum_smul_single (c : MMP.Mori.PrimeDivisor X → ℤ)
    (P : MMP.Mori.PrimeDivisor X) :
    (∑ Q ∈ s, c Q • Finsupp.single Q (1 : ℤ) : Divisor X).coeff P = if P ∈ s then c P else 0 := by
  change (∑ Q ∈ s, c Q • Finsupp.single Q (1 : ℤ)) P = _
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The coefficient of `A + n • A'` at a prime divisor `P` is `A.coeff P + n * A'.coeff P`. -/
theorem coeff_add_nsmul (A A' : Divisor X) (n : ℕ) (P : MMP.Mori.PrimeDivisor X) :
    (A + n • A').coeff P = A.coeff P + n * A'.coeff P := by
  change (A + n • A') P = A P + n * A' P
  rw [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]

/-- The integral divisor `∑ E ∈ D.support, D E • E` built from a divisor `D` with natural
coefficients has the same coefficients as `D`. -/
theorem coeff_sum_natCast_smul_single (D : DivisorWithCoeffs ℕ X) (P : MMP.Mori.PrimeDivisor X) :
    (∑ E ∈ D.support, (D E : ℤ) • Finsupp.single E (1 : ℤ) : Divisor X).coeff P = D P := by
  classical
  rw [coeff_sum_smul_single]
  split_ifs with hP
  · rfl
  · rw [Finsupp.notMem_support_iff.1 hP, Nat.cast_zero]

open scoped Classical in
private theorem coeff_sum_single (P : MMP.Mori.PrimeDivisor X) :
    (∑ Q ∈ s, Finsupp.single Q (1 : ℤ) : Divisor X).coeff P = if P ∈ s then 1 else 0 := by
  simpa using coeff_sum_smul_single s 1 P

private theorem mem_support_sum_single (P : MMP.Mori.PrimeDivisor X) :
    P ∈ (∑ Q ∈ s, Finsupp.single Q (1 : ℤ) : Divisor X).support ↔ P ∈ s := by
  rw [Finsupp.mem_support_iff]
  change (∑ Q ∈ s, Finsupp.single Q (1 : ℤ) : Divisor X).coeff P ≠ 0 ↔ _
  rw [coeff_sum_single]
  split_ifs with hP <;> simp [hP]

private theorem isReducedEffective_sum_single :
    MMP.Intersection.IsReducedEffective (∑ Q ∈ s, Finsupp.single Q (1 : ℤ) : Divisor X) := by
  intro P
  rw [coeff_sum_single]
  split_ifs <;> simp

private theorem coe_supp_sum_single :
    ((∑ Q ∈ s, Finsupp.single Q (1 : ℤ) : Divisor X).supp : Set X) =
      ⋃ P ∈ s, (P.idealSheaf.support : Set X) := by
  rw [DivisorWithCoeffs.coe_supp]
  ext w
  simp only [Set.mem_iUnion₂, exists_prop, mem_support_sum_single]

end ReducedSum

/-! ### Blow-up sequences away from their centres -/

section BlowupSequences

/-- The double locus of an ordered divisor is closed. -/
private theorem isClosed_doubleLocus {X : Scheme.{u}} (E : OrderedDivisor X) :
    IsClosed E.doubleLocus := by
  have e : E.doubleLocus = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j),
      ((E.E i).support : Set X) ∩ ((E.E j).support : Set X) := by
    ext x
    simp only [OrderedDivisor.doubleLocus, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      exists_prop]
  rw [e]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => (E.E i).support.isClosed.inter (E.E j).support.isClosed

/-- On an integral scheme, the stalks of an effective Cartier divisor are generated by a nonzero
element. -/
private theorem exists_ne_zero_stalk_eq_span_singleton {X : Scheme.{u}} [IsIntegral X]
    (J : X.IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ t ≠ 0, IdealSheafData.stalk J x = Ideal.span {t} := by
  obtain ⟨U, hU, hxU, f, hreg, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor J hJ x
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨X.presheaf.germ U x hxU f, fun h0 => hreg.ne_zero
    (germ_injective_of_isIntegral X x hxU (h0.trans (map_zero _).symm)), ?_⟩
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hf, Ideal.map_span, Set.image_singleton]

/-- On an integral scheme, an effective Cartier divisor misses the generic point. -/
private theorem genericPoint_notMem_support_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    [IsIntegral X] (J : X.IdealSheafData) (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    genericPoint X ∉ J.support := by
  obtain ⟨t, ht, hJt⟩ := exists_ne_zero_stalk_eq_span_singleton J hJ (genericPoint X)
  rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, hJt, Ideal.span_singleton_eq_top]
  exact (show IsUnit (t : X.functionField) from isUnit_iff_ne_zero.2 ht)

/-- On an integral scheme, the double locus of an ordered divisor misses the generic point. -/
private theorem genericPoint_notMem_doubleLocus {X : Scheme.{u}} [IsIntegral X]
    {E : OrderedDivisor X} (hE : E.IsOrderedDivisor) : genericPoint X ∉ E.doubleLocus :=
  fun ⟨i, _, _, hi, _⟩ => genericPoint_notMem_support_of_isEffectiveCartierDivisor _ (hE i).2 hi

/-- A blow-up sequence whose centres lie over `S` (`X` mapping to `X₀` by `f`) is an isomorphism
over every open of `X` disjoint from `f⁻¹ S`. -/
private theorem isIso_toBase_restrict_of_centersLieOver :
    ∀ {X X₀ : Scheme.{u}} (B : ClosedBlowupSequence X) (f : X ⟶ X₀) (S : Set X₀),
      B.CentersLieOver f S → ∀ V : X.Opens, Disjoint (f ⁻¹' S) (V : Set X) →
        IsIso (B.toBase ∣_ V)
  | _, _, .nil X, f, S, _, V, _ => by
    rw [ClosedBlowupSequence.toBase]
    exact IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (inferInstanceAs (IsIso (𝟙 X))) V
  | _, _, .cons Z B, f, S, h, V, hV => by
    rw [ClosedBlowupSequence.CentersLieOver] at h
    obtain ⟨hZ, hB⟩ := h
    change IsIso ((B.toBase ≫ blowUpToBase Z : B.target ⟶ _) ∣_ V)
    rw [morphismRestrict_comp]
    haveI := isIso_blowUp_restrict_compl_support Z
    exact IsIso.comp_isIso'
      (isIso_toBase_restrict_of_centersLieOver B _ S hB (blowUpToBase Z ⁻¹ᵁ V)
        (Set.disjoint_left.mpr fun _ hy hyV => Set.disjoint_left.mp hV hy hyV))
      (Kollar.isIso_morphismRestrict_of_le _ (W := Z.support.compl)
        fun x hxV hxZ => Set.disjoint_left.mp hV (hZ ⟨x, hxZ, rfl⟩) hxV)

/-- The target of a smooth blow-up sequence over a smooth variety `Y ⟶ X`, dominant over `X`,
whose centres lie over a set `S ⊆ X` missing the generic point, is a smooth variety. -/
private theorem isVariety_and_isSmoothScheme_toBase {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) (S : Set X) (hS : genericPoint X ∉ S) :
    ∀ {Y : Scheme.{u}} (B : ClosedBlowupSequence Y) (f : Y ⟶ X),
      AlgebraicGeometry.IsVariety k (f ≫ sX) → IsDominant f → IsSmoothScheme (f ≫ sX) →
      B.IsSmooth (f ≫ sX) → B.CentersLieOver f S →
      AlgebraicGeometry.IsVariety k (B.toBase ≫ f ≫ sX) ∧ IsSmoothScheme (B.toBase ≫ f ≫ sX)
  | _, .nil _, f, hv, _, hs, _, _ => by
    simpa [ClosedBlowupSequence.toBase] using ⟨hv, hs⟩
  | Y, .cons Z B, f, hv, _, hs, ⟨_, hZsm, hBsm⟩, ⟨hZS, hBS⟩ => by
    haveI : IsIntegral Y := hv.toIsIntegral
    have hZgen : genericPoint Y ∉ Z.support := fun h =>
      hS (map_genericPoint_of_isDominant f ▸ hZS ⟨_, h, rfl⟩)
    haveI := hv
    obtain ⟨hv', -, -⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational (f ≫ sX) Z
        (ne_bot_of_genericPoint_notMem_support hZgen)
    have hsm' := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (f ≫ sX) Z
      ⟨hs, hZsm⟩).1
    haveI := isDominant_blowUpToBase Z hZgen
    have := isVariety_and_isSmoothScheme_toBase sX S hS B (blowUpToBase Z ≫ f)
      (by rwa [Category.assoc]) inferInstance
      (by rw [Category.assoc]; exact MMP.Mori.isSmoothScheme_of_smooth hsm')
      (by rwa [Category.assoc]) hBS
    rwa [show (ClosedBlowupSequence.cons Z B).toBase ≫ f ≫ sX =
      B.toBase ≫ blowUpToBase Z ≫ f ≫ sX from Category.assoc _ _ _]

end BlowupSequences

/-! ### Factors of monomial ideals -/

section MonomialFactor

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A divisor of `p^c m`, `p` prime, is `p^a g'` with `g' ∣ m`. -/
private theorem exists_eq_pow_mul_of_dvd_pow_mul (p : R) :
    ∀ (c : ℕ), (c ≠ 0 → Prime p) → ∀ {g m : R}, g ∣ p ^ c * m →
      ∃ (a : ℕ) (g' : R), g = p ^ a * g' ∧ g' ∣ m
  | 0, _, g, _, h => ⟨0, g, by rw [pow_zero, one_mul], by rwa [pow_zero, one_mul] at h⟩
  | c + 1, hp, g, m, h => by
    have hp := hp c.succ_ne_zero
    rw [pow_succ', mul_assoc] at h
    by_cases hpg : p ∣ g
    · obtain ⟨g₁, rfl⟩ := hpg
      obtain ⟨a, g', rfl, hg'⟩ := exists_eq_pow_mul_of_dvd_pow_mul p c (fun _ => hp)
        ((mul_dvd_mul_iff_left hp.ne_zero).1 h)
      exact ⟨a + 1, g', by ring, hg'⟩
    · obtain ⟨t, ht⟩ := h
      obtain ⟨t', rfl⟩ := (hp.dvd_or_dvd ⟨_, ht.symm⟩).resolve_left hpg
      refine exists_eq_pow_mul_of_dvd_pow_mul p c (fun _ => hp) ⟨t', ?_⟩
      exact mul_left_cancel₀ hp.ne_zero (by rw [ht]; ring)

/-- In a domain, a divisor of `∏ zᵢ^{cᵢ}`, every `zᵢ` with `cᵢ ≠ 0` prime, is associated to a
product `∏ zᵢ^{aᵢ}`. -/
private theorem exists_associated_prod_pow_of_dvd :
    ∀ {n : ℕ} (z : Fin n → R) (c : Fin n → ℕ), (∀ i, c i ≠ 0 → Prime (z i)) →
      ∀ {g : R}, g ∣ ∏ i, z i ^ c i → ∃ a : Fin n → ℕ, Associated g (∏ i, z i ^ a i)
  | 0, _, _, _, g, hg => ⟨Fin.elim0, by
      rw [Fin.prod_univ_zero] at hg ⊢
      exact associated_one_iff_isUnit.2 (isUnit_of_dvd_one hg)⟩
  | n + 1, z, c, hz, g, hg => by
    rw [Fin.prod_univ_succ] at hg
    obtain ⟨a₀, g', rfl, hg'⟩ := exists_eq_pow_mul_of_dvd_pow_mul (z 0) (c 0) (hz 0) hg
    obtain ⟨a, ha⟩ := exists_associated_prod_pow_of_dvd (fun i => z i.succ) (fun i => c i.succ)
      (fun i => hz i.succ) hg'
    refine ⟨Fin.cons a₀ a, ?_⟩
    rw [Fin.prod_univ_succ]
    simpa only [Fin.cons_zero, Fin.cons_succ] using ha.mul_left _

end MonomialFactor

/-- **A factor of a monomial ideal is monomial.** On an integral locally Noetherian scheme, if
`J` is an effective Cartier divisor and `J·M` is a monomial effective Cartier divisor, then `J` is
monomial: at every point `J` is generated by a divisor of `∏ zᵢ^{cᵢ}`, and the `zᵢ` are prime
because `𝒪_{X,x}/(zᵢ)` is regular. -/
private theorem isMonomialIdeal_of_mul {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {J M : X.IdealSheafData} (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (hJMc : Stacks.Divisors.IsEffectiveCartierDivisor (J * M)) (hJM : IsMonomialIdeal (J * M)) :
    IsMonomialIdeal J := by
  intro x
  obtain ⟨n, z, c, hz, hstalk⟩ := hJM x
  obtain ⟨g, -, hg⟩ := exists_ne_zero_stalk_eq_span_singleton J hJ x
  obtain ⟨t, ht, hJMt⟩ := exists_ne_zero_stalk_eq_span_singleton _ hJMc x
  have hprod : ∏ i, z i ^ c i ≠ 0 := fun h0 => ht (Ideal.span_singleton_eq_bot.1
    (by rw [← hJMt, hstalk, h0, Ideal.span_singleton_eq_bot]))
  haveI := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hprime : ∀ i, c i ≠ 0 → Prime (z i) := by
    intro i hi
    have hzi : z i ≠ 0 := fun h0 =>
      hprod (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, zero_pow hi]))
    have hreg := isRegularLocalRing_quotient_span_image z hz {i}
    rw [Finset.coe_singleton, Set.image_singleton] at hreg
    haveI := IsRegularLocalRing.isDomain (_ ⧸ Ideal.span {z i})
    exact (Ideal.span_singleton_prime hzi).1
      ((Ideal.Quotient.isDomain_iff_prime _).1 inferInstance)
  have hdvd : g ∣ ∏ i, z i ^ c i := by
    rw [← Ideal.mem_span_singleton, ← hg]
    have : ∏ i, z i ^ c i ∈ IdealSheafData.stalk (J * M) x := by
      rw [hstalk]
      exact Ideal.mem_span_singleton_self _
    rw [IdealSheafData.stalk_mul] at this
    exact Ideal.mul_le_left this
  obtain ⟨a, ha⟩ := exists_associated_prod_pow_of_dvd z c hprime hdvd
  exact ⟨n, z, a, hz, hg.trans (Ideal.span_singleton_eq_span_singleton.2 ha)⟩

/-! ### The main construction -/

/-- On an integral scheme, an ideal sheaf is nonzero at the generic points of the irreducible
components exactly when it is a unit at the generic point. -/
private theorem isNonzeroAtGenericPoints_iff {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) : IsNonzeroAtGenericPoints I ↔ genericPoint X ∉ I.support := by
  rw [← IdealSheafData.stalk_eq_top_iff_notMem_support]
  refine ⟨fun h => ((Ideal.eq_bot_or_top (K := X.functionField) _).resolve_left
    (h _ ?_)), fun h η hη => ?_⟩
  · rw [(genericPoint_spec X).def, irreducibleComponents_eq_singleton]; rfl
  · have hgen : IsGenericPoint η (⊤ : Set X) :=
      hη.eq_of_le (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)
    rw [hgen.eq (genericPoint_spec X), h]
    exact top_ne_bot

/-- The structure sheaf of `Spec ℂ` is an ample invertible module. -/
theorem exists_isAmple_spec_complex :
    ∃ (M : (Spec (.of ℂ)).Modules) (hM : Stacks.Ample.IsInvertibleModule _ M),
      letI : Stacks.Ample.IsInvertibleModule _ M := hM
      Stacks.Ample.IsAmple _ M :=
  ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩

/-- If `|g| < N` and `k ≠ 0`, then `g + N k` is positive. -/
theorem pos_add_mul_of_natAbs_lt {g : ℤ} {k N : ℕ} (hk : k ≠ 0) (hN : g.natAbs < N) :
    0 < g + N * k := by
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hN' : (g.natAbs : ℤ) + 1 ≤ N := by exact_mod_cast hN
  have hg : -(g.natAbs : ℤ) ≤ g := by rw [Int.natCast_natAbs]; exact neg_abs_le _
  nlinarith

/-- **A principalized model dominating a blow-up of the base.** Let `f₀ : W₀ ⟶ S` be a
projective resolution of a normal quasi-projective complex variety, `K` an ideal sheaf on `S`
nonzero at the generic point, `M` an ideal sheaf on `W₀` nonzero at the generic point, and `E` an
ordered snc divisor on `W₀`. There is a multiple `I` of `K`, with the same cosupport as `K` over
the biregular locus of `f₀`, such that the canonical principalization `B` of
`(W₀, I 𝒪_{W₀} · M, E)` has the following properties. It is a smooth blow-up sequence whose
centres have simple normal crossings with `E` and lie over `V(I 𝒪_{W₀} M) ∪ E^{(2)}`, and
`(I 𝒪_{W₀} M)·𝒪_W` is monomial on its target `W`. Its composite `r : W ⟶ W₀` is projective and
an isomorphism over every open missing `V(I 𝒪_{W₀} M) ∪ E^{(2)}`; `f = r ≫ f₀` is a projective
resolution with `W` quasi-projective and `I 𝒪_W` invertible; `(I 𝒪_{W₀} M)·𝒪_W` has simple
normal crossing components `E'`, the prime divisors whose generic points map into
`V(I 𝒪_{W₀} M)`; and some `D` with `-D` Cartier and `f`-ample has positive coefficients on the
`E'` and no other components than the `E'` and prime divisors over `E^{(2)}`. -/
theorem exists_principalization_isRelativelyAmple_neg {S W₀ : Scheme.{0}} [IsNormal S]
    [IsIntegral S] {sS : S ⟶ Spec (.of ℂ)} (hS : IsQuasiProjectiveVariety ℂ sS)
    {f₀ : W₀ ⟶ S} (hf₀ : MMP.Intersection.IsResolution sS f₀)
    (hgenbir : genericPoint S ∈ biregularLocus f₀) (K : S.IdealSheafData)
    (hK : genericPoint S ∉ K.support) (M : W₀.IdealSheafData) (hM : IsNonzeroAtGenericPoints M)
    (E : OrderedDivisor W₀) (hE : E.IsOrderedSNC (f₀ ≫ sS)) :
    ∃ I : S.IdealSheafData, (∃ A : S.IdealSheafData, I = A * K) ∧ K.support ≤ I.support ∧
      (∀ y ∈ biregularLocus f₀, y ∉ K.support → y ∉ I.support) ∧
      ∃ B : ClosedBlowupSequence W₀, B.IsSmooth (f₀ ≫ sS) ∧
        B.CentersHaveSNCWith (f₀ ≫ sS) E.support ∧
        B.CentersLieOver (𝟙 W₀) (((I.comap f₀ * M).support : Set W₀) ∪ E.doubleLocus) ∧
        IsMonomialIdeal ((I.comap f₀ * M).comap B.toBase) ∧
        ∃ (_ : IsLocallyNoetherian B.target) (_ : IsNormal B.target)
          (_ : CompactSpace B.target),
        MMP.Intersection.IsResolution sS (B.toBase ≫ f₀) ∧
        IsQuasiProjectiveVariety ℂ (B.toBase ≫ f₀ ≫ sS) ∧ IsProjectiveMorphism B.toBase ∧
        (∀ U : W₀.Opens,
          Disjoint (U : Set W₀) (((I.comap f₀ * M).support : Set W₀) ∪ E.doubleLocus) →
            IsIso (B.toBase ∣_ U)) ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (B.toBase ≫ f₀)) ∧
        ∃ DJ : DivisorWithCoeffs ℕ B.target, DJ.IsSNC (B.toBase ≫ f₀ ≫ sS) ∧
          (∀ P : MMP.Mori.PrimeDivisor B.target,
            P ∈ DJ.support ↔ B.toBase P.genericPoint ∈ (I.comap f₀ * M).support) ∧
          (((I.comap f₀ * M).comap B.toBase).support : Set B.target) =
            ⋃ P ∈ DJ.support, (P.idealSheaf.support : Set B.target) ∧
          ∃ D : Divisor B.target, (∀ P ∈ DJ.support, 0 < D.coeff P) ∧
            (∀ P ∉ DJ.support, D.coeff P ≠ 0 → B.toBase P.genericPoint ∈ E.doubleLocus) ∧
            ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (B.toBase ≫ f₀) h := by
  classical
  obtain ⟨hSv, hWv, hWs, hproj, hbir⟩ := hf₀
  haveI : IsIntegral W₀ := hWv.toIsIntegral
  haveI : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : LocallyOfFiniteType (f₀ ≫ sS) := hWv.toLocallyOfFiniteType
  haveI : QuasiCompact (f₀ ≫ sS) := hWv.toQuasiCompact
  haveI : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian (f₀ ≫ sS)
  haveI : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace (f₀ ≫ sS)
  haveI : AlgebraicGeometry.IsNoetherian W₀ := ⟨⟩
  haveI : QuasiSeparatedSpace W₀ := quasiSeparatedSpace_of_quasiSeparated (f₀ ≫ sS)
  -- the dominating blow-up
  obtain ⟨I, hIA, hIgen, hKI, hIbir, r, hr⟩ :=
    exists_blowUp_dominating f₀ hproj hbir hgenbir K hK
  refine ⟨I, hIA, hKI, hIbir, ?_⟩
  -- the canonical principalization `B` of `(W₀, J, E)`, `J = I·𝒪_{W₀}·M`
  haveI : IsDominant f₀ := hbir.isDominant
  have hJgen := genericPoint_notMem_support_comap f₀ hIgen
  set J := I.comap f₀ * M with hJdef
  have hJMgen : genericPoint W₀ ∉ J.support := by
    rw [hJdef, Scheme.IdealSheafData.support_mul]
    rintro (h | h)
    · exact hJgen h
    · exact (isNonzeroAtGenericPoints_iff M).1 hM h
  set Sx : Set W₀ := (J.support : Set W₀) ∪ E.doubleLocus with hSxdef
  have hSxc : IsClosed Sx := J.support.isClosed.union (isClosed_doubleLocus E)
  have hSxgen : genericPoint W₀ ∉ Sx := by
    rintro (h | h)
    · exact hJMgen h
    · exact genericPoint_notMem_doubleLocus hE.1 h
  have ht : (⟨⟨W₀, J, E⟩, ℂ, f₀ ≫ sS⟩ : FieldBlowupTriple.{0}) ∈ triples :=
    ⟨inferInstance, hWs, inferInstance, inferInstance,
      TopologicalSpace.Equidimensional.of_preirreducibleSpace W₀,
      (isNonzeroAtGenericPoints_iff J).2 hJMgen, hE⟩
  obtain ⟨-, hBsm, hJmono, hBlie, -⟩ :=
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{0, 0, 0}
  set B := canonicalPrincipalization _ (triples_subset_sncTriples ht) with hBdef
  obtain ⟨hBsm, hBsnc⟩ := hBsm _ ht
  have hJmono : IsMonomialIdeal (J.comap B.toBase) := hJmono _ ht
  have hBlie : B.CentersLieOver (𝟙 W₀) Sx := hBlie _ ht
  have hπiso : ∀ U : W₀.Opens, Disjoint (U : Set W₀) Sx → IsIso (B.toBase ∣_ U) :=
    fun U hU => isIso_toBase_restrict_of_centersLieOver B (𝟙 W₀) Sx hBlie U hU.symm
  refine ⟨B, hBsm, hBsnc, hBlie, hJmono, ?_⟩
  -- `W = B.target` is a smooth variety, projective and birational over `W₀`
  obtain ⟨hWvar, hWsm⟩ : AlgebraicGeometry.IsVariety ℂ (B.toBase ≫ f₀ ≫ sS) ∧
      IsSmoothScheme (B.toBase ≫ f₀ ≫ sS) := by
    have := isVariety_and_isSmoothScheme_toBase (f₀ ≫ sS) Sx hSxgen B (𝟙 W₀)
      (by rwa [Category.id_comp]) inferInstance (by rwa [Category.id_comp])
      (by rwa [Category.id_comp]) hBlie
    simpa only [Category.id_comp] using this
  have hπproj : AlgebraicGeometry.IsProjective B.toBase :=
    ClosedBlowupSequence.isProjective_toBase B
  haveI : IsIntegral B.target := hWvar.toIsIntegral
  let O : W₀.Opens := ⟨Sxᶜ, hSxc.isOpen_compl⟩
  haveI : IsIso (B.toBase ∣_ O) := hπiso O disjoint_compl_left
  have hOne : (O : Set W₀).Nonempty := ⟨_, hSxgen⟩
  have hπbir : IsBirationalMorphism B.toBase := by
    obtain ⟨z, -⟩ := (B.toBase ∣_ O).surjective ⟨_, hSxgen⟩
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE B.toBase (B.toBase ⁻¹ᵁ O) O
      ⟨_, z.2⟩ hOne le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  -- instances on `W = B.target`
  haveI : LocallyOfFiniteType (B.toBase ≫ f₀ ≫ sS) := hWvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian B.target :=
    LocallyOfFiniteType.isLocallyNoetherian (B.toBase ≫ f₀ ≫ sS)
  haveI : QuasiCompact (B.toBase ≫ f₀ ≫ sS) := hWvar.toQuasiCompact
  haveI : CompactSpace B.target := QuasiCompact.compactSpace_of_compactSpace (B.toBase ≫ f₀ ≫ sS)
  haveI : Smooth (B.toBase ≫ f₀ ≫ sS) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWsm
  haveI : IsNormal B.target := isNormal_of_smooth_over_field (B.toBase ≫ f₀ ≫ sS)
  -- projectivity
  have hW₀qp : IsQuasiProjective (f₀ ≫ sS) :=
    isQuasiProjective_comp_of_exists_isAmple f₀ sS exists_isAmple_spec_complex
      (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f₀ hproj.isHQuasiProjective)
      hS.isQuasiProjective
  have hWqp : IsQuasiProjectiveVariety ℂ (B.toBase ≫ f₀ ≫ sS) :=
    (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hWvar, isQuasiProjective_comp_of_exists_isAmple
      B.toBase (f₀ ≫ sS) exists_isAmple_spec_complex (isQuasiProjective_of_isProjective hπproj)
      hW₀qp⟩
  haveI := hπproj.isProper
  have hπH : IsProjectiveMorphism B.toBase :=
    haveI := hWqp
    haveI := hWv
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
      (B.toBase ≫ f₀ ≫ sS) (f₀ ≫ sS) B.toBase rfl
  have hfbir : IsBirationalMorphism (B.toBase ≫ f₀) := isBirationalMorphism_comp hπbir hbir
  -- `J 𝒪_W` and its factor `I 𝒪_W` are monomial, hence invertible
  have hJcart : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap B.toBase) :=
    (exists_divisorWithCoeffs_of_isMonomialIdeal (B.toBase ≫ f₀ ≫ sS) hWsm _
      hJmono).choose_spec.2.1
  have hJcart' : Stacks.Divisors.IsEffectiveCartierDivisor
      ((I.comap f₀).comap B.toBase * M.comap B.toBase) := by
    rwa [← Stacks.IdealSheaf.comap_mul]
  have hIcart : Stacks.Divisors.IsEffectiveCartierDivisor ((I.comap f₀).comap B.toBase) :=
    AlgebraicGeometry.isEffectiveCartierDivisor_right_of_mul _ _
      (mul_comm (M.comap B.toBase) _ ▸ hJcart')
  have hImono : IsMonomialIdeal ((I.comap f₀).comap B.toBase) :=
    isMonomialIdeal_of_mul hIcart hJcart' (by rw [← Stacks.IdealSheaf.comap_mul]; exact hJmono)
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (B.toBase ≫ f₀)) := by
    rwa [Scheme.IdealSheafData.comap_comp]
  -- the lifts to `Bl_J W₀` and to `T = Bl_I S`
  set h₁ := blowUpLift J B.toBase hJcart with hh₁def
  have hh₁ : h₁ ≫ blowUpToBase J = B.toBase := blowUpLift_comp _ _ _
  set h := blowUpLift I (B.toBase ≫ f₀) hcart with hhdef
  have hh : h ≫ blowUpToBase I = B.toBase ≫ f₀ := blowUpLift_comp _ _ _
  haveI : IsProper (blowUpToBase J) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian J)
  haveI : QuasiCompact (h₁ ≫ blowUpToBase J) := by rw [hh₁]; infer_instance
  haveI : QuasiCompact h₁ := QuasiCompact.of_comp h₁ (blowUpToBase J)
  haveI : IsProper (blowUpToBase I) :=
    TwoStepTower.isProper_blowUpToBase (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  haveI : IsProper f₀ := isProper_of_isProjectiveMorphism f₀ hproj
  haveI : QuasiCompact (h ≫ blowUpToBase I) := by rw [hh]; infer_instance
  haveI : QuasiCompact h := QuasiCompact.of_comp h (blowUpToBase I)
  have hπr : h ≫ r = B.toBase := by
    haveI : IsSeparated f₀ := (isProper_of_isProjectiveMorphism f₀ hproj).toIsSeparated
    refine eq_of_comp_eq_of_isSeparated f₀ (by rw [Category.assoc, hr, hh]) ?_
    refine ⟨genericPoint B.target, ?_⟩
    change ((h ≫ r) ≫ f₀) (genericPoint _) ∈ biregularLocus f₀
    rw [Category.assoc, hr, hh]
    haveI : IsDominant (B.toBase ≫ f₀) := hfbir.isDominant
    rw [map_genericPoint_of_isDominant]
    exact hgenbir
  -- a `π`-exceptional divisor whose negative is relatively ample
  obtain ⟨G, hGc, hGamp, hGsupp⟩ : ∃ G : Divisor B.target, ∃ hGc : (-G).IsCartier,
      (-G).IsRelativelyAmple B.toBase hGc ∧
        ∀ P : MMP.Mori.PrimeDivisor B.target, G.coeff P ≠ 0 → B.toBase P.genericPoint ∈ Sx := by
    haveI : IsDominant B.toBase := hπbir.isDominant
    haveI : Smooth (f₀ ≫ sS) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWs
    haveI : IsNormal W₀ := isNormal_of_smooth_over_field (f₀ ≫ sS)
    have hW₀qpv : IsQuasiProjectiveVariety ℂ (f₀ ≫ sS) :=
      (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hWv, hW₀qp⟩
    have hW₀H : Stacks.HProjective.IsHQuasiProjective (f₀ ≫ sS) :=
      ((isQuasiProjectiveVariety_iff_isHQuasiProjective ℂ _).1 hW₀qpv).2
    obtain ⟨G, hGc, hGπ, hGs⟩ :=
      exists_isRelativelyAmple_neg_of_isIso B.toBase hWvar hWv hW₀H hWs hπH O hOne
    exact ⟨G, hGc, hGπ, fun P hP => by_contra fun hc => hGs P hP hc⟩
  -- the monomial divisors of `J 𝒪_W` and of `I 𝒪_W`
  obtain ⟨DJ, hDJsnc, -, hDJprod⟩ :=
    exists_divisorWithCoeffs_of_isMonomialIdeal (B.toBase ≫ f₀ ≫ sS) hWsm _ hJmono
  have hDJmem : ∀ P : MMP.Mori.PrimeDivisor B.target,
      P ∈ DJ.support ↔ B.toBase P.genericPoint ∈ J.support := by
    intro P
    rw [mem_support_iff_genericPoint_mem DJ hDJprod P, Scheme.IdealSheafData.support_comap]
    rfl
  have hsuppJ : ((J.comap B.toBase).support : Set B.target) =
      ⋃ P ∈ DJ.support, (P.idealSheaf.support : Set B.target) := by
    rw [hDJprod, coe_support_prod_pow _ _ _ fun E hE => Finsupp.mem_support_iff.1 hE]
  obtain ⟨DI, -, -, hDIprod⟩ :=
    exists_divisorWithCoeffs_of_isMonomialIdeal (B.toBase ≫ f₀ ≫ sS) hWsm _ hImono
  have hDIDJ : ∀ P ∈ DI.support, P ∈ DJ.support := by
    intro P hP
    rw [mem_support_iff_genericPoint_mem DI hDIprod P, Scheme.IdealSheafData.support_comap] at hP
    rw [hDJmem, hJdef, Scheme.IdealSheafData.support_mul]
    exact Or.inl hP
  -- composition with the blow-up `Bl_J W₀ ⟶ W₀`: `G₁ = G + n₁ K_J`
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∃ hc : (-(G + n •
      (∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ)))).IsCartier,
      (-(G + n • (∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ)))).IsRelativelyAmple
        B.toBase hc := by
    have hGh₁ : (-G).IsRelativelyAmple h₁ hGc := by
      haveI := hGc.isInvertibleModule_divisorialSheaf
      have h1 := stacks_of_isRelativelyAmple B.toBase _ hGamp
      rw [← hh₁] at h1
      exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
        (Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp h₁
          (blowUpToBase J) _ h1 inferInstance)
    rw [← hh₁]
    exact exists_isRelativelyAmple_neg_add_nsmul_of_blowUp _ hWsm J h₁ DJ.support DJ
      (by rwa [hh₁]) hGc hGh₁
  set KJ : Divisor B.target := ∑ E ∈ DJ.support, (DJ E : ℤ) • Finsupp.single E (1 : ℤ)
    with hKJdef
  set N₁ : ℕ := n₁ + ∑ P ∈ DJ.support, (G.coeff P).natAbs + 1 with hN₁def
  obtain ⟨hG₁c, hG₁amp⟩ := hn₁ N₁ (by omega)
  set G₁ := G + N₁ • KJ with hG₁def
  have hG₁pos : ∀ P ∈ DJ.support, 0 < G₁.coeff P := by
    intro P hP
    rw [hG₁def, coeff_add_nsmul, coeff_sum_natCast_smul_single]
    have hGle : (G.coeff P).natAbs ≤ ∑ Q ∈ DJ.support, (G.coeff Q).natAbs :=
      Finset.single_le_sum (f := fun Q => (G.coeff Q).natAbs) (fun _ _ => Nat.zero_le _) hP
    exact pos_add_mul_of_natAbs_lt (Finsupp.mem_support_iff.1 hP) (by rw [hN₁def]; omega)
  have hG₁out : ∀ P ∉ DJ.support, G₁.coeff P ≠ 0 → B.toBase P.genericPoint ∈ E.doubleLocus := by
    intro P hP hG
    rw [hG₁def, coeff_add_nsmul, coeff_sum_natCast_smul_single, Finsupp.notMem_support_iff.1 hP,
      Nat.cast_zero, mul_zero, add_zero] at hG
    exact (hGsupp P hG).resolve_left fun h => hP ((hDJmem P).2 h)
  -- composition with the blow-up `T ⟶ S`: `D = G₁ + n₀ K_I`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ hc : (-(G₁ + n •
      (∑ E ∈ DI.support, (DI E : ℤ) • Finsupp.single E (1 : ℤ)))).IsCartier,
      (-(G₁ + n • (∑ E ∈ DI.support, (DI E : ℤ) • Finsupp.single E (1 : ℤ)))).IsRelativelyAmple
        (B.toBase ≫ f₀) hc := by
    haveI : QuasiCompact sS := hSv.toQuasiCompact
    haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
    haveI : AlgebraicGeometry.IsNoetherian S := ⟨⟩
    have hG₁h : (-G₁).IsRelativelyAmple h hG₁c := by
      haveI := hG₁c.isInvertibleModule_divisorialSheaf
      have h1 := stacks_of_isRelativelyAmple B.toBase _ hG₁amp
      rw [← hπr] at h1
      exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
        (Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp h r _ h1
          inferInstance)
    rw [← hh]
    exact exists_isRelativelyAmple_neg_add_nsmul_of_blowUp _ hWsm I h DI.support DI
      (by rw [hh, Scheme.IdealSheafData.comap_comp]; exact hDIprod) hG₁c hG₁h
  obtain ⟨hDc, hDamp⟩ := hn₀ n₀ le_rfl
  have hDcoeff : ∀ P, (G₁ + n₀ • (∑ E ∈ DI.support, (DI E : ℤ) • Finsupp.single E (1 : ℤ) :
      Divisor B.target)).coeff P = G₁.coeff P + n₀ * DI P := by
    intro P
    rw [coeff_add_nsmul, coeff_sum_natCast_smul_single]
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨hSv, hWvar, hWsm, hπH.comp hproj, hfbir⟩, hWqp, hπH,
    fun U hU => hπiso U hU, hcart, DJ, isSNC_of_isSNCFamily _ DJ hDJsnc, hDJmem, hsuppJ, _,
    fun P hP => ?_, fun P hP hD => ?_, hDc, hDamp⟩
  · rw [hDcoeff]
    have := hG₁pos P hP
    positivity
  · have hDI : DI P = 0 := Finsupp.notMem_support_iff.1 fun h => hP (hDIDJ P h)
    rw [hDcoeff, hDI, Nat.cast_zero, mul_zero, add_zero] at hD
    exact hG₁out P hP hD

/-- On a fourfold of finite type over `ℂ`, a point of a closed subset of dimension at most one
has coheight at least two. -/
theorem one_lt_coheight_of_mem {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    [LocallyOfFiniteType sX] (hXdim : topologicalKrullDim X = 4) (C : Closeds X)
    (hC : topologicalKrullDim (C : Set X) ≤ 1) {x : X} (hx : x ∈ (C : Set X)) :
    1 < Order.coheight x := by
  rw [← not_le]
  intro hle
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x
  rw [hXdim] at h
  have hsub : closure ({x} : Set X) ⊆ (C : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2 hx) C.isClosed
  have ha : topologicalKrullDim (closure ({x} : Set X)) ≤ 1 :=
    ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hC
  have h2 : topologicalKrullDim (closure ({x} : Set X)) + (Order.coheight x : WithBot ℕ∞) ≤
      1 + 1 := add_le_add ha (by exact_mod_cast hle)
  rw [h] at h2
  exact absurd h2 (by decide)

/-- **A dominating snc model with an antiample exceptional divisor, biregular off `C`.** Let
`p : Y ⟶ X` be a projective birational morphism of normal projective complex fourfolds and
`C ⊆ X` a closed subset of dimension at most one. There is a projective morphism `r : Z ⟶ Y` such
that `f = r ≫ p` is a projective resolution of `X` with `Z` projective, the exceptional set of `f`
is the support of a reduced snc divisor `F`, some `D = ∑ mᵢ Fᵢ` with all `mᵢ > 0` has `-D` Cartier
and `f`-ample, and `f⁻¹(C)` is the support of a reduced snc divisor. Moreover `f` is an
isomorphism over every point `x ∉ C` over which `p` is an isomorphism and whose preimage lies in
the smooth locus of `Y`; for `p = 𝟙` this says that `r` is an isomorphism over `Y_reg ∖ C`. -/
public theorem exists_isResolution_comp_isSNC_isRelativelyAmple_neg_and_mem_biregularLocus
    {X Y : Scheme.{0}} [IsNormal X] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {p : Y ⟶ X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXdim : topologicalKrullDim X = 4)
    (hY : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX)) (hYdim : topologicalKrullDim Y = 4)
    (hp : IsProjectiveMorphism p) (hpb : MMP.Mori.IsBirationalMorphism p)
    (C : Closeds X) (hC : topologicalKrullDim (C : Set X) ≤ 1) :
    ∃ (Z : Scheme.{0}) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (_ : CompactSpace Z)
      (r : Z ⟶ Y),
      IsProjectiveMorphism r ∧ MMP.Intersection.IsResolution sX (r ≫ p) ∧
      MMP.Mori.IsProjectiveVariety ℂ (r ≫ p ≫ sX) ∧
      (∀ x : X, x ∉ (C : Set X) → x ∈ biregularLocus p →
        (∀ y, p y = x → y ∈ smoothLocus (p ≫ sX)) → x ∈ biregularLocus (r ≫ p)) ∧
      (∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
        DivisorWithCoeffs.IsSNC (r ≫ p ≫ sX) F ∧
        (F.supp : Set Z) = exceptionalSet (r ≫ p) ∧
        ∃ D : Divisor Z, (∀ P ∈ F.support, 0 < D.coeff P) ∧ (∀ P ∉ F.support, D.coeff P = 0) ∧
          ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (r ≫ p) h) ∧
      ∃ G : Divisor Z, MMP.Intersection.IsReducedEffective G ∧
        DivisorWithCoeffs.IsSNC (r ≫ p ≫ sX) G ∧
        (G.supp : Set Z) = (r ≫ p).base ⁻¹' (C : Set X) := by
  classical
  obtain ⟨hXv, hXproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sX).1 hX
  obtain ⟨hYv, hYproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ (p ≫ sX)).1 hY
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- quasi-projectivity of `X` and `Y`
  have hXqp : IsQuasiProjectiveVariety ℂ sX := (isQuasiProjectiveVariety_iff ℂ _).2
    ⟨hXv, Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX
      hXproj.isHQuasiProjective⟩
  have hYqp : IsQuasiProjectiveVariety ℂ (p ≫ sX) := (isQuasiProjectiveVariety_iff ℂ _).2
    ⟨hYv, Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective _
      hYproj.isHQuasiProjective⟩
  -- a projective resolution `q : Y₀ ⟶ Y`
  have htop : (⊤ : Y.IdealSheafData) ≠ ⊥ := ne_bot_of_genericPoint_notMem_support (by
    rw [Scheme.IdealSheafData.support_top]; exact id)
  obtain ⟨Y₀, q, hY₀v, hqproj, hqbir, hY₀s, hqiso, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (p ≫ sX) hYv
      ⊤ htop
  haveI := hqproj.isProper
  haveI : QuasiCompact (p ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (p ≫ sX)
  have hY₀qp : IsQuasiProjectiveVariety ℂ (q ≫ p ≫ sX) :=
    (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hY₀v, isQuasiProjective_comp_of_exists_isAmple
      q (p ≫ sX) exists_isAmple_spec_complex (isQuasiProjective_of_isProjective hqproj)
      hYqp.isQuasiProjective⟩
  have hqH : IsProjectiveMorphism q :=
    haveI := hY₀qp
    haveI := hYv
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety
      (q ≫ p ≫ sX) (p ≫ sX) q rfl
  haveI : IsIntegral Y₀ := hY₀v.toIsIntegral
  have hf₀ : MMP.Intersection.IsResolution sX (q ≫ p) :=
    ⟨hXv, by rw [Category.assoc]; exact hY₀v, by rw [Category.assoc]; exact hY₀s,
      hqH.comp hp, isBirationalMorphism_comp hqbir hpb⟩
  haveI : IsProper (q ≫ p) := isProper_of_isProjectiveMorphism _ (hqH.comp hp)
  -- points of codimension at most one lie in the biregular locus of `q ≫ p`
  have hcodim : ∀ x : X, Order.coheight x ≤ 1 → x ∈ biregularLocus (q ≫ p) := fun x hx =>
    MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one ⟨hXv, inferInstance⟩ (q ≫ p)
      hf₀.2.1 hf₀.2.2.2.2 (by rw [ringKrullDim_stalk_eq_coheight]; exact_mod_cast hx)
  -- points of `C` have coheight at least two
  have hCcoh : ∀ x ∈ (C : Set X), ¬ Order.coheight x ≤ 1 := fun _ hx =>
    not_le.2 (one_lt_coheight_of_mem sX hXdim C hC hx)
  have hgencoh : Order.coheight (genericPoint X) = 0 :=
    Order.coheight_eq_zero.2 fun z _ => Scheme.le_iff_specializes.2 (genericPoint_specializes z)
  have hgenbir : genericPoint X ∈ biregularLocus (q ≫ p) := hcodim _ (by rw [hgencoh]; simp)
  -- the ideal `K = I_{Ex} · I_C`
  set Nb : Closeds X := (biregularLocus (q ≫ p)).compl with hNbdef
  set nb : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Nb with hnbdef
  set m : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal C with hmdef
  have hnbsupp : (nb.support : Set X) = Nb := by
    rw [hnbdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hmsupp : (m.support : Set X) = C := by
    rw [hmdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hKsupp : ∀ y : X, y ∈ (nb * m).support ↔ y ∉ biregularLocus (q ≫ p) ∨ y ∈ C := by
    intro y
    rw [Scheme.IdealSheafData.support_mul]
    change y ∈ (nb.support : Set X) ∨ y ∈ (m.support : Set X) ↔ _
    rw [hnbsupp, hmsupp]
    rfl
  have hK : genericPoint X ∉ (nb * m).support := by
    rw [hKsupp]
    rintro (h | h)
    · exact h hgenbir
    · exact hCcoh _ h (by rw [hgencoh]; simp)
  -- the principalized model, with no further ideal and empty boundary
  have hEempty : (OrderedDivisor.empty Y₀).IsOrderedSNC ((q ≫ p) ≫ sX) := by
    haveI : Smooth ((q ≫ p) ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hf₀.2.2.1
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
    have := isRegularLocalRing_stalk_of_smooth_over_field ((q ≫ p) ≫ sX) x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y₀.presheaf.stalk x)
    exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩
  have htop : IsNonzeroAtGenericPoints (⊤ : Y₀.IdealSheafData) :=
    (isNonzeroAtGenericPoints_iff _).2 (by rw [Scheme.IdealSheafData.support_top]; exact id)
  obtain ⟨I, ⟨A, hIA⟩, hKI, hIbir, B, -, -, -, -, _, _, _, hres, hWqp, hrH, hriso, hcart, DJ,
    hDJsnc, hDJmem, hsuppJ, D, hDpos, hD0, hDc, hDamp⟩ :=
    exists_principalization_isRelativelyAmple_neg hXqp hf₀ hgenbir (nb * m) hK ⊤ htop
      (OrderedDivisor.empty Y₀) hEempty
  let W : Scheme.{0} := B.target
  set r : W ⟶ Y₀ := B.toBase with hrdef
  have hnodouble : ∀ y : Y₀, y ∉ (OrderedDivisor.empty Y₀).doubleLocus :=
    fun _ ⟨i, _⟩ => i.elim0
  rw [← Scheme.IdealSheafData.one_eq_top, mul_one] at hriso hDJmem hsuppJ
  replace hriso : IsIso (r ∣_ (I.comap (q ≫ p)).support.compl) :=
    hriso _ (Set.disjoint_union_right.2 ⟨disjoint_compl_left, Set.disjoint_left.2
      fun y _ => hnodouble y⟩)
  replace hDJmem : ∀ P : MMP.Mori.PrimeDivisor W,
      P ∈ DJ.support ↔ (r ≫ q ≫ p) P.genericPoint ∈ I.support := fun P =>
    (hDJmem P).trans (by rw [Scheme.IdealSheafData.support_comap]; rfl)
  rw [← Scheme.IdealSheafData.comap_comp] at hsuppJ
  replace hD0 : ∀ P ∉ DJ.support, D.coeff P = 0 :=
    fun P hP => by_contra fun h => hnodouble _ (hD0 P hP h)
  -- the cosupport of `I`
  have hIsupp : ∀ y : X, y ∈ I.support ↔ y ∉ biregularLocus (q ≫ p) ∨ y ∈ C := by
    intro y
    rw [← hKsupp]
    refine ⟨fun hy => ?_, fun hy => hKI hy⟩
    by_contra hyK
    refine hIbir y ?_ hyK hy
    by_contra hyb
    exact hyK ((hKsupp y).2 (Or.inl hyb))
  set f := r ≫ q ≫ p with hfdef
  haveI : IsDominant f := hres.2.2.2.2.isDominant
  -- `f` is an isomorphism off `V(I)`
  have hUf : ∀ y : X, y ∉ I.support → y ∈ biregularLocus f := by
    set U₀ : X.Opens := I.support.compl with hU₀
    have hU₀b : U₀ ≤ biregularLocus (q ≫ p) := fun y hy => by
      by_contra hyb
      exact hy ((hIsupp y).2 (Or.inl hyb))
    haveI : IsIso ((q ≫ p) ∣_ U₀) := isBiregular_iff_le_biregularLocus.2 hU₀b
    have e : (q ≫ p) ⁻¹ᵁ U₀ = (I.comap (q ≫ p)).support.compl := by
      ext y
      change (q ≫ p) y ∉ I.support ↔ y ∉ (I.comap (q ≫ p)).support
      rw [Scheme.IdealSheafData.support_comap]
      rfl
    haveI : IsIso (r ∣_ (q ≫ p) ⁻¹ᵁ U₀) := by rwa [e]
    haveI := isIso_restrict_comp r (q ≫ p) U₀
    intro y hy
    exact le_biregularLocus (f := r ≫ q ≫ p) (V := U₀) this hy
  -- `q ≫ p` is an isomorphism over the points of `biregularLocus p` with smooth fibre
  have hbir : ∀ x : X, x ∈ biregularLocus p → (∀ y, p y = x → y ∈ smoothLocus (p ≫ sX)) →
      x ∈ biregularLocus (q ≫ p) := by
    intro x hxp hxs
    haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
    have hFc : IsClosed (p.base '' ((smoothLocus (p ≫ sX) : Set Y)ᶜ)) :=
      p.isClosedMap _ (smoothLocus (p ≫ sX)).isOpen.isClosed_compl
    let O : X.Opens := biregularLocus p ⊓ ⟨_, hFc.isOpen_compl⟩
    haveI : IsIso (p ∣_ biregularLocus p) := isBiregular_biregularLocus p
    haveI : IsIso (p ∣_ O) := Kollar.isIso_morphismRestrict_of_le p inf_le_left
    have hle : p ⁻¹ᵁ O ≤ smoothLocus (p ≫ sX) ⊓ (⊤ : Y.IdealSheafData).support.compl :=
      fun y hy => ⟨by_contra fun hys => hy.2 ⟨y, hys, rfl⟩, by
        change y ∉ (⊤ : Y.IdealSheafData).support
        rw [Scheme.IdealSheafData.support_top]
        exact id⟩
    haveI : IsIso (q ∣_ p ⁻¹ᵁ O) := Kollar.isIso_morphismRestrict_of_le q hle
    exact le_biregularLocus (isIso_restrict_comp q p O)
      ⟨hxp, fun ⟨y, hy, hyx⟩ => hy (hxs y hyx)⟩
  have hreg : ∀ x : X, x ∉ (C : Set X) → x ∈ biregularLocus p →
      (∀ y, p y = x → y ∈ smoothLocus (p ≫ sX)) → x ∈ biregularLocus f :=
    fun x hxC hxp hxs => hUf x fun hx => ((hIsupp x).1 hx).elim (· (hbir x hxp hxs)) hxC
  -- no generic point of a component of `I 𝒪_W` maps into the biregular locus of `f`
  have hgenP : ∀ P : MMP.Mori.PrimeDivisor W, f P.genericPoint ∈ I.support →
      f P.genericPoint ∉ biregularLocus f := by
    intro P hP hb
    have hco : Order.coheight (f P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    rcases (hIsupp _).1 hP with h | h
    · exact h (hcodim _ hco.le)
    · exact hCcoh _ h hco.le
  -- `Ex(f) = f⁻¹ V(I)`
  have hEx : ∀ w : W, w ∈ exceptionalSet f ↔ f w ∈ I.support := by
    intro w
    rw [mem_exceptionalSet]
    refine ⟨fun hw => by_contra fun h => hw (hUf _ h), fun hw hb => ?_⟩
    have hwJ : w ∈ ((I.comap f).support : Set W) := by
      rwa [Scheme.IdealSheafData.support_comap]
    rw [hsuppJ] at hwJ
    obtain ⟨P, hP, hwP⟩ := Set.mem_iUnion₂.1 hwJ
    have hsp := (Aux.genericPoint_specializes_of_mem_support P hwP).map f.base.hom.continuous
    exact hgenP P ((hDJmem P).1 hP) (hsp.mem_open (biregularLocus f).isOpen hb)
  -- the reduced exceptional divisor `F`
  set F : Divisor W := ∑ Q ∈ DJ.support, Finsupp.single Q (1 : ℤ) with hFdef
  have hDJsnc' : DJ.IsSNC (r ≫ q ≫ p ≫ sX) := by simpa only [Category.assoc] using hDJsnc
  have hFsnc : DivisorWithCoeffs.IsSNC (r ≫ q ≫ p ≫ sX) F :=
    hDJsnc'.of_support_subset fun P hP => (mem_support_sum_single _ P).1 hP
  have hFsupp : (F.supp : Set W) = exceptionalSet f := by
    ext w
    have h1 : w ∈ (F.supp : Set W) ↔ w ∈ ((I.comap f).support : Set W) := by
      rw [hFdef, coe_supp_sum_single, hsuppJ]
    rw [h1, Scheme.IdealSheafData.support_comap]
    exact (hEx w).symm
  -- `m 𝒪_W` is invertible
  have hmcart : Stacks.Divisors.IsEffectiveCartierDivisor (m.comap f) := by
    have h := hcart
    rw [hIA, Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_mul] at h
    exact AlgebraicGeometry.isEffectiveCartierDivisor_right_of_mul _ _
      (AlgebraicGeometry.isEffectiveCartierDivisor_right_of_mul _ _ h)
  -- the reduced divisor `G` with support `f⁻¹(C)`
  set s' := DJ.support.filter fun P => f P.genericPoint ∈ (C : Set X) with hs'
  set Gd : Divisor W := ∑ Q ∈ s', Finsupp.single Q (1 : ℤ) with hGddef
  have hGdsnc : DivisorWithCoeffs.IsSNC (r ≫ q ≫ p ≫ sX) Gd :=
    hDJsnc'.of_support_subset fun P hP =>
      (Finset.mem_filter.1 ((mem_support_sum_single _ P).1 hP)).1
  have hGdsupp : (Gd.supp : Set W) = f.base ⁻¹' (C : Set X) := by
    rw [hGddef, coe_supp_sum_single]
    ext w
    simp only [Set.mem_iUnion₂, Set.mem_preimage]
    refine ⟨fun ⟨P, hP, hwP⟩ => ((Aux.genericPoint_specializes_of_mem_support P hwP).map
      f.base.hom.continuous).mem_closed C.isClosed (Finset.mem_filter.1 hP).2, fun hw => ?_⟩
    have hcomap : ∀ w', w' ∈ ((m.comap f).support : Set W) ↔ f w' ∈ (C : Set X) := fun w' => by
      rw [Scheme.IdealSheafData.support_comap, ← hmsupp]; rfl
    obtain ⟨P, hP, hPm, hwP⟩ := exists_primeDivisor_of_isEffectiveCartierDivisor _ hmcart
      DJ.support (fun w' hw' => by
        rw [← hsuppJ, Scheme.IdealSheafData.support_comap]
        exact (hIsupp _).2 (Or.inr ((hcomap w').1 hw'))) ((hcomap w).2 hw)
    exact ⟨P, Finset.mem_filter.2 ⟨hP, (hcomap _).1 hPm⟩, hwP⟩
  -- assembling
  refine ⟨W, inferInstance, inferInstance, inferInstance, r ≫ q, hrH.comp hqH, ?_⟩
  simp only [Category.assoc]
  refine ⟨hres, (MMP.Mori.isProjectiveVariety_iff ℂ _).2 ⟨?_, ?_⟩, hreg,
    ⟨F, isReducedEffective_sum_single _, hFsnc, hFsupp, D,
      fun P hP => hDpos P ((mem_support_sum_single _ P).1 hP),
      fun P hP => hD0 P fun h => hP ((mem_support_sum_single _ P).2 h), hDc, hDamp⟩,
    Gd, isReducedEffective_sum_single _, hGdsnc, hGdsupp⟩
  · simpa only [hfdef, Category.assoc] using hres.2.1
  · simpa only [hfdef, Category.assoc] using hres.2.2.2.1.comp hXproj

/-- **A dominating snc model with an antiample exceptional divisor.** Let `p : Y ⟶ X` be a
projective birational morphism of normal projective complex fourfolds and `C ⊆ X` a closed subset
of dimension at most one. There is a projective morphism `r : Z ⟶ Y` such that `f = r ≫ p` is a
projective resolution of `X` with `Z` projective, the exceptional set of `f` is the support of a
reduced snc divisor `F`, some `D = ∑ mᵢ Fᵢ` with all `mᵢ > 0` has `-D` Cartier and `f`-ample, and
`f⁻¹(C)` is the support of a reduced snc divisor. -/
@[mmp "thm_mmp_conductor_antiample_snc_domination"]
public theorem exists_isResolution_comp_isSNC_isRelativelyAmple_neg
    {X Y : Scheme.{0}} [IsNormal X] [IsNormal Y] {sX : X ⟶ Spec (.of ℂ)} {p : Y ⟶ X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXdim : topologicalKrullDim X = 4)
    (hY : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX)) (hYdim : topologicalKrullDim Y = 4)
    (hp : IsProjectiveMorphism p) (hpb : MMP.Mori.IsBirationalMorphism p)
    (C : Closeds X) (hC : topologicalKrullDim (C : Set X) ≤ 1) :
    ∃ (Z : Scheme.{0}) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (_ : CompactSpace Z)
      (r : Z ⟶ Y),
      IsProjectiveMorphism r ∧ MMP.Intersection.IsResolution sX (r ≫ p) ∧
      MMP.Mori.IsProjectiveVariety ℂ (r ≫ p ≫ sX) ∧
      (∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
        DivisorWithCoeffs.IsSNC (r ≫ p ≫ sX) F ∧
        (F.supp : Set Z) = exceptionalSet (r ≫ p) ∧
        ∃ D : Divisor Z, (∀ P ∈ F.support, 0 < D.coeff P) ∧ (∀ P ∉ F.support, D.coeff P = 0) ∧
          ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (r ≫ p) h) ∧
      ∃ G : Divisor Z, MMP.Intersection.IsReducedEffective G ∧
        DivisorWithCoeffs.IsSNC (r ≫ p ≫ sX) G ∧
        (G.supp : Set Z) = (r ≫ p).base ⁻¹' (C : Set X) := by
  obtain ⟨Z, h₁, h₂, h₃, r, hr, hres, hproj, -, hF, hG⟩ :=
    exists_isResolution_comp_isSNC_isRelativelyAmple_neg_and_mem_biregularLocus hX hXdim hY
      hYdim hp hpb C hC
  exact ⟨Z, h₁, h₂, h₃, r, hr, hres, hproj, hF, hG⟩

end MMP.Fourfold
