module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.RealPltSpecialTermination
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Divisor.Principal
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.PltReference

/-!
# Level-one flips with scaling avoid every floor component of a log minimal model

Let `X` be a smooth projective complex fourfold over a projective variety `Z`, and let
`B, C ≥ 0` be real divisors such that `(X, B + C)` is a dlt pair with simple normal crossing
support, and `B` contains an effective ample `ℚ`-divisor `A` with no component in `⌊B + C⌋`.
Let `(Y, B_Y + C_Y)` be a log minimal model of `(X, B + C)` over `Z`, where `C_Y` is the strict
transform of `C` and `B_Y` is the strict transform of `B` plus every prime divisor of `Y`
exceptional over `X` (with coefficient one). Fix any component `E` of `⌊B_Y⌋`.

Consider an infinite sequence `Y = Y_0 ⤏ Y_1 ⤏ ⋯` of `(K_Y + B_Y)`-flips
`Y_i ⟶ Z_i ⟵ Y_{i+1}` over `Z` with scaling of `C_Y` at level one: the boundaries `B_i`, `C_i`
are the strict transforms of `B_Y`, `C_Y`, the upper adjoint `K_{Y_i} + B_i + C_i` is nef over
`Z` and numerically trivial over `Z_i`. Then, for all large `i`, the flipping locus of
`Y_i ⟶ Z_i` is disjoint from the strict transform `E_i` of `E`, and the flipped locus of
`Y_{i+1} ⟶ Z_i` is disjoint from `E_{i+1}`.

The proof builds a plt reference: `E` is either a component of `⌊B + C⌋` or a zero place of
`(X, B + C)`, extracted by stratum blow-ups; a principal perturbation of `B_Y + ε C_Y` makes `E`
the only reduced component while keeping a globally ample component, and special termination for
real plt flips with scaling
(`MMP.Fourfold.eventually_disjoint_exceptionalSet_of_realPltFlip_scaling`) applies.

## Main results

* `MMP.Fourfold.IsRealLogMinimalModel.eventually_disjoint_exceptionalSet_of_levelOne_scaling`.

## Implementation notes

* The flip sequence is written as a family `Y : ℕ → Scheme`, with `Y 0` the log minimal model;
  every step is a real flip (`MMP.Fourfold.IsRealFlipStep`) of projective `ℚ`-factorial
  fourfolds, and the flipping contractions are over `Z` (`f_i ≫ g_i = π_i`,
  `f_i⁺ ≫ g_i = π_{i+1}`). A finite sequence satisfies the conclusion trivially.
* Scaling at level one is: `K_{Y_i} + B_i + C_i` is nef over `Z` and numerically trivial over
  `Z_i`, and it descends crepantly: it is the pull-back of an `ℝ`-Cartier divisor `D_i` on `Z_i`
  whose pull-back to `Y_{i+1}` is the strict transform of `K_{Y_i} + B_i + C_i`. The descent is
  stated with the strict transform rather than `K_{Y_{i+1}} + B_{i+1} + C_{i+1}`, since the
  canonical divisors `K_{Y_i}` are fixed only up to linear equivalence. Together with the
  `(K_{Y_i} + B_i)`-negativity of the step, the scaling threshold of the step is then exactly
  one.
* The strict transforms `E_i` of `E` are data, pinned by `MMP.Fourfold.flipTransformPrimeDivisor`.
* The flipping locus is the exceptional set `MMP.Mori.exceptionalSet`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_lem_fourfold_upper_zero_place_constant_level_reference

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Flips

/-- A scheme separated over `Spec ℂ` is separated over the terminal scheme. -/
private theorem isSeparated_terminal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [Subsingleton.elim (X ↘ ⊤_ Scheme) (sX ≫ Limits.terminal.from _)]
  infer_instance

/-! ### Composites of partial isomorphisms -/

section Composite

variable {X Y Z : Scheme.{0}}

/-- The underlying partial map of a partial isomorphism is dominant. -/
private theorem isDominant_toPartialMap_hom (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  have := AlgebraicGeometry.Opens.isDominant_ι e.dense_target
  change IsDominant (e.iso.hom ≫ e.target.ι)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem isoOfEq_isoImage_inv_ι {S : Scheme.{0}} (U : S.Opens) {A B : U.toScheme.Opens}
    (h : A = B) : (S.isoOfEq (congrArg (U.ι ''ᵁ ·) h)).hom ≫ (U.ι.isoImage B).inv ≫ B.ι =
      (U.ι.isoImage A).inv ≫ A.ι := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The composite `e.trans φ` of partial isomorphisms is the composite of their partial maps. -/
private theorem toPartialMap_trans [IrreducibleSpace X] [Nonempty Y] (e : X.PartialIso Y)
    (φ : Y.PartialIso Z) [IsDominant e.toPartialMap.hom] :
    (e.trans φ).toPartialMap = e.toPartialMap.comp φ.toPartialMap := by
  have h3 : e.iso.inv ''ᵁ (e.target.ι ⁻¹ᵁ (e.target ⊓ φ.source)) =
      (e.iso.hom ≫ e.target.ι) ⁻¹ᵁ φ.source := by
    ext x
    simp only [Scheme.Hom.comp_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · exact fun hx ↦ ⟨e.iso.hom x, by simpa using hx, by simp⟩
  ext1
  · ext x
    simp [Scheme.PartialIso.trans]
  · simp [Scheme.PartialIso.trans]
    simp only [← Category.assoc]
    congr 2
    rw [← cancel_mono φ.source.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Opens.isoOfLE_inv_ι,
      Scheme.Opens.isoOfLE_hom_ι]
    have h2 : (Scheme.Hom.isoImage e.iso.inv (e.target.ι ⁻¹ᵁ (e.target ⊓ φ.source))).inv ≫
        (e.target.ι ⁻¹ᵁ (e.target ⊓ φ.source)).ι =
        (e.iso.inv ''ᵁ (e.target.ι ⁻¹ᵁ (e.target ⊓ φ.source))).ι ≫ e.iso.hom := by
      rw [← Scheme.Hom.isoImage_inv_ι_assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% h2, ← reassoc_of% (isoOfEq_isoImage_inv_ι e.source h3)]
    rfl

/-- The value of a composite partial map at a point of its domain. -/
private theorem comp_hom_apply [PreirreducibleSpace X] [Nonempty Y] (g : X.PartialMap Y)
    [IsDominant g.hom] (h : Y.PartialMap Z) {x : X} (hx : x ∈ g.domain)
    (hy : g.hom ⟨x, hx⟩ ∈ h.domain) :
    ∃ hx' : x ∈ (g.comp h).domain, (g.comp h).hom ⟨x, hx'⟩ = h.hom ⟨g.hom ⟨x, hx⟩, hy⟩ := by
  have hx' : x ∈ g.domain.ι ''ᵁ g.hom ⁻¹ᵁ h.domain := ⟨⟨x, hx⟩, hy, rfl⟩
  refine ⟨hx', ?_⟩
  have h1 : (g.hom ⁻¹ᵁ h.domain).ι ((g.domain.ι.isoImage (g.hom ⁻¹ᵁ h.domain)).inv ⟨x, hx'⟩) =
      ⟨x, hx⟩ := by
    apply g.domain.ι.isOpenEmbedding.injective
    exact congrArg (fun k => k ⟨x, hx'⟩) (Scheme.Hom.isoImage_inv_ι g.domain.ι (g.hom ⁻¹ᵁ h.domain))
  have h2 : (g.hom ∣_ h.domain) ((g.domain.ι.isoImage (g.hom ⁻¹ᵁ h.domain)).inv ⟨x, hx'⟩) =
      ⟨g.hom ⟨x, hx⟩, hy⟩ := by
    apply h.domain.ι.isOpenEmbedding.injective
    have h' := congrArg (fun k => k ((g.domain.ι.isoImage (g.hom ⁻¹ᵁ h.domain)).inv ⟨x, hx'⟩))
      (morphismRestrict_ι g.hom h.domain)
    simp only [Scheme.Hom.comp_apply] at h'
    rw [h', h1]
    rfl
  simp only [Scheme.PartialMap.comp_hom]
  exact congrArg h.hom h2

/-- **Strict transforms along a composite.** If `e : X ⤏ Y` sends a prime divisor `P` to `Q` and
the partial isomorphism `φ : Y ⤏ Z` is defined at the generic point of `Q`, sending it to the
generic point of `Q'`, then `e.trans φ` sends `P` to `Q'`. -/
private theorem transformPrimeDivisor_trans_eq_some [IsIntegral X] [IsIntegral Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)] (e : X.PartialIso Y)
    (φ : Y.PartialIso Z) {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    {Q' : MMP.Mori.PrimeDivisor Z}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some Q)
    (hQ : Q.genericPoint ∈ φ.source)
    (hQ' : Q'.genericPoint = φ.toPartialMap.hom ⟨Q.genericPoint, hQ⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor (e.trans φ).toRationalMap P = some Q' := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
  obtain ⟨g, hPg, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hgQ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hPg
  haveI := isDominant_toPartialMap_hom e
  haveI : IsDominant g.hom := (Scheme.PartialMap.isDominant_hom_iff_of_equiv g e.toPartialMap
    (Scheme.PartialMap.toRationalMap_eq_iff.mp hg)).mpr inferInstance
  have hQg : g.hom ⟨P.genericPoint, hPg⟩ ∈ φ.toPartialMap.domain := hgQ ▸ hQ
  obtain ⟨hx', hval⟩ := comp_hom_apply g φ.toPartialMap hPg hQg
  refine MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq (g.comp φ.toPartialMap) ?_
    hx' ?_
  · change _ = (e.trans φ).toPartialMap.toRationalMap
    rw [toPartialMap_trans]
    exact Scheme.PartialMap.toRationalMap_eq_iff.mpr
      (Scheme.PartialMap.comp_equiv_of_equiv_left
        (Scheme.PartialMap.toRationalMap_eq_iff.mp hg) _)
  · rw [hval]
    refine hQ'.trans ?_
    congr 1
    exact Subtype.ext hgQ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A partial isomorphism followed by its inverse is equivalent to the identity. -/
private theorem comp_symm_equiv_id [IsReduced Y] [IsSeparated (Y ↘ ⊤_ Scheme)]
    [PreirreducibleSpace Y] [Nonempty Z] (φ : Y.PartialIso Z) [IsDominant φ.toPartialMap.hom] :
    (φ.toPartialMap.comp φ.symm.toPartialMap).equiv (Scheme.PartialMap.id Y) := by
  rw [Scheme.PartialMap.id,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  have h1 : (φ.toPartialMap.hom ∣_ φ.target) =
      (φ.toPartialMap.hom ⁻¹ᵁ φ.target).ι ≫ φ.iso.hom := by
    rw [← cancel_mono φ.target.ι, morphismRestrict_ι]
    rfl
  simp only [Scheme.PartialMap.comp_hom, Scheme.PartialMap.comp_domain, Category.comp_id]
  change _ ≫ (φ.toPartialMap.hom ∣_ φ.target) ≫ φ.iso.inv ≫ φ.source.ι = _
  rw [h1, Category.assoc, Iso.hom_inv_id_assoc]
  exact Scheme.Hom.isoImage_inv_ι _ _

/-- Composing with a partial isomorphism and then with its inverse gives back the rational map. -/
private theorem toRationalMap_trans_trans_symm [IrreducibleSpace X] [IsReduced Y]
    [IrreducibleSpace Y] [IsSeparated (Y ↘ ⊤_ Scheme)] [Nonempty Z] (e : X.PartialIso Y)
    (φ : Y.PartialIso Z) : ((e.trans φ).trans φ.symm).toRationalMap = e.toRationalMap := by
  haveI := isDominant_toPartialMap_hom e
  haveI := isDominant_toPartialMap_hom φ
  haveI := isDominant_toPartialMap_hom (e.trans φ)
  change ((e.trans φ).trans φ.symm).toPartialMap.toRationalMap = e.toPartialMap.toRationalMap
  rw [toPartialMap_trans]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_
  have h1 : (e.trans φ).toPartialMap.equiv (e.toPartialMap.comp φ.toPartialMap) := by
    rw [toPartialMap_trans]
  refine (Scheme.PartialMap.comp_equiv_of_equiv_left h1 _).trans ?_
  rw [Scheme.PartialMap.comp_assoc]
  refine (Scheme.PartialMap.comp_equiv_of_equiv_right _ (comp_symm_equiv_id φ)).trans ?_
  rw [Scheme.PartialMap.comp_id]

/-- **Strict transforms back along a composite.** If `e.trans φ` sends `P` to `Q'`, the generic
point of `Q'` lies in the target of `φ`, and `φ⁻¹` sends it to the generic point of `Q`, then `e`
sends `P` to `Q`. -/
private theorem transformPrimeDivisor_eq_some_of_trans [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    (e : X.PartialIso Y) (φ : Y.PartialIso Z) {P : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y} {Q' : MMP.Mori.PrimeDivisor Z}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor (e.trans φ).toRationalMap P = some Q')
    (hQ' : Q'.genericPoint ∈ φ.target)
    (hQ : Q.genericPoint = φ.symm.toPartialMap.hom ⟨Q'.genericPoint, hQ'⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some Q := by
  have := transformPrimeDivisor_trans_eq_some (e.trans φ) φ.symm h hQ' hQ
  rwa [toRationalMap_trans_trans_symm] at this

/-- The inverse of a composite of partial isomorphisms is, as a rational map, the composite of the
inverses in the opposite order. -/
private theorem toRationalMap_symm_trans [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    (e : X.PartialIso Y)
    (φ : Y.PartialIso Z) :
    (e.trans φ).symm.toRationalMap = (φ.symm.trans e.symm).toRationalMap := by
  haveI := isDominant_toPartialMap_hom e
  haveI := isDominant_toPartialMap_hom φ
  haveI := isDominant_toPartialMap_hom e.symm
  haveI := isDominant_toPartialMap_hom φ.symm
  haveI := isDominant_toPartialMap_hom (e.trans φ)
  haveI := isDominant_toPartialMap_hom (e.trans φ).symm
  change (e.trans φ).symm.toPartialMap.toRationalMap =
    (φ.symm.trans e.symm).toPartialMap.toRationalMap
  rw [toPartialMap_trans φ.symm e.symm]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_
  -- `a.comp r ≈ id`, with `a = e.trans φ` and `r = φ⁻¹.comp e⁻¹`
  have hcomp : ((e.trans φ).toPartialMap.comp (φ.symm.toPartialMap.comp e.symm.toPartialMap)).equiv
      (Scheme.PartialMap.id X) := by
    have h0 : (e.trans φ).toPartialMap.equiv (e.toPartialMap.comp φ.toPartialMap) := by
      rw [toPartialMap_trans]
    refine (Scheme.PartialMap.comp_equiv_of_equiv_left h0 _).trans ?_
    rw [Scheme.PartialMap.comp_assoc, ← Scheme.PartialMap.comp_assoc φ.toPartialMap]
    refine (Scheme.PartialMap.comp_equiv_of_equiv_right _
      (Scheme.PartialMap.comp_equiv_of_equiv_left (comp_symm_equiv_id φ) _)).trans ?_
    rw [Scheme.PartialMap.id_comp]
    exact comp_symm_equiv_id e
  have hleft : ((e.trans φ).symm.toPartialMap.comp (e.trans φ).toPartialMap).equiv
      (Scheme.PartialMap.id Z) := comp_symm_equiv_id (e.trans φ).symm
  have h1 := Scheme.PartialMap.comp_equiv_of_equiv_right (e.trans φ).symm.toPartialMap hcomp
  rw [Scheme.PartialMap.comp_id, ← Scheme.PartialMap.comp_assoc] at h1
  have h3 := Scheme.PartialMap.comp_equiv_of_equiv_left hleft
    (φ.symm.toPartialMap.comp e.symm.toPartialMap)
  rw [Scheme.PartialMap.id_comp] at h3
  exact h1.symm.trans h3

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The generic germ of a dominant morphism followed by a partial map is the map of function
fields followed by the generic germ of the partial map. -/
private theorem fromFunctionField_toPartialMap_comp [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    [IsDominant p] (g : Y.PartialMap Z) :
    haveI : IsDominant p.toPartialMap.hom := by
      change IsDominant ((⊤ : X.Opens).ι ≫ p); infer_instance
    (p.toPartialMap.comp g).fromFunctionField =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ g.fromFunctionField := by
  haveI : IsDominant p.toPartialMap.hom := by
    change IsDominant ((⊤ : X.Opens).ι ≫ p); infer_instance
  have hY : genericPoint Y ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  have hX : genericPoint X ∈ (p.toPartialMap.comp g).domain :=
    (genericPoint_specializes _).mem_open (p.toPartialMap.comp g).domain.2
      (p.toPartialMap.comp g).dense_domain.nonempty.choose_spec
  change (p.toPartialMap.comp g).domain.fromSpecStalkOfMem _ hX ≫ (p.toPartialMap.comp g).hom =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      (g.domain.fromSpecStalkOfMem _ hY ≫ g.hom)
  simp only [Scheme.PartialMap.comp_hom, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι]
  simp only [Category.assoc, morphismRestrict_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [show ((p.toPartialMap.hom ⁻¹ᵁ g.domain).ι ≫ p.toPartialMap.hom) =
      (p.toPartialMap.hom ⁻¹ᵁ g.domain).ι ≫ p.toPartialMap.domain.ι ≫ p from rfl,
    Scheme.Hom.isoImage_inv_ι_assoc]
  change (p.toPartialMap.comp g).domain.fromSpecStalkOfMem _ hX ≫
    (p.toPartialMap.comp g).domain.ι ≫ p = _
  rw [Scheme.Opens.fromSpecStalkOfMem_ι_assoc, AlgebraicGeometry.functionFieldMap_fromSpecStalk]

/-- **Injectivity at a point where the inverse is defined.** If the inverse of a partial
isomorphism `e` is defined at the generic point of `Q`, at most one prime divisor is sent to `Q`
by `e`: its generic point is the image of that of `Q` under `e⁻¹`. -/
private theorem eq_of_transformPrimeDivisor_eq_some_of_mem_domain [IsIntegral X] [IsIntegral Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] (e : X.PartialIso Y)
    {P₁ P₂ : MMP.Mori.PrimeDivisor X}
    {Q : MMP.Mori.PrimeDivisor Y}
    (h₁ : MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P₁ = some Q)
    (h₂ : MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P₂ = some Q)
    (hQ : Q.genericPoint ∈ e.symm.toRationalMap.domain) : P₁ = P₂ := by
  obtain ⟨q, hQq, hq⟩ := Scheme.RationalMap.mem_domain.mp hQ
  haveI := isDominant_toPartialMap_hom e
  have key : ∀ P : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some Q →
        P.genericPoint = q.hom ⟨Q.genericPoint, hQq⟩ := by
    intro P hP
    obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hP
    obtain ⟨g, hPg, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
    have hgQ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g hg hPg
    haveI : IsDominant g.hom := (Scheme.PartialMap.isDominant_hom_iff_of_equiv g e.toPartialMap
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hg)).mpr inferInstance
    have hmem : g.hom ⟨P.genericPoint, hPg⟩ ∈ q.domain := hgQ ▸ hQq
    obtain ⟨hx', hval⟩ := comp_hom_apply g q hPg hmem
    have hid : (g.comp q).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
      refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_
      refine (Scheme.PartialMap.comp_equiv_of_equiv_left
        (Scheme.PartialMap.toRationalMap_eq_iff.mp hg) q).trans ?_
      refine (Scheme.PartialMap.comp_equiv_of_equiv_right _
        (Scheme.PartialMap.toRationalMap_eq_iff.mp hq)).trans ?_
      exact comp_symm_equiv_id e
    have h3 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hid hx'
      (show P.genericPoint ∈ (Scheme.PartialMap.id X).domain from trivial)
    rw [hval] at h3
    have h4 : (⟨g.hom ⟨P.genericPoint, hPg⟩, hmem⟩ : q.domain.toScheme) =
        ⟨Q.genericPoint, hQq⟩ := Subtype.ext hgQ.symm
    rw [h4] at h3
    exact h3.symm
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((key P₁ h₁).trans (key P₂ h₂).symm)

end Composite

/-! ### Partial isomorphisms that are isomorphisms in codimension one -/

section CodimOne

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsSeparated (Y ↘ ⊤_ Scheme)]

/-- A partial isomorphism defined at the generic point of a prime divisor `Q` sends it to the
generic point of a prime divisor, the strict transform of `Q`. -/
private theorem exists_transformPrimeDivisor_eq_some (φ : X.PartialIso Y)
    (Q : MMP.Mori.PrimeDivisor X) (hQ : Q.genericPoint ∈ φ.source) :
    ∃ Q' : MMP.Mori.PrimeDivisor Y,
      MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap Q = some Q' ∧
        Q'.genericPoint = φ.toPartialMap.hom ⟨Q.genericPoint, hQ⟩ := by
  have hemb : Topology.IsOpenEmbedding φ.toPartialMap.hom :=
    (φ.iso.hom ≫ φ.target.ι).isOpenEmbedding
  have h1 : Order.coheight (φ.toPartialMap.hom ⟨Q.genericPoint, hQ⟩) = 1 := by
    have e1 := Topology.IsOpenEmbedding.coheight_eq (x := ⟨Q.genericPoint, hQ⟩) _ hemb
    have e2 := Topology.IsOpenEmbedding.coheight_eq (x := ⟨Q.genericPoint, hQ⟩) _
      φ.source.ι.isOpenEmbedding
    exact e1.trans (e2.symm.trans (MMP.Mori.PrimeDivisor.coheight_genericPoint Q))
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1⟩
  exact MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap rfl hQ
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1)

/-- The strict transform of prime divisors under a partial isomorphism is injective on the prime
divisors whose generic points lie in its source. -/
private theorem transformPrimeDivisor_injective (φ : X.PartialIso Y)
    {Q₁ Q₂ : MMP.Mori.PrimeDivisor X} {Q' : MMP.Mori.PrimeDivisor Y}
    (hQ₁ : Q₁.genericPoint ∈ φ.source) (hQ₂ : Q₂.genericPoint ∈ φ.source)
    (h₁ : MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap Q₁ = some Q')
    (h₂ : MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap Q₂ = some Q') :
    Q₁ = Q₂ := by
  have e₁ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h₁ φ.toPartialMap rfl hQ₁
  have e₂ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h₂ φ.toPartialMap rfl hQ₂
  have hinj : Function.Injective φ.toPartialMap.hom :=
    (φ.iso.hom ≫ φ.target.ι).isOpenEmbedding.injective
  have := hinj (e₁.symm.trans e₂)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (congrArg Subtype.val this)

/-- The coefficient of a strict transform under a partial isomorphism which is defined at the
generic points of all prime divisors. -/
private theorem coeff_transformDivisor_of_eq_some {R : Type*} [AddCommMonoid R]
    (φ : X.PartialIso Y) (hs : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ φ.source)
    {Q : MMP.Mori.PrimeDivisor X} {Q' : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap Q = some Q')
    (D : DivisorWithCoeffs R X) :
    (MMP.Mori.RationalMap.transformDivisor φ.toRationalMap D) Q' = D Q :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h
    (fun _ h' => transformPrimeDivisor_injective φ (hs _) (hs Q) h' h) D

/-- A prime divisor whose generic point lies in the target of a partial isomorphism is the strict
transform of a prime divisor whose generic point lies in the source. -/
private theorem exists_transformPrimeDivisor_eq_some_of_mem_target [IsSeparated (X ↘ ⊤_ Scheme)]
    (φ : X.PartialIso Y) (Q' : MMP.Mori.PrimeDivisor Y) (hQ' : Q'.genericPoint ∈ φ.target) :
    ∃ (Q : MMP.Mori.PrimeDivisor X) (hQ : Q.genericPoint ∈ φ.source),
      MMP.Mori.RationalMap.transformPrimeDivisor φ.toRationalMap Q = some Q' ∧
        Q'.genericPoint = φ.toPartialMap.hom ⟨Q.genericPoint, hQ⟩ := by
  obtain ⟨Q, -, hQ⟩ := exists_transformPrimeDivisor_eq_some φ.symm Q' hQ'
  set y : φ.target.toScheme := ⟨Q'.genericPoint, hQ'⟩ with hy
  set p : φ.source.toScheme := φ.iso.inv y with hp
  have hQp : Q.genericPoint = φ.source.ι p := hQ
  have hmem : Q.genericPoint ∈ φ.source := by rw [hQp]; exact p.2
  have key : φ.iso.hom p = y := by
    rw [hp, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have hval : φ.toPartialMap.hom ⟨Q.genericPoint, hmem⟩ = Q'.genericPoint := by
    have e1 : (⟨Q.genericPoint, hmem⟩ : φ.source.toScheme) = p := Subtype.ext hQp
    change (φ.iso.hom ≫ φ.target.ι) ⟨Q.genericPoint, hmem⟩ = _
    rw [e1, Scheme.Hom.comp_apply, key]
    rfl
  exact ⟨Q, hmem, MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap rfl
    hmem hval.symm, hval.symm⟩

/-- **Divisor transforms along a composite.** If `φ : Y ⤏ Z` is a partial isomorphism defined at
the generic points of all prime divisors of `Y` and of `Z`, then `(e.trans φ)_* = φ_* ∘ e_*`. -/
private theorem transformDivisor_trans {Z : Scheme.{0}} [IsIntegral Z] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {R : Type*} [AddCommMonoid R] (e : X.PartialIso Y) (φ : Y.PartialIso Z)
    (hs : ∀ Q : MMP.Mori.PrimeDivisor Y, Q.genericPoint ∈ φ.source)
    (ht : ∀ Q : MMP.Mori.PrimeDivisor Z, Q.genericPoint ∈ φ.target)
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (e.trans φ).toRationalMap D =
      MMP.Mori.RationalMap.transformDivisor φ.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor e.toRationalMap D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' hD hD' => rw [map_add, map_add, map_add, hD, hD']
  | single P r =>
    rw [MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases h : MMP.Mori.RationalMap.transformPrimeDivisor e.toRationalMap P with
    | none =>
      cases h' : MMP.Mori.RationalMap.transformPrimeDivisor (e.trans φ).toRationalMap P with
      | none => simp
      | some Q' =>
        exfalso
        obtain ⟨Q, -, hQ⟩ := exists_transformPrimeDivisor_eq_some φ.symm Q' (ht Q')
        have := transformPrimeDivisor_eq_some_of_trans e φ h' (ht Q') hQ
        rw [h] at this
        exact absurd this (by simp)
    | some Q =>
      obtain ⟨Q', hQ', hval⟩ := exists_transformPrimeDivisor_eq_some φ Q (hs Q)
      rw [transformPrimeDivisor_trans_eq_some e φ h (hs Q) hval]
      simp only [Option.elim]
      rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some hQ']

/-- **Generic points of extracted primes along a composite.** Let `φ : Y ⤏ Z` be a partial
isomorphism defined at the generic points of all prime divisors of `Y` and `Z`. If every prime of
`Y` extracted by `e : X ⤏ Y` has its generic point sent outside `A` by `e⁻¹`, the same holds for
`e.trans φ`. -/
private theorem forall_isInverseExceptional_trans {Z : Scheme.{0}} [IsIntegral Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (X ↘ ⊤_ Scheme)] (e : X.PartialIso Y)
    (φ : Y.PartialIso Z) (hs : ∀ Q : MMP.Mori.PrimeDivisor Y, Q.genericPoint ∈ φ.source)
    (ht : ∀ Q : MMP.Mori.PrimeDivisor Z, Q.genericPoint ∈ φ.target) (A : Set X)
    (H : ∀ F : MMP.Mori.PrimeDivisor Y,
      MMP.Flips.RationalMap.IsInverseExceptional e.toRationalMap F →
      ∀ q : Y.PartialMap X, q.toRationalMap = e.symm.toRationalMap →
        ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ A) :
    ∀ F : MMP.Mori.PrimeDivisor Z,
      MMP.Flips.RationalMap.IsInverseExceptional (e.trans φ).toRationalMap F →
      ∀ q : Z.PartialMap X, q.toRationalMap = (e.trans φ).symm.toRationalMap →
        ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ A := by
  intro F' hF' q hq hF'q
  obtain ⟨F, hFs, hFF', hval⟩ := exists_transformPrimeDivisor_eq_some_of_mem_target φ F' (ht F')
  have hFexc : MMP.Flips.RationalMap.IsInverseExceptional e.toRationalMap F := fun P hP =>
    hF' P (transformPrimeDivisor_trans_eq_some e φ hP hFs hval)
  haveI := isDominant_toPartialMap_hom e.symm
  haveI := isDominant_toPartialMap_hom φ
  haveI := isDominant_toPartialMap_hom φ.symm
  have hmem : φ.toPartialMap.hom ⟨F.genericPoint, hFs⟩ ∈ q.domain := hval ▸ hF'q
  obtain ⟨hx', hval'⟩ := comp_hom_apply φ.toPartialMap q hFs hmem
  have hq' : (φ.toPartialMap.comp q).toRationalMap = e.symm.toRationalMap := by
    rw [toRationalMap_symm_trans, Scheme.PartialIso.toRationalMap, toPartialMap_trans] at hq
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ?_
    refine (Scheme.PartialMap.comp_equiv_of_equiv_right _
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hq)).trans ?_
    rw [← Scheme.PartialMap.comp_assoc]
    refine (Scheme.PartialMap.comp_equiv_of_equiv_left (comp_symm_equiv_id φ) _).trans ?_
    rw [Scheme.PartialMap.id_comp]
  have := H F hFexc (φ.toPartialMap.comp q) hq' hx'
  rw [hval'] at this
  have e1 : (⟨F'.genericPoint, hF'q⟩ : q.domain.toScheme) =
      ⟨φ.toPartialMap.hom ⟨F.genericPoint, hFs⟩, hmem⟩ := Subtype.ext hval
  rw [e1]
  exact this

/-- A partial isomorphism over a base is a rational map over the base. -/
private theorem isOver_toRationalMap {S : Scheme.{0}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (e : X.PartialIso Y) (he : e.IsOver sX sY) :
    MMP.Flips.RationalMap.IsOver sX sY e.toRationalMap := by
  unfold MMP.Flips.RationalMap.IsOver
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
  change _ = sX.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap sX.toPartialMap e.source e.dense_source le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change e.iso.hom ≫ e.target.ι ≫ sY = (X.isoOfEq rfl).hom ≫ X.homOfLE le_top ≫ (⊤ : X.Opens).ι ≫ sX
  rw [he, Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp, Scheme.homOfLE_ι_assoc]

/-- A partial isomorphism whose rational map lies over a separated base lies over it. -/
private theorem isOver_of_isOver_toRationalMap [IsReduced X] {S : Scheme.{0}}
    [IsSeparated (S ↘ ⊤_ Scheme)] {sX : X ⟶ S} {sY : Y ⟶ S} (e : X.PartialIso Y)
    (h : MMP.Flips.RationalMap.IsOver sX sY e.toRationalMap) : e.IsOver sX sY := by
  unfold MMP.Flips.RationalMap.IsOver at h
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap] at h
  change _ = sX.toPartialMap.toRationalMap at h
  have h' := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  exact (Category.assoc _ _ _).symm.trans h'

end CodimOne

/-! ### The flip as a partial isomorphism -/

section FlipPartialIso

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
  {fp : X' ⟶ Z}

/-- An open subset of an irreducible scheme containing every point of codimension at most one
is dense. -/
private theorem dense_of_forall_coheight_le_one {Y : Scheme.{0}} [IrreducibleSpace Y]
    (U : Y.Opens) (hU : ∀ y : Y, Order.coheight y ≤ 1 → y ∈ U) : Dense (U : Set Y) := by
  have hg : Order.coheight (genericPoint Y) ≤ 1 := by
    rw [Order.coheight_eq_zero.mpr]
    · exact zero_le_one
    · intro b _
      exact Scheme.le_iff_specializes.mpr ((genericPoint_spec Y).specializes (Set.mem_univ b))
  exact U.isOpen.dense ⟨_, hU _ hg⟩

/-- **The flip of a real flip step as a partial isomorphism.** Both contractions are isomorphisms
over an open `V` of the base over which lie the points of codimension at most one; the induced
isomorphism `f⁻¹(V) ≅ (f⁺)⁻¹(V)` is a partial isomorphism `X ⤏ X⁺` over `Z` and over `ℂ`. -/
private theorem IsRealFlipStep.exists_partialIso (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) :
    ∃ φ : X.PartialIso X', φ.toRationalMap.compHom fp = f.toRationalMap ∧ φ.IsOver sX sX' ∧
      (∀ x : X, Order.coheight x ≤ 1 → x ∈ φ.source) ∧
      (∀ x : X', Order.coheight x ≤ 1 → x ∈ φ.target) ∧
      (∀ (R : Type) [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor φ.toRationalMap D = flipTransform f fp D) ∧
      (∀ (x : X) (hx : x ∈ φ.source), fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x) ∧
      (∀ x ∈ φ.source, f x ∈ MMP.Mori.biregularLocus f) ∧
      ∀ x ∈ φ.target, fp x ∈ MMP.Mori.biregularLocus fp := by
  obtain ⟨V, hV, hV', hXV, hX'V⟩ := h.exists_opens_isIso
  have hfs : f ≫ sZ = sX := h.isSmall.comp_eq
  have hfps : fp ≫ sZ = sX' := h.isSmall_flip.comp_eq
  have hXv := h.isNegativeExtremalContraction.isNormalVariety_source
  have hZv := h.isNegativeExtremalContraction.isNormalVariety_target
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := h.isSmall.isProper
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI := isSeparated_terminal sX'
  have hd : Dense ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    dense_of_forall_coheight_le_one _ fun x hx => hXV x hx
  have hd' : Dense ((fp ⁻¹ᵁ V : X'.Opens) : Set X') :=
    dense_of_forall_coheight_le_one _ fun x hx => hX'V x hx
  have hinv : inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι ≫ fp = V.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  let φ : X.PartialIso X' := ⟨f ⁻¹ᵁ V, hd, fp ⁻¹ᵁ V, hd', asIso (f ∣_ V) ≪≫ (asIso (fp ∣_ V)).symm⟩
  have hcomp : φ.toRationalMap.compHom fp = f.toRationalMap := by
    rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
    change _ = f.toPartialMap.toRationalMap
    rw [← Scheme.PartialMap.restrict_toRationalMap f.toPartialMap (f ⁻¹ᵁ V) hd le_top]
    congr 1
    refine Scheme.PartialMap.ext _ _ rfl ?_
    change (f ∣_ V ≫ inv (fp ∣_ V)) ≫ (fp ⁻¹ᵁ V).ι ≫ fp =
      (X.isoOfEq rfl).hom ≫ X.homOfLE le_top ≫ (⊤ : X.Opens).ι ≫ f
    rw [Category.assoc, hinv, morphismRestrict_ι, Scheme.isoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, Scheme.homOfLE_ι_assoc]
  have hmor : (f ∣_ V ≫ inv (fp ∣_ V)) ≫ (fp ⁻¹ᵁ V).ι ≫ fp = (f ⁻¹ᵁ V).ι ≫ f := by
    rw [Category.assoc, hinv, morphismRestrict_ι]
  have hpt : ∀ (x : X) (hx : x ∈ φ.source), fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x := by
    intro x hx
    have := congrArg (fun k => k ⟨x, hx⟩) hmor
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  refine ⟨φ, hcomp, ?_, hXV, hX'V, fun R _ D =>
    MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZv (hfs ▸ hXv)
      h.isBirationalMorphism V hXV hX'V hcomp D, hpt,
    fun x hx => MMP.Mori.le_biregularLocus hV hx,
    fun x hx => MMP.Mori.le_biregularLocus hV' hx⟩
  change (asIso (f ∣_ V) ≪≫ (asIso (fp ∣_ V)).symm).hom ≫ (fp ⁻¹ᵁ V).ι ≫ sX' =
    (f ⁻¹ᵁ V).ι ≫ sX
  rw [← hfps, ← hfs]
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [reassoc_of% hinv, ← morphismRestrict_ι_assoc]

/-- **The canonical divisor of a real flip.** The strict transform `(f⁺)⁻¹_* f_* K₀` of a canonical
divisor `K₀` of `X` is a canonical divisor of `X⁺`. -/
private theorem IsRealFlipStep.isCanonicalDivisor_flipTransform
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) {n : ℕ} {K₀ : Divisor X}
    (hK₀ : K₀.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K₀) := by
  obtain ⟨V, hV, hV', hXV, hX'V⟩ := h.exists_opens_isIso
  have hfs : f ≫ sZ = sX := h.isSmall.comp_eq
  have hfps : fp ≫ sZ = sX' := h.isSmall_flip.comp_eq
  have hXv := h.isNegativeExtremalContraction.isNormalVariety_source
  have hZv := h.isNegativeExtremalContraction.isNormalVariety_target
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := h.isSmall.isProper
  have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZv (hfs ▸ hXv)
    (hfps ▸ hX'v) h.isBirationalMorphism h.isBirationalMorphism_flip V hXV hX'V
    (hfs ▸ hK₀ : K₀.IsCanonicalDivisor (f ≫ sZ) n)
  rwa [hfps] at this

end FlipPartialIso

/-- The strict transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {X Y : Scheme.{0}} (φ : X.RationalMap Y) {D : RDivisor X}
    (hD : 0 ≤ D) : 0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  intro Q
  change 0 ≤ (DivisorWithCoeffs.mapPrimeDivisors _ D) Q
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  rcases h : MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q'
  · simp [h]
  · simp only [h, Option.elim, Finsupp.singleAddHom_apply, Finsupp.single_apply]
    split_ifs
    · exact hD P
    · exact le_refl 0

/-! ### Principal divisors along a flip -/

section PrincipalTransport

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  [IsLocallyNoetherian Z] [IsNormal Z]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
  {fp : X' ⟶ Z}

/-- **The strict transform of a principal divisor under a flip**: for a rational function `u` of
the base `Z`, the strict transform of `div(f^* u)` is `div((f⁺)^* u)`. -/
private theorem IsRealFlipStep.flipTransform_principalDivisor_pullback [CompactSpace Z]
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (φ : X.PartialIso X')
    (hs : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ φ.source)
    (ht : ∀ Q : MMP.Mori.PrimeDivisor X', Q.genericPoint ∈ φ.target)
    (htr : ∀ D : Divisor X,
      MMP.Mori.RationalMap.transformDivisor φ.toRationalMap D = flipTransform f fp D)
    (hpt : ∀ (x : X) (hx : x ∈ φ.source), fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x)
    (hbir : ∀ x ∈ φ.source, f x ∈ MMP.Mori.biregularLocus f)
    (hbir' : ∀ x ∈ φ.target, fp x ∈ MMP.Mori.biregularLocus fp)
    (u : (RationalFunctions Z)ˣ)
    (hu : ∀ Z' : irreducibleComponents X,
      f (componentGenericPoint X Z') ∉ (principalDivisor u).supp)
    (hu' : ∀ Z' : irreducibleComponents X',
      fp (componentGenericPoint X' Z') ∉ (principalDivisor u).supp) :
    flipTransform f fp (principalDivisor (pullbackRationalFunction f u hu)) =
      principalDivisor (pullbackRationalFunction fp u hu') := by
  classical
  have hXv := h.isNegativeExtremalContraction.isNormalVariety_source
  have hX'v : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI := isSeparated_terminal sX
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI := isSeparated_terminal sX'
  ext Q'
  obtain ⟨Q, hQs, hQQ', hval⟩ := exists_transformPrimeDivisor_eq_some_of_mem_target φ Q' (ht Q')
  rw [← htr, DivisorWithCoeffs.coeff_apply, coeff_transformDivisor_of_eq_some φ hs hQQ']
  have hco : Order.coheight (f Q.genericPoint) = 1 :=
    (MMP.Positivity.coheight_map_of_mem_biregularLocus f (hbir _ hQs)).trans
      (MMP.Mori.PrimeDivisor.coheight_genericPoint Q)
  have hP : f Q.genericPoint = (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco).genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  have hP' : fp Q'.genericPoint =
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco).genericPoint := by
    rw [hval, hpt]
    exact hP
  haveI := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f (hbir _ hQs)
  haveI := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus fp (hbir' _ (ht Q'))
  have e1 := MMP.Positivity.coeff_eq_of_isPullback Q _ hP (Divisor.isCartier_principalDivisor u)
    (Divisor.isPullback_principalDivisor u hu)
  have e2 := MMP.Positivity.coeff_eq_of_isPullback Q' _ hP' (Divisor.isCartier_principalDivisor u)
    (Divisor.isPullback_principalDivisor u hu')
  exact e1.trans e2.symm

end PrincipalTransport

/-! ### Relative ampleness and pull-backs from the base -/

section Ample

variable {Y W : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {f : Y ⟶ W} [IsDominant f] [QuasiCompact f]

/-- A positive multiple of an `f`-ample `ℝ`-divisor is `f`-ample. -/
private theorem isRelativelyAmple_smul {G : RDivisor Y} (hG : IsRelativelyAmple f G) {c : ℝ}
    (hc : 0 < c) : IsRelativelyAmple f (c • G) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hG
  refine ⟨m, fun j => c * r j, L, hm, fun j => mul_pos hc (hr j), hL, ?_⟩
  rw [Finset.smul_sum]
  simp [mul_smul]

/-- An `f`-ample `ℝ`-divisor plus a real multiple of the pull-back of a Cartier divisor of the
base is `f`-ample: the multiple is absorbed by twisting one ample summand by a large multiple of
the pull-back. -/
private theorem isRelativelyAmple_add_smul_pullback {G : RDivisor Y} (hG : IsRelativelyAmple f G)
    {M : Divisor W} (hMc : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ M.supp}
    {M' : Divisor Y} (hM' : M.IsPullback f hB M') (s : ℝ) :
    IsRelativelyAmple f (G + s • Divisor.toRDivisor M') := by
  classical
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hG
  rcases eq_or_ne s 0 with rfl | hs
  · exact ⟨m, r, L, hm, hr, hL, by simp⟩
  set j0 : Fin m := ⟨0, hm⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (|s| / r j0)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg s) (hr j0).le) hN
  set ε : ℝ := |s| / N with hεdef
  have hε : 0 < ε := div_pos (abs_pos.mpr hs) hN0
  have hεr : ε < r j0 := by
    rw [hεdef, div_lt_iff₀ hN0]
    rw [div_lt_iff₀ (hr j0)] at hN
    linarith [mul_comm (r j0) (N : ℝ)]
  set σ : ℤ := if 0 < s then (N : ℤ) else -(N : ℤ) with hσdef
  have hσ : ε * (σ : ℝ) = s := by
    rw [hεdef, hσdef]
    split_ifs with h
    · rw [abs_of_pos h]; push_cast; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hs)]; push_cast; field_simp
  have hBσ : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (σ • M).supp :=
    fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _ Z
  have hpσ : (σ • M).IsPullback f hBσ (σ • M') := hM'.zsmul hMc σ hBσ
  have hcσ : (σ • M').IsCartier := hpσ.isCartier (hMc.zsmul σ)
  have hnew : IsRelativelyAmpleCartier f (L j0 + σ • M') :=
    isRelativelyAmpleCartier_of_isRelativelyAmple ((hL j0).1.add hcσ)
      (MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback f (hL j0).1
        (hL j0).isRelativelyAmple (hMc.zsmul σ) hpσ hcσ)
  refine ⟨m + 1, Fin.snoc (Function.update r j0 (r j0 - ε)) ε, Fin.snoc L (L j0 + σ • M'),
    by omega, ?_, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hε
    · simp only [Fin.snoc_castSucc]
      by_cases hj : j = j0
      · subst hj; simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne hj]; exact hr j
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hnew
    · simpa using hL j
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, map_add, map_zsmul, smul_add]
    have h1 : ∀ j, Function.update r j0 (r j0 - ε) j = r j - if j = j0 then ε else 0 := by
      intro j
      by_cases hj : j = j0
      · subst hj; simp
      · simp [hj]
    simp only [h1, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul, hσ]
    abel

/-- **An `f`-ample divisor plus a pull-back from the base is `f`-ample.** For `c > 0` and an
`ℝ`-Cartier pull-back `P = f^* D`, `c G + P` is `f`-ample when `G` is. -/
private theorem isRelativelyAmple_smul_add_of_isRCartierPullback {G : RDivisor Y}
    (hG : IsRelativelyAmple f G) {c : ℝ} (hc : 0 < c) {D : RDivisor W} {P : RDivisor Y}
    (hP : IsRCartierPullback f D P) : IsRelativelyAmple f (c • G + P) := by
  classical
  obtain ⟨n, s, M, M', hM, -, hM', rfl⟩ := hP
  have key : ∀ S : Finset (Fin n),
      IsRelativelyAmple f (c • G + ∑ j ∈ S, s j • Divisor.toRDivisor (M' j)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isRelativelyAmple_smul hG hc
    | insert j S hj ih =>
      obtain ⟨hB, hp⟩ := hM' j
      rw [Finset.sum_insert hj]
      have := isRelativelyAmple_add_smul_pullback ih (hM j) hp (s j)
      convert this using 1
      abel
  exact key Finset.univ

end Ample

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is a real combination of Cartier divisors. -/
private theorem isCartierCombination_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsQFactorial sX)
    (D : RDivisor X) : IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := MMP.Fourfold.IsQFactorial.isRCartier hX D
  refine ⟨m, r, C, hC, ?_⟩
  ext Γ
  rw [hD Γ]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rfl

/-! ### Relative nefness and principal divisors -/

section Nef

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- A principal divisor has intersection number zero with every proper curve. -/
private theorem IsCartierIntersectionNumber.eq_zero_of_principalDivisor {C : ProperCurve sX}
    (v : (RationalFunctions X)ˣ) {h : (principalDivisor v).IsCartier} {d : ℤ}
    (hd : IsCartierIntersectionNumber ℂ sX C (principalDivisor v) h d) : d = 0 := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := hd
  haveI := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  exact MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX (ν ≫ C.ι) hdim h
    ⟨v, by rw [sub_zero]⟩

/-- Adding a real multiple of a principal divisor preserves relative nefness. -/
private theorem isRelativelyNef_add_smul_principalDivisor {π : X ⟶ Z} {D : RDivisor X}
    (hD : IsRelativelyNef ℂ sX π D) (c : ℝ) (v : (RationalFunctions X)ˣ) :
    IsRelativelyNef ℂ sX π (D + c • Divisor.toRDivisor (principalDivisor v)) := by
  obtain ⟨m, r, L, hL, rfl, hnef⟩ := hD
  refine ⟨m + 1, Fin.snoc r c, Fin.snoc L (principalDivisor v), ?_, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using Divisor.isCartier_principalDivisor v
    · simpa using hL j
  · rw [Fin.sum_univ_castSucc]
    simp
  · intro C hC x hx
    obtain ⟨hL', d, -, hd, rfl⟩ := hx
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hlast : d (Fin.last m) = 0 := by
      have := hd (Fin.last m)
      simp only [Fin.snoc_last] at this
      exact IsCartierIntersectionNumber.eq_zero_of_principalDivisor v this
    rw [hlast, Int.cast_zero, mul_zero, add_zero]
    refine hnef C hC _ ⟨hL, fun j => d j.castSucc, rfl, fun j => ?_, rfl⟩
    have := hd j.castSucc
    simp only [Fin.snoc_castSucc] at this
    exact this

end Nef

/-! ### Log discrepancies along a pencil of boundaries -/

section Affine

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **Log discrepancies are affine along a pencil of boundaries.** If `C₀ = ∑ s_j M_j` with Cartier
`M_j` whose pull-backs to the model of `E` are `M'_j`, then
`a(E; X, B + t C₀) = a(E; X, B) - t ∑ s_j ord_E(M'_j)`. -/
private theorem isLogDiscrepancy_add_smul {n : ℕ} {B C₀ : RDivisor X} {E : DivisorOver ℂ sX}
    {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B E a) {m : ℕ} {s : Fin m → ℝ}
    {M : Fin m → Divisor X} (hMc : ∀ j, (M j).IsCartier)
    (hC₀ : C₀ = ∑ j, s j • Divisor.toRDivisor (M j)) {M' : Fin m → Divisor E.Y}
    (hM' : haveI := E.isLocallyNoetherian; haveI := E.isNormal
      ∀ j, ∃ hB, (M j).IsPullback E.f hB (M' j)) (t : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + t • C₀) E
      (a - t * ∑ j, s j * ((M' j).coeff E.E : ℝ)) := by
  obtain ⟨hX, hp, ω, hω, hK, m₁, r₁, C₁, C₁', hc₁, hsum₁, hpb₁, rfl⟩ := h
  refine ⟨hX, hp, ω, hω, hK, m₁ + m, Fin.append r₁ (fun j => t * s j), Fin.append C₁ M,
    Fin.append C₁' M', ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hc₁ i
    · simpa using hMc i
  · intro Γ
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, hC₀, MMP.Fourfold.coeff_sum_smul_toRDivisor]
    rw [← hsum₁ Γ, Finset.mul_sum]
    simp only [mul_assoc]
    ring
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · obtain ⟨hB, hp⟩ := hpb₁ i
      exact ⟨by simpa using hB, by simpa using hp⟩
    · obtain ⟨hB, hp⟩ := hM' i
      exact ⟨by simpa using hB, by simpa using hp⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.mul_sum, mul_assoc]
    ring

/-- **Log discrepancies along `B + ν C`.** On a `ℚ`-factorial variety, a divisor `E` over `X` with
log discrepancy `a` for `B + μ C` has log discrepancy `a + (μ - ν) c` for `B + ν C`, for one real
`c` (the order of `C` along `E`), which is nonnegative when `C` is effective. -/
private theorem exists_isLogDiscrepancy_add_smul [CompactSpace X] (hQ : IsQFactorial sX)
    {n : ℕ} {B C : RDivisor X} {μ : ℝ} {E : DivisorOver ℂ sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n (B + μ • C) E a) :
    ∃ c : ℝ, (0 ≤ C → 0 ≤ c) ∧
      ∀ ν : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (B + ν • C) E (a + (μ - ν) * c) := by
  classical
  obtain ⟨m, r, M, hMc, hCeq⟩ := MMP.Fourfold.IsQFactorial.isRCartier hQ C
  have hC₀ : C = ∑ j, r j • Divisor.toRDivisor (M j) := by
    ext Γ
    change C.coeff Γ = (∑ j, r j • Divisor.toRDivisor (M j)).coeff Γ
    rw [hCeq Γ, MMP.Fourfold.coeff_sum_smul_toRDivisor]
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : IsProper E.f := h.2.1
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hex := fun j => (hMc j).exists_isPullback
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
  choose N hN using hex
  refine ⟨∑ j, r j * ((N j).coeff E.E : ℝ), fun hC0 => ?_, fun ν => ?_⟩
  · have hG : IsRCartierPullback E.f C (∑ j, r j • Divisor.toRDivisor (N j)) :=
      ⟨m, r, M, N, hMc, hC₀, fun j => ⟨_, hN j⟩, rfl⟩
    have := (MMP.Fourfold.isEffective_of_isRCartierPullback E.f
      (MMP.Fourfold.IsQFactorial.isRCartier hQ C) hC0).2 _ hG E.E
    have h3 : (∑ j, r j • Divisor.toRDivisor (N j)) E.E = ∑ j, r j * ((N j).coeff E.E : ℝ) :=
      MMP.Fourfold.coeff_sum_smul_toRDivisor r N E.E
    rw [h3] at this
    simpa using this
  · have := isLogDiscrepancy_add_smul h hMc hC₀ (fun j => ⟨_, hN j⟩) (ν - μ)
    have hb : B + μ • C + (ν - μ) • C = B + ν • C := by module
    rw [hb] at this
    convert this using 1
    ring

end Affine

/-! ### Plt pairs across a flip -/

section PltStep

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  [IsIntegral Z]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {K' : Divisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Every proper divisor over the source of a real flip step has a log discrepancy for any
boundary on a `ℚ`-factorial source. -/
private theorem exists_isLogDiscrepancy_of_isQFactorial (hX : IsNormalVariety ℂ sX)
    (hQ : IsQFactorial sX) {m : ℕ} (hK : K.IsCanonicalDivisor sX m) (B : RDivisor X)
    (E : DivisorOver ℂ sX) (hE : IsProper E.f) :
    ∃ a, MMP.Intersection.IsLogDiscrepancy sX m B E a := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' hωK
  exact MMP.Fourfold.exists_isLogDiscrepancy hX hω0 (hdiv ▸ hK)
    (isCartierCombination_of_isQFactorial hQ _) E hE

/-- **The lower pair stays plt across a flip.** Log discrepancies do not decrease across a real
flip step, and divisors exceptional over the flip are exceptional over the source. -/
private theorem IsRealFlipStep.pos_of_isLogDiscrepancy {B : RDivisor X} {B' : RDivisor X'}
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hQ : IsQFactorial sX) {m : ℕ}
    (hK : K.IsCanonicalDivisor sX m)
    (hplt : ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX n B E a → 0 < a) :
    ∀ (n : ℕ) (E' : DivisorOver ℂ sX') (a' : ℝ), E'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX' n B' E' a' → 0 < a' := by
  intro n E' a' hE' ha'
  have hXv := h.isNegativeExtremalContraction.isNormalVariety_source
  obtain ⟨E, hEp, -, hpt, hcmp⟩ := h.exists_isLogDiscrepancy_le ⟨m, hK⟩ E' ha'.2.1
  obtain ⟨a, ha⟩ := exists_isLogDiscrepancy_of_isQFactorial hXv hQ hK B E hEp
  exact (hplt m E a (h.isExceptional_of_map_eq E E' hpt hE') ha).trans_le
    (hcmp m n a a' ha ha').1

/-- **The upper pair stays plt across a flip at a constant level.** If `(X, B + μ C)` is plt and
for every `0 < ν < μ` the same diagram is a real flip for `(K, B + ν C)`, then
`(X⁺, B⁺ + μ C⁺)` is plt: for `ν < μ` the log discrepancies of `B⁺ + ν C⁺` dominate those of
`B + ν C`, which dominate those of `B + μ C` since `C ≥ 0`, and the log discrepancies of
`B⁺ + ν C⁺` are affine in `ν`. -/
private theorem pos_of_isLogDiscrepancy_of_forall_lt {B C : RDivisor X} {B' C' : RDivisor X'}
    {μ : ℝ} (hμ : 0 < μ)
    (hfl : ∀ ν : ℝ, 0 < ν → ν < μ →
      IsRealFlipStep sX sZ sX' K (B + ν • C) K' (B' + ν • C') f fp)
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX') {m : ℕ} (hK : K.IsCanonicalDivisor sX m)
    (hC : 0 ≤ C)
    (hplt : ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX n (B + μ • C) E a → 0 < a) :
    ∀ (n : ℕ) (E' : DivisorOver ℂ sX') (a' : ℝ), E'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX' n (B' + μ • C') E' a' → 0 < a' := by
  intro n E' a' hE' ha'
  obtain ⟨c', -, hc'⟩ := exists_isLogDiscrepancy_add_smul hQ' ha'
  have h0 := hfl (μ / 2) (by positivity) (by linarith)
  have hXv := h0.isNegativeExtremalContraction.isNormalVariety_source
  haveI := h0.isBirationalMorphism.isDominant
  haveI := h0.isBirationalMorphism_flip.isDominant
  have hbij := h0.isBirationalMorphism.functionFieldMap_bijective
  -- the divisor over `X` realizing `E'` at the level `μ / 2`
  obtain ⟨E₀, hE₀p, hv₀, hpt₀, -⟩ := h0.exists_isLogDiscrepancy_le ⟨m, hK⟩ E' ha'.2.1
  obtain ⟨α, hα⟩ := exists_isLogDiscrepancy_of_isQFactorial hXv hQ hK (B + μ • C) E₀ hE₀p
  have hαpos : 0 < α := hplt m E₀ α (h0.isExceptional_of_map_eq E₀ E' hpt₀ hE') hα
  -- at every level `0 < ν < μ`, `α ≤ a' + (μ - ν) c'`
  have key : ∀ ν : ℝ, 0 < ν → ν < μ → α ≤ a' + (μ - ν) * c' := by
    intro ν hν hνμ
    have hν' := hfl ν hν hνμ
    obtain ⟨E, hEp, hv, -, hcmp⟩ := hν'.exists_isLogDiscrepancy_le ⟨m, hK⟩ E' ha'.2.1
    have hvE : E.valuation = E₀.valuation := by
      refine Valuation.ext fun x => ?_
      obtain ⟨y, rfl⟩ := hbij.2 x
      have h1 := congrArg (fun v => v y) (hv.trans hv₀.symm)
      simpa only [Valuation.comap_apply] using h1
    obtain ⟨b, hb⟩ := exists_isLogDiscrepancy_of_isQFactorial hXv hQ hK (B + μ • C) E hEp
    have hbα : b = α := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hb hα hvE
    obtain ⟨c, hc0, hcE⟩ := exists_isLogDiscrepancy_add_smul hQ hb
    have hle := (hcmp m n _ _ (hcE ν) (hc' ν)).1
    have := mul_nonneg (sub_nonneg.mpr hνμ.le) (hc0 hC)
    linarith
  -- choose `ν` close to `μ`
  set t : ℝ := min (μ / 2) (α / (2 * (|c'| + 1))) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htμ : t ≤ μ / 2 := min_le_left _ _
  have htα : t * (|c'| + 1) ≤ α / 2 := by
    have := min_le_right (μ / 2) (α / (2 * (|c'| + 1)))
    rw [← ht] at this
    calc t * (|c'| + 1) ≤ α / (2 * (|c'| + 1)) * (|c'| + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = α / 2 := by field_simp
  have h1 := key (μ - t) (by linarith) (by linarith)
  have h2 : (μ - (μ - t)) * c' ≤ t * |c'| := by
    rw [sub_sub_cancel]
    exact mul_le_mul_of_nonneg_left (le_abs_self c') ht0.le
  nlinarith [abs_nonneg c']

end PltStep

/-- The strict transform commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : QDivisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Rat.castHom ℝ).toAddMonoidHom)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases MMP.Mori.RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- A `ℚ`-divisor with a relatively ample multiple over `Spec k` is ample. -/
private theorem isAmple_of_hasRelativelyAmpleMultiple {W : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    {A : QDivisor W} (h : A.HasRelativelyAmpleMultiple sW) : A.IsAmple := by
  obtain ⟨m, hm, L, hL, hLA, hamp⟩ := h
  refine ⟨m, hm, L, ?_, hL, ?_⟩
  · rw [hLA, ← Int.cast_smul_eq_zsmul ℚ]
    simp
  · haveI := hL.isInvertibleModule_divisorialSheaf
    obtain ⟨V, -, hyV, hA⟩ := hamp (IsLocalRing.closedPoint _)
    have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
      rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact hyV)
    subst hV
    have : IsIso (sW ⁻¹ᵁ (⊤ : (Spec (.of ℂ)).Opens)).ι := inferInstanceAs (IsIso W.topIso.hom)
    exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ _ hA

/-! ### The plt reference on the log minimal model -/

section Reference

/-- **Averaging an upper plt reference with the log minimal model.** Let `B'_Y ∼_ℚ B_Y + C_Y` be a
plt boundary whose only reduced component is `E`, with `(Y, B_Y + C_Y)` lc, `C_Y ≥ 0` and
`B_Y(E) = 1`, and let `A ≤ B'_Y` be effective with `A(E) = 0`. Then `B̃ = (B'_Y + B_Y)/2` and
`B̃ + C_Y/2 = (B'_Y + B_Y + C_Y)/2` are plt, `B̃ + C_Y/2 ∼_ℚ B_Y + C_Y` and `A/2 ≤ B̃ - E`. -/
private theorem exists_half_of_pltReference {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sY)
    {BY CY BY' : RDivisor Y} (hBY0 : 0 ≤ BY) (hCY0 : 0 ≤ CY) {E : MMP.Mori.PrimeDivisor Y}
    (hBYE : BY.coeff E = 1) (hle : ∀ P, (BY + CY).coeff P ≤ 1)
    (hlc : ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY n (BY + CY) D a → 0 ≤ a)
    (hprinc : ∃ (m : ℕ) (u : (RationalFunctions Y)ˣ), 0 < m ∧
      (m : ℝ) • (BY' - (BY + CY)) = Divisor.toRDivisor (principalDivisor u))
    (hBY'0 : ∀ P, 0 ≤ BY'.coeff P) (hBY'E : BY'.coeff E = 1) (hBY'lt : ∀ F, F ≠ E → BY'.coeff F < 1)
    (hBY'plt : ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sY n BY' D a → 0 < a)
    {A : RDivisor Y} (hAE : A.coeff E = 0) (hAle : A ≤ BY') :
    (1 / 2 : ℝ) • A ≤ ((1 / 2 : ℝ) • (BY' + BY)) - Finsupp.single E 1 ∧
      (∃ (m : ℕ) (u : (RationalFunctions Y)ˣ), 0 < m ∧
        (m : ℝ) • ((1 / 2 : ℝ) • (BY' + BY) + (1 / 2 : ℝ) • CY - (BY + CY)) =
          Divisor.toRDivisor (principalDivisor u)) ∧
      ((∀ P, 0 ≤ ((1 / 2 : ℝ) • (BY' + BY)).coeff P ∧ ((1 / 2 : ℝ) • (BY' + BY)).coeff P ≤ 1) ∧
        ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy sY n ((1 / 2 : ℝ) • (BY' + BY)) D a → 0 < a) ∧
      ((∀ P, 0 ≤ ((1 / 2 : ℝ) • (BY' + BY) + (1 / 2 : ℝ) • CY).coeff P ∧
          ((1 / 2 : ℝ) • (BY' + BY) + (1 / 2 : ℝ) • CY).coeff P ≤ 1) ∧
        ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy sY n
            ((1 / 2 : ℝ) • (BY' + BY) + (1 / 2 : ℝ) • CY) D a → 0 < a) ∧
      ((1 / 2 : ℝ) • (BY' + BY)).coeff E = 1 := by
  classical
  have c0 : ∀ D : RDivisor Y, 0 ≤ D → ∀ P, (0 : ℝ) ≤ D.coeff P := fun D hD P => by
    rw [DivisorWithCoeffs.coeff_apply]; simpa using hD P
  have hBY1 : ∀ P, BY.coeff P ≤ 1 := fun P => by
    have := hle P; rw [DivisorWithCoeffs.coeff_add] at this; linarith [c0 _ hCY0 P]
  have hBY'1 : ∀ P, BY'.coeff P ≤ 1 := fun P => by
    by_cases hP : P = E
    · rw [hP, hBY'E]
    · exact (hBY'lt P hP).le
  -- `(Y, B_Y)` is lc
  have hlcB : ∀ (n : ℕ) (D : DivisorOver ℂ sY) (b : ℝ),
      MMP.Intersection.IsLogDiscrepancy sY n BY D b → 0 ≤ b := by
    intro n D b hb
    obtain ⟨c, hc0, hc⟩ := exists_isLogDiscrepancy_add_smul (μ := 0) hQ (C := CY)
      (by rwa [zero_smul, add_zero] :
        MMP.Intersection.IsLogDiscrepancy sY n (BY + (0 : ℝ) • CY) D b)
    have h1 := hc 1
    rw [one_smul] at h1
    have := hlc n D _ h1
    have := hc0 hCY0
    linarith
  -- averages of log discrepancies
  have havg : ∀ (G : RDivisor Y) (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
      (∀ b, MMP.Intersection.IsLogDiscrepancy sY n G D b → 0 ≤ b) →
      MMP.Intersection.IsLogDiscrepancy sY n ((1 / 2 : ℝ) • (BY' + G)) D a → 0 < a := by
    intro G n D a hD hG ha
    have hb : (1 / 2 : ℝ) • (BY' + G) = BY' + (1 / 2 : ℝ) • (G - BY') := by module
    rw [hb] at ha
    obtain ⟨c, -, hc⟩ := exists_isLogDiscrepancy_add_smul hQ ha
    have h0 := hc 0
    rw [zero_smul, add_zero] at h0
    have h1 := hc 1
    rw [one_smul, add_sub_cancel] at h1
    have := hBY'plt n D _ hD h0
    have := hG _ h1
    linarith
  refine ⟨fun P => ?_, ?_, ⟨fun P => ⟨?_, ?_⟩, fun n D a hD ha => havg BY n D a hD
    (hlcB n D) ha⟩, ⟨fun P => ⟨?_, ?_⟩, fun n D a hD ha => ?_⟩, ?_⟩
  · change ((1 / 2 : ℝ) • A).coeff P ≤ ((1 / 2 : ℝ) • (BY' + BY) - Finsupp.single E 1).coeff P
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, smul_eq_mul]
    have hA := hAle P
    change A.coeff P ≤ BY'.coeff P at hA
    by_cases hP : P = E
    · subst hP
      have : DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℝ) : RDivisor Y) P = 1 := by
        simp [DivisorWithCoeffs.coeff_apply]
      rw [this, hAE, hBY'E, hBYE]; norm_num
    · have : DivisorWithCoeffs.coeff (Finsupp.single E (1 : ℝ) : RDivisor Y) P = 0 := by
        simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hP]
      rw [this]
      linarith [c0 _ hBY0 P]
  · obtain ⟨m, u, hm, hu⟩ := hprinc
    refine ⟨2 * m, u, by omega, ?_⟩
    rw [← hu]
    push_cast
    module
  · simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul]
    linarith [hBY'0 P, c0 _ hBY0 P]
  · simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul]
    linarith [hBY'1 P, hBY1 P]
  · simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul]
    linarith [hBY'0 P, c0 _ hBY0 P, c0 _ hCY0 P]
  · have := hle P
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul] at this ⊢
    linarith [hBY'1 P]
  · have hb : (1 / 2 : ℝ) • (BY' + BY) + (1 / 2 : ℝ) • CY = (1 / 2 : ℝ) • (BY' + (BY + CY)) := by
      module
    rw [hb] at ha
    exact havg (BY + CY) n D a hD (hlc n D) ha
  · simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, smul_eq_mul, hBY'E,
      hBYE]
    norm_num

/-- **A level-one plt reference on the log minimal model.** In the setting of
`MMP.Fourfold.IsRealLogMinimalModel.eventually_disjoint_exceptionalSet_of_levelOne_scaling`, for a
component `E` of `⌊B_Y⌋` there are a small `μ > 0`, a normal projective reference `X₀` with a
normal prime divisor `S₀` and an effective ample `ℚ`-divisor `A₀` not containing `S₀`, a partial
isomorphism `e₀ : X₀ ⤏ Y` over `ℂ` sending `S₀` to `E` whose extracted primes have generic points
outside `Supp A₀`, and a boundary `B̃` on `Y` with `B̃ + μ C_Y ∼_ℚ B_Y + C_Y`, such that `B̃` and
`B̃ + μ C_Y` are plt with `E ⊆ ⌊B̃⌋` and `e₀_* A₀ ≤ B̃ - E`. -/
private theorem exists_levelOne_pltReference
    {X Z Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B C : RDivisor X} {A : QDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXsm : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 4) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C)) (hsnc : DivisorWithCoeffs.IsSNC sX (B + C))
    (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (QDivisor.toRDivisor A).coeff P ≤ B.coeff P)
    (hAfl : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {πY : Y ⟶ Z} {KY : Divisor Y} {BY CY : RDivisor Y}
    (hπY : πY ≫ sZ = sY) (hproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdimY : topologicalKrullDim Y = 4) {φ : X.RationalMap Y}
    (hCY : CY = MMP.Mori.RationalMap.transformDivisor φ C)
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y, BY.coeff F =
      (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        open Classical in if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsRealLogMinimalModel sX sY sZ π πY KX (B + C) KY (BY + CY) φ)
    (E : MMP.Mori.PrimeDivisor Y) (hE : BY.coeff E = 1) :
    ∃ (μ : ℝ) (_ : 0 < μ) (X₀ : Scheme.{0}) (_ : IsIntegral X₀) (_ : IsLocallyNoetherian X₀)
      (_ : IsNormal X₀) (_ : CompactSpace X₀) (sX₀ : X₀ ⟶ Spec (.of ℂ))
      (_ : IsNormalVariety ℂ sX₀) (_ : MMP.Mori.IsProjectiveVariety ℂ sX₀)
      (S₀ : MMP.Mori.PrimeDivisor X₀) (_ : IsNormal S₀.idealSheaf.subscheme) (A₀ : QDivisor X₀)
      (_ : 0 ≤ A₀) (_ : A₀.IsAmple) (_ : A₀.coeff S₀ = 0) (e₀ : X₀.PartialIso Y)
      (Bt : RDivisor Y),
      e₀.IsOver sX₀ sY ∧
      MMP.Mori.RationalMap.transformPrimeDivisor e₀.toRationalMap S₀ = some E ∧
      (∀ F : MMP.Mori.PrimeDivisor Y,
        MMP.Flips.RationalMap.IsInverseExceptional e₀.toRationalMap F →
        ∀ q : Y.PartialMap X₀, q.toRationalMap = e₀.symm.toRationalMap →
          ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀)) ∧
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor e₀.toRationalMap A₀) ≤
        Bt - Finsupp.single E 1 ∧
      (∃ (m : ℕ) (u : (RationalFunctions Y)ˣ), 0 < m ∧
        (m : ℝ) • (Bt + μ • CY - (BY + CY)) = Divisor.toRDivisor (principalDivisor u)) ∧
      ((∀ P, 0 ≤ Bt.coeff P ∧ Bt.coeff P ≤ 1) ∧
        ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy sY n Bt D a → 0 < a) ∧
      ((∀ P, 0 ≤ (Bt + μ • CY).coeff P ∧ (Bt + μ • CY).coeff P ≤ 1) ∧
        ∀ (n : ℕ) (D : DivisorOver ℂ sY) (a : ℝ), D.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy sY n (Bt + μ • CY) D a → 0 < a) ∧
      Bt.coeff E = 1 := by
  classical
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  have hYm := hY.toIsNefLogBirationalModel
  -- the inputs of the landed plt reference, with boundary `B + C` and no scaling divisor
  have hA' : A.HasRelativelyAmpleMultiple sX := by
    obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hA
    refine ⟨m, hm, D, hDc, ?_,
      MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple_divisorialSheaf sX hDc hDa⟩
    rw [hD, ← Int.cast_smul_eq_zsmul ℚ]
    simp
  have hY' : IsNefLogBirationalModel sX sY sZ π πY KX ((B + C) + (1 / 2 : ℝ) • (0 : RDivisor X))
      KY ((BY + CY) + (1 / 2 : ℝ) • MMP.Mori.RationalMap.transformDivisor φ (0 : RDivisor X))
      φ := by
    simpa using hYm
  have hBY' : ∀ F : MMP.Mori.PrimeDivisor Y, (BY + CY).coeff F =
      (MMP.Mori.RationalMap.transformDivisor φ (B + C)).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0 := by
    intro F
    rw [DivisorWithCoeffs.coeff_add, hBY F, hCY, map_add, DivisorWithCoeffs.coeff_add]
    ring
  have hCY0 : 0 ≤ CY := hCY ▸ transformDivisor_nonneg φ fun P => hC P
  have hBY0 : 0 ≤ BY := by
    intro F
    have h1 : (0 : ℝ) ≤ (MMP.Mori.RationalMap.transformDivisor φ B).coeff F :=
      transformDivisor_nonneg φ (fun P => hB P) F
    change (0 : ℝ) ≤ BY.coeff F
    rw [hBY F]
    split_ifs <;> linarith
  have hCYE : CY.coeff E = 0 := by
    have h1 := hY.isRealDltPair.2.1 E
    rw [DivisorWithCoeffs.coeff_add, hE] at h1
    have h2 : (0 : ℝ) ≤ CY.coeff E := by
      rw [DivisorWithCoeffs.coeff_apply]; simpa using hCY0 E
    linarith
  have hE' : (BY + CY).coeff E = 1 := by rw [DivisorWithCoeffs.coeff_add, hE, hCYE, add_zero]
  obtain ⟨W, _, _, _, _, sW, _, p, hp, ψ, EW, B', A', BY', hWp, hWs, hpW, hψff, -, hψE, -, -, -,
      hA'amp, hA'0, -, hA'EW, hprinc, ⟨hBY'lc, hBY'plt⟩, hBY'E, hBY'lt, hψA, -, -, hEWn, hordq⟩ :=
    exists_pltReference_of_isNefLogBirationalModel (C := 0) (t := 1 / 2) hX hXsm
      (by simpa using hdlt) (by simpa using hsnc)
      (fun P => by rw [DivisorWithCoeffs.coeff_add]; linarith [hB P, hC P])
      (fun P => by simp [DivisorWithCoeffs.coeff_apply])
      (fun P hP => absurd (by simp [DivisorWithCoeffs.coeff_apply]) hP) hA'
      (fun P => hA0 P)
      (fun P => by
        have := hAB P
        change (QDivisor.toRDivisor A).coeff P ≤ (B + C).coeff P
        rw [DivisorWithCoeffs.coeff_add]
        linarith [hC P])
      hAfl (by norm_num) (by norm_num) hBY' hY'
      (fun F hF D hD n a ha => hYm.isLogDiscrepancy_eq_zero F hF D hD n a ha) E hE'
  obtain ⟨e₀, he₀, he₀k⟩ : ∃ e₀ : W.PartialIso Y, e₀.toRationalMap = ψ ∧ e₀.IsOver sW sY := by
    haveI := hp.isDominant
    obtain ⟨eφ, heφ⟩ := hYm.isBirational
    obtain ⟨ep, hep⟩ := id hp
    haveI : IsSeparated sX := hXn.1.toIsSeparated
    haveI := isSeparated_terminal sX
    haveI : IsSeparated sY := hproj.toIsVariety.toIsSeparated
    haveI := isSeparated_terminal sY
    haveI := isDominant_toPartialMap_hom ep
    haveI : IsDominant p.toPartialMap.hom := by
      change IsDominant ((⊤ : W.Opens).ι ≫ p); infer_instance
    refine ⟨ep.trans eφ, ?_, ?_⟩
    · apply Scheme.RationalMap.eq_of_fromFunctionField_eq
      change (ep.trans eφ).toPartialMap.toRationalMap.fromFunctionField = _
      rw [toPartialMap_trans]
      have h1 : (ep.toPartialMap.comp eφ.toPartialMap).toRationalMap =
          (p.toPartialMap.comp eφ.toPartialMap).toRationalMap :=
        Scheme.PartialMap.toRationalMap_eq_iff.mpr
          (Scheme.PartialMap.comp_equiv_of_equiv_left
            (Scheme.PartialMap.toRationalMap_eq_iff.mp hep) _)
      rw [h1, Scheme.RationalMap.fromFunctionField_toRationalMap,
        fromFunctionField_toPartialMap_comp, ← hψff, ← heφ]
      rfl
    · have hpo : ep.IsOver sW sX := by
        refine isOver_of_isOver_toRationalMap ep ?_
        unfold MMP.Flips.RationalMap.IsOver
        rw [hep]
        change (p.toPartialMap.toRationalMap).compHom sX = sW.toPartialMap.toRationalMap
        rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom, hpW]
      have hφo : eφ.IsOver sX sY := by
        refine isOver_of_isOver_toRationalMap eφ ?_
        unfold MMP.Flips.RationalMap.IsOver
        rw [heφ, ← hπY, ← hYm.comp_eq]
        have hov := hYm.isOver
        unfold MMP.Flips.RationalMap.IsOver at hov
        obtain ⟨g, hg⟩ := φ.exists_rep
        rw [← hg] at hov ⊢
        rw [← Scheme.RationalMap.compHom_toRationalMap] at hov ⊢
        have : g.compHom (πY ≫ sZ) = (g.compHom πY).compHom sZ := by
          obtain ⟨U, hU, h⟩ := g
          simp only [Scheme.PartialMap.compHom, Category.assoc]
        rw [this, Scheme.RationalMap.compHom_toRationalMap, hov]
        change (π.toPartialMap.compHom sZ).toRationalMap = _
        rw [Scheme.Hom.toPartialMap_compHom]
      exact hpo.trans hφo
  have hA'amp' : A'.IsAmple := isAmple_of_hasRelativelyAmpleMultiple hA'amp
  have hAE : (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ A')).coeff E = 0 := by
    haveI : IsProper sW := isProper_of_isProjectiveMorphism sW hWp.isProjective
    haveI : IsSeparated sY := hproj.toIsVariety.toIsSeparated
    haveI := isSeparated_terminal sY
    haveI : IsSeparated sW := hWp.toIsVariety.toIsSeparated
    haveI := isSeparated_terminal sW
    have hdom : E.genericPoint ∈ e₀.symm.toRationalMap.domain :=
      MMP.Flips.RationalMap.mem_domain_of_coheight_le_one sY sW e₀.symm.toRationalMap
        (isOver_toRationalMap e₀.symm he₀k.symm)
        (MMP.Mori.PrimeDivisor.coheight_genericPoint E).le
    have huniq : ∀ P, MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some E → P = EW :=
      fun P hP => eq_of_transformPrimeDivisor_eq_some_of_mem_domain e₀ (he₀ ▸ hP) (he₀ ▸ hψE)
        hdom
    rw [QDivisor.coeff_toRDivisor]
    have h1 : (MMP.Mori.RationalMap.transformDivisor ψ A') E = A' EW :=
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hψE huniq A'
    change ((MMP.Mori.RationalMap.transformDivisor ψ A') E : ℝ) = 0
    rw [h1]
    change ((A'.coeff EW : ℚ) : ℝ) = 0
    rw [hA'EW, Rat.cast_zero]
  have hord' : ∀ F : MMP.Mori.PrimeDivisor Y,
      MMP.Flips.RationalMap.IsInverseExceptional e₀.toRationalMap F →
      ∀ q : Y.PartialMap W, q.toRationalMap = e₀.symm.toRationalMap →
        ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ (A'.supp : Set W) :=
    fun F hF q hq => hordq F (he₀ ▸ hF) q ⟨e₀, he₀, hq.symm⟩
  -- averaging `B'_Y` with `B_Y`
  have hAle : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ A') ≤ BY' := by
    rw [← transformDivisor_toRDivisor]
    exact hψA
  obtain ⟨hAB', hprinc', hplt', hplt_up', hBtE⟩ := exists_half_of_pltReference hQ hBY0 hCY0 hE
    hYm.isRealDltPair.2.1 hYm.isRealDltPair.1.2.2.2 hprinc (fun P => hBY'lc.2.1 P) hBY'E hBY'lt
    (fun n D a hD ha => hBY'plt n D hD a ha) hAE hAle
  have hWn : IsNormalVariety ℂ sW := ⟨hWp.toIsVariety, inferInstance⟩
  -- the reference divisor `A'/2`
  have hA₀ : ((1 / 2 : ℚ) • A').IsAmple := by
    obtain ⟨m, hm, D, hD, hDc, hDa⟩ := hA'amp'
    refine ⟨2 * m, by omega, D, ?_, hDc, hDa⟩
    rw [hD, smul_smul]
    congr 1
    push_cast
    ring
  have hA₀0 : 0 ≤ (1 / 2 : ℚ) • A' := fun P => by
    have := hA'0 P
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at this ⊢
    positivity
  have hA₀EW : ((1 / 2 : ℚ) • A').coeff EW = 0 := by
    rw [DivisorWithCoeffs.coeff_smul, hA'EW, smul_zero]
  have hsupp : ((1 / 2 : ℚ) • A').supp = A'.supp := by
    unfold DivisorWithCoeffs.supp
    rw [Finsupp.support_smul_eq (by norm_num)]
  have htrA : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor e₀.toRationalMap
      ((1 / 2 : ℚ) • A')) = (1 / 2 : ℝ) •
        QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ A') := by
    rw [he₀, ← MMP.Mori.RationalMap.transformDivisorₗ_apply ℚ, map_smul,
      MMP.Mori.RationalMap.transformDivisorₗ_apply]
    ext P
    simp [QDivisor.toRDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
    simp [DivisorWithCoeffs.coeff_apply, Finsupp.mapRange_apply]
  refine ⟨1 / 2, by norm_num, W, inferInstance, inferInstance, inferInstance, inferInstance, sW,
    hWn, hWp, EW, hEWn, (1 / 2 : ℚ) • A', hA₀0, hA₀, hA₀EW, e₀, (1 / 2 : ℝ) • (BY' + BY), he₀k,
    he₀ ▸ hψE, fun F hF q hq hFq => hsupp ▸ hord' F hF q hq hFq, htrA ▸ hAB', hprinc', hplt',
    hplt_up', hBtE⟩

end Reference

/-- **The constant-level modified flip sequence.** In the setting of `solution`, the plt
reference on `Y_0` gives a constant level `μ > 0` and boundaries `B̃_i`, transported along the
flips together with canonical divisors `K'_i`, such that the flips are flips of `(K', B̃)`, both
`B̃_i` and `B̃_i + μ C_i` are plt, `K'_i + B̃_i + μ C_i` is nef over `Z` and descends crepantly to
the bases, and the reference `(X₀, S₀, A₀)` maps to `(Y_i, E_i)` with `A₀` carried into
`B̃_i - E_i`: the inputs of special termination for real plt flips with scaling. -/
private theorem exists_constantLevel_pltSequence
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B C : RDivisor X} {A : QDivisor X}
    -- the SNC fourfold setting
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXsm : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 4) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C)) (hsnc : DivisorWithCoeffs.IsSNC sX (B + C))
    (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (QDivisor.toRDivisor A).coeff P ≤ B.coeff P)
    (hAfl : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the flip sequence `Y_0 ⤏ Y_1 ⤏ ⋯` over `Z`
    (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i))
    (BY CY : ∀ i, RDivisor (Y i))
    (W : ℕ → Scheme.{0}) [∀ i, IsLocallyNoetherian (W i)] [∀ i, IsNormal (W i)]
    (sW : ∀ i, W i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ W i) (fp : ∀ i, Y (i + 1) ⟶ W i)
    (hπY : ∀ i, πY i ≫ sZ = sY i)
    (hK : ∀ i, ∃ m : ℕ, (KY i).IsCanonicalDivisor (sY i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (hQ : ∀ i, IsQFactorial (sY i))
    (hdimY : ∀ i, topologicalKrullDim (Y i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sY i) (sW i) (sY (i + 1)) (KY i) (BY i) (KY (i + 1))
      (BY (i + 1)) (f i) (fp i))
    (hCtr : ∀ i, CY (i + 1) = flipTransform (f i) (fp i) (CY i))
    -- scaling of `C_Y` at level one
    (hnef : ∀ i, IsRelativelyNef ℂ (sY i) (πY i) (logCanonicalDivisor (KY i) (BY i + CY i)))
    -- the upper levels descend crepantly to `W_i`
    (hdesc : ∀ i, ∃ D : RDivisor (W i),
      IsRCartierPullback (f i) D (logCanonicalDivisor (KY i) (BY i + CY i)) ∧
        IsRCartierPullback (fp i) D
          (flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i))))
    -- `Y_0` is a log minimal model of `(X, B + C)`
    {φ : X.RationalMap (Y 0)}
    (hCY : CY 0 = MMP.Mori.RationalMap.transformDivisor φ C)
    (hBY : ∀ F : MMP.Mori.PrimeDivisor (Y 0), (BY 0).coeff F =
      (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        open Classical in if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsRealLogMinimalModel sX (sY 0) sZ π (πY 0) KX (B + C) (KY 0) (BY 0 + CY 0) φ)
    -- a component `E_0` of `⌊B_Y⌋` and its strict transforms
    (E : ∀ i, MMP.Mori.PrimeDivisor (Y i)) (hE : (BY 0).coeff (E 0) = 1)
    (hEtr : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (E i) = some (E (i + 1))) :
    ∃ (K' : ∀ i, Divisor (Y i)) (Bt : ∀ i, RDivisor (Y i)) (μ : ℝ), 0 < μ ∧
      (∀ i, ∃ m : ℕ, (K' i).IsCanonicalDivisor (sY i) m) ∧
      (∀ i, IsRealFlipStep (sY i) (sW i) (sY (i + 1)) (K' i) (Bt i) (K' (i + 1))
        (Bt (i + 1)) (f i) (fp i)) ∧
      (∀ i, (∀ P, 0 ≤ (Bt i).coeff P ∧ (Bt i).coeff P ≤ 1) ∧
        RDivisor.IsRCartier (Divisor.toRDivisor (K' i) + Bt i) ∧
        ∀ (n : ℕ) (E : DivisorOver ℂ (sY i)) (a : ℝ), E.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy (sY i) n (Bt i) E a → 0 < a) ∧
      (∀ i, 0 ≤ CY i) ∧
      (∀ i, IsRelativelyNef ℂ (sY i) (πY i)
        (logCanonicalDivisor (K' i) (Bt i + μ • CY i))) ∧
      (∀ i, (∀ P, 0 ≤ (Bt i + μ • CY i).coeff P ∧ (Bt i + μ • CY i).coeff P ≤ 1) ∧
        RDivisor.IsRCartier (Divisor.toRDivisor (K' i) + (Bt i + μ • CY i)) ∧
        ∀ (n : ℕ) (E : DivisorOver ℂ (sY i)) (a : ℝ), E.IsExceptional →
          MMP.Intersection.IsLogDiscrepancy (sY i) n (Bt i + μ • CY i) E a → 0 < a) ∧
      (∀ i, ∃ D : RDivisor (W i),
        IsRCartierPullback (f i) D (logCanonicalDivisor (K' i) (Bt i + μ • CY i)) ∧
        IsRCartierPullback (fp i) D
          (logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + μ • CY (i + 1)))) ∧
      (∀ i, (Bt i).coeff (E i) = 1) ∧ (∀ i, (CY i).coeff (E i) = 0) ∧
      ∃ (X₀ : Scheme.{0}) (_ : IsIntegral X₀) (_ : IsLocallyNoetherian X₀) (_ : IsNormal X₀)
        (_ : CompactSpace X₀) (sX₀ : X₀ ⟶ Spec (.of ℂ)) (_ : IsNormalVariety ℂ sX₀)
        (_ : MMP.Mori.IsProjectiveVariety ℂ sX₀) (S₀ : MMP.Mori.PrimeDivisor X₀)
        (_ : IsNormal S₀.idealSheaf.subscheme) (A₀ : QDivisor X₀) (_ : 0 ≤ A₀)
        (_ : A₀.IsAmple) (_ : A₀.coeff S₀ = 0)
        (ψ : ∀ i, X₀.RationalMap (Y i)) (ψinv : ∀ i, (Y i).RationalMap X₀),
        (∀ i, MMP.Mori.RationalMap.IsInverse (ψ i) (ψinv i)) ∧
        (∀ i, MMP.Flips.RationalMap.IsOver sX₀ (sY i) (ψ i)) ∧
        (∀ i, MMP.Flips.RationalMap.IsOver (sY i) sX₀ (ψinv i)) ∧
        (∀ i, MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) S₀ = some (E i)) ∧
        (∀ i, ∀ F : MMP.Mori.PrimeDivisor (Y i),
          MMP.Flips.RationalMap.IsInverseExceptional (ψ i) F →
          ∀ q : (Y i).PartialMap X₀, q.toRationalMap = ψinv i →
            ∀ hF : F.genericPoint ∈ q.domain, q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀)) ∧
        (∀ i, QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor (ψ i) A₀) ≤
          Bt i - Finsupp.single (E i) 1) := by
  classical
  -- the plt reference on `Y 0`
  obtain ⟨μ, hμ, X₀, _, _, _, _, sX₀, hX₀, hX₀p, S₀, _, A₀, hA₀, hAamp, hAS, e₀, Bt₀,
    he₀k, he₀S, hord₀, hAB₀, hprinc₀, hplt₀, hplt_up₀, hBtE₀⟩ :=
    exists_levelOne_pltReference hX hXsm hdim hZ hB hC hdlt hsnc hA hA0 hAB hAfl (hπY 0)
      (hproj 0) (hQ 0) (hdimY 0) hCY hBY hY (E 0) hE
  -- separatedness over the terminal scheme
  have hsepY : ∀ i, IsSeparated (Y i ↘ ⊤_ Scheme) := fun i =>
    have := (hproj i).toIsVariety.toIsSeparated
    isSeparated_terminal (sY i)
  haveI : IsSeparated sX₀ := hX₀.1.toIsSeparated
  haveI := isSeparated_terminal sX₀
  -- the flips as partial isomorphisms
  choose fl hφcomp hφover hφs hφt hφtr hφpt hφbir hφbir' using
    fun i => IsRealFlipStep.exists_partialIso (hflip i)
  have hφs' : ∀ i (Q : MMP.Mori.PrimeDivisor (Y i)), Q.genericPoint ∈ (fl i).source :=
    fun i Q => hφs i _ (MMP.Mori.PrimeDivisor.coheight_genericPoint Q).le
  have hφt' : ∀ i (Q : MMP.Mori.PrimeDivisor (Y (i + 1))), Q.genericPoint ∈ (fl i).target :=
    fun i Q => hφt i _ (MMP.Mori.PrimeDivisor.coheight_genericPoint Q).le
  -- the composite partial isomorphisms `X₀ ⤏ Y i`, canonical divisors and boundaries
  let e : ∀ i, X₀.PartialIso (Y i) := fun i =>
    Nat.rec (motive := fun i => X₀.PartialIso (Y i)) e₀ (fun i ei => ei.trans (fl i)) i
  let K' : ∀ i, Divisor (Y i) := fun i =>
    Nat.rec (motive := fun i => Divisor (Y i)) (KY 0) (fun i K => flipTransform (f i) (fp i) K) i
  let Bt : ∀ i, RDivisor (Y i) := fun i =>
    Nat.rec (motive := fun i => RDivisor (Y i)) Bt₀ (fun i B => flipTransform (f i) (fp i) B) i
  have he : ∀ i, e (i + 1) = (e i).trans (fl i) := fun i => rfl
  have hBt : ∀ i, Bt (i + 1) = flipTransform (f i) (fp i) (Bt i) := fun i => rfl
  -- the flip sends `E i` to `E (i + 1)`
  have hφE : ∀ i, MMP.Mori.RationalMap.transformPrimeDivisor (fl i).toRationalMap (E i) =
      some (E (i + 1)) := by
    intro i
    obtain ⟨Q', hQ', -⟩ := exists_transformPrimeDivisor_eq_some (fl i) (E i) (hφs' i _)
    have h1 := hφtr i ℤ (Finsupp.single (E i) 1)
    rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some hQ',
      flipTransform_single_of_eq_some (hEtr i)] at h1
    rw [hQ', Finsupp.single_left_injective one_ne_zero h1]
  -- coefficients along a flip
  have hcoeffφ : ∀ i {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (Y i))
      {Q : MMP.Mori.PrimeDivisor (Y i)}
      {Q' : MMP.Mori.PrimeDivisor (Y (i + 1))},
      MMP.Mori.RationalMap.transformPrimeDivisor (fl i).toRationalMap Q = some Q' →
        (flipTransform (f i) (fp i) D).coeff Q' = D.coeff Q := fun i R _ D _ _ h => by
    rw [← hφtr i R D]
    exact coeff_transformDivisor_of_eq_some (fl i) (hφs' i) h D
  -- effectivity of the transforms of `C_Y`
  have hCeff : ∀ i, 0 ≤ CY i := by
    intro i
    induction i with
    | zero => rw [hCY]; exact transformDivisor_nonneg φ fun P => hC P
    | succ i ih =>
      intro Q'
      obtain ⟨Q, -, hQQ', -⟩ :=
        exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
      rw [hCtr i]
      change (0 : ℝ) ≤ (flipTransform (f i) (fp i) (CY i)).coeff Q'
      rw [hcoeffφ i (CY i) hQQ']
      exact ih Q
  have hK'can : ∀ i, ∃ m : ℕ, (K' i).IsCanonicalDivisor (sY i) m := by
    intro i
    induction i with
    | zero => exact hK 0
    | succ i ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨m, IsRealFlipStep.isCanonicalDivisor_flipTransform (hflip i) hm⟩
  -- the bases of the flips are integral and quasi-compact
  have hWv : ∀ i, IsNormalVariety ℂ (sW i) := fun i =>
    (hflip i).isNegativeExtremalContraction.isNormalVariety_target
  haveI : ∀ i, IsIntegral (W i) := fun i => (hWv i).1.toIsIntegral
  haveI : ∀ i, CompactSpace (W i) := fun i => by
    haveI : QuasiCompact (sW i) := (hWv i).1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (sW i)
  haveI : ∀ i, IsDominant (f i) := fun i => (hflip i).isBirationalMorphism.isDominant
  haveI : ∀ i, IsDominant (fp i) := fun i => (hflip i).isBirationalMorphism_flip.isDominant
  have hYnv : ∀ i, IsNormalVariety ℂ (sY i) := fun i => ⟨(hproj i).toIsVariety, inferInstance⟩
  -- linear algebra of the flip transforms
  have htoR : ∀ i (D : Divisor (Y i)), flipTransform (f i) (fp i) (Divisor.toRDivisor D) =
      Divisor.toRDivisor (flipTransform (f i) (fp i) D) := by
    intro i D
    ext Q'
    obtain ⟨Q, -, hQQ', -⟩ :=
      exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
    change (flipTransform (f i) (fp i) (Divisor.toRDivisor D)).coeff Q' =
      (Divisor.toRDivisor (flipTransform (f i) (fp i) D)).coeff Q'
    rw [hcoeffφ i _ hQQ', Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, hcoeffφ i D hQQ']
  have hsmulT : ∀ i (c : ℝ) (D : RDivisor (Y i)),
      flipTransform (f i) (fp i) (c • D) = c • flipTransform (f i) (fp i) D := by
    intro i c D
    ext Q'
    obtain ⟨Q, -, hQQ', -⟩ :=
      exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
    change (flipTransform (f i) (fp i) (c • D)).coeff Q' =
      (c • flipTransform (f i) (fp i) D).coeff Q'
    rw [hcoeffφ i _ hQQ', DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_smul,
      hcoeffφ i _ hQQ']
  have hBYtr : ∀ i, BY (i + 1) = flipTransform (f i) (fp i) (BY i) := fun i =>
    (hflip i).eq_flipTransform
  have hlogT : ∀ i, flipTransform (f i) (fp i) (logCanonicalDivisor (K' i) (Bt i + μ • CY i)) =
      logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + μ • CY (i + 1)) := by
    intro i
    simp only [logCanonicalDivisor, map_add, htoR, hsmulT, hBt, hCtr]
    rfl
  have hlogKY : ∀ i, flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i)) =
      Divisor.toRDivisor (flipTransform (f i) (fp i) (KY i)) + (BY (i + 1) + CY (i + 1)) := by
    intro i
    simp only [logCanonicalDivisor, map_add, htoR, hBYtr, hCtr]
  -- canonical divisors are linearly equivalent
  have hKlin : ∀ i, ∃ g : (RationalFunctions (Y (i + 1)))ˣ,
      flipTransform (f i) (fp i) (KY i) - KY (i + 1) = principalDivisor g := by
    intro i
    obtain ⟨m, hm⟩ := hK i
    obtain ⟨m', hm'⟩ := hK (i + 1)
    exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (sY (i + 1))
      (hYnv (i + 1)) (IsRealFlipStep.isCanonicalDivisor_flipTransform (hflip i) hm) hm'
  -- the modified adjoint differs from the original one by a rational principal divisor
  have hinv : ∀ i, ∃ (m : ℕ) (v : (RationalFunctions (Y i))ˣ), 0 < m ∧
      (m : ℝ) • (logCanonicalDivisor (K' i) (Bt i + μ • CY i) -
        logCanonicalDivisor (KY i) (BY i + CY i)) = Divisor.toRDivisor (principalDivisor v) := by
    intro i
    induction i with
    | zero =>
      obtain ⟨m, u, hm, hu⟩ := hprinc₀
      refine ⟨m, u, hm, ?_⟩
      rw [← hu]
      congr 1
      change Divisor.toRDivisor (KY 0) + (Bt₀ + μ • CY 0) -
        (Divisor.toRDivisor (KY 0) + (BY 0 + CY 0)) = _
      abel
    | succ i ih =>
      obtain ⟨m, v, hm, hv⟩ := ih
      obtain ⟨u, hu, rfl⟩ :=
        MMP.Fourfold.exists_pullbackRationalFunction_eq (hflip i).isBirationalMorphism v
      obtain ⟨g, hg⟩ := hKlin i
      have hu' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp i)
        (principalDivisor u)
      have hPT := IsRealFlipStep.flipTransform_principalDivisor_pullback (hflip i) (fl i)
        (hφs' i) (hφt' i) (hφtr i ℤ) (hφpt i) (hφbir i) (hφbir' i) u hu hu'
      refine ⟨m, pullbackRationalFunction (fp i) u hu' * g ^ m, hm, ?_⟩
      have e1 := congrArg (flipTransform (f i) (fp i)) hv
      rw [hsmulT, map_sub, hlogT, hlogKY, htoR, hPT] at e1
      have hgm : principalDivisor (g ^ m) = m • principalDivisor g := by
        have := map_nsmul (principalDivisorHom (X := Y (i + 1))) m (Additive.ofMul g)
        simpa using this
      rw [MMP.Mori.principalDivisor_mul, map_add, hgm, map_nsmul, ← hg, map_sub, ← e1,
        ← Nat.cast_smul_eq_nsmul ℝ]
      simp only [logCanonicalDivisor, smul_sub, smul_add]
      abel
  haveI : ∀ i, QuasiCompact (f i) := fun i => by
    haveI := (hflip i).isSmall.isProper; infer_instance
  haveI : ∀ i, QuasiCompact (fp i) := fun i => by
    haveI := (hflip i).isSmall_flip.isProper; infer_instance
  haveI : ∀ i, QuasiCompact (sY i) := fun i => (hYnv i).1.toQuasiCompact
  -- the modified adjoint as the original one plus a rational principal divisor
  have hadj : ∀ i, ∃ (m : ℕ) (u : (RationalFunctions (W i))ˣ)
      (hu : ∀ Z' : irreducibleComponents (Y i),
        f i (componentGenericPoint (Y i) Z') ∉ (principalDivisor u).supp)
      (hu' : ∀ Z' : irreducibleComponents (Y (i + 1)),
        fp i (componentGenericPoint (Y (i + 1)) Z') ∉ (principalDivisor u).supp),
      logCanonicalDivisor (K' i) (Bt i + μ • CY i) =
        logCanonicalDivisor (KY i) (BY i + CY i) + (1 / (m : ℝ)) •
          Divisor.toRDivisor (principalDivisor (pullbackRationalFunction (f i) u hu)) ∧
      logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + μ • CY (i + 1)) =
        flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i)) + (1 / (m : ℝ)) •
          Divisor.toRDivisor (principalDivisor (pullbackRationalFunction (fp i) u hu')) := by
    intro i
    obtain ⟨m, v, hm, hv⟩ := hinv i
    obtain ⟨u, hu, rfl⟩ :=
      MMP.Fourfold.exists_pullbackRationalFunction_eq (hflip i).isBirationalMorphism v
    have hu' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (fp i)
      (principalDivisor u)
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hA : logCanonicalDivisor (K' i) (Bt i + μ • CY i) =
        logCanonicalDivisor (KY i) (BY i + CY i) + (1 / (m : ℝ)) •
          Divisor.toRDivisor (principalDivisor (pullbackRationalFunction (f i) u hu)) := by
      rw [← hv, smul_smul, one_div_mul_cancel hm0, one_smul]
      abel
    refine ⟨m, u, hu, hu', hA, ?_⟩
    rw [← hlogT, hA, map_add, hsmulT, htoR,
      IsRealFlipStep.flipTransform_principalDivisor_pullback (hflip i) (fl i) (hφs' i)
        (hφt' i) (hφtr i ℤ) (hφpt i) (hφbir i) (hφbir' i) u hu hu']
  -- the modified upper adjoint descends crepantly
  have hdesc' : ∀ i, ∃ D : RDivisor (W i),
      IsRCartierPullback (f i) D (logCanonicalDivisor (K' i) (Bt i + μ • CY i)) ∧
      IsRCartierPullback (fp i) D
        (logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + μ • CY (i + 1))) := by
    intro i
    obtain ⟨m, u, hu, hu', hA, hA'⟩ := hadj i
    obtain ⟨D, hD, hD'⟩ := hdesc i
    refine ⟨D + (1 / (m : ℝ)) • Divisor.toRDivisor (principalDivisor u), ?_, ?_⟩
    · rw [hA]
      exact MMP.Fourfold.isRCartierPullback_add hD (MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor u) hu
          (Divisor.isPullback_principalDivisor u hu)))
    · rw [hA']
      exact MMP.Fourfold.isRCartierPullback_add hD' (MMP.Fourfold.isRCartierPullback_smul _
        (MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor u) hu'
          (Divisor.isPullback_principalDivisor u hu')))
  -- every level `0 ≤ ν < μ` of the modified sequence is a real flip
  have hflipν : ∀ i (ν : ℝ), 0 ≤ ν → ν < μ →
      IsRealFlipStep (sY i) (sW i) (sY (i + 1)) (K' i) (Bt i + ν • CY i) (K' (i + 1))
        (Bt (i + 1) + ν • CY (i + 1)) (f i) (fp i) := by
    intro i ν hν hνμ
    have hμν : 0 < μ - ν := sub_pos.mpr hνμ
    obtain ⟨D, hD, hD'⟩ := hdesc i
    obtain ⟨D', hDD, hDD'⟩ := hdesc' i
    have hst := hflip i
    obtain ⟨g, hg⟩ := hKlin i
    obtain ⟨ug, hug, hgeq⟩ :=
      MMP.Fourfold.exists_pullbackRationalFunction_eq (hflip i).isBirationalMorphism_flip g
    -- the lower adjoint stays negative
    have hneg : IsRelativelyAntiAmple (f i) (logCanonicalDivisor (K' i) (Bt i + ν • CY i)) := by
      have h1 := hst.isNegativeExtremalContraction.isRelativelyAntiAmple
      have hP : IsRCartierPullback (f i) ((μ - ν) • D + (-1 : ℝ) • D')
          ((μ - ν) • logCanonicalDivisor (KY i) (BY i + CY i) +
            (-1 : ℝ) • logCanonicalDivisor (K' i) (Bt i + μ • CY i)) :=
        MMP.Fourfold.isRCartierPullback_add (MMP.Fourfold.isRCartierPullback_smul _ hD)
          (MMP.Fourfold.isRCartierPullback_smul (-1) hDD)
      have := isRelativelyAmple_smul_add_of_isRCartierPullback h1 hμν hP
      unfold IsRelativelyAntiAmple
      convert this using 1
      simp only [logCanonicalDivisor]
      module
    -- the flipped adjoint stays positive
    have hpos : IsRelativelyAmple (fp i)
        (logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + ν • CY (i + 1))) := by
      have h1 := hst.isRelativelyAmple_flip
      have hP : IsRCartierPullback (fp i) (D' + (-(μ - ν)) • D + (μ - ν) • Divisor.toRDivisor
            (principalDivisor ug))
          (logCanonicalDivisor (K' (i + 1)) (Bt (i + 1) + μ • CY (i + 1)) +
            (-(μ - ν)) • flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i)) +
            (μ - ν) • Divisor.toRDivisor (principalDivisor g)) := by
        refine MMP.Fourfold.isRCartierPullback_add (MMP.Fourfold.isRCartierPullback_add hDD'
          (MMP.Fourfold.isRCartierPullback_smul _ hD')) (MMP.Fourfold.isRCartierPullback_smul _ ?_)
        rw [← hgeq]
        exact MMP.Fourfold.isRCartierPullback_toRDivisor (Divisor.isCartier_principalDivisor ug)
          hug (Divisor.isPullback_principalDivisor ug hug)
      have := isRelativelyAmple_smul_add_of_isRCartierPullback h1 hμν hP
      convert this using 1
      rw [hlogKY, ← hg, map_sub]
      simp only [logCanonicalDivisor]
      module
    exact
      { hst with
        isNegativeExtremalContraction :=
          { hst.isNegativeExtremalContraction with
            isCartierCombination := isCartierCombination_of_isQFactorial (hQ i) _
            isRelativelyAntiAmple := hneg }
        isCanonicalDivisor_flip := hK'can (i + 1)
        isRelativelyAmple_flip := hpos
        eq_flipTransform := by rw [map_add, hsmulT, ← hBt, ← hCtr] }
  refine ⟨K', Bt, μ, hμ, hK'can, ?hflip', ?hplt, hCeff, ?hnef', ?hplt_up, ?hcrep, ?hSB, ?hSC,
    X₀, inferInstance, inferInstance, inferInstance, inferInstance, sX₀, hX₀, hX₀p, S₀,
    inferInstance, A₀, hA₀, hAamp, hAS, fun i => (e i).toRationalMap,
    fun i => (e i).symm.toRationalMap, fun i => ⟨e i, rfl, rfl⟩, ?hψk, ?hψinvk, ?hψS, ?hord,
    ?hAB'⟩
  case hflip' =>
    intro i
    simpa using hflipν i 0 le_rfl hμ
  case hcrep => exact hdesc'
  case hnef' =>
    intro i
    obtain ⟨m, u, hu, -, hA, -⟩ := hadj i
    rw [hA]
    exact isRelativelyNef_add_smul_principalDivisor (hnef i) _ _
  case hSB =>
    intro i
    induction i with
    | zero => exact hBtE₀
    | succ i ih => rw [hBt, hcoeffφ i (Bt i) (hφE i), ih]
  case hSC =>
    intro i
    induction i with
    | zero =>
      have h1 := hY.isRealDltPair.2.1 (E 0)
      rw [DivisorWithCoeffs.coeff_add, hE] at h1
      exact le_antisymm (by linarith) (hCeff 0 (E 0))
    | succ i ih => rw [hCtr i, hcoeffφ i (CY i) (hφE i), ih]
  case hψk =>
    intro i
    refine isOver_toRationalMap (e i) ?_
    induction i with
    | zero => exact he₀k
    | succ i ih => exact ih.trans (hφover i)
  case hψinvk =>
    intro i
    refine isOver_toRationalMap (e i).symm (Scheme.PartialIso.IsOver.symm ?_)
    induction i with
    | zero => exact he₀k
    | succ i ih => exact ih.trans (hφover i)
  case hψS =>
    intro i
    induction i with
    | zero => exact he₀S
    | succ i ih =>
      obtain ⟨Q', hQ', hval⟩ := exists_transformPrimeDivisor_eq_some (fl i) (E i) (hφs' i _)
      rw [hφE i, Option.some.injEq] at hQ'
      subst hQ'
      exact transformPrimeDivisor_trans_eq_some (e i) (fl i) ih (hφs' i _) hval
  case hord =>
    intro i
    induction i with
    | zero => exact hord₀
    | succ i ih =>
      exact forall_isInverseExceptional_trans (e i) (fl i) (hφs' i) (hφt' i) _ ih
  case hAB' =>
    intro i
    induction i with
    | zero => exact hAB₀
    | succ i ih =>
      intro Q'
      obtain ⟨Q, -, hQQ', -⟩ :=
        exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
      have h1 : (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor
          (e (i + 1)).toRationalMap A₀)) Q' =
          (QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor
            (e i).toRationalMap A₀)) Q := by
        change ((MMP.Mori.RationalMap.transformDivisor (e (i + 1)).toRationalMap A₀ Q' : ℚ) :
          ℝ) = ((MMP.Mori.RationalMap.transformDivisor (e i).toRationalMap A₀ Q : ℚ) : ℝ)
        rw [he, transformDivisor_trans (e i) (fl i) (hφs' i) (hφt' i),
          coeff_transformDivisor_of_eq_some (fl i) (hφs' i) hQQ']
      have h2 : (Bt (i + 1) - Finsupp.single (E (i + 1)) 1 : RDivisor (Y (i + 1))) Q' =
          (Bt i - Finsupp.single (E i) 1 : RDivisor (Y i)) Q := by
        rw [hBt, ← hφtr i ℝ, ← MMP.Mori.RationalMap.transformDivisor_single_of_eq_some
          (hφE i), ← map_sub]
        exact coeff_transformDivisor_of_eq_some (fl i) (hφs' i) hQQ' _
      rw [h1, h2]
      exact ih Q
  case hplt =>
    intro i
    induction i with
    | zero => exact ⟨hplt₀.1, MMP.Fourfold.IsQFactorial.isRCartier (hQ 0) _, hplt₀.2⟩
    | succ i ih =>
      refine ⟨fun Q' => ?_, MMP.Fourfold.IsQFactorial.isRCartier (hQ (i + 1)) _, ?_⟩
      · obtain ⟨Q, -, hQQ', -⟩ :=
          exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
        rw [hBt, hcoeffφ i _ hQQ']
        exact ih.1 Q
      · obtain ⟨m, hm⟩ := hK'can i
        have := IsRealFlipStep.pos_of_isLogDiscrepancy (hflipν i 0 le_rfl hμ) (hQ i) hm
          (by simpa using ih.2.2)
        simpa using this
  case hplt_up =>
    intro i
    induction i with
    | zero => exact ⟨hplt_up₀.1, MMP.Fourfold.IsQFactorial.isRCartier (hQ 0) _, hplt_up₀.2⟩
    | succ i ih =>
      refine ⟨fun Q' => ?_, MMP.Fourfold.IsQFactorial.isRCartier (hQ (i + 1)) _, ?_⟩
      · obtain ⟨Q, -, hQQ', -⟩ :=
          exists_transformPrimeDivisor_eq_some_of_mem_target (fl i) Q' (hφt' i Q')
        rw [hBt, hCtr, ← hsmulT, ← map_add, hcoeffφ i _ hQQ']
        exact ih.1 Q
      · obtain ⟨m, hm⟩ := hK'can i
        exact pos_of_isLogDiscrepancy_of_forall_lt hμ
          (fun ν hν hνμ => hflipν i ν hν.le hνμ) (hQ i) (hQ (i + 1)) hm (hCeff i) ih.2.2

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B C : RDivisor X} {A : QDivisor X}
    -- the SNC fourfold setting
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXsm : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 4) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C)) (hsnc : DivisorWithCoeffs.IsSNC sX (B + C))
    (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (QDivisor.toRDivisor A).coeff P ≤ B.coeff P)
    (hAfl : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the flip sequence `Y_0 ⤏ Y_1 ⤏ ⋯` over `Z`
    (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i))
    (BY CY : ∀ i, RDivisor (Y i))
    (W : ℕ → Scheme.{0}) [∀ i, IsLocallyNoetherian (W i)] [∀ i, IsNormal (W i)]
    (sW : ∀ i, W i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ W i) (fp : ∀ i, Y (i + 1) ⟶ W i) (g : ∀ i, W i ⟶ Z)
    (hπY : ∀ i, πY i ≫ sZ = sY i) (hfg : ∀ i, f i ≫ g i = πY i)
    (hfpg : ∀ i, fp i ≫ g i = πY (i + 1))
    (hK : ∀ i, ∃ m : ℕ, (KY i).IsCanonicalDivisor (sY i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (hQ : ∀ i, IsQFactorial (sY i))
    (hdimY : ∀ i, topologicalKrullDim (Y i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sY i) (sW i) (sY (i + 1)) (KY i) (BY i) (KY (i + 1))
      (BY (i + 1)) (f i) (fp i))
    (hCtr : ∀ i, CY (i + 1) = flipTransform (f i) (fp i) (CY i))
    -- scaling of `C_Y` at level one
    (hnef : ∀ i, IsRelativelyNef ℂ (sY i) (πY i) (logCanonicalDivisor (KY i) (BY i + CY i)))
    (htriv : ∀ i, IsNumericallyTrivialOver ℂ (sY i) (f i)
      (logCanonicalDivisor (KY i) (BY i + CY i)))
    -- the upper levels descend crepantly to `W_i`
    (hdesc : ∀ i, ∃ D : RDivisor (W i),
      IsRCartierPullback (f i) D (logCanonicalDivisor (KY i) (BY i + CY i)) ∧
        IsRCartierPullback (fp i) D
          (flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i))))
    -- `Y_0` is a log minimal model of `(X, B + C)`
    {φ : X.RationalMap (Y 0)}
    (hCY : CY 0 = MMP.Mori.RationalMap.transformDivisor φ C)
    (hBY : ∀ F : MMP.Mori.PrimeDivisor (Y 0), (BY 0).coeff F =
      (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        open Classical in if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsRealLogMinimalModel sX (sY 0) sZ π (πY 0) KX (B + C) (KY 0) (BY 0 + CY 0) φ)
    -- a component `E_0` of `⌊B_Y⌋` and its strict transforms
    (E : ∀ i, MMP.Mori.PrimeDivisor (Y i)) (hE : (BY 0).coeff (E 0) = 1)
    (hEtr : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (E i) = some (E (i + 1))) :
    ∃ N : ℕ, ∀ i, N ≤ i →
      Disjoint (MMP.Mori.exceptionalSet (f i) : Set (Y i)) ((E i).support : Set (Y i)) ∧
      Disjoint (MMP.Mori.exceptionalSet (fp i) : Set (Y (i + 1)))
        ((E (i + 1)).support : Set (Y (i + 1))) := by
  classical
  -- the modified sequence: canonical divisors `K'`, lower boundaries `B̃`, the constant level
  -- `μ`, and the plt reference `(X₀, S₀, A₀, ψ)`
  obtain ⟨K', Bt, μ, hμ, hK', hflip', hplt, hCeff, hnef', hplt_up, hcrep, hSB, hSC,
      X₀, _, _, _, _, sX₀, hX₀, hX₀p, S₀, _, A₀, hA₀, hAamp, hAS, ψ, ψinv, hψ, hψk, hψinvk,
      hψS, hord, hAB⟩ :=
    exists_constantLevel_pltSequence hX hXsm hdim hZ hB hC hdlt hsnc hA hA0 hAB hAfl Y sY πY KY BY
      CY W sW f fp hπY hK hproj hQ hdimY hflip hCtr hnef hdesc hCY hBY hY E hE hEtr
  exact eventually_disjoint_exceptionalSet_of_realPltFlip_scaling Y sY K' Bt CY W sW f fp Z sZ hZ
    πY g hπY hfg hfpg hK' hproj hQ hdimY hflip' hplt hCeff hCtr (fun _ => μ) (fun _ => hμ)
    antitone_const hnef' hplt_up hcrep E hSB hSC hEtr X₀ sX₀ hX₀ hX₀p S₀ A₀ hA₀ hAamp hAS ψ ψinv
    hψ hψk hψinvk hψS hord hAB

end Proof_lem_fourfold_upper_zero_place_constant_level_reference

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Level-one flips with scaling avoid every floor component.** Let `X` be a smooth projective
complex fourfold over a projective variety `Z`, `B, C ≥ 0` real divisors with `(X, B + C)` dlt
with snc support, and `A ≤ B` an effective ample `ℚ`-divisor with no component in `⌊B + C⌋`.
Let `(Y_0, B_0 + C_0)` be a log minimal model of `(X, B + C)` over `Z` with `C_0 = φ_* C` and
`B_0 = φ_* B + ∑ F` (`F` exceptional over `X`), and `E_0` a prime divisor with coefficient one in
`B_0`. Let `Y_i ⟶ Z_i ⟵ Y_{i+1}` be an infinite sequence of real flips of `(Y_i, B_i)` over `Z`
of projective `ℚ`-factorial fourfolds, with `C_{i+1}` the strict transform of `C_i`, such that
`K_i + B_i + C_i` is nef over `Z`, numerically trivial over `Z_i`, and the pull-back along `f_i`
of an `ℝ`-Cartier `D_i` on `Z_i` whose pull-back along `f_i⁺` is the strict transform of
`K_i + B_i + C_i`, and let `E_{i+1}` be the
strict transform of `E_i`. Then for all large `i`, `Ex(f_i)` is disjoint from `E_i` and
`Ex(f_i⁺)` is disjoint from `E_{i+1}`. -/
@[mmp "lem_fourfold_upper_zero_place_constant_level_reference"]
public theorem IsRealLogMinimalModel.eventually_disjoint_exceptionalSet_of_levelOne_scaling
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)} {π : X ⟶ Z}
    {KX : Divisor X} {B C : RDivisor X} {A : QDivisor X}
    -- the SNC fourfold setting
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXsm : IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 4) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hdlt : IsRealDltPair sX (B + C)) (hsnc : DivisorWithCoeffs.IsSNC sX (B + C))
    (hA : A.IsAmple) (hA0 : ∀ P, 0 ≤ A.coeff P)
    (hAB : ∀ P, (QDivisor.toRDivisor A).coeff P ≤ B.coeff P)
    (hAfl : ∀ P, A.coeff P ≠ 0 → (B + C).coeff P < 1)
    -- the flip sequence `Y_0 ⤏ Y_1 ⤏ ⋯` over `Z`
    (Y : ℕ → Scheme.{0}) [∀ i, IsIntegral (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    (sY : ∀ i, Y i ⟶ Spec (.of ℂ)) (πY : ∀ i, Y i ⟶ Z) (KY : ∀ i, Divisor (Y i))
    (BY CY : ∀ i, RDivisor (Y i))
    (W : ℕ → Scheme.{0}) [∀ i, IsLocallyNoetherian (W i)] [∀ i, IsNormal (W i)]
    (sW : ∀ i, W i ⟶ Spec (.of ℂ))
    (f : ∀ i, Y i ⟶ W i) (fp : ∀ i, Y (i + 1) ⟶ W i) (g : ∀ i, W i ⟶ Z)
    (hπY : ∀ i, πY i ≫ sZ = sY i) (hfg : ∀ i, f i ≫ g i = πY i)
    (hfpg : ∀ i, fp i ≫ g i = πY (i + 1))
    (hK : ∀ i, ∃ m : ℕ, (KY i).IsCanonicalDivisor (sY i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i))
    (hQ : ∀ i, IsQFactorial (sY i))
    (hdimY : ∀ i, topologicalKrullDim (Y i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sY i) (sW i) (sY (i + 1)) (KY i) (BY i) (KY (i + 1))
      (BY (i + 1)) (f i) (fp i))
    (hCtr : ∀ i, CY (i + 1) = flipTransform (f i) (fp i) (CY i))
    -- scaling of `C_Y` at level one
    (hnef : ∀ i, IsRelativelyNef ℂ (sY i) (πY i) (logCanonicalDivisor (KY i) (BY i + CY i)))
    (htriv : ∀ i, IsNumericallyTrivialOver ℂ (sY i) (f i)
      (logCanonicalDivisor (KY i) (BY i + CY i)))
    -- the upper levels descend crepantly to `W_i`
    (hdesc : ∀ i, ∃ D : RDivisor (W i),
      IsRCartierPullback (f i) D (logCanonicalDivisor (KY i) (BY i + CY i)) ∧
        IsRCartierPullback (fp i) D
          (flipTransform (f i) (fp i) (logCanonicalDivisor (KY i) (BY i + CY i))))
    -- `Y_0` is a log minimal model of `(X, B + C)`
    {φ : X.RationalMap (Y 0)}
    (hCY : CY 0 = MMP.Mori.RationalMap.transformDivisor φ C)
    (hBY : ∀ F : MMP.Mori.PrimeDivisor (Y 0), (BY 0).coeff F =
      (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        open Classical in if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsRealLogMinimalModel sX (sY 0) sZ π (πY 0) KX (B + C) (KY 0) (BY 0 + CY 0) φ)
    -- a component `E_0` of `⌊B_Y⌋` and its strict transforms
    (E : ∀ i, MMP.Mori.PrimeDivisor (Y i)) (hE : (BY 0).coeff (E 0) = 1)
    (hEtr : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (E i) = some (E (i + 1))) :
    ∃ N : ℕ, ∀ i, N ≤ i →
      Disjoint (MMP.Mori.exceptionalSet (f i) : Set (Y i)) ((E i).support : Set (Y i)) ∧
      Disjoint (MMP.Mori.exceptionalSet (fp i) : Set (Y (i + 1)))
        ((E (i + 1)).support : Set (Y (i + 1))) :=
  Proof_lem_fourfold_upper_zero_place_constant_level_reference.solution hX hXsm hdim hZ hB hC
    hdlt hsnc hA hA0 hAB hAfl Y sY πY KY BY CY W sW f fp g hπY hfg hfpg hK hproj hQ hdimY hflip
    hCtr hnef htriv hdesc hCY hBY hY E hE hEtr

end MMP.Fourfold
