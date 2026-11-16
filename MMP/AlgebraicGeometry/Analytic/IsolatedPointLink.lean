module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
public import MMP.AlgebraicTopology.SingularCohomology.Relative.Homotopy
public import MMP.Geometry.Manifold.Corners.Rounding
public import MMP.Analysis.Convex.ConvexCover
public import MMP.AlgebraicGeometry.Analytic.CornerPresentation
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
public import MMP.AlgebraicGeometry.Analytic.SchemeManifold

/-!
# Links of isolated points of a closed algebraic subset

Let `P` be a reduced projective scheme over `ℂ` and `S ⊆ P` a closed subset containing the
singular locus of `P` and no irreducible component of `P`. An isolated point `x` of `S^an` has a
cofinal system of open neighbourhoods `C` in `P^an` with `C ∩ S^an = {x}` on which the punctured
cohomology `H^q(C ∖ {x}; ℚ)` is finite dimensional and the restriction maps between these groups
are isomorphisms. Consequently the local punctured cohomology
`colim_{V ∋ x} H^q(V ∖ {x}; ℚ)` is finite dimensional.

The cofinal system is made of cones `{x} ∪ e(L × (0, ε))` for an embedding
`e : L × (0, 1) → P^an ∖ S^an` (the collar of the fibre `L` of `∂M → S` over `x`, in a corner
presentation `P ≅ M ∪_{∂M} S`): each punctured cone deformation retracts onto `e(L × {ε/2})`, so
the projection to `L` is an isomorphism on rational cohomology, compatibly with restriction.
The cones are open in the pushout `M ∪_{∂M} S^an` because their preimages in `M` and in `S^an`
are, and they shrink to `x` by the tube lemma applied to the compact fibre `L`.

`H^q(L; ℚ)` is finite dimensional: `L` is clopen in `∂M`, hence a retract of it, and `∂M` is
homotopy equivalent to a finite disjoint union of compact sets of positive reach in Euclidean
spaces, each homotopy equivalent to a finite union of open balls. Mayer–Vietoris finiteness for
open covers by two sets, proved from excision and the exact sequence of a pair, gives the
finiteness for finite unions of open convex sets.

## Main results

* `MMP.Fourfold.exists_cofinal_isIso_punctured_cohomology_of_isolated`: the cofinal system of
  neighbourhoods, and finite dimensionality of the stalk at `x` of the presheaf
  `V ↦ H^q(V ∖ {x}; ℚ)`.

## Implementation notes

* `H^q(V ∖ {x}; ℚ)` is the value at `V` of `MMP.Fourfold.directImagePresheaf j q` for the
  inclusion `j : P^an ∖ {x} ⟶ P^an`; its restriction maps are the maps of that presheaf. The
  colimit over the open neighbourhoods `V ∋ x` contained in a given open neighbourhood `P'` of `x`
  is the stalk of this presheaf at `x`, those neighbourhoods being cofinal among all; the statement
  is made for the stalk.
* `S` is a Zariski closed subset of `P`, and `S^an` is its inverse image under
  `MMP.Analytic.ComplexPoints.toScheme`; "isolated" is in the analytic topology.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.Proof_lem_mmp_curvels_isolated_link_finite`. Among them:
  `stalk_finiteDimensional_of_cofinal_isIso` (finite-dimensional stalk of a presheaf of
  `ℚ`-modules from a cofinal system with isomorphic restriction maps),
  `cofinal_system_of_conical` (such a system for `V ↦ H^q(V ∖ {x}; ℚ)` from open cones),
  `fd_of_union_eq_univ` (Mayer–Vietoris finiteness of rational cohomology), `fd_boundary`
  (finiteness for the boundary of a finite disjoint union of compact manifolds with corners) and
  `conical_of_isPushout` (conical neighbourhoods in a pushout `M ∪_{∂M} S` with a collared
  boundary).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
* [B. Iversen, *Cohomology of sheaves*][iversen1986], III.1, for singular and sheaf cohomology.
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Opposite MMP.Fourfold

namespace MMP.Proof_lem_mmp_curvels_isolated_link_finite

/-- A presheaf of `ℚ`-modules with finite-dimensional sections and isomorphic restriction maps
over a cofinal set `𝒞` of open neighbourhoods of `x` has finite-dimensional stalk at `x`. -/
private theorem stalk_finiteDimensional_of_cofinal_isIso {X : TopCat.{0}}
    (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X) (x : X)
    (𝒞 : Set (Opens X)) (hmem : ∀ C ∈ 𝒞, x ∈ C ∧ FiniteDimensional ℚ (F.obj (op C)))
    (hcof : ∀ V : Opens X, x ∈ V → ∃ C ∈ 𝒞, C ≤ V)
    (hiso : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ h : C' ≤ C, IsIso (F.map (homOfLE h).op)) :
    FiniteDimensional ℚ (F.stalk x) := by
  obtain ⟨C₀, hC₀, -⟩ := hcof ⊤ trivial
  obtain ⟨hx₀, hfd⟩ := hmem C₀ hC₀
  have hsurj : Function.Surjective (F.germ C₀ x hx₀) := by
    intro t
    obtain ⟨U, hU, hxU, s, rfl⟩ := F.exists_le_germ_eq t hx₀
    obtain ⟨C, hC, hCU⟩ := hcof U hxU
    have hCC₀ : C ≤ C₀ := hCU.trans hU
    haveI := hiso C₀ hC₀ C hC hCC₀
    obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective (F.map (homOfLE hCC₀).op)).1
      inferInstance (F.map (homOfLE hCU).op s)
    refine ⟨u, ?_⟩
    rw [← F.germ_res_apply (homOfLE hCC₀) x (hmem C hC).1, hu, F.germ_res_apply]
  exact LinearMap.finiteDimensional_of_surjective (F.germ C₀ x hx₀).hom
    (LinearMap.range_eq_top.2 hsurj)

/-- A map with a section `b` such that `a ≫ b` is homotopic to the identity induces an
isomorphism on rational cohomology. -/
private lemma isIso_rationalCohomologyMap_of_section {Z Y : TopCat.{0}} (a : Z ⟶ Y)
    (b : Y ⟶ Z) (h₁ : b ≫ a = 𝟙 Y) (H : TopCat.Homotopy (a ≫ b) (𝟙 Z)) (q : ℕ) :
    IsIso (rationalCohomologyMap a q) := by
  refine ⟨⟨rationalCohomologyMap b q, ?_, ?_⟩⟩
  · rw [← rationalCohomologyMap_comp, h₁, rationalCohomologyMap_id]
  · rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_id]
    unfold rationalCohomologyMap
    exact MMP.relativeSingularCohomology.map_eq_of_homotopy ℚ H
      (fun _ hy _ ↦ absurd (Set.mem_univ _) hy) _ _ _

/-! ### Conical neighbourhoods

Let `e : L × (0, 1) → X` be an embedding missing `x`, and `C ⊆ X` an open set equal to
`{x} ∪ e(L × (0, ε))`. Then `C ∖ {x}` deformation retracts onto `e(L × {ε/2})`, so the
projection `C ∖ {x} → L` induces an isomorphism on rational cohomology. -/

section Conical

variable {X : TopCat.{0}} {L : Type} [TopologicalSpace L] {e : L × Set.Ioo (0 : ℝ) 1 → X}
  {x : X} {C : Opens X} {ε : ℝ}

/-- The inclusion `X ∖ {x} ⟶ X`. -/
private abbrev puncture (x : X) : TopCat.of ({x}ᶜ : Set X) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private lemma exists_eq_of_mem_conical
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε}))
    (z : preimageSpace (puncture x) C) : ∃ p, (p.2 : ℝ) < ε ∧ e p = z.1.1 := by
  have h : z.1.1 ∈ insert x (e '' {p | (p.2 : ℝ) < ε}) := by
    rw [← hC]
    exact z.2
  exact h.resolve_left z.1.2

/-- The coordinates in `L × (0, 1)` of a point of `C ∖ {x}`. -/
private noncomputable def conicalCoord (he : IsEmbedding e)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε}))
    (z : preimageSpace (puncture x) C) : L × Set.Ioo (0 : ℝ) 1 :=
  he.toHomeomorph.symm ⟨z.1.1, by
    obtain ⟨p, -, hp⟩ := exists_eq_of_mem_conical hC z
    exact ⟨p, hp⟩⟩

private lemma apply_conicalCoord (he : IsEmbedding e)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε}))
    (z : preimageSpace (puncture x) C) : e (conicalCoord he hC z) = z.1.1 := by
  unfold conicalCoord
  exact congrArg Subtype.val (he.toHomeomorph.apply_symm_apply _)

private lemma conicalCoord_lt (he : IsEmbedding e)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε}))
    (z : preimageSpace (puncture x) C) : ((conicalCoord he hC z).2 : ℝ) < ε := by
  obtain ⟨p, hp, hpe⟩ := exists_eq_of_mem_conical hC z
  rwa [he.injective ((apply_conicalCoord he hC z).trans hpe.symm)]

private lemma continuous_conicalCoord (he : IsEmbedding e)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) :
    Continuous (conicalCoord he hC) :=
  he.toHomeomorph.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

private lemma mem_conical (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε}))
    (p : L × Set.Ioo (0 : ℝ) 1) (hp : (p.2 : ℝ) < ε) : e p ∈ (C : Set X) := by
  rw [hC]
  exact Or.inr ⟨p, hp, rfl⟩

/-- The projection `C ∖ {x} → L`. -/
private noncomputable def conicalProj (he : IsEmbedding e)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) :
    preimageSpace (puncture x) C ⟶ TopCat.of L :=
  TopCat.ofHom ⟨fun z ↦ (conicalCoord he hC z).1,
    continuous_fst.comp (continuous_conicalCoord he hC)⟩

/-- The section `y ↦ e(y, ε/2)` of `conicalProj`. -/
private noncomputable def conicalSection (he : IsEmbedding e) (hx : ∀ p, e p ≠ x)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    TopCat.of L ⟶ preimageSpace (puncture x) C :=
  TopCat.ofHom ⟨fun y ↦ ⟨⟨e (y, ⟨ε / 2, by positivity, by linarith⟩), hx _⟩,
      mem_conical hC _ (half_lt_self hε)⟩,
    by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact he.continuous.comp (continuous_id.prodMk continuous_const)⟩

private lemma conicalSection_comp_conicalProj (he : IsEmbedding e) (hx : ∀ p, e p ≠ x)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    conicalSection he hx hC hε hε1 ≫ conicalProj he hC = 𝟙 _ := by
  ext y
  change (conicalCoord he hC _).1 = y
  unfold conicalCoord
  exact congrArg Prod.fst (he.toHomeomorph_symm_apply _)

/-- The straight-line deformation of `C ∖ {x}` onto `e(L × {ε/2})`. -/
private noncomputable def conicalHomotopy (he : IsEmbedding e) (hx : ∀ p, e p ≠ x)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    TopCat.Homotopy (conicalProj he hC ≫ conicalSection he hx hC hε hε1) (𝟙 _) := by
  have hmem : ∀ (s : unitInterval) (z : preimageSpace (puncture x) C),
      (1 - (s : ℝ)) * (ε / 2) + (s : ℝ) * ((conicalCoord he hC z).2 : ℝ) ∈ Set.Ioo 0 ε := by
    intro s z
    have h := (convex_Ioo (0 : ℝ) ε) (x := ε / 2) (y := ((conicalCoord he hC z).2 : ℝ))
      ⟨by positivity, by linarith⟩ ⟨(conicalCoord he hC z).2.2.1, conicalCoord_lt he hC z⟩
      (sub_nonneg.2 s.2.2) s.2.1 (by ring)
    simpa [smul_eq_mul] using h
  have hc := continuous_conicalCoord he hC
  exact
  { toFun := fun p ↦ ⟨⟨e ((conicalCoord he hC p.2).1,
        ⟨(1 - (p.1 : ℝ)) * (ε / 2) + (p.1 : ℝ) * ((conicalCoord he hC p.2).2 : ℝ),
          (hmem p.1 p.2).1, (hmem p.1 p.2).2.trans_le hε1⟩), hx _⟩,
      mem_conical hC _ (hmem p.1 p.2).2⟩
    continuous_toFun := by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      refine he.continuous.comp (Continuous.prodMk ?_ ?_)
      · exact continuous_fst.comp (hc.comp continuous_snd)
      · apply Continuous.subtype_mk
        have h2 : Continuous fun p : unitInterval × preimageSpace (puncture x) C ↦
            ((conicalCoord he hC p.2).2 : ℝ) :=
          continuous_subtype_val.comp (continuous_snd.comp (hc.comp continuous_snd))
        have h1 : Continuous fun p : unitInterval × preimageSpace (puncture x) C ↦
            (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
        exact ((continuous_const.sub h1).mul continuous_const).add (h1.mul h2)
    map_zero_left := fun z ↦ by
      refine Subtype.ext (Subtype.ext ?_)
      change e _ = e _
      congr 1
      exact Prod.ext rfl (Subtype.ext (by simp))
    map_one_left := fun z ↦ by
      refine Subtype.ext (Subtype.ext ?_)
      change e _ = z.1.1
      refine Eq.trans ?_ (apply_conicalCoord he hC z)
      congr 1
      exact Prod.ext rfl (Subtype.ext (by simp)) }

private lemma isIso_conicalProj (he : IsEmbedding e) (hx : ∀ p, e p ≠ x)
    (hC : (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ) : IsIso (rationalCohomologyMap (conicalProj he hC) q) :=
  isIso_rationalCohomologyMap_of_section _ _ (conicalSection_comp_conicalProj he hx hC hε hε1)
    (conicalHomotopy he hx hC hε hε1) q

end Conical

/-- An embedding `e : L × (0, 1) → X` missing a set `T ∋ x`, whose cones
`{x} ∪ e(L × (0, ε))` are open and shrink to `x`, and with `H^*(L; ℚ)` finite dimensional, gives
a cofinal system of neighbourhoods of `x` with finite-dimensional punctured cohomology and
isomorphic restriction maps. -/
private theorem cofinal_system_of_conical {X : TopCat.{0}} {L : Type} [TopologicalSpace L]
    {e : L × Set.Ioo (0 : ℝ) 1 → X} (he : IsEmbedding e) (x : X) (T : Set X) (hxT : x ∈ T)
    (hT : ∀ p, e p ∉ T)
    (hopen : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, IsOpen (insert x (e '' {p | (p.2 : ℝ) < ε})))
    (hshrink : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ ε ∈ Set.Ioc (0 : ℝ) 1, e '' {p | (p.2 : ℝ) < ε} ⊆ V)
    (hfd : ∀ q : ℕ, FiniteDimensional ℚ (rationalCohomology (TopCat.of L) q)) :
    ∃ 𝒞 : Set (Opens X),
      (∀ C ∈ 𝒞, x ∈ C ∧ (C : Set X) ∩ T = {x} ∧
        ∀ q : ℕ, FiniteDimensional ℚ ((directImagePresheaf (puncture x) q).obj (op C))) ∧
      (∀ V : Opens X, x ∈ V → ∃ C ∈ 𝒞, C ≤ V) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ h : C' ≤ C, ∀ q : ℕ,
        IsIso ((directImagePresheaf (puncture x) q).map (homOfLE h).op)) := by
  have hx : ∀ p, e p ≠ x := fun p h ↦ hT p (h ▸ hxT)
  refine ⟨{C | ∃ ε ∈ Set.Ioc (0 : ℝ) 1, (C : Set X) = insert x (e '' {p | (p.2 : ℝ) < ε})},
    ?_, ?_, ?_⟩
  · rintro C ⟨ε, ⟨hε, hε1⟩, hC⟩
    refine ⟨?_, ?_, fun q ↦ ?_⟩
    · change x ∈ (C : Set X)
      rw [hC]
      exact Set.mem_insert _ _
    · rw [hC]
      ext y
      constructor
      · rintro ⟨h | ⟨p, -, rfl⟩, hyT⟩
        · exact h
        · exact absurd hyT (hT p)
      · rintro rfl
        exact ⟨Set.mem_insert _ _, hxT⟩
    · haveI := isIso_conicalProj he hx hC hε hε1 q
      haveI := hfd q
      exact LinearEquiv.finiteDimensional
        (asIso (rationalCohomologyMap (conicalProj he hC) q)).toLinearEquiv
  · intro V hxV
    obtain ⟨ε, hε, hsub⟩ := hshrink V V.isOpen hxV
    exact ⟨⟨_, hopen ε hε⟩, ⟨ε, hε, rfl⟩, Set.insert_subset hxV hsub⟩
  · rintro C ⟨ε, ⟨hε, hε1⟩, hC⟩ C' ⟨ε', ⟨hε', hε1'⟩, hC'⟩ h q
    change IsIso (rationalCohomologyMap (preimageInclusion (puncture x) h) q)
    have hcomp : preimageInclusion (puncture x) h ≫ conicalProj he hC = conicalProj he hC' := rfl
    haveI := isIso_conicalProj he hx hC hε hε1 q
    haveI : IsIso (rationalCohomologyMap (conicalProj he hC) q ≫
        rationalCohomologyMap (preimageInclusion (puncture x) h) q) := by
      rw [← rationalCohomologyMap_comp, hcomp]
      exact isIso_conicalProj he hx hC' hε' hε1' q
    exact IsIso.of_isIso_comp_left (rationalCohomologyMap (conicalProj he hC) q) _

/-! ### Finite-dimensional rational cohomology

`H^n(Z; ℚ)` is computed here by the relative cochain cohomology relative to the empty set. It is
invariant under homotopy equivalence, satisfies Mayer–Vietoris finiteness for open covers by two
sets, and is therefore finite dimensional for finite unions of open convex sets, for compact sets
of positive reach, for the boundary of a compact manifold with corners and for its clopen pieces.
-/

section Finiteness

open MMP MMP.SingularCochain MMP.SingularChain

/-- The absolute cochain cohomology `H^n(Z; ℚ)`, as cocycles modulo coboundaries. -/
private abbrev H (Z : TopCat.{0}) (n : ℕ) : Type :=
  relCohomology ℚ ((Set.univ : Set Z)ᶜ) n

/-- All rational cohomology groups of `Z` are finite dimensional. -/
private def FD (Z : TopCat.{0}) : Prop := ∀ n, FiniteDimensional ℚ (H Z n)

/-- Every cochain vanishes on the simplices of a set containing no point. -/
private lemma mem_vanishing_of_forall_notMem {Y : TopCat.{0}} {n : ℕ} {S : Set Y}
    (h : ∀ y, y ∉ S) (φ : Simplex Y n → ℚ) : φ ∈ vanishing ℚ n S := fun σ hσ ↦ by
  obtain ⟨y, hy⟩ := Set.range_nonempty σ
  exact absurd (hσ hy) (h y)

private lemma mem_vanishing_compl_univ {Y : TopCat.{0}} {n : ℕ} (φ : Simplex Y n → ℚ) :
    φ ∈ vanishing ℚ n (Set.univ : Set Y)ᶜ :=
  mem_vanishing_of_forall_notMem (S := (Set.univ : Set Y)ᶜ) (fun y h ↦ h (Set.mem_univ y)) φ

private lemma compl_univ_subset {X X' : TopCat.{0}} (f : X ⟶ X') {A : Set X'} :
    (Set.univ : Set X)ᶜ ⊆ f ⁻¹' A := fun x hx ↦ absurd (Set.mem_univ x) hx

private lemma relCohomologyMap_comp_apply {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y)
    {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (n : ℕ)
    (x : relCohomology ℚ A n) :
    relCohomologyMap ℚ g hg n (relCohomologyMap ℚ f hf n x) =
      relCohomologyMap ℚ (g ≫ f) (fun _ h ↦ hf (hg h)) n x := by
  induction x using Submodule.Quotient.induction_on with
  | H φ => rfl

private lemma relCohomologyMap_id_apply {Y : TopCat.{0}} {A : Set Y} (h : A ⊆ 𝟙 Y ⁻¹' A)
    (n : ℕ) (x : relCohomology ℚ A n) : relCohomologyMap ℚ (𝟙 Y) h n x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H φ => rfl

/-- A map `g` with a homotopy left inverse is surjective on cohomology, so the cohomology of its
source is finite dimensional when that of its target is. -/
private lemma finiteDimensional_of_homotopy {Z Z' : TopCat.{0}} (g : Z ⟶ Z') (r : Z' ⟶ Z)
    (Hm : TopCat.Homotopy (g ≫ r) (𝟙 Z)) (n : ℕ) [FiniteDimensional ℚ (H Z' n)] :
    FiniteDimensional ℚ (H Z n) := by
  refine LinearMap.finiteDimensional_of_surjective (relCohomologyMap ℚ g (compl_univ_subset g) n)
    (LinearMap.range_eq_top.2 fun x ↦ ⟨relCohomologyMap ℚ r (compl_univ_subset r) n x, ?_⟩)
  calc relCohomologyMap ℚ g (compl_univ_subset g) n (relCohomologyMap ℚ r (compl_univ_subset r) n x)
      = relCohomologyMap ℚ (g ≫ r) (compl_univ_subset _) n x :=
        relCohomologyMap_comp_apply _ _ _ _ _ _
    _ = relCohomologyMap ℚ (𝟙 Z) (compl_univ_subset _) n x := by
      rw [relCohomologyMap_eq_of_homotopy Hm (fun _ hy _ ↦ absurd (Set.mem_univ _) hy)
        (compl_univ_subset _) (compl_univ_subset _)]
    _ = x := relCohomologyMap_id_apply _ _ _

private lemma fd_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (h : FD (TopCat.of Y)) : FD (TopCat.of X) := fun n ↦ by
  haveI := h n
  exact finiteDimensional_of_homotopy (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some n

private lemma fd_of_finite_simplex {Z : TopCat.{0}} (h : ∀ n, Finite (Simplex Z n)) : FD Z :=
  fun n ↦ by
    haveI := h n
    infer_instance

private lemma fd_of_isEmpty {Z : TopCat.{0}} (h : IsEmpty Z) : FD Z :=
  fd_of_finite_simplex fun n ↦ by
    haveI : IsEmpty (Simplex Z n) := ⟨fun σ ↦ h.false (σ (Classical.arbitrary _))⟩
    infer_instance

private lemma fd_of_contractibleSpace {X : Type} [TopologicalSpace X] [ContractibleSpace X] :
    FD (TopCat.of X) :=
  fd_of_homotopyEquiv (ContractibleSpace.hequiv_unit' (X := X)).some <|
    fd_of_finite_simplex fun n ↦ by
      haveI : Subsingleton (Simplex (TopCat.of Unit) n) :=
        ⟨fun σ τ ↦ ContinuousMap.ext fun _ ↦ rfl⟩
      infer_instance

/-- Extension by zero of cochains, as a linear map. -/
private noncomputable def extendₗ {Y : TopCat.{0}} (V : Set Y) (n : ℕ) :
    (Simplex (TopCat.of V) n → ℚ) →ₗ[ℚ] (Simplex Y n → ℚ) where
  toFun := extendCochain
  map_add' φ ψ := by
    ext σ
    by_cases h : Set.range σ ⊆ V <;> simp [extendCochain, h]
  map_smul' c φ := by
    ext σ
    by_cases h : Set.range σ ⊆ V <;> simp [extendCochain, h]

private lemma coboundary_extend_of_subset {Y : TopCat.{0}} {V : Set Y} {n : ℕ}
    (ψ : Simplex (TopCat.of V) n → ℚ) {σ : Simplex Y (n + 1)} (hσ : Set.range σ ⊆ V) :
    coboundary ℚ n (extendCochain ψ) σ = coboundary ℚ n ψ (liftSimplex σ hσ) := by
  rw [coboundary_extendCochain (A := ∅) (mem_vanishing_of_forall_notMem (fun _ h ↦ h) _)
    (Or.inl hσ), extendCochain_of_subset _ hσ]

private lemma finiteDimensional_of_ker_le_range {U V W : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ U]
    [FiniteDimensional ℚ W] (f : V →ₗ[ℚ] W) (g : U →ₗ[ℚ] V)
    (h : LinearMap.ker f ≤ LinearMap.range g) : FiniteDimensional ℚ V := by
  refine Module.finite_def.2 ?_
  refine Submodule.fg_of_fg_map_of_fg_inf_ker f (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq]
  haveI := Submodule.finiteDimensional_of_le h
  exact Module.Finite.iff_fg.1 inferInstance

/-- `H^n(Y)` is finite dimensional when `H^n(Y, A)` and `H^n(A)` are. -/
private lemma finiteDimensional_of_pair {Y : TopCat.{0}} (A : Set Y) (n : ℕ)
    [FiniteDimensional ℚ (relCohomology ℚ A n)] [FiniteDimensional ℚ (H (TopCat.of A) n)] :
    FiniteDimensional ℚ (H Y n) := by
  refine finiteDimensional_of_ker_le_range
    (relCohomologyMap ℚ (subspaceInclusion Y A) (compl_univ_subset _) n)
    (relCohomologyMap ℚ (𝟙 Y) (compl_univ_subset _ (A := A)) n) ?_
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H φ =>
  rw [LinearMap.mem_ker, relCohomologyMap_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hx
  have hφ := (mem_relCocycles_iff _ _ _ _).1 φ.2
  cases n with
  | zero =>
    have h0 : cochainPullback ℚ (subspaceInclusion Y A) 0 φ.1 = 0 := (Submodule.mem_bot ℚ).1 hx
    have hv : φ.1 ∈ vanishing ℚ 0 A := fun σ hσ ↦ congrFun h0 (liftSimplex σ hσ)
    exact ⟨Submodule.Quotient.mk ⟨φ.1, (mem_relCocycles_iff _ _ _ _).2 ⟨hv, hφ.2⟩⟩, rfl⟩
  | succ m =>
    obtain ⟨α, -, hα⟩ := hx
    have hv : φ.1 - coboundary ℚ m (extendCochain α) ∈ vanishing ℚ (m + 1) A := fun σ hσ ↦ by
      rw [Pi.sub_apply, coboundary_extend_of_subset _ hσ, hα]
      exact sub_self _
    have hc : coboundary ℚ (m + 1) (φ.1 - coboundary ℚ m (extendCochain α)) = 0 := by
      rw [map_sub, hφ.2, coboundary_coboundary, sub_zero]
    refine ⟨Submodule.Quotient.mk ⟨_, (mem_relCocycles_iff _ _ _ _).2 ⟨hv, hc⟩⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    refine ⟨-extendCochain α, mem_vanishing_compl_univ _, ?_⟩
    change coboundary ℚ m (-extendCochain α) = (φ.1 - coboundary ℚ m (extendCochain α)) - φ.1
    rw [map_neg]
    abel

private lemma coboundary_extendₗ_mem_relCocycles {B : TopCat.{0}} (D : Set B) (m : ℕ)
    (γ : relCocycles ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m) :
    coboundary ℚ m (extendₗ D m γ.1) ∈ relCocycles ℚ D (m + 1) := by
  refine (mem_relCocycles_iff _ _ _ _).2 ⟨fun σ hσ ↦ ?_, coboundary_coboundary _ _⟩
  change coboundary ℚ m (extendCochain γ.1) σ = 0
  rw [coboundary_extend_of_subset _ hσ, ((mem_relCocycles_iff _ _ _ _).1 γ.2).2]
  rfl

private lemma coboundary_extendCochain_mem_relCoboundaries {B : TopCat.{0}} (D : Set B) (m : ℕ)
    (γ : Simplex (TopCat.of D) m → ℚ)
    (hγ : γ ∈ relCoboundaries ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m) :
    coboundary ℚ m (extendCochain γ) ∈ relCoboundaries ℚ D (m + 1) := by
  cases m with
  | zero =>
    rw [(Submodule.mem_bot ℚ).1 hγ, extendCochain_zero, map_zero]
    exact Submodule.zero_mem _
  | succ k =>
    obtain ⟨η, -, hη⟩ := hγ
    refine ⟨extendCochain γ - coboundary ℚ k (extendCochain η), fun σ hσ ↦ ?_, ?_⟩
    · rw [Pi.sub_apply, coboundary_extend_of_subset _ hσ, extendCochain_of_subset _ hσ, hη]
      exact sub_self _
    · change coboundary ℚ (k + 1) (extendCochain γ - coboundary ℚ k (extendCochain η)) = _
      rw [map_sub, coboundary_coboundary, sub_zero]

/-- `H^0(B, D)` is finite dimensional when `H^0(B)` is. -/
private lemma finiteDimensional_relCohomology_zero {B : TopCat.{0}} (D : Set B)
    [FiniteDimensional ℚ (H B 0)] : FiniteDimensional ℚ (relCohomology ℚ D 0) := by
  refine Module.Finite.of_injective
    (relCohomologyMap ℚ (𝟙 B) (compl_univ_subset _ (A := D)) 0) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H ψ =>
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rwa [relCohomologyMap_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx

/-- `H^{m+1}(B, D)` is finite dimensional when `H^{m+1}(B)` and `H^m(D)` are. -/
private lemma finiteDimensional_relCohomology_succ {B : TopCat.{0}} (D : Set B) (m : ℕ)
    [FiniteDimensional ℚ (H B (m + 1))] [FiniteDimensional ℚ (H (TopCat.of D) m)] :
    FiniteDimensional ℚ (relCohomology ℚ D (m + 1)) := by
  let c₀ := (Submodule.mkQ ((relCoboundaries ℚ D (m + 1)).comap
    (relCocycles ℚ D (m + 1)).subtype)).comp (LinearMap.codRestrict (relCocycles ℚ D (m + 1))
    ((coboundary ℚ m).comp ((extendₗ D m).comp
      (relCocycles ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m).subtype))
    (coboundary_extendₗ_mem_relCocycles D m))
  have hc₀ : (relCoboundaries ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m).comap
      (relCocycles ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m).subtype ≤ LinearMap.ker c₀ := by
    intro γ hγ
    rw [Submodule.mem_comap] at hγ
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact coboundary_extendCochain_mem_relCoboundaries D m γ.1 hγ
  refine finiteDimensional_of_ker_le_range
    (relCohomologyMap ℚ (𝟙 B) (compl_univ_subset _ (A := D)) (m + 1))
    (Submodule.liftQ _ c₀ hc₀) ?_
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H ψ =>
  rw [LinearMap.mem_ker, relCohomologyMap_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at hx
  obtain ⟨β, -, hβ⟩ := hx
  have hψ := (mem_relCocycles_iff _ _ _ _).1 ψ.2
  have hγ : cochainPullback ℚ (subspaceInclusion B D) m β ∈
      relCocycles ℚ ((Set.univ : Set (TopCat.of D))ᶜ) m := by
    refine (mem_relCocycles_iff _ _ _ _).2 ⟨mem_vanishing_compl_univ _, ?_⟩
    rw [coboundary_cochainPullback]
    change cochainPullback ℚ (subspaceInclusion B D) (m + 1) (coboundary ℚ m β) = 0
    rw [hβ]
    funext τ
    exact hψ.1 _ (range_subspaceInclusion_comp τ)
  refine ⟨Submodule.Quotient.mk ⟨_, hγ⟩, ?_⟩
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨extendCochain (cochainPullback ℚ (subspaceInclusion B D) m β) - β,
    fun σ hσ ↦ ?_, ?_⟩
  · rw [Pi.sub_apply, extendCochain_of_subset _ hσ]
    exact sub_self _
  · change _ = coboundary ℚ m (extendCochain (cochainPullback ℚ (subspaceInclusion B D) m β))
      - ψ.1
    rw [map_sub, hβ]
    rfl

/-- `H^n(B, D)` is finite dimensional when `H^n(B)` and `H^{n-1}(D)` are. -/
private lemma finiteDimensional_relCohomology {B : TopCat.{0}} (D : Set B) (n : ℕ)
    [FiniteDimensional ℚ (H B n)]
    (hD : ∀ m, n = m + 1 → FiniteDimensional ℚ (H (TopCat.of D) m)) :
    FiniteDimensional ℚ (relCohomology ℚ D n) := by
  cases n with
  | zero => exact finiteDimensional_relCohomology_zero D
  | succ m =>
    haveI := hD m rfl
    exact finiteDimensional_relCohomology_succ D m

private lemma fd_congr {Y : TopCat.{0}} {S T : Set Y} (h : S = T) (hT : FD (TopCat.of T)) :
    FD (TopCat.of S) :=
  fd_of_homotopyEquiv (Homeomorph.setCongr h).toHomotopyEquiv hT

/-- `H^n(Y, A)` is finite dimensional when `H^n(B, A ∩ B)` is, for an open cover `{A, B}` of
`Y` (by excision). -/
private lemma finiteDimensional_relCohomology_of_excision {Y : TopCat.{0}} {A B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = Set.univ) (n : ℕ)
    [FiniteDimensional ℚ (relCohomology ℚ ((subspaceInclusion Y B) ⁻¹' Aᶜ)ᶜ n)] :
    FiniteDimensional ℚ (relCohomology ℚ A n) := by
  have hXV : Aᶜ ⊆ B := fun x hx ↦
    ((Set.mem_union _ _ _).1 (hAB ▸ Set.mem_univ x)).resolve_left hx
  have := (LinearEquiv.ofBijective _ (bijective_relCohomologyMap_subspaceInclusion (R := ℚ) hB
    hA.isClosed_compl hXV n)).symm.finiteDimensional
  rwa [compl_compl] at this

/-- **Mayer–Vietoris finiteness.** If `Y = A ∪ B` with `A`, `B` open and `A`, `B`, `A ∩ B` have
finite-dimensional rational cohomology, so has `Y`. -/
private lemma fd_of_union_eq_univ {Y : TopCat.{0}} {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (hAB : A ∪ B = Set.univ) (hfA : FD (TopCat.of A)) (hfB : FD (TopCat.of B))
    (hfAB : FD (TopCat.of (A ∩ B : Set Y))) : FD Y := fun n ↦ by
  haveI := hfA n
  haveI := hfB n
  let D : Set (TopCat.of B) := ((subspaceInclusion Y B) ⁻¹' Aᶜ)ᶜ
  let e : D ≃ₜ (A ∩ B : Set Y) :=
    { toFun := fun x ↦ ⟨x.1.1, Classical.byContradiction fun h ↦ x.2 h, x.1.2⟩
      invFun := fun y ↦ ⟨⟨y.1, y.2.2⟩, fun h ↦ h y.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  haveI := finiteDimensional_relCohomology D n fun m _ ↦
    fd_of_homotopyEquiv e.toHomotopyEquiv hfAB m
  haveI := finiteDimensional_relCohomology_of_excision hA hB hAB n
  exact finiteDimensional_of_pair A n

private lemma fd_union {Y : TopCat.{0}} {S T : Set Y} (hS : IsOpen S) (hT : IsOpen T)
    (h₁ : FD (TopCat.of S)) (h₂ : FD (TopCat.of T)) (h₃ : FD (TopCat.of (S ∩ T : Set Y))) :
    FD (TopCat.of (S ∪ T : Set Y)) :=
  fd_of_union_eq_univ (Y := TopCat.of (S ∪ T : Set Y)) (A := Subtype.val ⁻¹' S)
    (B := Subtype.val ⁻¹' T) (hS.preimage continuous_subtype_val)
    (hT.preimage continuous_subtype_val) (Set.eq_univ_of_forall fun x ↦ x.2)
    (fd_of_homotopyEquiv (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (Subtype.range_coe.symm ▸ Set.subset_union_left)).toHomotopyEquiv h₁)
    (fd_of_homotopyEquiv (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (Subtype.range_coe.symm ▸ Set.subset_union_right)).toHomotopyEquiv h₂)
    (fd_of_homotopyEquiv (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (s := S ∩ T)
      (Subtype.range_coe.symm ▸
        Set.inter_subset_left.trans Set.subset_union_left)).toHomotopyEquiv h₃)

/-- A finite union of members of a family of open sets closed under intersection, all with
finite-dimensional rational cohomology, has finite-dimensional rational cohomology. -/
private lemma fd_biUnion {Y : TopCat.{0}} (𝒢 : Set (Set Y)) (hopen : ∀ U ∈ 𝒢, IsOpen U)
    (hinter : ∀ U ∈ 𝒢, ∀ V ∈ 𝒢, U ∩ V ∈ 𝒢) (hfd : ∀ U ∈ 𝒢, FD (TopCat.of U)) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) :
    ∀ U : ι → Set Y, (∀ i ∈ s, U i ∈ 𝒢) → FD (TopCat.of (⋃ i ∈ s, U i : Set Y)) := by
  induction s using Finset.induction_on with
  | empty => exact fun U _ ↦ fd_of_isEmpty ⟨fun x ↦ by simpa using x.2⟩
  | insert a s ha ih =>
    intro U hU
    have hs : ∀ i ∈ s, U i ∈ 𝒢 := fun i hi ↦ hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    refine fd_congr (Finset.set_biUnion_insert a s U) ?_
    refine fd_union (hopen _ ha') (isOpen_biUnion fun i hi ↦ hopen _ (hs i hi)) (hfd _ ha')
      (ih U hs) ?_
    refine fd_congr (Set.inter_iUnion₂ _ _) ?_
    exact ih (fun i ↦ U a ∩ U i) fun i hi ↦ hinter _ ha' _ (hs i hi)

/-- A convex set has finite-dimensional rational cohomology: it is empty or contractible. -/
private lemma fd_of_convex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E}
    (hC : Convex ℝ C) : FD (TopCat.of C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact fd_of_isEmpty ⟨fun x ↦ x.2⟩
  · haveI := hC.contractibleSpace hne
    exact fd_of_contractibleSpace

/-- A finite union of open convex sets has finite-dimensional rational cohomology. -/
private lemma fd_sUnion_convex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝒞 : Set (Set E)} (hf : 𝒞.Finite) (ho : ∀ C ∈ 𝒞, IsOpen C) (hc : ∀ C ∈ 𝒞, Convex ℝ C) :
    FD (TopCat.of (⋃₀ 𝒞 : Set E)) := by
  classical
  have h := fd_biUnion (Y := TopCat.of E) {C | IsOpen C ∧ Convex ℝ C}
    (fun _ h ↦ h.1) (fun _ hU _ hV ↦ ⟨hU.1.inter hV.1, hU.2.inter hV.2⟩)
    (fun _ h ↦ fd_of_convex h.2) hf.toFinset id fun C hC ↦
      ⟨ho C (hf.mem_toFinset.1 hC), hc C (hf.mem_toFinset.1 hC)⟩
  refine fd_congr ?_ h
  ext y
  simp

/-- A finite disjoint union of spaces with finite-dimensional rational cohomology has
finite-dimensional rational cohomology. -/
private lemma fd_sigma {ι : Type} [Finite ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, FD (TopCat.of (X i))) : FD (TopCat.of (Σ i, X i)) := by
  classical
  haveI := Fintype.ofFinite ι
  refine fd_of_homotopyEquiv (Homeomorph.Set.univ (Σ i, X i)).symm.toHomotopyEquiv ?_
  have h' := fd_biUnion (Y := TopCat.of (Σ i, X i))
    ({U | ∃ i, U = Set.range (Sigma.mk i : X i → Σ i, X i)} ∪ {∅})
    (by
      rintro U (⟨i, rfl⟩ | rfl)
      · exact isOpen_range_sigmaMk
      · exact isOpen_empty)
    (by
      rintro U (⟨i, rfl⟩ | rfl) V (⟨j, rfl⟩ | rfl)
      · obtain rfl | hij := eq_or_ne i j
        · exact Or.inl ⟨i, Set.inter_self _⟩
        · refine Or.inr (Set.eq_empty_iff_forall_notMem.2 ?_)
          rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
          exact hij (congrArg Sigma.fst hb).symm
      · exact Or.inr (Set.inter_empty _)
      · exact Or.inr (Set.empty_inter _)
      · exact Or.inr (Set.empty_inter _))
    (by
      rintro U (⟨i, rfl⟩ | rfl)
      · exact fd_of_homotopyEquiv
          (Topology.IsEmbedding.sigmaMk.toHomeomorph
            (f := (Sigma.mk i : X i → Σ i, X i))).symm.toHomotopyEquiv (h i)
      · exact fd_of_isEmpty ⟨fun x ↦ x.2⟩)
    (Finset.univ : Finset ι) (fun i ↦ Set.range (Sigma.mk i)) fun i _ ↦ Or.inl ⟨i, rfl⟩
  refine fd_congr ?_ h'
  ext ⟨i, y⟩
  simp

/-- A compact set of positive reach in a Euclidean space has finite-dimensional rational
cohomology: it is homotopy equivalent to a finite union of balls. -/
private lemma fd_of_hasUniqueNearestPoints {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin N))}
    (hA : IsCompact A) {τ : ℝ} (hτ : 0 < τ) (hu : MMP.Topology.HasUniqueNearestPoints A τ) :
    FD (TopCat.of A) := by
  obtain ⟨π, hπc, hπA, hπn, hπF⟩ := hu.exists_nearestPoint hA.isClosed
  obtain ⟨s, hsf, -, ⟨e⟩⟩ :=
    MMP.Topology.exists_nonempty_homotopyEquiv_sUnion_ball_of_nearestPoint hA hτ π hπc hπA hπn hπF
  refine fd_of_homotopyEquiv e (fd_sUnion_convex (hsf.image _) ?_ ?_)
  · rintro _ ⟨x, -, rfl⟩
    exact Metric.isOpen_ball
  · rintro _ ⟨x, -, rfl⟩
    exact convex_ball _ _

open scoped Manifold ContDiff in
/-- The boundary of a finite disjoint union of compact smooth manifolds with corners has
finite-dimensional rational cohomology. -/
private lemma fd_boundary {ι : Type} [Finite ι] {n : ι → ℕ} {M : ι → Type}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (EuclideanQuadrant (n i)) (M i)]
    [∀ i, IsManifold (modelWithCornersEuclideanQuadrant (n i)) ∞ (M i)]
    [∀ i, CompactSpace (M i)] [∀ i, T2Space (M i)] :
    FD (TopCat.of
      {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}) := by
  set g : (Σ i, (modelWithCornersEuclideanQuadrant (n i)).boundary (M i)) → Σ i, M i :=
    Sigma.map id fun _ x ↦ x.1 with hg
  have hge : Topology.IsEmbedding g :=
    (Topology.isEmbedding_sigmaMap Function.injective_id).2 fun _ ↦ Topology.IsEmbedding.subtypeVal
  have hrange : Set.range g =
      {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} := by
    ext ⟨i, x⟩
    constructor
    · rintro ⟨⟨j, y⟩, hy⟩
      simp only [hg, Sigma.map, id] at hy
      obtain ⟨rfl, hy⟩ := Sigma.mk.inj_iff.1 hy
      obtain rfl := eq_of_heq hy
      exact y.2
    · exact fun hx ↦ ⟨⟨i, x, hx⟩, rfl⟩
  refine fd_of_homotopyEquiv
    (hge.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm.toHomotopyEquiv ?_
  refine fd_sigma fun i ↦ ?_
  obtain ⟨N, A, hA, ⟨τ, hτ, hu⟩, ⟨e⟩⟩ :=
    MMP.Topology.exists_isCompact_hasUniqueNearestPoints_homotopyEquiv_boundary (n := n i)
      (M := M i)
  exact fd_of_homotopyEquiv e (fd_of_hasUniqueNearestPoints hA hτ hu)

/-- A clopen subset of a space with finite-dimensional rational cohomology has
finite-dimensional rational cohomology: it is a retract. -/
private lemma fd_of_isClopen {Y : Type} [TopologicalSpace Y] {L : Set Y} (hL : IsClopen L)
    (h : FD (TopCat.of Y)) : FD (TopCat.of L) := by
  classical
  rcases L.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · exact fd_of_isEmpty ⟨fun x ↦ x.2⟩
  let r : C(Y, L) := ⟨fun y ↦ if hy : y ∈ L then ⟨y, hy⟩ else ⟨l₀, hl₀⟩, by
    refine continuous_def.2 fun V hV ↦ ?_
    have : (fun y ↦ if hy : y ∈ L then (⟨y, hy⟩ : L) else ⟨l₀, hl₀⟩) ⁻¹' V =
        (Subtype.val '' V) ∪ (if (⟨l₀, hl₀⟩ : L) ∈ V then Lᶜ else ∅) := by
      ext y
      by_cases hy : y ∈ L <;> by_cases h0 : (⟨l₀, hl₀⟩ : L) ∈ V <;> simp [hy, h0]
    rw [this]
    refine (hL.isOpen.isOpenMap_subtype_val V hV).union ?_
    split_ifs
    · exact hL.isClosed.isOpen_compl
    · exact isOpen_empty⟩
  have hr : TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(L, Y)) ≫ TopCat.ofHom r =
      𝟙 (TopCat.of L) := by
    ext ⟨y, hy⟩
    change ((if hy' : y ∈ L then (⟨y, hy'⟩ : L) else ⟨l₀, hl₀⟩ : L) : Y) = y
    rw [dif_pos hy]
  intro n
  haveI := h n
  have H : TopCat.Homotopy (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(L, Y)) ≫
      TopCat.ofHom r) (𝟙 (TopCat.of L)) := by
    rw [hr]
    exact ContinuousMap.Homotopy.refl _
  exact finiteDimensional_of_homotopy _ (TopCat.ofHom r) H n

/-- In a pushout square of topological spaces, a set is open as soon as its preimages under both
legs are. -/
private lemma isOpen_of_isPushout {A B C D : TopCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D}
    {inr : C ⟶ D} (h : IsPushout f g inl inr) (U : Set D)
    (h₁ : IsOpen (inl ⁻¹' U)) (h₂ : IsOpen (inr ⁻¹' U)) : IsOpen U := by
  refine (TopCat.isOpen_iff_of_isColimit _ h.isColimit U).2 ?_
  rintro (_ | _ | _)
  · exact h₁.preimage f.hom.continuous
  · exact h₁
  · exact h₂

end Finiteness

section Collar

variable {M X : Type} [TopologicalSpace M] [TopologicalSpace X] {B : Set M}
  {S : Set X} (φ : C(B, S)) (κ : C(M, X)) {c : B × Set.Ico (0 : ℝ) 1 → M}

/-- The points of `∂M` over `x`. -/
private abbrev fibre (x : X) : Set B := {b | (φ b : X) = x}

/-- The collar coordinates `L × (0, 1) → M` on the fibre `L` over `x`. -/
private def collarMap (c : B × Set.Ico (0 : ℝ) 1 → M) (x : X) :
    fibre φ x × Set.Ioo (0 : ℝ) 1 → M :=
  fun p ↦ c (p.1.1, Set.inclusion Set.Ioo_subset_Ico_self p.2)

private lemma collarMap_mem_compl (hc : Topology.IsOpenEmbedding c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y) (x : X)
    (p : fibre φ x × Set.Ioo (0 : ℝ) 1) : collarMap φ c x p ∈ (Bᶜ : Set M) := fun h ↦ by
  have := hc.injective ((hc0 ⟨collarMap φ c x p, h⟩ ⟨0, le_rfl, one_pos⟩ rfl).trans rfl :
    c (⟨collarMap φ c x p, h⟩, ⟨0, le_rfl, one_pos⟩) = collarMap φ c x p)
  exact p.2.2.1.ne' (congrArg (fun q : B × Set.Ico (0 : ℝ) 1 ↦ (q.2 : ℝ)) this).symm

private lemma apply_notMem_of_notMem
    (hrange : Set.range (fun p : (Bᶜ : Set M) ↦ κ p) = Sᶜ) {m : M} (hm : m ∉ B) : κ m ∉ S := by
  have : κ m ∈ Set.range (fun p : (Bᶜ : Set M) ↦ κ p) := ⟨⟨m, hm⟩, rfl⟩
  rwa [hrange] at this

private lemma fibre_eq_preimage (x : X) (hxS : x ∈ S) : fibre φ x = φ ⁻¹' {⟨x, hxS⟩} := by
  ext b
  simp [Subtype.ext_iff]

private lemma comp_collarMap_notMem (hrange : Set.range (fun p : (Bᶜ : Set M) ↦ κ p) = Sᶜ)
    (hc : Topology.IsOpenEmbedding c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y) (x : X)
    (p : fibre φ x × Set.Ioo (0 : ℝ) 1) : (κ ∘ collarMap φ c x) p ∉ S :=
  apply_notMem_of_notMem κ hrange (collarMap_mem_compl φ hc hc0 x p)

/-- The preimage in `M` of the cone `{x} ∪ κ(c(L × (0, ε)))` is the collar `c(L × [0, ε))`. -/
private lemma preimage_insert_collar_image (hcomm : ∀ b : B, κ b = (φ b : X))
    (hint : Topology.IsOpenEmbedding (fun p : (Bᶜ : Set M) ↦ κ p))
    (hrange : Set.range (fun p : (Bᶜ : Set M) ↦ κ p) = Sᶜ)
    (hc : Topology.IsOpenEmbedding c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y)
    (x : X) (hxS : x ∈ S) {ε : ℝ} (hε : 0 < ε) :
    κ ⁻¹' insert x ((κ ∘ collarMap φ c x) '' {p | (p.2 : ℝ) < ε}) =
      c '' (fibre φ x ×ˢ {t : Set.Ico (0 : ℝ) 1 | (t : ℝ) < ε}) := by
  have hS := comp_collarMap_notMem φ κ hrange hc hc0 x
  ext m
  constructor
  · rintro (hm | ⟨p, hp, hpm⟩)
    · by_cases hmB : m ∈ B
      · refine ⟨(⟨m, hmB⟩, ⟨0, le_rfl, one_pos⟩), ⟨?_, hε⟩, hc0 _ _ rfl⟩
        change (φ ⟨m, hmB⟩ : X) = x
        rw [← hcomm]
        exact hm
      · exact absurd (hm ▸ hxS) (apply_notMem_of_notMem κ hrange hmB)
    · have hmB : m ∉ B := fun hmB ↦ hS p (hpm ▸ hcomm ⟨m, hmB⟩ ▸ (φ _).2)
      have := hint.injective (a₁ := ⟨m, hmB⟩)
        (a₂ := ⟨_, collarMap_mem_compl φ hc hc0 x p⟩) hpm.symm
      exact ⟨(p.1.1, Set.inclusion Set.Ioo_subset_Ico_self p.2), ⟨p.1.2, hp⟩,
        (congrArg Subtype.val this).symm⟩
  · rintro ⟨⟨b, t⟩, ⟨hb, ht⟩, rfl⟩
    by_cases ht0 : (t : ℝ) = 0
    · left
      change κ (c (b, t)) = x
      rw [hc0 _ _ ht0, hcomm]
      exact hb
    · right
      exact ⟨(⟨b, hb⟩, ⟨t, lt_of_le_of_ne t.2.1 (Ne.symm ht0), t.2.2⟩), ht, rfl⟩

/-- The cones `{x} ∪ κ(c(L × (0, ε)))` are open in the pushout. -/
private lemma isOpen_insert_collar_image (hcomm : ∀ b : B, κ b = (φ b : X))
    (hopenU : ∀ U : Set X, IsOpen (κ ⁻¹' U) → IsOpen ((↑) ⁻¹' U : Set S) → IsOpen U)
    (hint : Topology.IsOpenEmbedding (fun p : (Bᶜ : Set M) ↦ κ p))
    (hrange : Set.range (fun p : (Bᶜ : Set M) ↦ κ p) = Sᶜ)
    (hc : Topology.IsOpenEmbedding c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y)
    (x : X) (hxS : x ∈ S) (hx : IsOpen ({⟨x, hxS⟩} : Set S)) {ε : ℝ} (hε : 0 < ε) :
    IsOpen (insert x ((κ ∘ collarMap φ c x) '' {p | (p.2 : ℝ) < ε})) := by
  have hS := comp_collarMap_notMem φ κ hrange hc hc0 x
  have hLopen : IsOpen (fibre φ x) := fibre_eq_preimage φ x hxS ▸ hx.preimage φ.continuous
  refine hopenU _ ?_ ?_
  · rw [preimage_insert_collar_image φ κ hcomm hint hrange hc hc0 x hxS hε]
    exact hc.isOpenMap _ (hLopen.prod (isOpen_lt continuous_subtype_val continuous_const))
  · convert hx using 1
    ext s
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
    constructor
    · rintro (h | ⟨p, -, hp⟩)
      · exact h
      · exact absurd (hp ▸ s.2) (hS p)
    · exact Or.inl

/-- The cones `κ(c(L × (0, ε)))` shrink to `x`, by the tube lemma for the compact fibre `L`. -/
private lemma exists_collar_image_subset [T1Space X] (hB : IsCompact B)
    (hcomm : ∀ b : B, κ b = (φ b : X)) (hc : Continuous c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y)
    (x : X) (hxS : x ∈ S) {V : Set X} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ ε ∈ Set.Ioc (0 : ℝ) 1, (κ ∘ collarMap φ c x) '' {p | (p.2 : ℝ) < ε} ⊆ V := by
  haveI : CompactSpace B := isCompact_iff_compactSpace.1 hB
  have hLclosed : IsClosed (fibre φ x) :=
    fibre_eq_preimage φ x hxS ▸ isClosed_singleton.preimage φ.continuous
  have hN : IsOpen (c ⁻¹' (κ ⁻¹' V)) := (hV.preimage κ.continuous).preimage hc
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma
    (s := fibre φ x) hLclosed.isCompact
    (t := {(⟨0, le_rfl, one_pos⟩ : Set.Ico (0 : ℝ) 1)}) isCompact_singleton hN
    (by
      rintro ⟨b, t⟩ ⟨hb, rfl⟩
      change κ (c (b, _)) ∈ V
      rw [hc0 _ _ rfl, hcomm]
      change (φ b : X) ∈ V
      rw [show (φ b : X) = x from hb]
      exact hxV)
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.1 hv _ (h0v rfl)
  refine ⟨min r 1, ⟨lt_min hr one_pos, min_le_right _ _⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  refine huv ⟨hKu p.1.2, hrv ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq]
  change dist (p.2 : ℝ) 0 < r
  rw [Real.dist_eq, sub_zero, abs_of_pos p.2.2.1]
  exact hp.trans_le (min_le_left _ _)

/-- **The conical neighbourhoods of an isolated point of `S` in a pushout `M ∪_{∂M} S`.** -/
private theorem conical_of_isPushout [T1Space X] (hB : IsCompact B)
    (hcomm : ∀ b : B, κ b = (φ b : X))
    (hopenU : ∀ U : Set X, IsOpen (κ ⁻¹' U) → IsOpen ((↑) ⁻¹' U : Set S) → IsOpen U)
    (hint : Topology.IsOpenEmbedding (fun p : (Bᶜ : Set M) ↦ κ p))
    (hrange : Set.range (fun p : (Bᶜ : Set M) ↦ κ p) = Sᶜ)
    (hc : Topology.IsOpenEmbedding c)
    (hc0 : ∀ y (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (y, t) = y)
    (x : X) (hxS : x ∈ S) (hx : IsOpen ({⟨x, hxS⟩} : Set S)) :
    IsClopen (fibre φ x) ∧ Topology.IsEmbedding (κ ∘ collarMap φ c x) ∧
      (∀ p, (κ ∘ collarMap φ c x) p ∉ S) ∧
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        IsOpen (insert x ((κ ∘ collarMap φ c x) '' {p | (p.2 : ℝ) < ε}))) ∧
      (∀ V : Set X, IsOpen V → x ∈ V →
        ∃ ε ∈ Set.Ioc (0 : ℝ) 1, (κ ∘ collarMap φ c x) '' {p | (p.2 : ℝ) < ε} ⊆ V) := by
  have hL := fibre_eq_preimage φ x hxS
  have hLopen : IsOpen (fibre φ x) := hL ▸ hx.preimage φ.continuous
  have hLclosed : IsClosed (fibre φ x) := hL ▸ isClosed_singleton.preimage φ.continuous
  have h1 : Topology.IsEmbedding (collarMap φ c x) :=
    hc.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.prodMap
      (Topology.IsEmbedding.inclusion Set.Ioo_subset_Ico_self))
  exact ⟨⟨hLclosed, hLopen⟩,
    hint.isEmbedding.comp (h1.codRestrict _ (collarMap_mem_compl φ hc hc0 x)),
    comp_collarMap_notMem φ κ hrange hc hc0 x,
    fun ε hε ↦ isOpen_insert_collar_image φ κ hcomm hopenU hint hrange hc hc0 x hxS hx hε.1,
    fun V hV hxV ↦ exists_collar_image_subset φ κ hB hcomm hc.continuous hc0 x hxS hV hxV⟩

end Collar

private lemma finiteDimensional_rationalCohomology {Z : TopCat.{0}} (h : FD Z) (q : ℕ) :
    FiniteDimensional ℚ (rationalCohomology Z q) := by
  haveI := h q
  exact LinearEquiv.finiteDimensional
    (MMP.SingularCochain.relativeSingularCohomologyEquiv ℚ _ q).symm

open scoped Manifold ContDiff in
private theorem exists_conical_link_of_isolated
    {P : Scheme.{0}} (sP : P ⟶ Spec (.of ℂ)) [IsReduced P] (hP : IsProjective sP)
    (S : Closeds P) (hSing : MMP.Mori.singularLocus sP ≤ S)
    (hcomp : ∀ Z ∈ irreducibleComponents P, ¬ Z ⊆ (S : Set P))
    (x : MMP.Analytic.ComplexPoints sP) (hxS : x.toScheme ∈ S)
    (hx : 𝓝[MMP.Analytic.ComplexPoints.toScheme ⁻¹' (S : Set P) \ {x}] x = ⊥) :
    ∃ (L : Type) (_ : TopologicalSpace L)
      (e : L × Set.Ioo (0 : ℝ) 1 → MMP.Analytic.ComplexPoints sP),
      IsEmbedding e ∧ (∀ p, MMP.Analytic.ComplexPoints.toScheme (e p) ∉ (S : Set P)) ∧
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1, IsOpen (insert x (e '' {p | (p.2 : ℝ) < ε}))) ∧
      (∀ V : Set (MMP.Analytic.ComplexPoints sP), IsOpen V → x ∈ V →
        ∃ ε ∈ Set.Ioc (0 : ℝ) 1, e '' {p | (p.2 : ℝ) < ε} ⊆ V) ∧
      ∀ q : ℕ, FiniteDimensional ℚ (rationalCohomology (TopCat.of L) q) := by
  haveI : IsSeparated sP := hP.isSeparated
  obtain ⟨ι, _, n, M, _, _, _, _, _, -, φ, κ, hpush, hint, hrange⟩ :=
    MMP.Analytic.exists_isPushout_manifoldWithCorners_boundary sP hP S hSing hcomp
  obtain ⟨-, -, c, hc, hc0⟩ := MMP.exists_collar_and_homotopyEquiv_finite_simplicialComplex
    (ι := ι) (n := n) (M := M)
  have hcomm : ∀ b, κ b.1 = (φ b).1 := fun b ↦ ConcreteCategory.congr_hom hpush.w b
  let B : Set (Σ i, M i) :=
    {p | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}
  let T : Set (MMP.Analytic.ComplexPoints sP) :=
    MMP.Analytic.ComplexPoints.toScheme ⁻¹' (S : Set P)
  have hB : IsCompact B := by
    refine IsClosed.isCompact (isClosed_sigma_iff.2 fun i ↦ ?_)
    exact ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanQuadrant (n i)) (M := M i) (n := ∞) (by simp)
  have hint' : IsOpenEmbedding (fun p : (Bᶜ : Set (Σ i, M i)) ↦ κ p) := hint
  have hrange' : Set.range (fun p : (Bᶜ : Set (Σ i, M i)) ↦ κ p) = Tᶜ := hrange
  have hopenU : ∀ U : Set (MMP.Analytic.ComplexPoints sP), IsOpen (κ ⁻¹' U) →
      IsOpen ((↑) ⁻¹' U : Set T) → IsOpen U := fun U ↦ isOpen_of_isPushout hpush U
  obtain ⟨hclopen, hemb, hS, hopen, hshrink⟩ := conical_of_isPushout φ κ hB hcomm hopenU hint'
    hrange' hc hc0 x hxS ((isOpen_singleton_iff_punctured_nhds (⟨x, hxS⟩ : T)).2 <|
      nhds_ne_subtype_eq_bot_iff.2 <| by
        rwa [nhdsWithin, inf_assoc, Filter.inf_principal, Set.inter_comm, ← Set.diff_eq])
  exact ⟨_, _, _, hemb, hS, hopen, hshrink,
    finiteDimensional_rationalCohomology (fd_of_isClopen hclopen fd_boundary)⟩

end MMP.Proof_lem_mmp_curvels_isolated_link_finite

@[expose] public section

namespace MMP.Fourfold

open MMP.Proof_lem_mmp_curvels_isolated_link_finite

/-- Let `P` be a reduced projective scheme over `ℂ`, `S ⊆ P` a closed subset containing the
singular locus and no irreducible component of `P`, and `x` an isolated point of `S^an`. Then
`x` has a cofinal set `𝒞` of open neighbourhoods `C` in `P^an` with `C ∩ S^an = {x}` such that
every `H^q(C ∖ {x}; ℚ)` is finite dimensional and every restriction map between them is an
isomorphism; and the stalk `colim_{V ∋ x} H^q(V ∖ {x}; ℚ)` is finite dimensional. -/
@[mmp "lem_mmp_curvels_isolated_link_finite"]
public theorem exists_cofinal_isIso_punctured_cohomology_of_isolated
    {P : Scheme.{0}} (sP : P ⟶ Spec (.of ℂ)) [IsReduced P] (hP : IsProjective sP)
    (S : Closeds P) (hSing : MMP.Mori.singularLocus sP ≤ S)
    (hcomp : ∀ Z ∈ irreducibleComponents P, ¬ Z ⊆ (S : Set P))
    (x : MMP.Analytic.ComplexPoints sP) (hxS : x.toScheme ∈ S)
    (hx : 𝓝[MMP.Analytic.ComplexPoints.toScheme ⁻¹' (S : Set P) \ {x}] x = ⊥) :
    let j : TopCat.of ({x}ᶜ : Set (MMP.Analytic.ComplexPoints sP)) ⟶
        MMP.Analytic.Analytification.space sP :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    ∃ 𝒞 : Set (Opens (MMP.Analytic.Analytification.space sP)),
      (∀ C ∈ 𝒞, x ∈ C ∧
        (C : Set (MMP.Analytic.ComplexPoints sP)) ∩
          MMP.Analytic.ComplexPoints.toScheme ⁻¹' (S : Set P) = {x} ∧
        ∀ q : ℕ, FiniteDimensional ℚ ((directImagePresheaf j q).obj (op C))) ∧
      (∀ V : Opens (MMP.Analytic.Analytification.space sP), x ∈ V → ∃ C ∈ 𝒞, C ≤ V) ∧
      (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∀ h : C' ≤ C, ∀ q : ℕ,
        IsIso ((directImagePresheaf j q).map (homOfLE h).op)) ∧
      ∀ q : ℕ, FiniteDimensional ℚ ((directImagePresheaf j q).stalk x) := by
  intro j
  obtain ⟨L, _, e, he, hT, hopen, hshrink, hfd⟩ :=
    exists_conical_link_of_isolated sP hP S hSing hcomp x hxS hx
  obtain ⟨𝒞, hmem, hcof, hiso⟩ :=
    cofinal_system_of_conical (X := MMP.Analytic.Analytification.space sP) he x
      (MMP.Analytic.ComplexPoints.toScheme ⁻¹' (S : Set P)) hxS hT hopen hshrink hfd
  exact ⟨𝒞, hmem, hcof, hiso, fun q ↦ stalk_finiteDimensional_of_cofinal_isIso _ x 𝒞
    (fun C hC ↦ ⟨(hmem C hC).1, (hmem C hC).2.2 q⟩) hcof fun C hC C' hC' h ↦ hiso C hC C' hC' h q⟩

end MMP.Fourfold
