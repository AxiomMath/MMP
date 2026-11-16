module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.Analysis.Complex.Submanifold
import MMP.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocal
import MMP.Algebra.Category.ModuleCat.Sheaf.FreeSections
import MMP.Analysis.Complex.Coherent.CoherentTransport
import MMP.Topology.Sheaves.ExtRightDerived
import MMP.Topology.Sheaves.GodementOpenEmbedding
import MMP.Topology.Algebra.RangeUniformity
import MMP.Topology.Algebra.MittagLeffler
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.Analysis.Complex.Coherent.CartanMatrixSplitting
import MMP.Analysis.Complex.HolomorphicCompactConvergence
import MMP.Analysis.Complex.HolomorphicRunge
import MMP.Analysis.Complex.Coherent.CartanBlocksGluing
import MMP.Analysis.Complex.Coherent.OkaInduction
import MMP.Topology.Sheaves.GodementFlasqueResolution
import MMP.Analysis.Complex.Coherent.Basic
import MMP.AlgebraicGeometry.Analytic.GAGA.DolbeaultVanishing

/-!
# Oka's coherence theorem and Cartan's theorems on blocks and boxes

A *block* in `ℂⁿ` is a product `K₁ × ⋯ × Kₙ` of closed rectangles `[aᵢ, bᵢ] × [cᵢ, dᵢ]` in `ℂ`
with sides parallel to the axes, possibly degenerate to segments or points; a *box* is a product
of open rectangles `(aᵢ, bᵢ) × (cᵢ, dᵢ)`.

**Oka's coherence theorem.** The sheaf `𝒪_M` of holomorphic functions on a complex manifold `M`
is a coherent sheaf of rings. Consequently, for a scheme `X` locally of finite type over `ℂ`, the
structure sheaf of the analytification `X^an` is coherent, and `F^an` is a coherent
`𝒪_{X^an}`-module for every coherent `𝒪_X`-module `F`.

**Cartan's theorems on compact blocks.** Let `𝒮` be a coherent module over the holomorphic
functions on an open set `U ⊆ ℂⁿ` containing a block `K`. Then `𝒮` has a finite free resolution
on some open neighbourhood of `K`, obtained by subdividing `K` into a grid of small blocks and
gluing local resolutions along Cartan's matrix splitting; hence there is a surjection
`𝒪_Wᵖ → 𝒮|_W` on a neighbourhood `W` of `K`. Dimension shifting along the resolution and
Dolbeault vanishing on boxes show that every class in `H^q(W', 𝒮)`, `q ≥ 1`, `W' ⊇ K`, restricts
to zero on some box containing `K`.

**Cartan's Theorem B on boxes.** Let `D ⊆ ℂⁿ` be a bounded box and `Z ⊆ D` a closed complex
submanifold. Then `H^q(Z, 𝒮) = 0` for every coherent `𝒪_Z`-module `𝒮` and `q ≥ 1`. Pushing
forward along `Z ⟶ D` reduces this to `Z = D`. The box is exhausted by the boxes `U_j` obtained
by moving every side inwards by `1/(j+1)`, whose closures `K_j` are blocks with
`K_j ⊆ U_{j+1}`. By the theorem on compact blocks, higher classes on `U_{j+1}` die near `K_j`,
and `lim¹_j 𝒮(U_j) = 0` by the Mittag-Leffler lemma for the images `Q_j ⊆ 𝒮(U_j)` of `𝒪(U_j)ᵖ`
under the generators of presentations near the blocks, with the quotient of the topology of
compact convergence: the relations are closed, and the transition maps have dense image by
Runge's theorem. The Milnor sequence of the Godement complexes then gives the vanishing.

## Main results

* `MMP.Analytic.isCoherentRing_holomorphic_and_analytification`: Oka's coherence theorem and its
  consequences for analytifications.
* `MMP.Analytic.cartan_compact_blocks`: finite free resolutions, surjections from free modules
  and vanishing of higher cohomology near a block.
* `MMP.Analytic.cartan_theoremB_box`: `H^q(Z, 𝒮) = 0` for `q ≥ 1` on a closed submanifold of a
  box.

## Implementation notes

* `ℂⁿ` is `EuclideanSpace ℂ (Fin n)`, and an open subset of it is a complex manifold through its
  induced charts; `𝒪_U` is `MMP.Analytic.holomorphicRingCatSheaf n U` and coherence is
  `MMP.Analytic.IsCoherentModule`. Subsets of `ℂⁿ` are compared with opens of `U` through
  `Subtype.val`.
* Oka's theorem is stated for an arbitrary complex manifold `M` modelled on `ℂⁿ`, coherence being
  a local property; `M = ℂⁿ` is the model space with its trivial atlas. The finiteness hypothesis
  on `X` is that the structure morphism is locally of finite type.
* A closed rectangle is `Set.Icc a b ×ℂ Set.Icc c d` (`Set.reProdIm`), an open one
  `Set.Ioo a b ×ℂ Set.Ioo c d`. No `aᵢ ≤ bᵢ` is imposed: an empty block or box makes the
  statements trivial.
* The restriction of `𝒮` to an open `W` is `SheafOfModules.over`. A finite free resolution on `W`
  is a bounded chain complex of finite free `𝒪_W`-modules, exact in positive degrees, with an
  augmentation onto `𝒮|_W` making it exact in degree `0`.
* `H^q(W', 𝒮)` is `MMP.Analytic.sheafCohomology` of the inverse image of the underlying abelian
  sheaf of `𝒮` along the inclusion of `W'`; the restriction of a class to `P ⊆ W'` is
  `MMP.Analytic.sheafCohomologyPullback` along the inclusion `P ⟶ W'`.
* A closed complex submanifold is `MMP.Analytic.IsClosedComplexSubmanifold`, and `𝒪_Z` is
  `MMP.Analytic.submanifoldStructureSheaf`, viewed as a sheaf of rings.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Grauert–Remmert, *Coherent analytic sheaves*]
* [Grauert–Remmert, *Theory of Stein spaces*, Chapter IV]
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace MMP.Analytic

/-! ## Cartan's theorems on compact blocks -/

section CompactBlocks

open CartanCompactBlocks

attribute [local instance] globalSections_additive in
/-- **Dolbeault vanishing, read on `P`.** If the image of `P ⊆ U` in `ℂⁿ` is a product of
open rectangles, the holomorphic functions on `P` have no higher `Ext`-cohomology. -/
private lemma subsingleton_ext_Ψ_unit {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}
    {P W : Opens (TopCat.of U)} (h : P ≤ W) {a' b' c' d' : Fin n → ℝ}
    (hP : Subtype.val '' (P : Set U) =
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)})
    [HasExt (Sheaf (Opens.grothendieckTopology P) AddCommGrpCat.{0})] (q : ℕ) :
    Subsingleton (Abelian.Ext (freeYonedaTop (TopCat.of P))
      ((Ψ (R := holomorphicRingCatSheaf n U) h).obj (SheafOfModules.unit _)) (q + 1)) := by
  let D : Opens (EuclideanSpace ℂ (Fin n)) :=
    ⟨Subtype.val '' (P : Set U), U.isOpenEmbedding'.isOpenMap _ P.isOpen⟩
  have hD : (D : Set (EuclideanSpace ℂ (Fin n))) = Subtype.val '' (P : Set U) := rfl
  have hz := (isZero_sheafCohomology_holomorphic_of_isProductDomain n).1 D
    (fun j => Set.Ioo (a' j) (b' j) ×ℂ Set.Ioo (c' j) (d' j))
    (fun j => Or.inl ⟨a' j, b' j, c' j, d' j, rfl⟩) (by rw [hD, hP]) ((q + 1 : ℕ) : ℤ)
    (by positivity)
  have := isIso_sheafCohomologyPullback (homP U P D hD) (isOpenEmbedding_homP U P D hD)
    (fun y => by
      obtain ⟨⟨x, hx⟩, hxP, hxy⟩ := (show y.1 ∈ Subtype.val '' (P : Set U) from y.2)
      exact ⟨⟨⟨x, hx⟩, hxP⟩, Subtype.ext hxy⟩)
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (X := TopCat.of (EuclideanSpace ℂ (Fin n))) D)).obj
        ((SheafOfModules.toSheaf _).obj
          (SheafOfModules.unit (holomorphicRingCatSheaf n (EuclideanSpace ℂ (Fin n))))))
    ((q + 1 : ℕ) : ℤ)
  have hz2 := hz.of_iso (asIso (sheafCohomologyPullback (homP U P D hD) _ _)).symm
  have hz3 := hz2.of_iso ((sheafCohomology (TopCat.of P) _).mapIso
    (dolbeaultSheafIso U P D hD)).symm
  have hz4 := hz3.of_iso ((sheafCohomologyIso (TopCat.of P) (q + 1)).app _).symm
  refine subsingleton_ext_of_iso ?_ (subsingleton_H'_of_isZero_rightDerived _ q hz4)
  exact ((Opens.sheafEquivOver P).functor ⋙ (𝟭 _)).mapIso
    ((SheafOfModules.toSheaf _).mapIso (SheafOfModules.overMapUnitIso (homOfLE h)).symm)

section GlueResolutions

variable {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}

/-- Near an open product of open rectangles `P ≤ W`, every section of `N` lifts along an
epimorphism `ofTop s : 𝒪ᵖ ⟶ N` whose kernel has a finite free resolution. -/
private lemma exists_lift_near_box {P W : Opens (TopCat.of U)} (hPW : P ≤ W)
    {a' b' c' d' : Fin n → ℝ}
    (hP : Subtype.val '' (P : Set U) =
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)})
    {N : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over W)} {p ℓ : ℕ}
    (s : Fin p → Γ N) [Epi (ofTop s)] (hk : HasFFR (kernel (ofTop s)) ℓ)
    (m : Γ ((res _ ((boxTop_le P).trans hPW)).obj N)) :
    ∃ y : (SheafOfModules.free (R := (holomorphicRingCatSheaf n U).over W) (Fin p)).val.obj
        (op ((Over.map (homOfLE hPW)).obj ((Opens.overEquivalence P).inverse.obj ⊤))),
      (ofTop s).val.app
        (op ((Over.map (homOfLE hPW)).obj ((Opens.overEquivalence P).inverse.obj ⊤))) y = m := by
  have := preservesFiniteLimits_Ψ (R := holomorphicRingCatSheaf n U) hPW
  have := preservesFiniteColimits_Ψ (R := holomorphicRingCatSheaf n U) hPW
  have := additive_Ψ (R := holomorphicRingCatSheaf n U) hPW
  obtain ⟨K, ε, hfree, hzero, hexact, hε, h0, hex⟩ := hk
  have hk1 := (subsingleton_ext_map_of_resolution (Ψ (R := holomorphicRingCatSheaf n U) hPW)
    (freeYonedaTop (TopCat.of P)) (fun q hq => by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact subsingleton_ext_Ψ_unit hPW hP q')
    K ε hfree hzero hexact hε h0 hex).2 1 le_rfl
  exact exists_lift_of_subsingleton_ext (X' := TopCat.of P)
    (Ψ (R := holomorphicRingCatSheaf n U) hPW) (ofTop s) hk1
    m

/-- **Lifting near a block.** Let `φ = ofTop s : 𝒪ᵖ ⟶ N` be an epimorphism on `W` whose kernel
has a finite free resolution, and `P ≤ W` an open product of open rectangles. Every section of
`N` over `P` is a holomorphic combination of the `s j`. -/
private lemma exists_combination {P W : Opens (TopCat.of U)} (hPW : P ≤ W)
    {a' b' c' d' : Fin n → ℝ}
    (hP : Subtype.val '' (P : Set U) =
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)})
    {N : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over W)} {p ℓ : ℕ}
    (s : Fin p → Γ N) [Epi (ofTop s)] (hk : HasFFR (kernel (ofTop s)) ℓ)
    (m : Γ ((res _ ((boxTop_le P).trans hPW)).obj N)) :
    ∃ c : Fin p → ((holomorphicRingCatSheaf n U).over (boxTop P)).obj.obj
        (op (topOver (boxTop P))),
      m = ∑ j, c j • rΓ ((boxTop_le P).trans hPW) N (s j) := by
  refine Exists.elim (exists_lift_near_box hPW hP s hk m) fun y hy => ?_
  let X : (Over W)ᵒᵖ := op ((Over.map (homOfLE hPW)).obj ((Opens.overEquivalence P).inverse.obj ⊤))
  refine Exists.elim (MMP.exists_eq_sum_smul_freeSection
    (R := (holomorphicRingCatSheaf n U).over W) X y) fun c hc => ⟨c, ?_⟩
  have e1 : ∀ j, (ofTop s).val.app X
      ((SheafOfModules.freeSection (R := (holomorphicRingCatSheaf n U).over W) j).1 X) =
      rΓ ((boxTop_le P).trans hPW) N (s j) := fun j =>
    congrArg (fun t : N.sections => t.1 X)
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := N)
        (fun i => secOfTop N (s i)) j)
  refine hy.symm.trans ((congrArg ((ofTop s).val.app X).hom hc).trans ?_)
  refine (map_sum ((ofTop s).val.app X).hom _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact (map_smul ((ofTop s).val.app X).hom _ _).trans (congrArg (c j • ·) (e1 j))

/-- **Lifting, in matrix form.** Near a block, the sections `s₂` are holomorphic combinations of
the generators `s₁` of an epimorphism with a resolved kernel. -/
private lemma exists_lift_matrix {V W₁ W₂ P : Opens (TopCat.of U)} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V)
    (hP₁ : P ≤ W₁) (hP₂ : P ≤ W₂) (hBV : boxTop P ≤ V) {a' b' c' d' : Fin n → ℝ}
    (hP : Subtype.val '' (P : Set U) =
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)})
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)) {p₁ p₂ ℓ : ℕ}
    (s₁ : Fin p₁ → Γ ((res _ h₁).obj M)) [Epi (ofTop s₁)] (hk : HasFFR (kernel (ofTop s₁)) ℓ)
    (s₂ : Fin p₂ → Γ ((res _ h₂).obj M)) :
    ∃ A : Matrix (Fin p₂) (Fin p₁)
        (((holomorphicRingCatSheaf n U).over (boxTop P)).obj.obj (op (topOver (boxTop P)))),
      ∀ k, resΓ hBV h₂ ((boxTop_le P).trans hP₂) M (s₂ k) =
        ∑ j, A k j • resΓ hBV h₁ ((boxTop_le P).trans hP₁) M (s₁ j) := by
  have key : ∀ k, ∃ c : Fin p₁ → ((holomorphicRingCatSheaf n U).over (boxTop P)).obj.obj
      (op (topOver (boxTop P))), resΓ hBV h₂ ((boxTop_le P).trans hP₂) M (s₂ k) =
        ∑ j, c j • resΓ hBV h₁ ((boxTop_le P).trans hP₁) M (s₁ j) := by
    intro k
    obtain ⟨c, hc⟩ := exists_combination hP₁ hP s₁ hk
      ((resResIso ((boxTop_le P).trans hP₁) h₁ hBV M).inv.val.app _
        (resΓ hBV h₂ ((boxTop_le P).trans hP₂) M (s₂ k)))
    refine ⟨c, ?_⟩
    have := congrArg ((resResIso ((boxTop_le P).trans hP₁) h₁ hBV M).hom.val.app _) hc
    rw [map_sum] at this
    refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
    exact map_smul _ _ _
  choose c hc using key
  exact ⟨Matrix.of c, hc⟩

/-- If finite free resolutions of length `ℓ` near `K₁` and near `K₂` glue, then so do those of
length `ℓ + 1`. -/
private lemma glue_step {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hsplit : SplitProp K₁ K₂) (hKU : K₁ ∪ K₂ ⊆ U) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    {a b c d : Fin n → ℝ} (hL : K₁ ∩ K₂ = block a b c d) {ℓ : ℕ}
    (IH : ∀ (V' : Opens (TopCat.of U))
      (Q : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V')),
      (∃ (W₁ : Opens (TopCat.of U)) (h : W₁ ≤ V'), (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁ ∧
        HasFFR ((res _ h).obj Q) ℓ) →
      (∃ (W₂ : Opens (TopCat.of U)) (h : W₂ ≤ V'), (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂ ∧
        HasFFR ((res _ h).obj Q) ℓ) →
      ∃ (W : Opens (TopCat.of U)) (h : W ≤ V'), (Subtype.val : U → _) ⁻¹' (K₁ ∪ K₂) ⊆ W ∧
        ∃ ℓ', HasFFR ((res _ h).obj Q) ℓ')
    {V W₁ W₂ : Opens (TopCat.of U)} (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V)
    (hK₁ : (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁) (hK₂ : (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂)
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V))
    (hM₁ : HasFFR ((res _ h₁).obj M) (ℓ + 1)) (hM₂ : HasFFR ((res _ h₂).obj M) (ℓ + 1)) :
    ∃ (W : Opens (TopCat.of U)) (h : W ≤ V), (Subtype.val : U → _) ⁻¹' (K₁ ∪ K₂) ⊆ W ∧
      ∃ ℓ', HasFFR ((res _ h).obj M) ℓ' := by
  obtain ⟨C₁, ε₁, hfree₁, hzero₁, hexact₁, hε₁, h0₁, hex₁⟩ := hM₁
  obtain ⟨C₂, ε₂, hfree₂, hzero₂, hexact₂, hε₂, h0₂, hex₂⟩ := hM₂
  have hk₁ := hasFFR_kernel C₁ ε₁ hfree₁ hzero₁ hexact₁ hε₁ h0₁ hex₁
  have hk₂ := hasFFR_kernel C₂ ε₂ hfree₂ hzero₂ hexact₂ hε₂ h0₂ hex₂
  obtain ⟨p₁, ⟨e₁⟩⟩ := hfree₁ 0
  obtain ⟨p₂, ⟨e₂⟩⟩ := hfree₂ 0
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : Fin p₁ → Γ ((res _ h₁).obj M), e₁.inv ≫ ε₁ = ofTop s₁ :=
    ⟨_, eq_ofTop _⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : Fin p₂ → Γ ((res _ h₂).obj M), e₂.inv ≫ ε₂ = ofTop s₂ :=
    ⟨_, eq_ofTop _⟩
  have he₁ : Epi (ofTop s₁) := by rw [← hs₁]; exact epi_comp _ _
  have he₂ : Epi (ofTop s₂) := by rw [← hs₂]; exact epi_comp _ _
  have hk₁' : HasFFR (kernel (ofTop s₁)) ℓ :=
    (hk₁.of_iso (kernelIsIsoComp e₁.inv ε₁).symm).of_iso (kernelIsoOfEq hs₁)
  have hk₂' : HasFFR (kernel (ofTop s₂)) ℓ :=
    (hk₂.of_iso (kernelIsIsoComp e₂.inv ε₂).symm).of_iso (kernelIsoOfEq hs₂)
  have hLU : block a b c d ⊆ U := hL ▸ fun z hz => hKU (Or.inl hz.1)
  obtain ⟨P, hPO, ⟨a', b', c', d', hPbox⟩, hLP⟩ := exists_box_between U a b c d hLU (W₁ ⊓ W₂)
    (fun x hx => by
      rw [← hL] at hx
      exact ⟨hK₁ hx.1, hK₂ hx.2⟩)
  have hP₁ : P ≤ W₁ := hPO.trans inf_le_left
  have hP₂ : P ≤ W₂ := hPO.trans inf_le_right
  have hB₁ : boxTop P ≤ W₁ := (boxTop_le P).trans hP₁
  have hB₂ : boxTop P ≤ W₂ := (boxTop_le P).trans hP₂
  have hBV : boxTop P ≤ V := hB₁.trans h₁
  have hLB : (Subtype.val : U → _) ⁻¹' (K₁ ∩ K₂) ⊆ (boxTop P : Opens (TopCat.of U)) := by
    intro x hx
    rw [hL] at hx
    exact le_boxTop P (hLP hx)
  obtain ⟨A, hA⟩ := exists_lift_matrix h₁ h₂ hP₁ hP₂ hBV hPbox M s₁ hk₁' s₂
  obtain ⟨B, hB⟩ := exists_lift_matrix h₂ h₁ hP₂ hP₁ hBV hPbox M s₂ hk₂' s₁
  let σ₁ : Fin p₁ ⊕ Fin p₂ → Γ ((res _ h₁).obj M) :=
    Sum.elim s₁ (0 : Fin p₂ → Γ ((res _ h₁).obj M))
  let σ₂ : Fin p₁ ⊕ Fin p₂ → Γ ((res _ h₂).obj M) :=
    Sum.elim (0 : Fin p₁ → Γ ((res _ h₂).obj M)) s₂
  have hσ₁ : ∀ y, resΓ hBV h₁ hB₁ M (σ₁ y) =
      Sum.elim (fun j => resΓ hBV h₁ hB₁ M (s₁ j)) (0 : Fin p₂ → Γ ((res _ hBV).obj M)) y := by
    rintro (j | k)
    · rfl
    · exact resΓ_zero _ _ _ M
  have hσ₂ : ∀ y, resΓ hBV h₂ hB₂ M (σ₂ y) =
      Sum.elim (0 : Fin p₁ → Γ ((res _ hBV).obj M)) (fun k => resΓ hBV h₂ hB₂ M (s₂ k)) y := by
    rintro (j | k)
    · exact resΓ_zero _ _ _ M
    · rfl
  have hrel : ∀ x, resΓ hBV h₂ hB₂ M (σ₂ x) =
      ∑ y, Matrix.fromBlocks (1 - B * A) (-B) A 1 x y • resΓ hBV h₁ hB₁ M (σ₁ y) := by
    intro x
    rw [hσ₂]
    refine (fromBlocks_relation (fun j => resΓ hBV h₁ hB₁ M (s₁ j))
      (fun k => resΓ hBV h₂ hB₂ M (s₂ k)) A B hA hB x).trans ?_
    exact Finset.sum_congr rfl fun y _ => congrArg _ (hσ₁ y).symm
  obtain ⟨T₁, T₂, hT₁, hT₂, U₁, U₁', U₂, U₂', hK₁T, hK₂T, f1, f2, f3, f4, τ, hτ₁, hτ₂⟩ :=
    exists_glue_tuple hsplit hKU hc₁ hc₂ h₁ h₂ hB₁ hB₂ hK₁ hK₂ hLB M σ₁ σ₂ _ _
      (fromBlocks_mul_inv A B) (fromBlocks_inv_mul A B) hBV hrel
  have hT : T₁ ⊔ T₂ ≤ V := sup_le (hT₁.trans h₁) (hT₂.trans h₂)
  obtain ⟨hepi₁, hker₁⟩ := step_local₁ hT h₁ (hT₁.trans h₁) le_sup_left hT₁ M τ s₁ U₁ U₁' f1 f2
    hτ₁ hk₁'
  obtain ⟨hepi₂, hker₂⟩ := step_local₂ hT h₂ (hT₂.trans h₂) le_sup_right hT₂ M τ s₂ U₂ U₂' f3 f4
    hτ₂ hk₂'
  have hepi : Epi (ofTop τ) := epi_of_epi_res le_sup_left le_sup_right le_rfl _ hepi₁ hepi₂
  have := preservesFiniteLimits_res (holomorphicRingCatSheaf n U) (le_sup_left : T₁ ≤ T₁ ⊔ T₂)
  have := preservesFiniteLimits_res (holomorphicRingCatSheaf n U) (le_sup_right : T₂ ≤ T₁ ⊔ T₂)
  obtain ⟨W, hWT, hKW, ℓ', hQW⟩ := IH (T₁ ⊔ T₂) (kernel (ofTop τ))
    ⟨T₁, le_sup_left, hK₁T, hker₁.of_iso (PreservesKernel.iso _ _).symm⟩
    ⟨T₂, le_sup_right, hK₂T, hker₂.of_iso (PreservesKernel.iso _ _).symm⟩
  have := preservesFiniteLimits_res (holomorphicRingCatSheaf n U) hWT
  have := (SheafOfModules.overMapPushforwardAdj (holomorphicRingCatSheaf n U)
    (homOfLE hWT)).isLeftAdjoint
  have hφ : Epi ((res _ hWT).map (ofTop τ)) := Functor.map_epi _ _
  have hfin := hasFFR_of_epi ((freeRes hWT (Fin p₁ ⊕ Fin p₂)).symm ≪≫
    freeCongrIso finSumFinEquiv) ((res _ hWT).map (ofTop τ))
    (hQW.of_iso (PreservesKernel.iso _ _))
  exact ⟨W, hWT.trans hT, hKW, ℓ' + 1, hfin.of_iso (resResIso hWT hT (hWT.trans hT) M)⟩

/-- **Gluing finite free resolutions along a cut** (induction on the length). -/
private theorem glue_resolutions {K₁ K₂ : Set (EuclideanSpace ℂ (Fin n))}
    (hsplit : SplitProp K₁ K₂) (hKU : K₁ ∪ K₂ ⊆ U) (hc₁ : IsCompact K₁) (hc₂ : IsCompact K₂)
    {a b c d : Fin n → ℝ} (hL : K₁ ∩ K₂ = block a b c d) (hLne : (K₁ ∩ K₂).Nonempty) :
    ∀ (ℓ : ℕ) (V : Opens (TopCat.of U))
      (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over V)),
      (∃ (W₁ : Opens (TopCat.of U)) (h : W₁ ≤ V), (Subtype.val : U → _) ⁻¹' K₁ ⊆ W₁ ∧
        HasFFR ((res _ h).obj M) ℓ) →
      (∃ (W₂ : Opens (TopCat.of U)) (h : W₂ ≤ V), (Subtype.val : U → _) ⁻¹' K₂ ⊆ W₂ ∧
        HasFFR ((res _ h).obj M) ℓ) →
      ∃ (W : Opens (TopCat.of U)) (h : W ≤ V), (Subtype.val : U → _) ⁻¹' (K₁ ∪ K₂) ⊆ W ∧
        ∃ ℓ', HasFFR ((res _ h).obj M) ℓ' := by
  intro ℓ
  induction ℓ with
  | zero =>
    rintro V M ⟨W₁, h₁, hK₁, hM₁⟩ ⟨W₂, h₂, hK₂, hM₂⟩
    obtain ⟨C₁, ε₁, hfree₁, hzero₁, -, hε₁, h0₁, hex₁⟩ := hM₁
    obtain ⟨C₂, ε₂, hfree₂, hzero₂, -, hε₂, h0₂, hex₂⟩ := hM₂
    have := isIso_of_hasFFR_zero C₁ ε₁ hzero₁ hε₁ h0₁ hex₁
    have := isIso_of_hasFFR_zero C₂ ε₂ hzero₂ hε₂ h0₂ hex₂
    obtain ⟨r₁, ⟨e₁⟩⟩ := hfree₁ 0
    obtain ⟨r₂, ⟨e₂⟩⟩ := hfree₂ 0
    obtain ⟨W, h, hKW, hW⟩ := glue_base hsplit hKU hc₁ hc₂ hLne h₁ h₂ hK₁ hK₂ M
      (e₁.symm ≪≫ asIso ε₁) (e₂.symm ≪≫ asIso ε₂)
    exact ⟨W, h, hKW, 0, hW⟩
  | succ ℓ ih =>
    rintro V M ⟨W₁, h₁, hK₁, hM₁⟩ ⟨W₂, h₂, hK₂, hM₂⟩
    exact glue_step hsplit hKU hc₁ hc₂ hL ih h₁ h₂ hK₁ hK₂ M hM₁ hM₂

end GlueResolutions

/-- A block whose corner is `z₀` and whose sides have length `≤ δ / (3 (n + 1))` lies in the ball
of radius `δ` around `z₀`. -/
private lemma mem_ball_of_mem_block {n : ℕ} {a' b' c' d' : Fin n → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ i, b' i - a' i ≤ δ / (3 * (n + 1))) (hd : ∀ i, d' i - c' i ≤ δ / (3 * (n + 1)))
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ block a' b' c' d') :
    y ∈ Metric.ball ((EuclideanSpace.equiv (Fin n) ℂ).symm fun i => ⟨a' i, c' i⟩) δ := by
  set z₀ : EuclideanSpace ℂ (Fin n) := (EuclideanSpace.equiv (Fin n) ℂ).symm fun i => ⟨a' i, c' i⟩
  have hη : 0 < δ / (3 * (n + 1)) := by positivity
  rw [Metric.mem_ball, dist_eq_norm]
  have hcoord : ∀ i, ‖(y - z₀) i‖ < 3 * (δ / (3 * (n + 1))) := by
    intro i
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hy i
    have hre : |((y - z₀) i).re| ≤ δ / (3 * (n + 1)) := by
      change |(y i).re - a' i| ≤ _
      rw [abs_le]
      constructor <;> linarith [hb i]
    have him : |((y - z₀) i).im| ≤ δ / (3 * (n + 1)) := by
      change |(y i).im - c' i| ≤ _
      rw [abs_le]
      constructor <;> linarith [hd i]
    calc _ ≤ |((y - z₀) i).re| + |((y - z₀) i).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 * (δ / (3 * (n + 1))) := by linarith
      _ < 3 * (δ / (3 * (n + 1))) := by linarith
  calc _ < (n + 1) * (3 * (δ / (3 * (n + 1)))) := norm_lt_of_forall_norm_lt (by positivity) hcoord
    _ = δ := by field_simp

/-- A block with an empty side carries a finite free resolution of `S` near it, on `⊥`. -/
private lemma exists_hasFFR_of_block_empty {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}
    {a b c d : Fin n → ℝ} (hne : ¬ ∀ i, a i ≤ b i ∧ c i ≤ d i)
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) :
    ∃ W : Opens (TopCat.of U), (Subtype.val : U → _) ⁻¹' block a b c d ⊆ W ∧
      ∃ ℓ, HasFFR (S.over W) ℓ := by
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hempty : block a b c d = ∅ := by
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hz
    obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hz i
    by_cases h : a i ≤ b i
    · exact absurd (e3.trans e4) (hi h).not_ge
    · exact h (e1.trans e2)
  have hz : IsZero (S.over (⊥ : Opens (TopCat.of U))) := isZero_of_forall_subsingleton _ fun A =>
    ⟨fun s t => over_ext ((SheafOfModules.toSheaf _).obj (S.over ⊥)) A (Y := Empty.elim)
      (fun e => e.elim) (fun x hx => (A.hom.le hx : x ∈ (⊥ : Opens (TopCat.of U))).elim) s t
      (fun e => e.elim)⟩
  have hK : (Subtype.val : U → _) ⁻¹' block a b c d ⊆ (⊥ : Opens (TopCat.of U)) := by
    rw [hempty]
    exact fun x hx => hx.elim
  have hiso : SheafOfModules.free (R := (holomorphicRingCatSheaf n U).over ⊥) (Fin 0) ≅
      S.over (⊥ : Opens (TopCat.of U)) :=
    (isZero_free_fin_zero (R := (holomorphicRingCatSheaf n U).over ⊥)).iso hz
  exact ⟨⊥, hK, 0, hasFFR_zero_of_iso hiso⟩

/-- Finite free resolutions near the two halves of a block cut in the real part of a
coordinate glue to one near the block. -/
private lemma glue_block_re {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) {a b c d : Fin n → ℝ} {i : Fin n}
    {t : ℝ} (hKU : block a b c d ⊆ U) (hab : a ≤ b) (hcd : c ≤ d) (ht₀ : a i < t) (ht₁ : t < b i)
    (hG₁ : ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤),
      (Subtype.val : U → _) ⁻¹' block a (Function.update b i t) c d ⊆ W ∧
        ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ)
    (hG₂ : ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤),
      (Subtype.val : U → _) ⁻¹' block (Function.update a i t) b c d ⊆ W ∧
        ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ) :
    ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤), (Subtype.val : U → _) ⁻¹' block a b c d ⊆ W ∧
      ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ := by
  obtain ⟨W₁, hW₁, hK₁, ℓ₁, hM₁⟩ := hG₁
  obtain ⟨W₂, hW₂, hK₂, ℓ₂, hM₂⟩ := hG₂
  have hU : block a (Function.update b i t) c d ∪ block (Function.update a i t) b c d ⊆ U := by
    rw [block_cut_re_union i ht₀.le ht₁.le]
    exact hKU
  obtain ⟨W, h, hKW, ℓ', hW⟩ :=
    glue_resolutions (splitProp_block_re a b c d hab hcd i t ht₀ ht₁)
    hU (isCompact_block _ _ _ _) (isCompact_block _ _ _ _)
    (block_cut_re_inter i ht₀.le ht₁.le)
    (by rw [block_cut_re_inter i ht₀.le ht₁.le]
        refine block_nonempty (fun j => ?_) hcd
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj, hab j])
    (max ℓ₁ ℓ₂) ⊤ (S.over ⊤) ⟨W₁, hW₁, hK₁, hM₁.mono (le_max_left _ _)⟩
    ⟨W₂, hW₂, hK₂, hM₂.mono (le_max_right _ _)⟩
  rw [block_cut_re_union i ht₀.le ht₁.le] at hKW
  exact ⟨W, h, hKW, ℓ', hW⟩

/-- Finite free resolutions near the two halves of a block cut in the imaginary part of a
coordinate glue to one near the block. -/
private lemma glue_block_im {n : ℕ} {U : Opens (EuclideanSpace ℂ (Fin n))}
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) {a b c d : Fin n → ℝ} {i : Fin n}
    {t : ℝ} (hKU : block a b c d ⊆ U) (hab : a ≤ b) (hcd : c ≤ d) (ht₀ : c i < t) (ht₁ : t < d i)
    (hG₁ : ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤),
      (Subtype.val : U → _) ⁻¹' block a b c (Function.update d i t) ⊆ W ∧
        ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ)
    (hG₂ : ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤),
      (Subtype.val : U → _) ⁻¹' block a b (Function.update c i t) d ⊆ W ∧
        ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ) :
    ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤), (Subtype.val : U → _) ⁻¹' block a b c d ⊆ W ∧
      ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ := by
  obtain ⟨W₁, hW₁, hK₁, ℓ₁, hM₁⟩ := hG₁
  obtain ⟨W₂, hW₂, hK₂, ℓ₂, hM₂⟩ := hG₂
  have hU : block a b c (Function.update d i t) ∪ block a b (Function.update c i t) d ⊆ U := by
    rw [block_cut_im_union i ht₀.le ht₁.le]
    exact hKU
  obtain ⟨W, h, hKW, ℓ', hW⟩ :=
    glue_resolutions (splitProp_block_im a b c d hab hcd i t ht₀ ht₁)
    hU (isCompact_block _ _ _ _) (isCompact_block _ _ _ _)
    (block_cut_im_inter i ht₀.le ht₁.le)
    (by rw [block_cut_im_inter i ht₀.le ht₁.le]
        refine block_nonempty hab (fun j => ?_)
        by_cases hj : j = i
        · subst hj
          simp
        · simp [Function.update_of_ne hj, hcd j])
    (max ℓ₁ ℓ₂) ⊤ (S.over ⊤) ⟨W₁, hW₁, hK₁, hM₁.mono (le_max_left _ _)⟩
    ⟨W₂, hW₂, hK₂, hM₂.mono (le_max_right _ _)⟩
  rw [block_cut_im_union i ht₀.le ht₁.le] at hKW
  exact ⟨W, h, hKW, ℓ', hW⟩

/-- Part (1): a coherent sheaf has a finite free resolution near a block. -/
private theorem exists_finite_free_resolution_near_block {n : ℕ}
    (U : Opens (EuclideanSpace ℂ (Fin n))) (a b c d : Fin n → ℝ)
    (hKU : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)}
      ⊆ U)
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) (hS : IsCoherentModule S) :
    ∃ W : Opens (TopCat.of U),
      (Subtype.val : U → _) ⁻¹'
        {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)} ⊆ W ∧
      ∃ (C : ChainComplex (SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over W)) ℕ)
        (ε : C.X 0 ⟶ S.over W) (ℓ : ℕ),
        (∀ i, ∃ r : ℕ, Nonempty (C.X i ≅ SheafOfModules.free (Fin r))) ∧
        (∀ i, ℓ < i → Limits.IsZero (C.X i)) ∧ (∀ i, 0 < i → C.ExactAt i) ∧ Epi ε ∧
        ∃ h : C.d 1 0 ≫ ε = 0, (ShortComplex.mk _ _ h).Exact := by
  suffices hW : ∃ W : Opens (TopCat.of U), (Subtype.val : U → _) ⁻¹' block a b c d ⊆ W ∧
      ∃ ℓ, HasFFR (S.over W) ℓ by
    obtain ⟨W, hKW, ℓ, C, ε, h1, h2, h3, h4, h5⟩ := hW
    exact ⟨W, hKW, C, ε, ℓ, h1, h2, h3, h4, h5⟩
  by_cases hne : ∀ i, a i ≤ b i ∧ c i ≤ d i
  · have hab : a ≤ b := fun i => (hne i).1
    have hcd : c ≤ d := fun i => (hne i).2
    have hloc : ∀ x : U, ∃ W : Opens (TopCat.of U), x ∈ W ∧ ∃ ℓ, HasFFR (S.over W) ℓ := by
      intro x
      obtain ⟨W, hxW, C, ε, h1, h2, h3, h4, h5⟩ :=
        (coherent_analytic_toolkit (n := n) (M := U)).2.2.2.2.1 S hS x
      exact ⟨W, hxW, n, C, ε, h1, h2, h3, h4, h5⟩
    choose Wx hxWx ℓx hgood using hloc
    have hcov : block a b c d ⊆ ⋃ x : U, (imO (Wx x) : Set (EuclideanSpace ℂ (Fin n))) :=
      fun z hz => Set.mem_iUnion.2 ⟨⟨z, hKU hz⟩, ⟨⟨z, hKU hz⟩, hxWx _, rfl⟩⟩
    obtain ⟨δ, hδ, hδc⟩ := lebesgue_number_lemma_of_metric (isCompact_block a b c d)
      (fun x => (imO (Wx x)).isOpen) hcov
    have hη : 0 < δ / (3 * (n + 1)) := by positivity
    let G : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → Prop := fun a' b' c' d' =>
      ∃ (W : Opens (TopCat.of U)) (h : W ≤ ⊤), (Subtype.val : U → _) ⁻¹' block a' b' c' d' ⊆ W ∧
        ∃ ℓ, HasFFR ((res _ h).obj (S.over ⊤)) ℓ
    have hG := block_induction G a b c d hab hcd hη
      (fun a' b' c' d' h1 h2 h3 h4 h5 h6 hb hd => by
        obtain ⟨x, hx⟩ := hδc ((EuclideanSpace.equiv (Fin n) ℂ).symm fun i => ⟨a' i, c' i⟩)
          fun i => ⟨⟨h1 i, (h2 i).trans (h3 i)⟩, h4 i, (h5 i).trans (h6 i)⟩
        exact ⟨Wx x, le_top, fun y hy => mem_of_mem_imO' (hx (mem_ball_of_mem_block hδ hb hd hy)),
          ℓx x, (hgood x).of_iso ((SheafOfModules.overFunctorMap _ (homOfLE le_top)).app S).symm⟩)
      (fun a' b' c' d' i t h1 h2 h3 h4 h5 h6 ht₀ ht₁ =>
        glue_block_re S ((block_mono h1 h3 h4 h6).trans hKU) h2 h5 ht₀ ht₁)
      (fun a' b' c' d' i t h1 h2 h3 h4 h5 h6 ht₀ ht₁ =>
        glue_block_im S ((block_mono h1 h3 h4 h6).trans hKU) h2 h5 ht₀ ht₁)
    obtain ⟨W, hW, hKW, ℓ, hM⟩ := hG
    exact ⟨W, hKW, ℓ, hM.of_iso ((SheafOfModules.overFunctorMap _ (homOfLE hW)).app S)⟩
  · exact exists_hasFFR_of_block_empty hne S

/-- Part (3): higher cohomology classes die on a product of open rectangles around a block. -/
private theorem sheafCohomologyPullback_eq_zero_near_block {n : ℕ}
    (U : Opens (EuclideanSpace ℂ (Fin n))) (a b c d : Fin n → ℝ)
    (hKU : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)}
      ⊆ U)
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) (hS : IsCoherentModule S)
    (W' : Opens (TopCat.of U))
    (hKW : (Subtype.val : U → _) ⁻¹'
      {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)} ⊆ W')
    (q : ℤ) (hq : 1 ≤ q)
    (x : (sheafCohomology (TopCat.of W') q).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W')).obj
            ((SheafOfModules.toSheaf _).obj S))) :
    ∃ (P : Opens (TopCat.of U)) (hPW : P ≤ W'),
      (∃ a' b' c' d' : Fin n → ℝ, Subtype.val '' (P : Set U) =
        {z : EuclideanSpace ℂ (Fin n) |
          ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)}) ∧
      (Subtype.val : U → _) ⁻¹'
        {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)} ⊆ P ∧
      sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hPW, by fun_prop⟩) _ q x = 0 := by
  obtain ⟨W, hKW₀, C, ε, ℓ, hfree, hzero, hexact, hε, h0, hex⟩ :=
    exists_finite_free_resolution_near_block U a b c d hKU S hS
  obtain ⟨P, hPO, ⟨a', b', c', d', hPbox⟩, hKP⟩ :=
    exists_box_between U a b c d hKU (W ⊓ W') (fun x hx => ⟨hKW₀ hx, hKW hx⟩)
  have hPW₀ : P ≤ W := hPO.trans inf_le_left
  have hPW' : P ≤ W' := hPO.trans inf_le_right
  refine ⟨P, hPW', ⟨a', b', c', d', hPbox⟩, hKP, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = ((m + 1 : ℕ) : ℤ) := ⟨(q - 1).toNat, by omega⟩
  letI : HasExt (Sheaf (Opens.grothendieckTopology P) AddCommGrpCat.{0}) := HasExt.standard _
  have := preservesFiniteLimits_Ψ (R := holomorphicRingCatSheaf n U) hPW₀
  have := preservesFiniteColimits_Ψ (R := holomorphicRingCatSheaf n U) hPW₀
  have := additive_Ψ (R := holomorphicRingCatSheaf n U) hPW₀
  have hM := (subsingleton_ext_map_of_resolution (Ψ (R := holomorphicRingCatSheaf n U) hPW₀)
    (freeYonedaTop (TopCat.of P)) (fun q hq => by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact subsingleton_ext_Ψ_unit hPW₀ hPbox q')
    C ε hfree hzero hexact hε h0 hex).2 (m + 1) (by omega)
  have : (globalSections (TopCat.of P)).Additive := globalSections_additive _
  have hR := isZero_rightDerived_globalSections_of_subsingleton_H' (X := TopCat.of P) _ m hM
  have hH := hR.of_iso ((sheafCohomologyIso (TopCat.of P) (m + 1)).app _)
  let e : (TopCat.Sheaf.pullback AddCommGrpCat.{0} (TopCat.ofHom (X := TopCat.of P)
      (Y := TopCat.of W') ⟨Set.inclusion hPW', by fun_prop⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W')).obj
          ((SheafOfModules.toSheaf _).obj S)) ≅
      (Ψ (R := holomorphicRingCatSheaf n U) hPW₀).obj (S.over W) :=
    pullbackPullbackIso ((SheafOfModules.toSheaf _).obj S) hPW' ≪≫
      ((Opens.sheafEquivOver P).functor.mapIso ((SheafOfModules.toSheaf _).mapIso
        ((SheafOfModules.overFunctorMap (holomorphicRingCatSheaf n U) (homOfLE hPW₀)).app S))).symm
  have hF := hH.of_iso ((sheafCohomology (TopCat.of P) _).mapIso e)
  have := AddCommGrpCat.subsingleton_of_isZero hF
  exact Subsingleton.elim _ _

/-- **Cartan's theorems on compact blocks.** Let `K = ∏ᵢ [aᵢ, bᵢ] × [cᵢ, dᵢ] ⊆ ℂⁿ` be a block
contained in an open `U ⊆ ℂⁿ`, and `𝒮` a coherent `𝒪_U`-module. Then `𝒮` has a finite free
resolution on some open neighbourhood of `K`; there is a surjection `𝒪_Wᵖ → 𝒮|_W` on some open
neighbourhood `W` of `K`; and for every open `W' ⊇ K` and `q ≥ 1`, every class in `H^q(W', 𝒮)`
restricts to zero on some open product of open rectangles `P` with `K ⊆ P ⊆ W'`. -/
@[mmp "thm_mmp_gaga_cartan_compact_blocks"]
public theorem cartan_compact_blocks {n : ℕ} (U : Opens (EuclideanSpace ℂ (Fin n)))
    (a b c d : Fin n → ℝ)
    (hKU : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)}
      ⊆ U)
    (S : SheafOfModules.{0} (holomorphicRingCatSheaf n U)) (hS : IsCoherentModule S) :
    let K : Set U :=
      Subtype.val ⁻¹' {z | ∀ i, z i ∈ Set.Icc (a i) (b i) ×ℂ Set.Icc (c i) (d i)}
    -- (1) a finite free resolution near `K`
    (∃ W : Opens (TopCat.of U), K ⊆ W ∧
      ∃ (C : ChainComplex (SheafOfModules.{0} ((holomorphicRingCatSheaf n U).over W)) ℕ)
        (ε : C.X 0 ⟶ S.over W) (ℓ : ℕ),
        (∀ i, ∃ r : ℕ, Nonempty (C.X i ≅ SheafOfModules.free (Fin r))) ∧
        (∀ i, ℓ < i → Limits.IsZero (C.X i)) ∧ (∀ i, 0 < i → C.ExactAt i) ∧ Epi ε ∧
        ∃ h : C.d 1 0 ≫ ε = 0, (ShortComplex.mk _ _ h).Exact) ∧
    -- (2) a surjection `𝒪_Wᵖ → 𝒮|_W` near `K`
    (∃ W : Opens (TopCat.of U), K ⊆ W ∧
      ∃ (p : ℕ) (f : SheafOfModules.free (Fin p) ⟶ S.over W), Epi f) ∧
    -- (3) higher cohomology classes die on a product of open rectangles around `K`
    (∀ (W' : Opens (TopCat.of U)), K ⊆ W' → ∀ q : ℤ, 1 ≤ q →
      ∀ x : (sheafCohomology (TopCat.of W') q).obj
          ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W')).obj
            ((SheafOfModules.toSheaf _).obj S)),
        ∃ (P : Opens (TopCat.of U)) (hPW : P ≤ W'),
          (∃ a' b' c' d' : Fin n → ℝ, Subtype.val '' (P : Set U) =
            {z | ∀ i, z i ∈ Set.Ioo (a' i) (b' i) ×ℂ Set.Ioo (c' i) (d' i)}) ∧
          K ⊆ P ∧
          sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hPW, by fun_prop⟩) _ q x = 0) := by
  intro K
  have h1 := exists_finite_free_resolution_near_block U a b c d hKU S hS
  refine ⟨h1, ?_, fun W' hKW q hq x =>
    sheafCohomologyPullback_eq_zero_near_block U a b c d hKU S hS W' hKW q hq x⟩
  obtain ⟨W, hKW, C, ε, -, hfree, -, -, hε, -⟩ := h1
  obtain ⟨r, ⟨e⟩⟩ := hfree 0
  exact ⟨W, hKW, r, e.inv ≫ ε, epi_comp _ _⟩

end CompactBlocks

/-! ## Oka's coherence theorem -/

open AlgebraicGeometry OkaCoherence in
/-- **Oka's coherence theorem.** For every complex manifold `M` of dimension `n` (in particular
`M = ℂⁿ`), the sheaf `𝒪_M` of holomorphic functions is a coherent sheaf of rings. Consequently,
for a scheme `X` locally of finite type over `ℂ`, the structure sheaf of the analytification
`MMP.Analytic.analytification sX` is coherent, and `MMP.Analytic.analytifyModule sX` sends
coherent `𝒪_X`-modules to coherent `𝒪_{X^an}`-modules. -/
@[mmp "thm_mmp_gaga_oka_coherence"]
public theorem isCoherentRing_holomorphic_and_analytification :
    (∀ (n : ℕ) (M : Type) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
        [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M],
        IsCoherentRing (holomorphicRingCatSheaf n M)) ∧
      ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX],
        IsCoherentRing (ringCatSheaf sX) ∧
          ∀ F : X.Modules, IsCoherentModule F →
            IsCoherentModule ((analytifyModule sX).obj F) :=
  ⟨fun n M _ _ _ => isCoherentRing_holomorphicRingCatSheaf n M,
    fun X sX _ => ⟨isCoherentRing_ringCatSheaf X sX,
      fun F hF => isCoherentModule_analytifyModule X sX F hF⟩⟩

/-! ## Cartan's Theorem B on boxes -/

section TheoremB

open scoped ComplexOrder

/-! ### The exhaustion of a box by blocks -/

/-- The open box `∏ᵢ (aᵢ + ε, bᵢ - ε) × (cᵢ + ε, dᵢ - ε)`. -/
private def openBlock {n : ℕ} (a b c d : Fin n → ℝ) (ε : ℝ) : Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ i, z i ∈ Set.Ioo (a i + ε) (b i - ε) ×ℂ Set.Ioo (c i + ε) (d i - ε)}

/-- The block `∏ᵢ [aᵢ + ε, bᵢ - ε] × [cᵢ + ε, dᵢ - ε]`. -/
private def closedBlock {n : ℕ} (a b c d : Fin n → ℝ) (ε : ℝ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | ∀ i, z i ∈ Set.Icc (a i + ε) (b i - ε) ×ℂ Set.Icc (c i + ε) (d i - ε)}

private lemma isOpen_openBlock {n : ℕ} (a b c d : Fin n → ℝ) (ε : ℝ) :
    IsOpen (openBlock a b c d ε) := by
  simp only [openBlock, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i =>
    (IsOpen.reProdIm isOpen_Ioo isOpen_Ioo).preimage (PiLp.continuous_apply 2 _ i)

/-- The shrinking parameter `ε_j = 1/(j+1)`. -/
private noncomputable def shrink (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

private lemma shrink_pos (j : ℕ) : 0 < shrink j := by
  unfold shrink; positivity

private lemma shrink_succ_lt (j : ℕ) : shrink (j + 1) < shrink j := by
  unfold shrink
  apply one_div_lt_one_div_of_lt (by positivity)
  push_cast; linarith

private lemma shrink_antitone : Antitone shrink := by
  intro i j h
  unfold shrink
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right h 1

private lemma openBlock_subset_closedBlock {n : ℕ} (a b c d : Fin n → ℝ) (ε : ℝ) :
    openBlock a b c d ε ⊆ closedBlock a b c d ε := fun z hz i =>
  ⟨Set.Ioo_subset_Icc_self (hz i).1, Set.Ioo_subset_Icc_self (hz i).2⟩

private lemma closedBlock_subset_openBlock {n : ℕ} (a b c d : Fin n → ℝ) {ε ε' : ℝ}
    (h : ε' < ε) : closedBlock a b c d ε ⊆ openBlock a b c d ε' := fun z hz i => by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private lemma openBlock_anti {n : ℕ} (a b c d : Fin n → ℝ) {ε ε' : ℝ}
    (h : ε' ≤ ε) : openBlock a b c d ε ⊆ openBlock a b c d ε' := fun z hz i => by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private lemma openBlock_subset_box {n : ℕ} (a b c d : Fin n → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    openBlock a b c d ε ⊆
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)} := fun z hz i => by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The block `K_j` lies in the box. -/
private lemma closedBlock_shrink_subset_box {n : ℕ} (a b c d : Fin n → ℝ) (j : ℕ) :
    closedBlock a b c d (shrink j) ⊆
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)} :=
  (closedBlock_subset_openBlock a b c d (shrink_succ_lt j)).trans
    (openBlock_subset_box a b c d (shrink_pos _).le)

/-- Every point of the box lies in some `openBlock … ε_j`. -/
private lemma exists_mem_openBlock {n : ℕ} (a b c d : Fin n → ℝ)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ
      Set.Ioo (c i) (d i)}) :
    ∃ j, z ∈ openBlock a b c d (shrink j) := by
  have hev : ∀ r : ℝ, 0 < r → ∀ᶠ j in Filter.atTop, shrink j < r := fun r hr =>
    (tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 r hr
  have : ∀ᶠ j in Filter.atTop, ∀ i, z i ∈ Set.Ioo (a i + shrink j) (b i - shrink j) ×ℂ
      Set.Ioo (c i + shrink j) (d i - shrink j) := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz i
    filter_upwards [hev _ (sub_pos.2 h1), hev _ (sub_pos.2 h2), hev _ (sub_pos.2 h3),
      hev _ (sub_pos.2 h4)] with j e1 e2 e3 e4
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  exact this.exists

/-- The open boxes `U_j`, as opens of the box `D`. -/
private def exhaustion {n : ℕ} (a b c d : Fin n → ℝ) (D : Opens (EuclideanSpace ℂ (Fin n)))
    (j : ℕ) : Opens (TopCat.of D) :=
  ⟨Subtype.val ⁻¹' openBlock a b c d (shrink j),
    (isOpen_openBlock a b c d _).preimage continuous_subtype_val⟩

private lemma exhaustion_mono {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n))) : Monotone (exhaustion a b c d D) :=
  fun _ _ h _ hz => openBlock_anti a b c d (shrink_antitone h) hz

private lemma iSup_exhaustion {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)}) :
    ⨆ j, exhaustion a b c d D j = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  have hz : (z : EuclideanSpace ℂ (Fin n)) ∈ (D : Set _) := z.2
  rw [hD] at hz
  obtain ⟨j, hj⟩ := exists_mem_openBlock a b c d hz
  exact Opens.mem_iSup.2 ⟨j, hj⟩

/-! ### Theorem B on the box -/

/-- Restriction kills higher cohomology along the exhaustion: a class on `U_{j+1}` vanishes on
some open `P` with `U_j ⊆ P ⊆ U_{j+1}` (`MMP.Analytic.cartan_compact_blocks`). -/
private lemma exhaustion_restriction_zero {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T)
    (j : ℕ) (q : ℤ) (hq : 1 ≤ q)
    (x : (sheafCohomology (TopCat.of (exhaustion a b c d D (j + 1))) q).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0}
        (Opens.inclusion' (exhaustion a b c d D (j + 1)))).obj
        ((SheafOfModules.toSheaf _).obj T))) :
    ∃ (P : Opens (TopCat.of D)) (hP : P ≤ exhaustion a b c d D (j + 1)),
      exhaustion a b c d D j ≤ P ∧
      sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hP, by fun_prop⟩) _ q x = 0 := by
  obtain ⟨-, -, h3⟩ := cartan_compact_blocks D (fun i => a i + shrink j) (fun i => b i - shrink j)
    (fun i => c i + shrink j) (fun i => d i - shrink j)
    (hD ▸ closedBlock_shrink_subset_box a b c d j) T hT
  have hKW : (Subtype.val ⁻¹' closedBlock a b c d (shrink j) : Set D) ⊆
      (exhaustion a b c d D (j + 1) : Set D) :=
    Set.preimage_mono (closedBlock_subset_openBlock a b c d (shrink_succ_lt j))
  obtain ⟨P, hPW, -, hKP, hx⟩ := h3 _ hKW q hq x
  exact ⟨P, hPW, fun z hz => hKP (openBlock_subset_closedBlock a b c d _ hz), hx⟩

/-- The image of `U_j` in `ℂⁿ` is the open box `openBlock … ε_j`. -/
private lemma range_openInclusion_exhaustion {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)}) (j : ℕ) :
    Set.range (openInclusion (exhaustion a b c d D j)) = openBlock a b c d (shrink j) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact w.2
  · intro hz
    have hzD : z ∈ (D : Set (EuclideanSpace ℂ (Fin n))) := by
      rw [hD]
      exact openBlock_subset_box a b c d (shrink_pos j).le hz
    exact ⟨⟨⟨z, hzD⟩, hz⟩, rfl⟩

/-- **Runge along the exhaustion.** For the topology of compact convergence, the restriction
`𝒪(U_{j+1}) → 𝒪(U_j)` has dense range: every compact subset of `U_j` lies in a block inside
`U_j`, and blocks are Runge. -/
private theorem denseRange_exhaustion_restrict {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)}) (j : ℕ) :
    @DenseRange _ (holomorphicCompactConvergence (exhaustion a b c d D j)).toTopologicalSpace
      _ (𝒪[n, D].presheaf.map (homOfLE (exhaustion_mono a b c d D (Nat.le_succ j))).op).hom := by
  refine denseRange_holomorphic_restrict _ fun K hK hKne hKs => ?_
  rw [range_openInclusion_exhaustion a b c d D hD] at hKs ⊢
  exact exists_block_of_isCompact_subset_box hK hKne _ _ _ _ hKs

/-- The restriction `𝒮(U_j) → 𝒮(U_i)`, `i ≤ j`, along the exhaustion. -/
private noncomputable abbrev exhaustionRes {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) {i j : ℕ} (h : i ≤ j) :
    ((SheafOfModules.toSheaf _).obj T).obj.obj (op (exhaustion a b c d D j)) →+
      ((SheafOfModules.toSheaf _).obj T).obj.obj (op (exhaustion a b c d D i)) :=
  (((SheafOfModules.toSheaf _).obj T).obj.map (homOfLE (exhaustion_mono a b c d D h)).op).hom

/-! ### Free modules over the holomorphic functions -/

section FreeCoherence

open OkaCoherence

variable {T : TopCat.{0}} {A : TopCat.Sheaf RingCat.{0} T}

/-- **A criterion for coherence of a free module.** If the relations among finitely many vectors
of `A^q` are locally finitely generated, the free module `A^q` is coherent: the kernel of a
morphism `A^p → A^q|_V` is generated, near every point, by the finitely many relations given by
the hypothesis. -/
private theorem isCoherentModule_free_of_relations {q : ℕ} (h : RelationsLocallyFinite A q) :
    IsCoherentModule (SheafOfModules.free (R := A) (Fin q)) := by
  refine ⟨MMP.isFiniteType_free (Fin q), fun V p σ => ?_⟩
  let M := SheafOfModules.free (R := A) (Fin q)
  let g := (M.over V).freeHomEquiv.symm σ
  choose F hF using fun i => MMP.exists_eq_sum_smul_freeSection (R := A) (op V)
    (secAt (σ i) (op (Over.mk (𝟙 V))))
  have hσZ : ∀ (Z : Over V) (i : Fin p), secAt (σ i) (op Z) =
      ∑ j, res Z.hom.le (F i j) • freeElt (R := A) j (op Z.left) := by
    intro Z i
    have h0 := PresheafOfModules.sections_property (σ i)
      (Over.homMk (U := Z) (V := Over.mk (𝟙 V)) Z.hom (by simp)).op
    refine h0.symm.trans ?_
    change M.val.map (homOfLE Z.hom.le).op (secAt (σ i) (op (Over.mk (𝟙 V)))) = _
    rw [hF i]
    exact free_map_sum_smul _ _
  have hg : ∀ (Z : Over V) (a : Fin p → A.obj.obj (op Z.left)),
      g.val.app (op Z) (∑ i, toOver Z (a i) • freeElt (R := A.over V) i (op Z)) =
        ∑ j, (∑ i, a i * res Z.hom.le (F i j)) • freeElt (R := A) j (op Z.left) := by
    intro Z a
    rw [freeHomEquiv_symm_app_sum]
    refine (Finset.sum_congr rfl fun i _ => congrArg _ (hσZ Z i)).trans ?_
    exact (free_sum_smul_eq_sum_smul _ a _ fun j => rfl).symm
  choose W hWV hxW s r hr hgen using fun x : V => h V p F x.1 x.2
  let Y : V → Over V := fun x => Over.mk (homOfLE (hWV x))
  refine isFiniteType_kernel_of_local g (Y := Y) ?_ s
    (fun x k => ∑ i, toOver (Y x) (r x k i) •
      freeElt (R := A.over V) i (op (Y x))) (fun x k => ?_) ?_
  · intro U
    rw [GrothendieckTopology.mem_over_iff]
    intro y hy
    let x : V := ⟨y, U.hom.le hy⟩
    refine ⟨U.left ⊓ W x, homOfLE inf_le_left, ?_, ⟨hy, hxW x⟩⟩
    rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff]
    exact ⟨x, ⟨Over.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _)⟩⟩
  · refine (hg (Y x) (r x k)).trans ?_
    exact Finset.sum_eq_zero fun j _ => by rw [hr x k j, zero_smul]; rfl
  · intro x Z z m hm
    obtain ⟨a, rfl⟩ := MMP.exists_eq_sum_smul_freeSection (op Z) m
    have hZW : Z.left ≤ W x := z.left.le
    let a' : Fin p → A.obj.obj (op Z.left) := a
    have hm' : ∀ j, ∑ i, a' i * res (hZW.trans (hWV x)) (F i j) = 0 := by
      have h0 : ∑ j, (∑ i, a' i * res Z.hom.le (F i j)) • freeElt (R := A) j (op Z.left) =
          ∑ j, (0 : A.obj.obj (op Z.left)) • freeElt (R := A) j (op Z.left) :=
        (hg Z a').symm.trans (hm.trans (by simp only [zero_smul, Finset.sum_const_zero]; rfl))
      exact fun j => coeff_eq_of_sum_smul_eq h0 j
    choose U' hU' hyU' c hc using hgen x Z.left hZW a' hm'
    let S : Sieve Z :=
      { arrows := fun W' _ => ∃ y : Z.left, W'.left ≤ U' y.1 y.2
        downward_closed := fun {W' W''} _ ⟨y, hy⟩ g => ⟨y, g.left.le.trans hy⟩ }
    refine ⟨S, ?_, ?_⟩
    · rw [GrothendieckTopology.mem_over_iff]
      intro y hy
      refine ⟨U' y hy, homOfLE (hU' y hy), ?_, hyU' y hy⟩
      rw [Sieve.overEquiv_iff]
      exact ⟨⟨y, hy⟩, le_rfl⟩
    · rintro W' φ ⟨⟨y, hy⟩, hle⟩
      refine ⟨fun k => toOver W' (res hle (c y hy k)), (free_map_sum_smul φ.op a).trans ?_⟩
      simp only [free_map_sum_smul]
      refine free_sum_smul_eq_sum_smul _ _ _ fun i => ?_
      have key := congrArg (res (A := A) hle) (hc y hy i)
      rw [res_res, res_sum] at key
      simp only [res_mul, res_res] at key
      exact key

end FreeCoherence

open OkaCoherence in
/-- The kernel of a presentation `𝒪_Wᵖ ⟶ T|_W` of a coherent sheaf on `D`, read on the image
`W' ⊆ ℂⁿ` of `W`, is a coherent subsheaf of `𝒪_{W'}ᵖ`: it is of finite type
(`isFiniteType_kernel_imageFreeIso_hom_comp`) and a subsheaf of the coherent sheaf `𝒪_{W'}ᵖ`
(`coherent_analytic_toolkit` (1)). -/
private theorem isCoherentModule_kernel_imageFreeIso_hom_comp {n : ℕ}
    {D : Opens (EuclideanSpace ℂ (Fin n))} (W : Opens (TopCat.of D))
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T) {p : ℕ}
    (f : SheafOfModules.free (Fin p) ⟶ T.over W) :
    IsCoherentModule (Limits.kernel ((imageFreeIso W (Fin p)).hom ≫
      (imageModuleEquivalence W).functor.map f)) :=
  (coherent_analytic_toolkit (n := n) (M := imageOpens W)).2.1 (Limits.kernel.ι _)
    (isCoherentModule_free_of_relations (relationsLocallyFinite_of_one
      (relationsLocallyFinite_holomorphic n (imageOpens W)) p))
    (isFiniteType_kernel_imageFreeIso_hom_comp W T hT f)

/-! ### Towers of section complexes -/

private lemma map_map_apply {T : TopCat.{0}} (P : TopCat.Presheaf AddCommGrpCat.{0} T)
    {V W W' : Opens T} (f : W ⟶ V) (g : W' ⟶ W) (y : P.obj (op V)) :
    P.map g.op (P.map f.op y) = P.map (g ≫ f).op y := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The cone `op ⊤ ⟶ op U_j` over an increasing family of opens. -/
private def topCone {T : TopCat.{0}} (U : ℕ → Opens T) (hU : Monotone U) :
    Limits.Cone hU.functor.op where
  pt := op ⊤
  π := { app := fun j => (homOfLE le_top).op }

/-- The sections of a sheaf over an exhaustion `U_0 ⊆ U_1 ⊆ ⋯` of `T`: `F(T) = lim_j F(U_j)`. -/
private lemma isLimit_mapCone_topCone {T : TopCat.{0}} (X : TopCat.Sheaf AddCommGrpCat.{0} T)
    (U : ℕ → Opens T) (hU : Monotone U) (hcov : ⨆ j, U j = ⊤) :
    Nonempty (IsLimit (X.obj.mapCone (topCone U hU))) := by
  refine ⟨isLimitOfReflects (forget AddCommGrpCat.{0}) (Classical.choice ?_)⟩
  rw [Types.isLimit_iff]
  intro s hs
  have hs' : ∀ {i j : ℕ} (h : i ≤ j), X.obj.map (homOfLE (hU h)).op (s (op j)) = s (op i) :=
    fun {i j} h => hs (homOfLE h).op
  have hcomp : TopCat.Presheaf.IsCompatible X.obj U (fun j => s (op j)) := by
    intro i k
    dsimp only
    rcases le_total i k with h | h
    · rw [← hs' h, map_map_apply]
      rfl
    · rw [← hs' h, map_map_apply]
      rfl
  obtain ⟨g, hg, hgu⟩ := X.existsUnique_gluing U (fun j => s (op j)) hcomp
  refine ⟨X.obj.map (homOfLE hcov.ge).op g, ?_, ?_⟩
  · intro j
    change X.obj.map (homOfLE le_top).op (X.obj.map (homOfLE hcov.ge).op g) = s j
    rw [map_map_apply]
    exact hg j.unop
  · intro y hy
    have hy' : TopCat.Presheaf.IsGluing X.obj U (fun j => s (op j))
        (X.obj.map (homOfLE le_top).op y) := fun j =>
      (map_map_apply X.obj _ _ y).trans (hy (op j))
    rw [← hgu _ hy']
    refine ((map_map_apply X.obj _ _ y).trans ?_).symm
    exact (congrArg (fun φ => X.obj.map φ y) (Subsingleton.elim _ (𝟙 _))).trans
      (by rw [X.obj.map_id]; rfl)

/-- The complexes of sections `Γ(W, G^•)` of a complex of sheaves, as a functor of `W`. -/
private noncomputable def secFunctor {T : TopCat.{0}}
    (G : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} T) ℕ) :
    (Opens T)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj W :=
    (((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj W).mapHomologicalComplex
      _).obj G
  map f := (NatTrans.mapHomologicalComplex
    ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map f) _).app G
  map_id W := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]; rfl
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]; rfl

/-- `Γ(T, G^•) = lim_j Γ(U_j, G^•)`, extended by zero to `ℤ`-indexed complexes. -/
private lemma isLimit_extend_secFunctor {T : TopCat.{0}}
    (G : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} T) ℕ)
    (U : ℕ → Opens T) (hU : Monotone U) (hcov : ⨆ j, U j = ⊤) :
    Nonempty (IsLimit ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{0}).mapCone
      ((secFunctor G).mapCone (topCone U hU)))) := by
  refine ⟨HomologicalComplex.isLimitOfEval _ _ fun p => ?_⟩
  by_cases hp : 0 ≤ p
  · have hk : ComplexShape.embeddingUpNat.f p.toNat = p := by
      change ((p.toNat : ℕ) : ℤ) = p
      exact Int.toNat_of_nonneg hp
    have h0 : IsLimit ((HomologicalComplex.eval _ _ p.toNat).mapCone
        ((secFunctor G).mapCone (topCone U hU))) :=
      Classical.choice (isLimit_mapCone_topCone (G.X p.toNat) U hU hcov)
    exact IsLimit.mapConeEquiv
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{0} hk).symm h0
  · have hp' : ∀ k : ℕ, ComplexShape.embeddingUpNat.f k ≠ p := fun k hk => by
      change ((k : ℕ) : ℤ) = p at hk
      omega
    have hz : ∀ K : CochainComplex AddCommGrpCat.{0} ℕ,
        IsZero ((K.extend ComplexShape.embeddingUpNat).X p) := fun K =>
      K.isZero_extend_X _ p hp'
    exact
      { lift := fun s => 0
        fac := fun s j => (hz _).eq_of_tgt _ _
        uniq := fun s m _ => (hz _).eq_of_tgt _ _ }

/-! ### `lim¹` of the degree-zero cohomology of the tower -/

/-- `lim¹` vanishes for a tower receiving a levelwise surjective map from a tower with
vanishing `lim¹`, the latter given elementwise. -/
private lemma isZero_cokernel_delta_of_surjective {G' G : ℕᵒᵖ ⥤ AddCommGrpCat.{0}} (ψ : G' ⟶ G)
    (hψ : ∀ j, Function.Surjective (ψ.app j))
    (h : ∀ s : (j : ℕ) → G'.obj (op j), ∃ t : (j : ℕ) → G'.obj (op j),
      ∀ j, s j = t j - G'.map (homOfLE (Nat.le_succ j)).op (t (j + 1))) :
    IsZero (cokernel (Pi.lift fun j : ℕ => Pi.π (fun j : ℕ => G.obj (op j)) j -
      Pi.π (fun j : ℕ => G.obj (op j)) (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op)) := by
  have : Epi (Pi.lift fun j : ℕ => Pi.π (fun j : ℕ => G.obj (op j)) j -
      Pi.π (fun j : ℕ => G.obj (op j)) (j + 1) ≫ G.map (homOfLE (Nat.le_succ j)).op) := by
    refine (AddCommGrpCat.epi_iff_surjective _).2 fun x => ?_
    choose s hs using fun j : ℕ => hψ (op j) (Pi.π (fun j : ℕ => G.obj (op j)) j x)
    obtain ⟨t, ht⟩ := h s
    refine ⟨(Concrete.productEquiv _).symm fun j => ψ.app (op j) (t j),
      Concrete.limit_ext _ _ _ fun ⟨j⟩ => ?_⟩
    rw [← ConcreteCategory.comp_apply]
    erw [Pi.lift_comp_π]
    simp only [← hs j, ht j, map_sub, AddCommGrpCat.hom_sub, AddMonoidHom.sub_apply,
      ConcreteCategory.comp_apply, Concrete.productEquiv_symm_apply_π]
    rw [← ConcreteCategory.comp_apply, ← ψ.naturality, ConcreteCategory.comp_apply]
  exact isZero_cokernel_of_epi _

/-- The sections over `W`, as a functor on sheaves on `T`. -/
private abbrev secΓ {T : TopCat.{0}} (W : (Opens T)ᵒᵖ) :
    TopCat.Sheaf AddCommGrpCat.{0} T ⥤ AddCommGrpCat.{0} :=
  sectionsFunctor T W

private lemma godementResolution_d_zero {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T) :
    ((godementResolution T).obj F).d 0 1 =
      CokernelCoresolution.d (godementFunctor T) (godementUnit T) F 0 :=
  CokernelCoresolution.complex_d _ _ F 0

/-- A section of `G^0(F)` killed by `d^0` comes from a section of `F`. -/
private lemma exists_godementUnit_eq {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (W : (Opens T)ᵒᵖ) (x : (secΓ W).obj ((godementFunctor T).obj F))
    (hx : (secΓ W).map (((godementResolution T).obj F).d 0 1) x = 0) :
    ∃ s : (secΓ W).obj F, (secΓ W).map ((godementUnit T).app F) s = x := by
  haveI := mono_godementUnit_app F
  have hK : IsLimit (KernelFork.ofι ((godementUnit T).app F)
      (CokernelCoresolution.app_comp_d_zero (godementFunctor T) (godementUnit T) F)) :=
    isKernelCompMono (Abelian.monoIsKernelOfCokernel _
      (cokernelIsCokernel ((godementUnit T).app F))) _
      (hg := mono_godementUnit_app _)
      (CokernelCoresolution.d_zero (godementFunctor T) (godementUnit T) F)
  haveI : PreservesLimitsOfShape WalkingParallelPair (secΓ W) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf _ _ ⋙ (evaluation _ AddCommGrpCat.{0}).obj W))
  have hK' := KernelFork.mapIsLimit _ hK (secΓ W)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hK' (AddCommGrpCat.ofHom (zmultiplesHom _ x)) (by
    apply AddCommGrpCat.ext
    intro n
    change ((secΓ W).map (CokernelCoresolution.d (godementFunctor T) (godementUnit T) F 0)).hom
      (n • x) = 0
    refine (map_zsmul _ n x).trans ?_
    rw [← godementResolution_d_zero]
    change n • ((secΓ W).map (((godementResolution T).obj F).d 0 1)) x = 0
    rw [hx, smul_zero])
  refine ⟨l (1 : ℤ), (congrArg (fun φ => φ (1 : ℤ)) hl).trans ?_⟩
  change (zmultiplesHom _ x) (1 : ℤ) = x
  exact (zmultiplesHom_apply _ x 1).trans (one_zsmul x)

private lemma embeddingUpNat_f_zero : ComplexShape.embeddingUpNat.f 0 = 0 := rfl

private lemma embeddingUpNat_f_one : ComplexShape.embeddingUpNat.f 1 = 1 := rfl

/-- The augmentation `F ⟶ G^0(F)`, `s ↦ (s_x)_x`. -/
private noncomputable def unitG0 {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T) :
    F ⟶ ((godementResolution T).obj F).X 0 :=
  (godementUnit T).app F

private lemma unitG0_d {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T) :
    unitG0 F ≫ ((godementResolution T).obj F).d 0 1 = 0 := by
  rw [godementResolution_d_zero]
  exact CokernelCoresolution.app_comp_d_zero (godementFunctor T) (godementUnit T) F

/-- The section `s ↦ (s_x)_x` of `G^0(F)` over `W`, read in degree `0` of the extended complex
`Γ(W, G^•(F))`. -/
private noncomputable def unitToExtend {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (W : (Opens T)ᵒᵖ) :
    (secΓ W).obj F ⟶ (((secFunctor ((godementResolution T).obj F)).obj W).extend
      ComplexShape.embeddingUpNat).X 0 :=
  @CategoryStruct.comp _ _ _ (((secFunctor ((godementResolution T).obj F)).obj W).X 0) _
    ((secΓ W).map (unitG0 F))
    (((secFunctor ((godementResolution T).obj F)).obj W).extendXIso
      ComplexShape.embeddingUpNat embeddingUpNat_f_zero).inv

private lemma unitToExtend_d {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (W : (Opens T)ᵒᵖ) :
    unitToExtend F W ≫ (((secFunctor ((godementResolution T).obj F)).obj W).extend
      ComplexShape.embeddingUpNat).d 0 1 = 0 := by
  rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat embeddingUpNat_f_zero
    embeddingUpNat_f_one, unitToExtend]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  change (secΓ W).map (unitG0 F) ≫ (secΓ W).map (((godementResolution T).obj F).d 0 1) ≫ _ = 0
  erw [← Functor.map_comp_assoc, unitG0_d, Functor.map_zero, Limits.zero_comp]

/-- The map `F(W) ⟶ H^0(Γ(W, G^•(F)))`. -/
private noncomputable def unitToH0 {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (W : (Opens T)ᵒᵖ) :
    F.presheaf.obj W ⟶ (((secFunctor ((godementResolution T).obj F)).obj W).extend
      ComplexShape.embeddingUpNat).homology 0 :=
  (((secFunctor ((godementResolution T).obj F)).obj W).extend
      ComplexShape.embeddingUpNat).liftCycles (unitToExtend F W) 1 (by simp)
      (unitToExtend_d F W) ≫
    (((secFunctor ((godementResolution T).obj F)).obj W).extend
      ComplexShape.embeddingUpNat).homologyπ 0

private lemma unitToExtend_naturality {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    {W W' : (Opens T)ᵒᵖ} (f : W ⟶ W') :
    unitToExtend F W ≫ (HomologicalComplex.extendMap
      ((secFunctor ((godementResolution T).obj F)).map f) ComplexShape.embeddingUpNat).f 0 =
      F.presheaf.map f ≫ unitToExtend F W' := by
  rw [HomologicalComplex.extendMap_f _ _ embeddingUpNat_f_zero, unitToExtend, unitToExtend]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  change (secΓ W).map (unitG0 F) ≫
      ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map f).app _ ≫ _ =
    ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map f).app F ≫
      (secΓ W').map (unitG0 F) ≫ _
  erw [← NatTrans.naturality_assoc]

private lemma unitToH0_naturality {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    {W W' : (Opens T)ᵒᵖ} (f : W ⟶ W') :
    F.presheaf.map f ≫ unitToH0 F W' = unitToH0 F W ≫ HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap ((secFunctor ((godementResolution T).obj F)).map f)
        ComplexShape.embeddingUpNat) 0 := by
  simp only [unitToH0, Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  rw [← Category.assoc, HomologicalComplex.comp_liftCycles]
  congr 2
  exact (unitToExtend_naturality F f).symm

/-- Every class in `H^0(Γ(W, G^•(F)))` comes from a section of `F` over `W`. -/
private lemma unitToH0_surjective {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} T)
    (W : (Opens T)ᵒᵖ) : Function.Surjective (unitToH0 F W) := by
  intro y
  let K := (secFunctor ((godementResolution T).obj F)).obj W
  let E := K.extend ComplexShape.embeddingUpNat
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (E.homologyπ 0)).1 inferInstance y
  let i0 := K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_zero
  let i1 := K.extendXIso ComplexShape.embeddingUpNat embeddingUpNat_f_one
  let v := E.iCycles 0 z
  have hv : (i0.hom ≫ K.d 0 1 ≫ i1.inv) v = 0 := by
    rw [← HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat embeddingUpNat_f_zero
      embeddingUpNat_f_one]
    change (E.iCycles 0 ≫ E.d 0 1) z = 0
    rw [HomologicalComplex.iCycles_d]
    rfl
  have hx : (secΓ W).map (((godementResolution T).obj F).d 0 1) (i0.hom v) = 0 := by
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hv
    have inj : Function.Injective i1.inv :=
      (AddCommGrpCat.mono_iff_injective i1.inv).1 inferInstance
    exact inj (hv.trans (map_zero _).symm)
  obtain ⟨s, hs⟩ := exists_godementUnit_eq F W (i0.hom v) hx
  refine ⟨s, ?_⟩
  change (E.liftCycles (unitToExtend F W) 1 (by simp) (unitToExtend_d F W) ≫ E.homologyπ 0) s =
    E.homologyπ 0 z
  rw [ConcreteCategory.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (E.iCycles 0)).1 inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  change i0.inv ((secΓ W).map (unitG0 F) s) = v
  erw [hs]
  exact i0.hom_inv_id_apply v

/-! ### Comparison of the tower with the cohomology of the opens -/

/-- The map of section complexes `Γ(V, K^•) ⟶ Γ(V, L^•)` induced by a map of complexes. -/
private noncomputable abbrev secMap {T : TopCat.{0}} (V : (Opens T)ᵒᵖ)
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} T) ℕ} (γ : K ⟶ L) :
    (secFunctor K).obj V ⟶ (secFunctor L).obj V :=
  ((secΓ V).mapHomologicalComplex _).map γ

private lemma secFunctor_map_comp_secMap {T : TopCat.{0}} {V V' : (Opens T)ᵒᵖ} (i : V ⟶ V')
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} T) ℕ} (γ : K ⟶ L) :
    (secFunctor K).map i ≫ secMap V' γ = secMap V γ ≫ (secFunctor L).map i := by
  ext n : 1
  exact (((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map i).naturality
    (γ.f n)).symm

private lemma homologyMap_injective_of_bijective {K L : CochainComplex AddCommGrpCat.{0} ℕ}
    (φ : K ⟶ L) (hφ : ∀ n, Function.Bijective (φ.f n)) (k : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap φ k) := by
  haveI : ∀ n, IsIso (φ.f n) := fun n => (ConcreteCategory.isIso_iff_bijective _).2 (hφ n)
  haveI := HomologicalComplex.Hom.isIso_of_components φ
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- A class `x` of `H^k(Γ(W, G^•(F)))` has an image `y ∈ H^k(W, F|_W)` such that `x` dies on every
open `P ⊆ W` on which `y` dies. The image is taken along `Γ(W, G^•_T(F)) ⟶ Γ(W, G^•_W(F|_W))`, and
on every `P ⊆ W` the comparison of Godement resolutions along an open embedding is bijective
(`MMP.Analytic.godementResolutionPullback_app_bijective`). -/
private lemma godementTower_restriction_eq_zero_nat {T : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) (W : Opens T) (k : ℕ)
    (x : ((secFunctor ((godementResolution T).obj F)).obj (op W)).homology k) :
    ∃ y : (sheafCohomology (TopCat.of W) (k : ℤ)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W)).obj F),
      ∀ (P : Opens T) (hPW : P ≤ W),
        sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hPW, by fun_prop⟩) _ (k : ℤ) y = 0 →
        HomologicalComplex.homologyMap
          ((secFunctor ((godementResolution T).obj F)).map (homOfLE hPW).op) k x = 0 := by
  let ιW := Opens.inclusion' W
  let FW := (TopCat.Sheaf.pullback AddCommGrpCat.{0} ιW).obj F
  let GW := (godementResolution (TopCat.of W)).obj FW
  let γW := godementResolutionPullback ιW F
  have hιW : Topology.IsOpenEmbedding ιW := W.isOpenEmbedding'
  let αW : (secFunctor ((godementResolution T).obj F)).obj (op W) ⟶
      (secFunctor GW).obj (op ⊤) :=
    secMap (op W) γW ≫ (secFunctor GW).map
      (homOfLE (fun z _ => z.2 : (⊤ : Opens (TopCat.of W)) ≤ (Opens.map ιW).obj W)).op
  refine ⟨(sheafCohomologyGodementIso (TopCat.of W) FW k).inv
    (HomologicalComplex.homologyMap αW k x), ?_⟩
  intro P hPW hy
  let j : TopCat.of P ⟶ TopCat.of W := TopCat.ofHom ⟨Set.inclusion hPW, by fun_prop⟩
  let γj := godementResolutionPullback j FW
  let z := HomologicalComplex.homologyMap αW k x
  -- the pullback along `j` read on the Godement resolutions
  have e1 := sheafCohomologyGodementIso_pullback j FW _ (𝟙 _) k
  let FP := (TopCat.Sheaf.pullback AddCommGrpCat.{0} j).obj FW
  have hid : HomologicalComplex.homologyMap
      (secMap (op ⊤) ((godementResolution (TopCat.of P)).map (𝟙 FP))) k = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id]
    simp only [CategoryTheory.Functor.map_id]
    exact HomologicalComplex.homologyMap_id _ k
  have hz : HomologicalComplex.homologyMap (secMap (op ⊤) γj) k z = 0 := by
    have e4 := (Iso.inv_hom_id_assoc (sheafCohomologyGodementIso (TopCat.of W) FW k) _).symm.trans
      (congrArg ((sheafCohomologyGodementIso (TopCat.of W) FW k).inv ≫ ·) e1.symm)
    have h2 := (ConcreteCategory.congr_hom e4 z).trans (show
      (sheafCohomologyGodementIso (TopCat.of P) FP k).hom
        ((sheafCohomology (TopCat.of P) k).map (𝟙 FP)
          (sheafCohomologyPullback j FW k ((sheafCohomologyGodementIso (TopCat.of W) FW k).inv z)))
        = 0 by erw [hy, map_zero, map_zero])
    have h5 : HomologicalComplex.homologyMap
        (secMap (op ⊤) ((godementResolution (TopCat.of P)).map (𝟙 FP))) k
        (HomologicalComplex.homologyMap (secMap (op ⊤) γj) k z) = 0 := h2
    exact (ConcreteCategory.congr_hom hid _).symm.trans h5
  let Q : Opens (TopCat.of W) := (Opens.map ιW).obj P
  have hj : Topology.IsOpenEmbedding j :=
    (Topology.IsOpenEmbedding.of_comp_iff _ hιW).1 P.isOpenEmbedding'
  have hQ : (Q : Set (TopCat.of W)) ⊆ Set.range j := fun w hw => ⟨⟨w.1, hw⟩, rfl⟩
  have inj1 := homologyMap_injective_of_bijective (secMap (op Q) γj)
    (fun n => godementResolutionPullback_app_bijective hj FW n Q hQ) k
  -- `z` dies on `Q = P ∩ W`
  let r : Q ⟶ ⊤ := homOfLE le_top
  have nat1 := secFunctor_map_comp_secMap r.op γj
  have h6 : HomologicalComplex.homologyMap (secMap (op Q) γj) k
      (HomologicalComplex.homologyMap ((secFunctor GW).map r.op) k z) = 0 :=
    ((ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp _ _ k).symm z).trans
      (ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.homologyMap φ k) nat1)
        z)).trans ((ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp _ _ k) z).trans
      ((congrArg (fun w => HomologicalComplex.homologyMap ((secFunctor
        (((TopCat.Sheaf.pushforward AddCommGrpCat.{0} j).mapHomologicalComplex _).obj
          ((godementResolution (TopCat.of P)).obj FP))).map r.op) k w) hz).trans (map_zero _)))
  have h7 := inj1 (h6.trans (map_zero _).symm)
  -- hence `x` dies on `P`
  have heq : αW ≫ (secFunctor GW).map r.op =
      (secFunctor ((godementResolution T).obj F)).map (homOfLE hPW).op ≫ secMap (op P) γW := by
    rw [secFunctor_map_comp_secMap]
    exact (Category.assoc _ _ _).trans
      (congrArg (secMap (op W) γW ≫ ·) ((secFunctor GW).map_comp _ _).symm)
  have h8 : HomologicalComplex.homologyMap (secMap (op P) γW) k
      (HomologicalComplex.homologyMap
        ((secFunctor ((godementResolution T).obj F)).map (homOfLE hPW).op) k x) = 0 :=
    ((ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp _ _ k).symm x).trans
      (ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.homologyMap φ k) heq.symm)
        x)).trans ((ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp _ _ k) x).trans
      h7)
  have hP : (P : Set T) ⊆ Set.range ιW := fun t ht => ⟨⟨t, hPW ht⟩, rfl⟩
  exact homologyMap_injective_of_bijective (secMap (op P) γW)
    (fun n => godementResolutionPullback_app_bijective hιW F n P hP) k (h8.trans (map_zero _).symm)

/-- A class of `H^{m+1}(Γ(W, G^•(F)))` has an image `y ∈ H^{m+1}(W, F|_W)` such that, whenever `y`
dies on an open `P ⊆ W`, the class itself dies in `H^{m+1}(Γ(V, G^•(F)))` for every `V ⊆ P`.
Here `y` is the image under `Γ(W, G^•_T(F)) ⟶ Γ(W, G^•_W(F|_W))`; the Godement resolution of
`F|_W` is the restriction of that of `F`, so the comparison is an isomorphism on cohomology,
compatible with restriction to `P`. -/
private lemma godementTower_restriction_eq_zero {T : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) (W : Opens T) (m : ℕ)
    (x : (((secFunctor ((godementResolution T).obj F)).obj (op W)).extend
      ComplexShape.embeddingUpNat).homology ((m + 1 : ℕ) : ℤ)) :
    ∃ y : (sheafCohomology (TopCat.of W) ((m + 1 : ℕ) : ℤ)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' W)).obj F),
      ∀ (P : Opens T) (hPW : P ≤ W) (V : Opens T) (hVP : V ≤ P),
        sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hPW, by fun_prop⟩) _
          ((m + 1 : ℕ) : ℤ) y = 0 →
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap
          ((secFunctor ((godementResolution T).obj F)).map (homOfLE (hVP.trans hPW)).op)
          ComplexShape.embeddingUpNat) ((m + 1 : ℕ) : ℤ) x = 0 := by
  let G := (godementResolution T).obj F
  let e := ComplexShape.embeddingUpNat
  have hk : e.f (m + 1) = ((m + 1 : ℕ) : ℤ) := rfl
  obtain ⟨y, hy⟩ := godementTower_restriction_eq_zero_nat F W (m + 1)
    ((HomologicalComplex.extendHomologyIso ((secFunctor G).obj (op W)) e hk).hom x)
  refine ⟨y, fun P hPW V hVP hP => ?_⟩
  have h := hy P hPW hP
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality
    ((secFunctor G).map (homOfLE (hVP.trans hPW)).op) e hk
  have hcomp : (secFunctor G).map (homOfLE (hVP.trans hPW)).op =
      (secFunctor G).map (homOfLE hPW).op ≫ (secFunctor G).map (homOfLE hVP).op :=
    (secFunctor G).map_comp (homOfLE hPW).op (homOfLE hVP).op
  have inj : Function.Injective
      (HomologicalComplex.extendHomologyIso ((secFunctor G).obj (op V)) e hk).hom :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  refine inj ((ConcreteCategory.congr_hom hnat x).trans ?_ |>.trans (map_zero _).symm)
  refine (ConcreteCategory.congr_hom (congrArg (fun φ => HomologicalComplex.homologyMap φ (m + 1))
    hcomp) _).trans ?_
  refine (ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp _ _ (m + 1)) _).trans ?_
  exact (congrArg (fun w => HomologicalComplex.homologyMap ((secFunctor G).map (homOfLE hVP).op)
    (m + 1) w) h).trans (map_zero _)

/-- **Vanishing of cohomology along an exhaustion.** Let `F` be a sheaf of abelian groups on
`T`, and `U_0 ⊆ U_1 ⊆ ⋯` opens covering `T`. Suppose that every class in `H^q(U_{j+1}, F)`,
`q ≥ 1`, restricts to zero on some open `P` with `U_j ⊆ P ⊆ U_{j+1}`, and that
`lim¹_j F(U_j) = 0`: every family `s_j ∈ F(U_j)` is of the form `t_j - t_{j+1}|_{U_j}`.
Then `H^q(T, F) = 0` for every `q ≥ 1`. -/
private theorem isZero_sheafCohomology_of_exhaustion {T : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) (U : ℕ → Opens T) (hU : Monotone U)
    (hcov : ⨆ j, U j = ⊤)
    (hres : ∀ (j : ℕ) (q : ℤ), 1 ≤ q →
      ∀ x : (sheafCohomology (TopCat.of (U (j + 1))) q).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (Opens.inclusion' (U (j + 1)))).obj F),
      ∃ (P : Opens T) (hP : P ≤ U (j + 1)), U j ≤ P ∧
        sheafCohomologyPullback (TopCat.ofHom ⟨Set.inclusion hP, by fun_prop⟩) _ q x = 0)
    (hlim : ∀ s : (j : ℕ) → F.presheaf.obj (op (U j)), ∃ t : (j : ℕ) → F.presheaf.obj (op (U j)),
      ∀ j, s j = t j - F.presheaf.map (homOfLE (hU (Nat.le_succ j))).op (t (j + 1)))
    (q : ℤ) (hq : 1 ≤ q) :
    Limits.IsZero ((sheafCohomology T q).obj F) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = ((k + 1 : ℕ) : ℤ) := ⟨q.toNat - 1, by omega⟩
  have hflasque := ((sheafCohomology_toolkit.{0, 0, 0, 0, 0} T).2.1.2.2.2 F).2
  let G := (godementResolution T).obj F
  let e := ComplexShape.embeddingUpNat
  let C : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℤ :=
    (hU.functor.op ⋙ secFunctor G) ⋙ e.extendFunctor AddCommGrpCat.{0}
  let c : Limits.Cone C := (e.extendFunctor AddCommGrpCat.{0}).mapCone
    ((secFunctor G).mapCone (topCone U hU))
  have hc : Limits.IsLimit c := Classical.choice (isLimit_extend_secFunctor G U hU hcov)
  have hsurj : ∀ (j : ℕ) (p : ℤ),
      Function.Surjective ((C.map (homOfLE (Nat.le_succ j)).op).f p) := by
    intro j p
    rw [← AddCommGrpCat.epi_iff_surjective]
    by_cases hp : 0 ≤ p
    · have hk : e.f p.toNat = p := by
        change ((p.toNat : ℕ) : ℤ) = p
        exact Int.toNat_of_nonneg hp
      change Epi (HomologicalComplex.extendMap _ e |>.f p)
      rw [HomologicalComplex.extendMap_f _ e hk]
      have := (hflasque p.toNat).epi (homOfLE (hU (Nat.le_succ j))).op
      exact epi_comp' inferInstance (epi_comp' this inferInstance)
    · have hp' : ∀ k : ℕ, e.f k ≠ p := fun k hk => by
        change ((k : ℕ) : ℤ) = p at hk
        omega
      exact Limits.IsZero.epi ((secFunctor G).obj _ |>.isZero_extend_X e p hp') _
  -- the vanishing of the transitions on `H^m(Γ(U_j, G^•))`, `m ≥ 1`
  have hzero : ∀ m : ℕ, ∀ j : ℕ,
      (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ)
        ((m + 1 : ℕ) : ℤ)).map (homOfLE (Nat.le_succ j)).op = 0 := by
    intro m j
    refine AddCommGrpCat.ext fun x => ?_
    obtain ⟨y, hy⟩ := godementTower_restriction_eq_zero F (U (j + 1)) m x
    obtain ⟨P, hP, hjP, hPy⟩ := hres j ((m + 1 : ℕ) : ℤ) (by omega) y
    exact (hy P hP (U j) hjP hPy).trans (AddCommGrpCat.zero_apply _ _ x).symm
  -- `lim¹_j H^0(Γ(U_j, G^•)) = lim¹_j F(U_j) = 0`
  have hlim1 : Limits.IsZero (Limits.cokernel (Limits.Pi.lift fun j : ℕ =>
      Limits.Pi.π (fun j : ℕ => (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
        (ComplexShape.up ℤ) 0).obj (op j)) j -
      Limits.Pi.π (fun j : ℕ => (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
        (ComplexShape.up ℤ) 0).obj (op j)) (j + 1) ≫
        (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) 0).map
          (homOfLE (Nat.le_succ j)).op)) := by
    let ψ : hU.functor.op ⋙ F.presheaf ⟶
        C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) 0 :=
      { app := fun j => unitToH0 F (op (U j.unop))
        naturality := fun _ _ f => unitToH0_naturality F _ }
    exact isZero_cokernel_delta_of_surjective ψ (fun j => unitToH0_surjective F _) hlim
  obtain ⟨⟨f, w, hSE⟩, h2⟩ := milnor_sequence C hsurj c hc (k : ℤ) ((k + 1 : ℕ) : ℤ)
    (by push_cast; ring)
  have hX₃ := (h2 (hzero k)).1
  have hX₁ : Limits.IsZero (Limits.cokernel (Limits.Pi.lift fun j : ℕ =>
      Limits.Pi.π (fun j : ℕ => (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
        (ComplexShape.up ℤ) k).obj (op j)) j -
      Limits.Pi.π (fun j : ℕ => (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0}
        (ComplexShape.up ℤ) k).obj (op j)) (j + 1) ≫
        (C ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) k).map
          (homOfLE (Nat.le_succ j)).op)) := by
    rcases k with _ | k
    · exact hlim1
    · obtain ⟨-, h2'⟩ := milnor_sequence C hsurj c hc (k : ℤ) ((k + 1 : ℕ) : ℤ)
        (by push_cast; ring)
      exact (h2' (hzero k)).2
  have hmid : Limits.IsZero (c.pt.homology ((k + 1 : ℕ) : ℤ)) :=
    hSE.exact.isZero_X₂ (hX₁.eq_of_src _ _) (hX₃.eq_of_tgt _ _)
  refine Limits.IsZero.of_iso ?_ (sheafCohomologyGodementIso T F (k + 1))
  exact Limits.IsZero.of_iso hmid
    (HomologicalComplex.extendHomologyIso _ e (j := k + 1) rfl).symm

/-! ### Lifting sections through an epimorphism of sheaves -/

/-- Functoriality of sections, on elements. -/
private lemma secΓ_map_map {T : TopCat.{0}} (U : (Opens T)ᵒᵖ)
    {F F' F'' : TopCat.Sheaf AddCommGrpCat.{0} T} (φ : F ⟶ F') (ψ : F' ⟶ F'')
    (x : (secΓ U).obj F) : (secΓ U).map ψ ((secΓ U).map φ x) = (secΓ U).map (φ ≫ ψ) x := by
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restriction of sections commutes with morphisms of sheaves, on elements. -/
private lemma restrict_secΓ_map {T : TopCat.{0}} {U U' : (Opens T)ᵒᵖ} (ι : U ⟶ U')
    {F F' : TopCat.Sheaf AddCommGrpCat.{0} T} (φ : F ⟶ F') (x : (secΓ U).obj F) :
    ((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map ι).app F'
        ((secΓ U).map φ x) =
      (secΓ U').map φ (((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map ι).app
        F x) := by
  have h := ConcreteCategory.congr_hom
    (((sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map ι).naturality φ) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- A class of `H¹` of a cochain complex of abelian groups which vanishes is represented by a
coboundary. -/
private lemma exists_d_eq_of_homologyπ_eq_zero (K : CochainComplex AddCommGrpCat.{0} ℕ)
    (z : K.cycles 1) (hz : K.homologyπ 1 z = 0) : ∃ w : K.X 0, K.d 0 1 w = K.iCycles 1 z := by
  have hex : (ShortComplex.mk (K.toCycles 0 1) (K.homologyπ 1)
      (K.toCycles_comp_homologyπ 0 1)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel 0 1 (by simp))
  obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).1 hex z hz
  refine ⟨w, ?_⟩
  rw [← hw, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]

/-- **Lifting through an epimorphism of sheaves.** For a short exact sequence `0 → A → B → C → 0`
of sheaves of abelian groups and a section `s` of `C` over `V`, there is a class `c` in the first
cohomology of the Godement complex `Γ(V, G^•(A))` such that `s` lifts to `B` over every open
`P ⊆ V` on which `c` vanishes. -/
private lemma exists_godement_class_lift {X : TopCat.{0}}
    (Y : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) (hY : Y.ShortExact) (V : Opens X)
    (s : (secΓ (op V)).obj Y.X₃) :
    ∃ c : ((secFunctor ((godementResolution X).obj Y.X₁)).obj (op V)).homology 1,
      ∀ (P : Opens X) (hPV : P ≤ V), HomologicalComplex.homologyMap
          ((secFunctor ((godementResolution X).obj Y.X₁)).map (homOfLE hPV).op) 1 c = 0 →
        ∃ a : (secΓ (op P)).obj Y.X₂, (secΓ (op P)).map Y.g a =
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
            (homOfLE hPV).op).app Y.X₃ s := by
  let G := godementResolution X
  let rs : ∀ {P : Opens X} (_ : P ≤ V) (F : TopCat.Sheaf AddCommGrpCat.{0} X),
      (secΓ (op V)).obj F ⟶ (secΓ (op P)).obj F := fun hPV F =>
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map (homOfLE hPV).op).app F
  have hS := fun k U => godementResolution_sections_shortExact X Y hY k U
  -- lift the germs of `s`
  obtain ⟨a0, ha0⟩ : ∃ a0 : (secΓ (op V)).obj ((G.obj Y.X₂).X 0),
      (secΓ (op V)).map ((G.map Y.g).f 0) a0 = (secΓ (op V)).map (unitG0 Y.X₃) s :=
    (hS 0 (op V)).ab_surjective_g ((secΓ (op V)).map (unitG0 Y.X₃) s)
  -- `d⁰ a0` comes from `A`
  have hd0 :
      (secΓ (op V)).map ((G.map Y.g).f 1) ((secΓ (op V)).map ((G.obj Y.X₂).d 0 1) a0) = 0 := by
    rw [secΓ_map_map, ← (G.map Y.g).comm 0 1, ← secΓ_map_map, ha0, secΓ_map_map, unitG0_d,
      Functor.map_zero]
    rfl
  obtain ⟨r1, hr1⟩ : ∃ r1 : (secΓ (op V)).obj ((G.obj Y.X₁).X 1),
      (secΓ (op V)).map ((G.map Y.f).f 1) r1 = (secΓ (op V)).map ((G.obj Y.X₂).d 0 1) a0 :=
    (ShortComplex.ab_exact_iff _).1 (hS 1 (op V)).exact _ hd0
  -- `r1` is a cocycle
  have hr1d : (secΓ (op V)).map ((G.obj Y.X₁).d 1 2) r1 = 0 := by
    apply (hS 2 (op V)).ab_injective_f
    change (secΓ (op V)).map ((G.map Y.f).f 2) _ = (secΓ (op V)).map ((G.map Y.f).f 2) 0
    rw [map_zero, secΓ_map_map, ← (G.map Y.f).comm 1 2, ← secΓ_map_map, hr1, secΓ_map_map,
      HomologicalComplex.d_comp_d, Functor.map_zero]
    rfl
  let K₁ := (secFunctor (G.obj Y.X₁)).obj (op V)
  have hcyc : AddCommGrpCat.ofHom (zmultiplesHom (K₁.X 1) r1) ≫ K₁.d 1 2 = 0 := by
    refine AddCommGrpCat.ext fun m => ?_
    have h0 : K₁.d 1 2 r1 = 0 := hr1d
    change (K₁.d 1 2).hom ((zmultiplesHom (K₁.X 1) r1) m) = 0
    erw [zmultiplesHom_apply, map_zsmul, h0, smul_zero]
  let z : K₁.cycles 1 := K₁.liftCycles (AddCommGrpCat.ofHom (zmultiplesHom (K₁.X 1) r1)) 2 (by simp)
    hcyc (1 : ℤ)
  have hz : K₁.iCycles 1 z = r1 := by
    change (K₁.liftCycles _ 2 _ hcyc ≫ K₁.iCycles 1) (1 : ℤ) = r1
    rw [HomologicalComplex.liftCycles_i]
    exact (zmultiplesHom_apply _ r1 1).trans (one_zsmul r1)
  refine ⟨K₁.homologyπ 1 z, fun P hPV hc => ?_⟩
  let φ := (secFunctor (G.obj Y.X₁)).map (homOfLE hPV).op
  have hc' : ((secFunctor (G.obj Y.X₁)).obj (op P)).homologyπ 1
      (HomologicalComplex.cyclesMap φ 1 z) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    exact hc
  obtain ⟨w, hw'⟩ : ∃ w : (secΓ (op P)).obj ((G.obj Y.X₁).X 0),
      (secΓ (op P)).map ((G.obj Y.X₁).d 0 1) w = rs hPV _ r1 := by
    obtain ⟨w, hw⟩ := exists_d_eq_of_homologyπ_eq_zero _ _ hc'
    refine ⟨w, hw.trans ?_⟩
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      hz]
    rfl
  -- correct the lift of the germs
  let a0' := rs hPV _ a0 - (secΓ (op P)).map ((G.map Y.f).f 0) w
  have hda0' : (secΓ (op P)).map ((G.obj Y.X₂).d 0 1) a0' = 0 := by
    simp only [a0', map_sub]
    have e1 : (secΓ (op P)).map ((G.obj Y.X₂).d 0 1) (rs hPV _ a0) =
        (secΓ (op P)).map ((G.map Y.f).f 1) (rs hPV _ r1) := by
      rw [← restrict_secΓ_map, ← hr1, restrict_secΓ_map]
    have e2 : (secΓ (op P)).map ((G.obj Y.X₂).d 0 1) ((secΓ (op P)).map ((G.map Y.f).f 0) w) =
        (secΓ (op P)).map ((G.map Y.f).f 1) (rs hPV _ r1) := by
      rw [secΓ_map_map, (G.map Y.f).comm 0 1, ← secΓ_map_map, hw']
    rw [e1, e2, sub_self]
  obtain ⟨a, ha⟩ := exists_godementUnit_eq Y.X₂ (op P) a0' hda0'
  refine ⟨a, godementUnit_app_hom_app_injective Y.X₃ (op P) ?_⟩
  change (secΓ (op P)).map (unitG0 Y.X₃) ((secΓ (op P)).map Y.g a) =
    (secΓ (op P)).map (unitG0 Y.X₃) (rs hPV _ s)
  have hnat : ∀ {F F' : TopCat.Sheaf AddCommGrpCat.{0} X} (ψ : F ⟶ F'),
      unitG0 F ≫ (G.map ψ).f 0 = ψ ≫ unitG0 F' := fun ψ => ((godementUnit X).naturality ψ).symm
  rw [secΓ_map_map, ← hnat, ← secΓ_map_map]
  change (secΓ (op P)).map ((G.map Y.g).f 0) ((secΓ (op P)).map ((godementUnit X).app Y.X₂) a) = _
  rw [ha]
  simp only [a0', map_sub]
  have e1 : (secΓ (op P)).map ((G.map Y.g).f 0) (rs hPV _ a0) =
      (secΓ (op P)).map (unitG0 Y.X₃) (rs hPV _ s) := by
    rw [← restrict_secΓ_map, ha0, restrict_secΓ_map]
  have e2 : (secΓ (op P)).map ((G.map Y.g).f 0) ((secΓ (op P)).map ((G.map Y.f).f 0) w) = 0 := by
    rw [secΓ_map_map, ← HomologicalComplex.comp_f, ← Functor.map_comp, Y.zero, Functor.map_zero,
      HomologicalComplex.zero_f, Functor.map_zero]
    rfl
  rw [e1, e2, sub_zero]

/-! ### Lifting through a presentation near a block -/

/-- An epimorphism of sheaves of modules is an epimorphism of the underlying sheaves of abelian
groups: its sheafified presheaf cokernel vanishes. -/
private lemma epi_toSheaf_map {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} [HasWeakSheafify J AddCommGrpCat.{0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {M N : SheafOfModules.{0} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((SheafOfModules.toSheaf R).map φ) := by
  let L := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let s := PresheafOfModules.sheafification (J := J) (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 R.obj)
  let g := L.map φ
  have e : Arrow.mk (s.map g) ≅ Arrow.mk φ :=
    Arrow.isoMk (asIso (adj.counit.app M)) (asIso (adj.counit.app N))
      ((adj.counit.naturality φ).symm)
  have hsg : Epi (s.map g) := ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff e).2 ‹_›
  have hπ : s.map (Limits.cokernel.π g) = 0 := by
    rw [← cancel_epi (s.map g), ← s.map_comp, Limits.cokernel.condition, s.map_zero,
      Limits.comp_zero]
  let P := PresheafOfModules.toPresheaf R.obj
  let Sh := presheafToSheaf J AddCommGrpCat.{0}
  have hc := Limits.CokernelCofork.mapIsColimit _
    (Limits.CokernelCofork.mapIsColimit _ (Limits.cokernelIsCokernel g) P) Sh
  have hπ' : Sh.map (P.map (Limits.cokernel.π g)) = 0 := by
    have := congrArg (SheafOfModules.toSheaf R).map hπ
    rw [Functor.map_zero] at this
    exact this
  have hc0 : Limits.IsColimit (Limits.CokernelCofork.ofπ (0 : Sh.obj (P.obj (L.obj N)) ⟶ _)
      (show Sh.map (P.map g) ≫ 0 = 0 by simp)) :=
    Limits.IsColimit.ofIsoColimit hc (Limits.Cofork.ext (Iso.refl _) (by simp [hπ']))
  have h1 : Epi (Sh.map (P.map g)) := NormalMonoCategory.epi_of_zero_cokernel _ _ hc0
  have e' : Arrow.mk (Sh.map (P.map g)) ≅ Arrow.mk ((SheafOfModules.toSheaf R).map φ) :=
    (SheafOfModules.toSheaf R).mapArrow.mapIso e
  exact ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff e').1 h1

/-- A kernel sequence `0 → K → M → N → 0` of an epimorphism of sheaves of modules is a short
exact sequence of sheaves of abelian groups. -/
private lemma shortExact_map_toSheaf_kernel {C : Type} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}} [HasWeakSheafify J AddCommGrpCat.{0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}] {K M N : SheafOfModules.{0} R} (i : K ⟶ M)
    (φ : M ⟶ N) (w : i ≫ φ = 0) (hi : Limits.IsLimit (Limits.KernelFork.ofι i w)) [Epi φ] :
    ((ShortComplex.mk i φ w).map (SheafOfModules.toSheaf R)).ShortExact := by
  have hS0 : (ShortComplex.mk i φ w).Exact := ShortComplex.exact_of_f_is_kernel _ hi
  haveI : Mono i := Limits.mono_of_isLimit_fork hi
  haveI : Epi ((SheafOfModules.toSheaf R).map φ) := epi_toSheaf_map φ
  haveI : Mono ((SheafOfModules.toSheaf R).map i) := inferInstance
  haveI : Limits.PreservesLimit (Limits.parallelPair φ 0) (SheafOfModules.toSheaf R) :=
    inferInstance
  exact ShortComplex.ShortExact.mk'
    (hS0.map_of_mono_of_preservesKernel (SheafOfModules.toSheaf R) ‹_› ‹_›) ‹_› ‹_›

/-- The open `V ∩ W` of `D`, as an open of the image `W' ⊆ ℂⁿ` of `W`. -/
private noncomputable abbrev imagePull {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (W : Opens (TopCat.of D))
    (V : Opens (TopCat.of D)) : Opens (TopCat.of (imageOpens W)) :=
  (Opens.map (TopCat.ofHom ⟨fun y => ⟨y.1, mem_of_mem_imageOpens y.2⟩, by fun_prop⟩ :
    TopCat.of (imageOpens W) ⟶ TopCat.of D)).obj V

private lemma imageOverEquivalence_left_le {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (W : Opens (TopCat.of D)) {V : Opens (TopCat.of D)} {P : Opens (TopCat.of (imageOpens W))}
    (hP : P ≤ imagePull W V) : ((imageOverEquivalence W).functor.obj P).left ≤ V := by
  intro x hx
  obtain ⟨h, hP'⟩ := (imageOverEquivalence_functor_obj_left W P x).1 hx
  exact hP hP'

private lemma mem_imageOverEquivalence_left {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (W : Opens (TopCat.of D)) {P : Opens (TopCat.of (imageOpens W))} {x : D} (hxW : x ∈ W)
    (hxP : (⟨x.1, x, hxW, rfl⟩ : imageOpens W) ∈ P) :
    x ∈ ((imageOverEquivalence W).functor.obj P).left :=
  (imageOverEquivalence_functor_obj_left W P x).2 ⟨_, hxP⟩

/-- **Lifting through a presentation near a block.** Let `f : 𝒪_Wᵖ → 𝒮|_W` be a surjection on an
open `W ⊆ D` containing a block `K ⊆ D`. A section of `𝒮` over an open `V ⊇ K` lifts through `f`
on an open subset of `V ∩ W` containing `K`: read on the image `W' ⊆ ℂⁿ` of `W`, the obstruction
lies in `H¹` of the kernel of `f`, a coherent sheaf, and dies near `K`
(`cartan_compact_blocks` (3)). -/
private theorem exists_lift_near_block {n : ℕ} (a b c d : Fin n → ℝ)
    {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T)
    (W : Opens (TopCat.of D)) {p : ℕ} (f : SheafOfModules.free (Fin p) ⟶ T.over W) [Epi f]
    (ε : ℝ) (hKD : closedBlock a b c d ε ⊆ (D : Set (EuclideanSpace ℂ (Fin n))))
    (hKW : (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ W) (V : Opens (TopCat.of D))
    (hKV : (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ V) (s : T.val.obj (op V)) :
    ∃ (P : Over W) (hPV : P.left ≤ V), (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ P.left ∧
      ∃ x : (SheafOfModules.free (Fin p)).val.obj (op P),
        f.val.app (op P) x = T.val.map (homOfLE hPV).op s := by
  let E := imageModuleEquivalence W
  let φ := (imageFreeIso W (Fin p)).hom ≫ E.functor.map f
  haveI : Epi φ := epi_comp' inferInstance inferInstance
  have hR : IsCoherentModule (Limits.kernel φ) :=
    isCoherentModule_kernel_imageFreeIso_hom_comp W T hT f
  let Y : ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
      AddCommGrpCat.{0}) :=
    (ShortComplex.mk (Limits.kernel.ι φ) φ (Limits.kernel.condition φ)).map
      (SheafOfModules.toSheaf (holomorphicRingCatSheaf n (imageOpens W)))
  have hY : Y.ShortExact := shortExact_map_toSheaf_kernel _ φ _ (Limits.kernelIsKernel φ)
  let V' := imagePull W V
  let Lv := (imageOverEquivalence W).functor.obj V'
  have hLV : Lv.left ≤ V := imageOverEquivalence_left_le W le_rfl
  let s' : (secΓ (op V')).obj Y.X₃ := T.val.map (homOfLE hLV).op s
  obtain ⟨cl, hcl⟩ := exists_godement_class_lift Y hY V' s'
  obtain ⟨y, hy⟩ := godementTower_restriction_eq_zero_nat Y.X₁ V' 1 cl
  have hblock : {z : EuclideanSpace ℂ (Fin n) | ∀ i, z i ∈ Set.Icc (a i + ε) (b i - ε) ×ℂ
      Set.Icc (c i + ε) (d i - ε)} ⊆ imageOpens W := fun z hz =>
    ⟨⟨z, hKD hz⟩, hKW hz, rfl⟩
  have h3 := (cartan_compact_blocks (imageOpens W) (fun i => a i + ε)
    (fun i => b i - ε) (fun i => c i + ε) (fun i => d i - ε) hblock (Limits.kernel φ) hR).2.2
  refine Exists.elim (h3 V' (fun z hz => hKV hz) ((1 : ℕ) : ℤ) (by norm_num) y)
    fun P hP => Exists.elim hP fun hPV' hP => ?_
  have hKP := hP.2.1
  refine Exists.elim (hcl P hPV' (hy P hPV' hP.2.2)) fun x' hx' => ?_
  refine ⟨(imageOverEquivalence W).functor.obj P, imageOverEquivalence_left_le W hPV',
    fun x hx => mem_imageOverEquivalence_left W (hKW hx) (hKP hx),
    (imageFreeIso W (Fin p)).hom.val.app (op P) x', ?_⟩
  refine hx'.trans ?_
  have h2 : ((imageOverEquivalence W).functor.obj P).left ≤ Lv.left :=
    ((imageOverEquivalence W).functor.map (homOfLE hPV')).left.le
  exact (PresheafOfModules.map_comp_apply T.val (homOfLE hLV).op (homOfLE h2).op s).symm

/-! ### Presentations near blocks -/

/-- Restriction of a linear combination of sections of a presheaf of modules. -/
private lemma map_sum_smul {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{0}}
    (M : PresheafOfModules.{0} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) {p : ℕ} (v : Fin p → R.obj X)
    (m : Fin p → M.obj X) :
    M.map f (∑ k, v k • m k) = ∑ k, R.map f (v k) • M.map f (m k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => M.map_smul f (v k) (m k)

/-- Restriction along `W ≤ U` factors through any `V` with `W ≤ V ≤ U`. -/
private lemma map_homOfLE_eq {T : TopCat.{0}} {R : (Opens T)ᵒᵖ ⥤ RingCat.{0}}
    (M : PresheafOfModules.{0} R) {U V W : Opens T} (h : W ≤ U) (h1 : V ≤ U) (h2 : W ≤ V)
    (x : M.obj (op U)) :
    M.map (homOfLE h).op x = M.map (homOfLE h2).op (M.map (homOfLE h1).op x) := by
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- A family `g` of sections of `T` over `W` *presents `T` near blocks*: a section of `T` over an
open set containing a block `K ⊆ W` is, on a smaller open set containing `K`, a combination of the
`g k` with holomorphic coefficients; and over every open `U ⊆ W` the relations among the `g k`
form a closed set for the topology of compact convergence. -/
private def IsBlockPresentation {n : ℕ} (a b c d : Fin n → ℝ) {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (W : Opens (TopCat.of D)) {p : ℕ}
    (g : Fin p → T.val.obj (op W)) : Prop :=
  (∀ ε : ℝ, closedBlock a b c d ε ⊆ (D : Set (EuclideanSpace ℂ (Fin n))) →
    (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ W →
    ∀ V : Opens (TopCat.of D), (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ V →
    ∀ s : T.val.obj (op V), ∃ (P : Opens (TopCat.of D)) (hPV : P ≤ V) (hPW : P ≤ W),
      (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ P ∧
      ∃ v : Fin p → (holomorphicRingCatSheaf n D).obj.obj (op P),
        T.val.map (homOfLE hPV).op s = ∑ k, v k • T.val.map (homOfLE hPW).op (g k)) ∧
  ∀ (U : Opens (TopCat.of D)) (hU : U ≤ W),
    @IsClosed (Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U))
      (@Pi.topologicalSpace _ _ fun _ => (holomorphicCompactConvergence U).toTopologicalSpace)
      {v | ∑ k, v k • T.val.map (homOfLE hU).op (g k) = 0}

/-! ### Closedness of the relations of a presentation -/

/-- The value of a morphism out of a free module on a tautological section. -/
private theorem val_app_freeSection {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} [HasWeakSheafify J AddCommGrpCat.{0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}] {I : Type} {N : SheafOfModules.{0} R}
    (ψ : SheafOfModules.free I ⟶ N) (i : I) (X : Cᵒᵖ) :
    ψ.val.app X ((SheafOfModules.freeSection (R := R) i).1 X) =
      (SheafOfModules.ιFree i ≫ ψ).val.app X
        (show (SheafOfModules.unit R).val.obj X from (1 : R.obj.obj X)) := by
  change (SheafOfModules.ιFree i ≫ 𝟙 _ ≫ ψ).val.app X _ = _
  rw [Category.id_comp]

/-- Convergence for the topology of compact convergence is uniform convergence on compact sets. -/
private lemma tendstoUniformlyOn_of_tendsto_holomorphic {n : ℕ}
    {D : Opens (EuclideanSpace ℂ (Fin n))} {U : Opens (TopCat.of D)}
    {F : ℕ → 𝒪[n, D].presheaf.obj (op U)} {f : 𝒪[n, D].presheaf.obj (op U)}
    (h : @Filter.Tendsto _ _ F Filter.atTop
      (@nhds _ (holomorphicCompactConvergence U).toTopologicalSpace f))
    (K : Set U) (hK : IsCompact K) :
    TendstoUniformlyOn (fun m (y : U) => F m y) (fun y => f y) Filter.atTop K := by
  letI := holomorphicCompactConvergence U
  have hc : Continuous (holomorphicToUniformOnFun U) := continuous_induced_dom
  have h1 := (hc.tendsto f).comp h
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 h1) K hK

/-- Restriction of holomorphic functions on `U` to the open `imagePull W U` of `W' ⊆ ℂⁿ`. -/
private noncomputable abbrev imagePullRingHom {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (W U : Opens (TopCat.of D)) :=
  precompRingHom (fun y : imagePull W U => (⟨⟨y.1.1, mem_of_mem_imageOpens y.1.2⟩, y.2⟩ : U))
    (contMDiff_of_val_val _ fun _ => rfl)

/-- The generators of `f`, read on an open `Q` of the image `W' ⊆ ℂⁿ` of `W`. -/
private lemma imageFree_app_freeSection {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (W : Opens (TopCat.of D)) {p : ℕ}
    (f : SheafOfModules.free (Fin p) ⟶ T.over W) (g : Fin p → T.val.obj (op W))
    (hfe : ∀ (P : Over W) (k : Fin p),
      f.val.app (op P) ((SheafOfModules.freeSection (R := (holomorphicRingCatSheaf n D).over W)
        k).1 (op P)) = T.val.map (homOfLE P.hom.le).op (g k))
    (Q : Opens (TopCat.of (imageOpens W))) (k : Fin p) :
    ((imageFreeIso W (Fin p)).hom ≫ (imageModuleEquivalence W).functor.map f).val.app (op Q)
      ((SheafOfModules.freeSection (R := holomorphicRingCatSheaf n (imageOpens W)) k).1 (op Q)) =
      T.val.map (homOfLE ((imageOverEquivalence W).functor.obj Q).hom.le).op (g k) := by
  let E := imageModuleEquivalence W
  let φ := (imageFreeIso W (Fin p)).hom ≫ E.functor.map f
  have h : SheafOfModules.ιFree k ≫ φ =
      (imageUnitIso W).hom ≫ E.functor.map (SheafOfModules.ιFree k ≫ f) := by
    rw [← Category.assoc, show imageFreeIso W (Fin p) = SheafOfModules.mapFreeIso E.functor
      (Fin p) (imageUnitIso W) from rfl, SheafOfModules.ιFree_mapFreeIso_hom, Category.assoc,
      ← Functor.map_comp]
  refine (val_app_freeSection φ k (op Q)).trans ?_
  refine (congrArg (fun ψ : SheafOfModules.unit (holomorphicRingCatSheaf n (imageOpens W)) ⟶
    E.functor.obj (T.over W) => ψ.val.app (op Q)
      (show (SheafOfModules.unit (holomorphicRingCatSheaf n (imageOpens W))).val.obj (op Q)
        from (1 : (holomorphicRingCatSheaf n (imageOpens W)).obj.obj (op Q)))) h).trans ?_
  exact Eq.trans rfl ((val_app_freeSection f k
    (op ((imageOverEquivalence W).functor.obj Q))).symm.trans (hfe _ k))

/-- A vector of `𝒪(U)ᵖ`, combined with the generators of `f` and read on `imagePull W U`. -/
private lemma imageFree_app_sum {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (W : Opens (TopCat.of D)) {p : ℕ}
    (f : SheafOfModules.free (Fin p) ⟶ T.over W) (g : Fin p → T.val.obj (op W))
    (hfe : ∀ (P : Over W) (k : Fin p),
      f.val.app (op P) ((SheafOfModules.freeSection (R := (holomorphicRingCatSheaf n D).over W)
        k).1 (op P)) = T.val.map (homOfLE P.hom.le).op (g k))
    (U : Opens (TopCat.of D)) (hU : U ≤ W)
    (w : Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U)) :
    ((imageFreeIso W (Fin p)).hom ≫ (imageModuleEquivalence W).functor.map f).val.app
      (op (imagePull W U))
      (∑ k, (show (holomorphicRingCatSheaf n (imageOpens W)).obj.obj (op (imagePull W U))
        from imagePullRingHom W U (w k)) •
        (show (SheafOfModules.free (R := holomorphicRingCatSheaf n
          (imageOpens W)) (Fin p)).val.obj (op (imagePull W U)) from
            (SheafOfModules.freeSection k).1 (op (imagePull W U)))) =
      T.val.map (homOfLE (imageOverEquivalence_left_le W le_rfl :
        ((imageOverEquivalence W).functor.obj (imagePull W U)).left ≤ U)).op
        (∑ k, w k • T.val.map (homOfLE hU).op (g k)) := by
  let φ := (imageFreeIso W (Fin p)).hom ≫ (imageModuleEquivalence W).functor.map f
  refine (map_sum (φ.val.app (op (imagePull W U))).hom _ _).trans
    (Eq.trans ?_ (map_sum_smul T.val _ w _).symm)
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (map_smul (φ.val.app (op (imagePull W U))).hom _ _).trans ?_
  refine (congrArg _ (imageFree_app_freeSection T W f g hfe (imagePull W U) k)).trans ?_
  exact congrArg _ (map_homOfLE_eq T.val
    ((imageOverEquivalence W).functor.obj (imagePull W U)).hom.le hU
    (imageOverEquivalence_left_le W le_rfl) (g k))

open OkaCoherence in
/-- **The relations of a presentation are closed.** Let `f : 𝒪_Wᵖ → 𝒮|_W` be a surjection with
generators `g k`. Over every open `U ⊆ W`, the vectors `v ∈ 𝒪(U)ᵖ` with `∑ v k • g k = 0` form a
closed set for the topology of compact convergence: read on the image `W' ⊆ ℂⁿ` of `W`, they are
the sections of the coherent kernel of `f`, closed under uniform convergence on compact sets
(`coherent_analytic_toolkit` (5)). -/
private theorem isClosed_relations {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T)
    (W : Opens (TopCat.of D)) {p : ℕ} (f : SheafOfModules.free (Fin p) ⟶ T.over W)
    (g : Fin p → T.val.obj (op W))
    (hfe : ∀ (P : Over W) (k : Fin p),
      f.val.app (op P) ((SheafOfModules.freeSection (R := (holomorphicRingCatSheaf n D).over W)
        k).1 (op P)) = T.val.map (homOfLE P.hom.le).op (g k))
    (U : Opens (TopCat.of D)) (hU : U ≤ W) :
    @IsClosed (Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U))
      (@Pi.topologicalSpace _ _ fun _ => (holomorphicCompactConvergence U).toTopologicalSpace)
      {v | ∑ k, v k • T.val.map (homOfLE hU).op (g k) = 0} := by
  letI : UniformSpace ((holomorphicRingCatSheaf n D).obj.obj (op U)) :=
    holomorphicCompactConvergence U
  haveI : FirstCountableTopology ((holomorphicRingCatSheaf n D).obj.obj (op U)) :=
    firstCountableTopology_holomorphicCompactConvergence U
  refine IsSeqClosed.isClosed fun v₀ v hv hlim => ?_
  let E := imageModuleEquivalence W
  let φ := (imageFreeIso W (Fin p)).hom ≫ E.functor.map f
  have hR : IsCoherentModule (Limits.kernel φ) :=
    isCoherentModule_kernel_imageFreeIso_hom_comp W T hT f
  let U' := imagePull W U
  let LU := (imageOverEquivalence W).functor.obj U'
  have hLU : LU.left ≤ U := imageOverEquivalence_left_le W le_rfl
  have hULU : U ≤ LU.left := fun x hx => mem_imageOverEquivalence_left W (hU hx) hx
  let θ : U' → U := fun y => ⟨⟨y.1.1, mem_of_mem_imageOpens y.1.2⟩, y.2⟩
  let pb := imagePullRingHom W U
  have key : ∀ w : Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U),
      φ.val.app (op U') (∑ k, (show (holomorphicRingCatSheaf n (imageOpens W)).obj.obj (op U')
        from pb (w k)) • (show (SheafOfModules.free (R := holomorphicRingCatSheaf n
          (imageOpens W)) (Fin p)).val.obj (op U') from (SheafOfModules.freeSection k).1 (op U'))) =
      T.val.map (homOfLE hLU).op (∑ k, w k • T.val.map (homOfLE hU).op (g k)) :=
    imageFree_app_sum T W f g hfe U hU
  -- the vectors `v₀ m` are relations on `U'`
  have h1 : ∀ m, ∃ r : (Limits.kernel φ).val.obj (op U'),
      ((Limits.kernel.ι φ).val.app (op U')).hom r = ∑ j,
        (show (holomorphicRingCatSheaf n (imageOpens W)).obj.obj (op U') from pb (v₀ m j)) •
        (show (SheafOfModules.free (R := holomorphicRingCatSheaf n (imageOpens W)) (Fin p)).val.obj
          (op U') from (SheafOfModules.freeSection j).1 (op U')) := by
    intro m
    refine exists_kernel_ι_app_eq φ (op U') _ ?_
    have hm : ∑ k, v₀ m k • T.val.map (homOfLE hU).op (g k) = 0 := hv m
    exact (key _).trans ((congrArg _ hm).trans (map_zero _))
  have h2 : ∀ (j : Fin p) (K : Set U'), IsCompact K →
      TendstoUniformlyOn (fun m (y : U') => pb (v₀ m j) y) (fun y => pb (v j) y)
        Filter.atTop K := by
    intro j K hK
    have hc : Continuous θ := by fun_prop
    have hj : Filter.Tendsto (fun m => v₀ m j) Filter.atTop (nhds (v j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hlim
    have := (tendstoUniformlyOn_of_tendsto_holomorphic hj (θ '' K) (hK.image hc)).comp θ
    exact this.mono (Set.subset_preimage_image θ K)
  have h5 := (coherent_analytic_toolkit (n := n) (M := imageOpens W)).2.2.2.2.2.2
  refine Exists.elim (h5 p (Limits.kernel φ) (Limits.kernel.ι φ) hR U' (fun m j => pb (v₀ m j))
    (fun j => pb (v j)) h1 h2) fun r hr => ?_
  have h3 : T.val.map (homOfLE hLU).op (∑ k, v k • T.val.map (homOfLE hU).op (g k)) = 0 :=
    (key v).symm.trans ((congrArg _ hr.symm).trans (kernel_condition_app φ (op U') r))
  change ∑ k, v k • T.val.map (homOfLE hU).op (g k) = 0
  have h5 : ∀ x : T.val.obj (op U),
      T.val.map (homOfLE hULU).op (T.val.map (homOfLE hLU).op x) = x :=
    fun x => by
      rw [← map_homOfLE_eq T.val le_rfl hLU hULU]
      exact ConcreteCategory.congr_hom (T.val.presheaf.map_id (op U)) x
  exact (h5 _).symm.trans ((congrArg _ h3).trans (map_zero _))

/-- **Presentations near blocks.** A coherent sheaf on the box has, near every block, a finite
family of sections presenting it near blocks: the generators of a surjection `𝒪_Wᵖ → 𝒮|_W`
(`cartan_compact_blocks` (2)). Lifting through the surjection near a block is possible because
the obstruction in `H¹` of the kernel dies near the block (`cartan_compact_blocks` (3)); the
relations are closed by `coherent_analytic_toolkit` (5). -/
private theorem exists_blockPresentation {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T) (ε : ℝ)
    (hK : closedBlock a b c d ε ⊆ (D : Set (EuclideanSpace ℂ (Fin n)))) :
    ∃ (W : Opens (TopCat.of D)) (p : ℕ) (g : Fin p → T.val.obj (op W)),
      (Subtype.val ⁻¹' closedBlock a b c d ε : Set D) ⊆ W ∧ IsBlockPresentation a b c d T W g := by
  obtain ⟨-, ⟨W, hKW, p, f, hf⟩, -⟩ := cartan_compact_blocks D (fun i => a i + ε)
    (fun i => b i - ε) (fun i => c i + ε) (fun i => d i - ε) hK T hT
  let t := (T.over W).freeHomEquiv f
  let g : Fin p → T.val.obj (op W) := fun k => (t k).1 (op (Over.mk (𝟙 W)))
  have hft : f = (T.over W).freeHomEquiv.symm t := ((T.over W).freeHomEquiv.symm_apply_apply f).symm
  have hfe : ∀ (P : Over W) (k : Fin p),
      f.val.app (op P) ((SheafOfModules.freeSection (R := (holomorphicRingCatSheaf n D).over W)
        k).1 (op P)) = T.val.map (homOfLE P.hom.le).op (g k) := by
    intro P k
    have h1 := congrArg (fun σ : (T.over W).sections => σ.1 (op P))
      (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection (M := T.over W) t k)
    have h2 := PresheafOfModules.sections_property (t k)
      (Over.homMk (U := P) (V := Over.mk (𝟙 W)) P.hom (by simp)).op
    rw [hft]
    exact h1.trans h2.symm
  refine ⟨W, p, g, hKW, fun ε' hK'D hK'W V hK'V s => ?_, fun U hU => ?_⟩
  · obtain ⟨P, hPV, hKP, x, hx⟩ := exists_lift_near_block a b c d T hT W f ε' hK'D hK'W V
      hK'V s
    obtain ⟨v, rfl⟩ := MMP.exists_eq_sum_smul_freeSection (op P) x
    refine ⟨P.left, hPV, P.hom.le, hKP, v, hx.symm.trans ?_⟩
    refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
    exact (map_smul _ _ _).trans (congrArg _ (hfe P k))
  · exact isClosed_relations T hT W f g hfe U hU

/-- The combinations `v ↦ ∑ vₖ gₖ|_U` of sections `gₖ` of `T` over `W ⊇ U`. -/
private noncomputable abbrev genComb {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) {U W : Opens (TopCat.of D)}
    (h : U ≤ W) {p : ℕ} (g : Fin p → T.val.obj (op W)) :
    (Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U)) →ₗ[
      (holomorphicRingCatSheaf n D).obj.obj (op U)] T.val.obj (op U) :=
  Fintype.linearCombination _ fun k => T.val.map (homOfLE h).op (g k)

/-- Restriction of a combination of the `gₖ`. -/
private lemma map_genComb {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) {V U W : Opens (TopCat.of D)}
    (hVU : V ≤ U) (h : U ≤ W) {p : ℕ} (g : Fin p → T.val.obj (op W))
    (y : Fin p → (holomorphicRingCatSheaf n D).obj.obj (op U)) :
    T.val.map (homOfLE hVU).op (genComb T h g y) = ∑ k, (holomorphicRingCatSheaf n D).obj.map
      (homOfLE hVU).op (y k) • T.val.map (homOfLE (hVU.trans h)).op (g k) := by
  refine (map_sum_smul T.val _ y _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [← map_homOfLE_eq T.val (hVU.trans h) h hVU]
  rfl

/-- A section which is a combination of the `gₖ` on `P` restricts, on `U ≤ P`, into the
combinations of the `gₖ`. -/
private lemma map_mem_range_genComb {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) {V P U W : Opens (TopCat.of D)}
    (hPV : P ≤ V) (hPW : P ≤ W) (hUP : U ≤ P) {p : ℕ}
    (g : Fin p → T.val.obj (op W)) (x : T.val.obj (op V))
    (v : Fin p → (holomorphicRingCatSheaf n D).obj.obj (op P))
    (hv : T.val.map (homOfLE hPV).op x = ∑ k, v k • T.val.map (homOfLE hPW).op (g k)) :
    T.val.map (homOfLE (hUP.trans hPV)).op x ∈ LinearMap.range (genComb T (hUP.trans hPW) g) := by
  refine ⟨fun k => (holomorphicRingCatSheaf n D).obj.map (homOfLE hUP).op (v k), ?_⟩
  rw [map_homOfLE_eq T.val _ hPV hUP, hv]
  refine ((map_sum_smul T.val _ v _).trans (Finset.sum_congr rfl fun k _ => ?_)).symm
  rw [← map_homOfLE_eq T.val (hUP.trans hPW) hPW hUP]
  rfl

/-- The restricted generators are combinations of the generators. -/
private lemma map_mem_range_genComb_self {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) {U W : Opens (TopCat.of D)}
    (h : U ≤ W) {p : ℕ} (g : Fin p → T.val.obj (op W)) (k : Fin p) :
    T.val.map (homOfLE h).op (g k) ∈ LinearMap.range (genComb T h g) :=
  ⟨Pi.single k 1, by
    change ∑ i, Pi.single k 1 i • T.val.map (homOfLE h).op (g i) = _
    rw [Finset.sum_eq_single k
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp), Pi.single_eq_same,
      one_smul]⟩

/-- The topology on the sections of a coherent sheaf along the exhaustion. There are subgroups
`Q_j ⊆ 𝒮(U_j)` containing the images of the restrictions `𝒮(U_{j+1}) → 𝒮(U_j)` and stable under
all restrictions, with complete, Hausdorff, first countable group uniformities for which the
restrictions `Q_j → Q_i` are continuous and `Q_{j+1} → Q_j` has dense image.

`Q_j` is the image of `𝒪(U_j)ᵖ → 𝒮(U_j)`, `v ↦ ∑ vₖ gₖ`, for the generators `gₖ` of a
presentation of `𝒮` near the block `K_{j+1} ⊇ U_{j+1}` (`exists_blockPresentation`), with the
quotient uniformity (`MMP.Topology.exists_uniformSpace_range_of_isClosed_ker`; the relations are
closed). A section over `U_{j+1}` lifts through the presentation near `K_j ⊇ U_j`, so the
restrictions land in `Q_j`. The restrictions `Q_j → Q_i` are continuous because they are induced
through the open quotient map `𝒪(U_j)ᵖ → Q_j` by a continuous map of coefficients. Density is
Runge's theorem for `𝒪` (`denseRange_holomorphic_restrict`), together with the fact that the
generators of level `j + 1` lie in `Q_{j+1}` once restricted to `U_{j+1}`, since they lift
through the presentation of level `j + 2`. -/
private theorem exists_subtowerUniformity {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T) :
    ∃ Q : ∀ j, AddSubgroup (((SheafOfModules.toSheaf _).obj T).obj.obj
        (op (exhaustion a b c d D j))),
      (∀ j x, exhaustionRes a b c d D T (Nat.le_succ j) x ∈ Q j) ∧
      ∃ (hQ : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) x, x ∈ Q j → exhaustionRes a b c d D T h x ∈ Q i)
        (U : ∀ j, UniformSpace (Q j)),
        (∀ j, @IsUniformAddGroup _ (U j) _) ∧ (∀ j, @CompleteSpace _ (U j)) ∧
        (∀ j, @T2Space _ (U j).toTopologicalSpace) ∧
        (∀ j, @FirstCountableTopology _ (U j).toTopologicalSpace) ∧
        (∀ ⦃i j : ℕ⦄ (h : i ≤ j), @Continuous (Q j) (Q i) (U j).toTopologicalSpace
          (U i).toTopologicalSpace fun x => ⟨exhaustionRes a b c d D T h x.1, hQ h x.1 x.2⟩) ∧
        ∀ j, @DenseRange (Q j) (U j).toTopologicalSpace (Q (j + 1))
          fun x => ⟨exhaustionRes a b c d D T (Nat.le_succ j) x.1, hQ (Nat.le_succ j) x.1 x.2⟩ := by
  let Ut := exhaustion a b c d D
  let K : ℕ → Set D := fun j => Subtype.val ⁻¹' closedBlock a b c d (shrink j)
  have hKD : ∀ j, closedBlock a b c d (shrink j) ⊆ (D : Set (EuclideanSpace ℂ (Fin n))) :=
    fun j => hD ▸ closedBlock_shrink_subset_box a b c d j
  have hUK : ∀ j, (Ut j : Set D) ⊆ K j := fun j =>
    Set.preimage_mono (openBlock_subset_closedBlock a b c d _)
  have hKU : ∀ j, K j ⊆ Ut (j + 1) := fun j =>
    Set.preimage_mono (closedBlock_subset_openBlock a b c d (shrink_succ_lt j))
  have hKK : ∀ j, K j ⊆ K (j + 1) := fun j => (hKU j).trans (hUK (j + 1))
  choose W p g hKW hpres using fun j => exists_blockPresentation a b c d D T hT (shrink j) (hKD j)
  have hUW : ∀ j, Ut j ≤ W (j + 1) := fun j => (hUK j).trans ((hKK j).trans (hKW (j + 1)))
  let ψ : ∀ j, (Fin (p (j + 1)) → (holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) →ₗ[
      (holomorphicRingCatSheaf n D).obj.obj (op (Ut j))] T.val.obj (op (Ut j)) := fun j =>
    genComb T (hUW j) (g (j + 1))
  have hψ : ∀ j v, ψ j v = ∑ k, v k • T.val.map (homOfLE (hUW j)).op (g (j + 1) k) :=
    fun j v => rfl
  let Q : ∀ j, AddSubgroup (((SheafOfModules.toSheaf _).obj T).obj.obj (op (Ut j))) := fun j =>
    (LinearMap.range (ψ j)).toAddSubgroup
  have hψres : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) y, T.val.map (homOfLE (exhaustion_mono a b c d D h)).op
      (ψ j y) = ∑ k, (holomorphicRingCatSheaf n D).obj.map
        (homOfLE (exhaustion_mono a b c d D h)).op (y k) •
        T.val.map (homOfLE ((exhaustion_mono a b c d D h).trans (hUW j))).op (g (j + 1) k) :=
    fun i j h y => map_genComb T (exhaustion_mono a b c d D h) (hUW j) (g (j + 1)) y
  -- sections over `U_{j+1}` restrict into `Q_j`
  -- a section near `K_j` restricts into `Q_j`: it lifts through the presentation of level `j + 1`
  have hlift : ∀ j (V : Opens (TopCat.of D)) (hKV : K j ⊆ V) (hUV : Ut j ≤ V)
      (x : T.val.obj (op V)), T.val.map (homOfLE hUV).op x ∈ LinearMap.range (ψ j) := by
    intro j V hKV hUV x
    refine Exists.elim ((hpres (j + 1)).1 (shrink j) (hKD j) ((hKK j).trans (hKW (j + 1))) V hKV x)
      fun P h => Exists.elim h fun hPV h => Exists.elim h fun hPW h => Exists.elim h.2 fun v hv =>
        map_mem_range_genComb T hPV hPW ((hUK j).trans h.1) (g (j + 1)) x v hv
  have hρ' : ∀ j (x : T.val.obj (op (Ut (j + 1)))),
      T.val.map (homOfLE (exhaustion_mono a b c d D (Nat.le_succ j))).op x ∈
        LinearMap.range (ψ j) := fun j => hlift j _ (hKU j) _
  have hρ : ∀ j x, exhaustionRes a b c d D T (Nat.le_succ j) x ∈ Q j := fun j x => hρ' j x
  have hQ' : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (x : T.val.obj (op (Ut j))), x ∈ LinearMap.range (ψ j) →
      T.val.map (homOfLE (exhaustion_mono a b c d D h)).op x ∈ LinearMap.range (ψ i) := by
    intro i j h x hx
    refine h.eq_or_lt.elim (fun hij => ?_) fun hlt => ?_
    · subst hij
      exact Exists.elim hx fun y hy =>
        ⟨_, ((hψ _ _).trans (hψres h y).symm).trans (congrArg _ hy)⟩
    · exact (congrArg (· ∈ LinearMap.range (ψ i)) (map_homOfLE_eq T.val
        (exhaustion_mono a b c d D h) (exhaustion_mono a b c d D (Nat.succ_le_of_lt hlt))
        (exhaustion_mono a b c d D (Nat.le_succ i)) x)).mpr
        (hρ' i (T.val.map (homOfLE (exhaustion_mono a b c d D (Nat.succ_le_of_lt hlt))).op x))
  have hQ : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) x, x ∈ Q j → exhaustionRes a b c d D T h x ∈ Q i :=
    fun i j h x hx => hQ' h x hx
  -- the topology of compact convergence on the coefficients
  letI uA : ∀ j, UniformSpace ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) := fun j =>
    holomorphicCompactConvergence (Ut j)
  haveI : ∀ j, IsUniformAddGroup ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) := fun j =>
    isUniformAddGroup_holomorphicCompactConvergence (Ut j)
  haveI : ∀ j, IsTopologicalRing ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) := fun j =>
    isTopologicalRing_holomorphicCompactConvergence (Ut j)
  haveI : ∀ j, CompleteSpace ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) := fun j =>
    completeSpace_holomorphicCompactConvergence (Ut j)
  haveI : ∀ j, FirstCountableTopology ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) :=
    fun j => firstCountableTopology_holomorphicCompactConvergence (Ut j)
  -- the quotient uniformities
  have hUni : ∀ j, ∃ U : UniformSpace (LinearMap.range (ψ j)), @IsUniformAddGroup _ U _ ∧
      @CompleteSpace _ U ∧ @T2Space _ U.toTopologicalSpace ∧
      @FirstCountableTopology _ U.toTopologicalSpace ∧
      @ContinuousSMul ((holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) _ _ _
        U.toTopologicalSpace ∧
      @IsOpenQuotientMap _ _ _ U.toTopologicalSpace (ψ j).rangeRestrict := fun j =>
    MMP.Topology.exists_uniformSpace_range_of_isClosed_ker (ψ j) ((hpres (j + 1)).2 (Ut j) (hUW j))
  choose U' hU1 hU2 hU3 hU4 _ hU6 using hUni
  let qQ : ∀ j, (Fin (p (j + 1)) → (holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) → Q j :=
    fun j v => ⟨ψ j v, v, rfl⟩
  -- the generators restricted to `U_i`, `i ≤ j`, lie in `Q_i`
  have hm : ∀ ⦃i j : ℕ⦄ (h : i ≤ j) (k : Fin (p (j + 1))), ∃ m, ψ i m =
      T.val.map (homOfLE ((exhaustion_mono a b c d D h).trans (hUW j))).op (g (j + 1) k) := by
    intro i j h k
    exact Exists.elim (hQ h (T.val.map (homOfLE (hUW j)).op (g (j + 1) k))
      (map_mem_range_genComb_self T (hUW j) (g (j + 1)) k)) fun m hm =>
        ⟨m, hm.trans (map_homOfLE_eq T.val _ (hUW j) (exhaustion_mono a b c d D h) _).symm⟩
  choose m hm using hm
  refine ⟨Q, hρ, hQ, U', hU1, hU2, hU3, hU4, fun i j h => ?_, fun j => ?_⟩
  · -- continuity of the restrictions
    letI : UniformSpace (Q i) := U' i
    letI : UniformSpace (Q j) := U' j
    refine (hU6 j).isQuotientMap.continuous_iff.2 ?_
    let L : (Fin (p (j + 1)) → (holomorphicRingCatSheaf n D).obj.obj (op (Ut j))) →
        (Fin (p (i + 1)) → (holomorphicRingCatSheaf n D).obj.obj (op (Ut i))) := fun v =>
      ∑ k, (holomorphicRingCatSheaf n D).obj.map (homOfLE (exhaustion_mono a b c d D h)).op (v k) •
        m h k
    have hL : Continuous L := by
      refine continuous_finset_sum _ fun k _ => ?_
      have hr : Continuous ((holomorphicRingCatSheaf n D).obj.map
          (homOfLE (exhaustion_mono a b c d D h)).op) :=
        @UniformContinuous.continuous _ _ (holomorphicCompactConvergence _)
          (holomorphicCompactConvergence _) _
          (uniformContinuous_holomorphic_restrict (exhaustion_mono a b c d D h))
      exact (hr.comp (continuous_apply k)).smul continuous_const
    have hfac : (fun x : Q j => (⟨exhaustionRes a b c d D T h x.1, hQ h x.1 x.2⟩ : Q i)) ∘
        (ψ j).rangeRestrict = (ψ i).rangeRestrict ∘ L := by
      funext v
      apply Subtype.ext
      change T.val.map (homOfLE (exhaustion_mono a b c d D h)).op (ψ j v) = ψ i (L v)
      exact (hψres h v).trans (((map_sum (ψ i) _ _).trans (Finset.sum_congr rfl fun k _ =>
        ((ψ i).map_smul _ _).trans (congrArg _ (hm h k)))).symm)
    exact ((hU6 i).continuous.comp hL).congr fun v => (congrFun hfac v).symm
  · -- density of the restrictions (Runge)
    letI : UniformSpace (Q j) := U' j
    letI : UniformSpace (Q (j + 1)) := U' (j + 1)
    have hUW' : ∀ j, Ut j ≤ W j := fun j => (hUK j).trans (hKW j)
    -- the generators of level `j + 1` restricted to `U_{j+1}` lie in `Q_{j+1}`
    have hgen : ∀ k, T.val.map (homOfLE (hUW' (j + 1))).op (g (j + 1) k) ∈
        LinearMap.range (ψ (j + 1)) := fun k => hlift (j + 1) _ (hKW (j + 1)) _ _
    have hdA : ∀ _ : Fin (p (j + 1)), DenseRange
        ((holomorphicRingCatSheaf n D).obj.map
          (homOfLE (exhaustion_mono a b c d D (Nat.le_succ j))).op) :=
      fun _ => denseRange_exhaustion_restrict a b c d D hD j
    have hd := (hU6 j).surjective.denseRange.comp (DenseRange.piMap hdA) (hU6 j).continuous
    refine hd.mono ?_
    rintro _ ⟨w, rfl⟩
    let z : T.val.obj (op (Ut (j + 1))) :=
      ∑ k, w k • T.val.map (homOfLE (hUW' (j + 1))).op (g (j + 1) k)
    have hz : z ∈ LinearMap.range (ψ (j + 1)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hgen k)
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    change T.val.map (homOfLE (exhaustion_mono a b c d D (Nat.le_succ j))).op z = ψ j _
    exact ((map_sum_smul T.val _ w _).trans (Finset.sum_congr rfl fun k _ => congrArg _
      (map_homOfLE_eq T.val (hUW j) (hUW' (j + 1))
        (exhaustion_mono a b c d D (Nat.le_succ j)) _).symm)).trans (hψ j _).symm

/-- `lim¹_j 𝒮(U_j) = 0` along the exhaustion of the box: the Mittag-Leffler lemma
(`MMP.Topology.exists_sub_eq_of_denseRange`) for the subgroups `Q_j` of
`exists_subtowerUniformity`, which compute `lim¹` (`MMP.Topology.exists_sub_eq_of_forall_mem`). -/
private theorem exhaustion_lim_one_eq_zero {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) (hT : IsCoherentModule T)
    (s : (j : ℕ) → ((SheafOfModules.toSheaf _).obj T).obj.obj (op (exhaustion a b c d D j))) :
    ∃ t : (j : ℕ) → ((SheafOfModules.toSheaf _).obj T).obj.obj (op (exhaustion a b c d D j)),
      ∀ j, s j = t j - ((SheafOfModules.toSheaf _).obj T).obj.map
        (homOfLE (exhaustion_mono a b c d D (Nat.le_succ j))).op (t (j + 1)) := by
  obtain ⟨Q, hρ, hQ, U, h1, h2, h3, h4, hcont, hdense⟩ :=
    exists_subtowerUniformity a b c d D hD T hT
  refine MMP.Topology.exists_sub_eq_of_forall_mem
    (fun j => exhaustionRes a b c d D T (Nat.le_succ j)) Q hρ (fun σ => ?_) s
  letI := U
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  let φ : ∀ ⦃i j : ℕ⦄, i ≤ j → Q j →+ Q i := fun i j h =>
    { toFun := fun x => ⟨exhaustionRes a b c d D T h x.1, hQ h x.1 x.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  obtain ⟨v, hv⟩ := MMP.Topology.exists_sub_eq_of_denseRange (G := fun j => Q j) φ
    (fun i j k hij hjk x => Subtype.ext (by
      change (((SheafOfModules.toSheaf _).obj T).obj.map
          (homOfLE (exhaustion_mono a b c d D hjk)).op
        ≫ ((SheafOfModules.toSheaf _).obj T).obj.map
          (homOfLE (exhaustion_mono a b c d D hij)).op) x.1 = _
      rw [← Functor.map_comp]
      rfl))
    hcont hdense σ
  exact ⟨v, fun j => congrArg Subtype.val (hv j)⟩

/-- Theorem B on the box `D` itself: `H^q(D, 𝒮) = 0` for a coherent `𝒪_D`-module and `q ≥ 1`. -/
private theorem box_vanishing {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D))
    (hT : IsCoherentModule T) (q : ℤ) (hq : 1 ≤ q) :
    Limits.IsZero ((sheafCohomology (TopCat.of D) q).obj ((SheafOfModules.toSheaf _).obj T)) :=
  isZero_sheafCohomology_of_exhaustion _ (exhaustion a b c d D) (exhaustion_mono a b c d D)
    (iSup_exhaustion a b c d D hD)
    (exhaustion_restriction_zero a b c d D hD T hT)
    (exhaustion_lim_one_eq_zero a b c d D hD T hT) q hq

/-- **Cartan's Theorem B on boxes.** Let `D = ∏ᵢ (aᵢ, bᵢ) × (cᵢ, dᵢ) ⊆ ℂⁿ` be a product of
bounded open rectangles and `Z ⊆ D` a closed complex submanifold. Then `H^q(Z, 𝒮) = 0` for
every coherent `𝒪_Z`-module `𝒮` and every `q ≥ 1`. -/
@[mmp "thm_mmp_gaga_cartan_polydiscs"]
public theorem cartan_theoremB_box {n : ℕ} (a b c d : Fin n → ℝ)
    (D : Opens (EuclideanSpace ℂ (Fin n)))
    (hD : (D : Set (EuclideanSpace ℂ (Fin n))) =
      {z | ∀ i, z i ∈ Set.Ioo (a i) (b i) ×ℂ Set.Ioo (c i) (d i)})
    (Z : Set D) (hZ : IsClosedComplexSubmanifold n Z)
    (S : SheafOfModules.{0}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{0})).obj (submanifoldStructureSheaf n Z)))
    (hS : IsCoherentModule S) (q : ℤ) (hq : 1 ≤ q) :
    Limits.IsZero ((sheafCohomology (TopCat.of Z) q).obj ((SheafOfModules.toSheaf _).obj S)) := by
  obtain ⟨-, -, -, -, -, h4, -⟩ := coherent_analytic_toolkit (n := n) (M := D)
  obtain ⟨-, -, h4, -⟩ := h4 Z hZ
  obtain ⟨hcoh, hiso⟩ := h4 S hS
  exact (box_vanishing a b c d D hD _ hcoh q hq).of_iso (@asIso _ _ _ _ _ (hiso q)).symm

end TheoremB

end MMP.Analytic
