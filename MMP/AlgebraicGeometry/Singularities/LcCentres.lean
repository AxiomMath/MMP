module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.LcCentrePushforwardStructureSheaf
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SNCGluing
import MMP.AlgebraicGeometry.Singularities.ConnectednessPushforwardSurjective
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup

/-!
# Finiteness, intersections and normality of lc centres

Let `(X, B)` be an lc pair with effective `ℚ`-boundary on a normal projective variety over `ℂ`.
An *lc centre* of `(X, B)` is the centre on `X` of a divisor `E` over `X` with discrepancy
`a(E, X, B) = -1`. Then:

* there are only finitely many lc centres;
* the intersection of two lc centres is the union of the lc centres it contains;
* an lc centre containing no smaller lc centre is normal, with its reduced scheme structure.

The proof works on one log resolution: every lc centre is the image of a stratum of the
coefficient-one part of the crepant boundary, and for a union `W` of centres the union `T` of the
coefficient-one components over `W` satisfies `g_* 𝒪_T = 𝒪_W`, which gives connected fibres
(hence the intersection statement) and, for a minimal `W`, a factorisation of `T → W` through the
normalisation of `W` that forces it to be an isomorphism.

## Main results

* `MMP.Mori.IsLcPair.finite_lcCentres_and_isNormal_of_minimal`: the statement.

## Implementation notes

An lc centre is an irreducible closed subset `Z` of `X` for which some divisor `E` over `X`
(exceptional, or a prime divisor of `X`) has `E.center = Z` and `IsDiscrepancy sX n K B E (-1)`.
A minimal lc centre is minimal for inclusion among all lc centres of `(X, B)`. Its scheme
structure is the reduced one, the closed subscheme cut out by
`Scheme.IdealSheafData.vanishingIdeal`.

## References

* [O. Fujino, *Fundamental theorems for the log minimal model program*][Fujino11]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

/-- **Connected fibres from `φ_* 𝒪 = 𝒪`.** If the comorphism of `φ : A ⟶ W` is bijective on every
open of `W`, then no fibre of `φ` over a point of an open `U` meets both members of a cover of
`φ⁻¹ U` by two disjoint relatively closed sets: the idempotent separating them would come from a
function on `U`, whose germ at the common image point would be both `0` and `1` modulo the maximal
ideal. -/
private theorem false_of_isIso_app {A W : Scheme.{0}} (φ : A ⟶ W) (hiso : ∀ U, IsIso (φ.app U))
    (U : W.Opens) (F₁ F₂ : Set A) (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂)
    (hcov : ∀ a, φ a ∈ U → a ∈ F₁ ∨ a ∈ F₂) (hdisj : ∀ a, φ a ∈ U → a ∈ F₁ → a ∉ F₂)
    {a₁ a₂ : A} (h₁ : a₁ ∈ F₁) (h₂ : a₂ ∈ F₂) (hU : φ a₁ ∈ U) (h12 : φ a₁ = φ a₂) : False := by
  let O₁ : A.Opens := φ ⁻¹ᵁ U ⊓ ⟨F₂ᶜ, hF₂.isOpen_compl⟩
  let O₂ : A.Opens := φ ⁻¹ᵁ U ⊓ ⟨F₁ᶜ, hF₁.isOpen_compl⟩
  have hO : O₁ ⊓ O₂ = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    obtain ⟨⟨ha1, h2⟩, -, h1⟩ := ha
    rcases hcov a ((Scheme.Hom.mem_preimage φ).1 ha1) with h | h
    · exact (h1 h).elim
    · exact (h2 h).elim
  have hsup : φ ⁻¹ᵁ U ≤ O₁ ⊔ O₂ := by
    intro a ha
    have ha' : φ a ∈ U := (Scheme.Hom.mem_preimage φ).1 ha
    by_cases h : a ∈ F₂
    · exact Or.inr ⟨ha, fun h1 => hdisj a ha' h1 h⟩
    · exact Or.inl ⟨ha, h⟩
  have hsub : Subsingleton Γ(A, O₁ ⊓ O₂) := by rw [hO]; infer_instance
  obtain ⟨s, hs1, hs2⟩ : ∃ s : Γ(A, O₁ ⊔ O₂), A.presheaf.map (homOfLE le_sup_left).op s = 1 ∧
      A.presheaf.map (homOfLE le_sup_right).op s = 0 :=
    ⟨(A.sheaf.objSupIsoProdEqLocus O₁ O₂).inv ⟨(1, 0), hsub.elim _ _⟩,
      A.sheaf.objSupIsoProdEqLocus_inv_fst O₁ O₂ _, A.sheaf.objSupIsoProdEqLocus_inv_snd O₁ O₂ _⟩
  let e : Γ(A, φ ⁻¹ᵁ U) := A.presheaf.map (homOfLE hsup).op s
  haveI := hiso U
  obtain ⟨f, hf⟩ : ∃ f : Γ(W, U), φ.app U f = e :=
    ⟨(inv (φ.app U)) e, by
      rw [← CategoryTheory.comp_apply, IsIso.inv_hom_id, CategoryTheory.id_apply]⟩
  have hU₁ : a₁ ∈ φ ⁻¹ᵁ U := (Scheme.Hom.mem_preimage φ).2 hU
  have hU₂' : φ a₂ ∈ U := h12 ▸ hU
  have hU₂ : a₂ ∈ φ ⁻¹ᵁ U := (Scheme.Hom.mem_preimage φ).2 hU₂'
  have ha₁ : a₁ ∈ O₁ := ⟨hU₁, hdisj a₁ hU h₁⟩
  have ha₂ : a₂ ∈ O₂ := ⟨hU₂, fun h => hdisj a₂ hU₂' h h₂⟩
  have g₁ : A.presheaf.germ (φ ⁻¹ᵁ U) a₁ hU₁ e = 1 := by
    simp only [e]
    rw [TopCat.Presheaf.germ_res_apply,
      ← TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE le_sup_left) a₁ ha₁, hs1, map_one]
  have g₂ : A.presheaf.germ (φ ⁻¹ᵁ U) a₂ hU₂ e = 0 := by
    simp only [e]
    rw [TopCat.Presheaf.germ_res_apply,
      ← TopCat.Presheaf.germ_res_apply A.presheaf (homOfLE le_sup_right) a₂ ha₂, hs2, map_zero]
  have hsum : W.presheaf.germ U (φ a₁) hU f + W.presheaf.germ U (φ a₁) hU (1 - f) = 1 := by
    rw [← map_add, add_sub_cancel, map_one]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · have hmem : φ a₂ ∈ W.basicOpen f := h12 ▸ (W.mem_basicOpen f (φ a₁) hU).2 h
    have hmem' : a₂ ∈ A.basicOpen (φ.app U f) := by
      rw [← Scheme.preimage_basicOpen]; exact (Scheme.Hom.mem_preimage φ).2 hmem
    rw [Scheme.mem_basicOpen _ _ _ hU₂, hf, g₂] at hmem'
    exact not_isUnit_zero hmem'
  · have hmem' : a₁ ∈ A.basicOpen (φ.app U (1 - f)) := by
      rw [← Scheme.preimage_basicOpen]
      exact (Scheme.Hom.mem_preimage φ).2 ((W.mem_basicOpen _ (φ a₁) hU).2 h)
    rw [Scheme.mem_basicOpen _ _ _ hU₁, map_sub, map_one, hf, map_sub, map_one, g₁, sub_self]
      at hmem'
    exact not_isUnit_zero hmem'

/-- A closed subset of a Noetherian quasi-sober space has only finitely many points with no proper
generalization inside it: each is the generic point of one of its finitely many irreducible
pieces. -/
private theorem finite_setOf_forall_specializes_eq {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] {Z : Set α} (hZ : IsClosed Z) :
    {y | y ∈ Z ∧ ∀ z ∈ Z, z ⤳ y → z = y}.Finite := by
  classical
  obtain ⟨S, hS, hZS⟩ := NoetherianSpace.exists_finset_irreducible (⟨Z, hZ⟩ : Closeds α)
  refine (S.attach.image fun C => (hS C).genericPoint).finite_toSet.subset ?_
  rintro y ⟨hyZ, hy⟩
  have hy' : y ∈ ((S.sup id : Closeds α) : Set α) := by rw [← hZS]; exact hyZ
  rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hy'
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Function.comp_apply, id] at hy'
  obtain ⟨C, hC, hyC⟩ := hy'
  have hgen := (hS ⟨C, hC⟩).isGenericPoint_genericPoint_closure
  rw [C.isClosed.closure_eq] at hgen
  have hCZ : (C : Set α) ⊆ Z := by
    have : C ≤ S.sup id := Finset.le_sup (f := id) hC
    rw [← hZS] at this
    exact this
  have := hy _ (hCZ hgen.mem) (hgen.specializes hyC)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and]
  exact ⟨⟨C, hC⟩, this⟩

open Classical in
/-- At a point `y`, at most `codim y` components of an snc divisor pass through `y`: their local
equations are distinct members of a regular system of parameters. -/
private theorem card_filter_le_coheight {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {S : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (y : Y) :
    ((S.filter fun G => y ∈ G.support).card : ℕ∞) ≤ Order.coheight y := by
  obtain ⟨N, z, j, hz, hj, -⟩ := exists_at_of_isSNC hsnc y
  rw [coheight_eq_of_isRegularSystemOfParameters hz]
  let j' : (S.filter fun G => y ∈ G.support) → Fin N := fun G =>
    j ⟨G.1, (Finset.mem_filter.1 G.2).1, (Finset.mem_filter.1 G.2).2⟩
  have hj' : Function.Injective j' := fun G G' h =>
    Subtype.ext (congrArg Subtype.val (hj h) :)
  have := Fintype.card_le_of_injective j' hj'
  simp only [Fintype.card_coe, Fintype.card_fin] at this
  exact_mod_cast this

open Classical in
/-- The points of a Noetherian scheme lying on as many components of an snc divisor as their
codimension are finitely many: each is a maximal point of an intersection of components. -/
private theorem finite_setOf_coheight_eq_card {k : Type} [Field k] {Y : Scheme.{0}}
    [NoetherianSpace Y] {sY : Y ⟶ Spec (.of k)} {S : Finset (MMP.Mori.PrimeDivisor Y)}
    (hsnc : DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    {y : Y | Order.coheight y = ((S.filter fun G => y ∈ G.support).card : ℕ∞)}.Finite := by
  refine (S.powerset.finite_toSet.biUnion fun T _ =>
    finite_setOf_forall_specializes_eq (Z := ⋂ G ∈ T, (G.support : Set Y))
      (isClosed_biInter fun G _ => by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_powerset]
  refine ⟨S.filter fun G => y ∈ G.support, Finset.filter_subset _ _,
    Set.mem_iInter₂.2 fun G hG => (Finset.mem_filter.1 hG).2, fun z hz hzy => ?_⟩
  by_contra hne
  have hlt : y < z := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hzy)
    (fun h => hne (hzy.antisymm (Scheme.le_iff_specializes.1 h)).eq)
  have h1 := Order.coheight_add_one_le hlt
  have h2 : ((S.filter fun G => y ∈ G.support).card : ℕ∞) ≤
      ((S.filter fun G => z ∈ G.support).card : ℕ∞) := by
    exact_mod_cast Finset.card_le_card fun G hG =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hG).1, Set.mem_iInter₂.1 hz G hG⟩
  have h3 := card_filter_le_coheight hsnc z
  rw [hy] at h1
  have := (add_le_add (h2.trans h3) (le_refl (1 : ℕ∞))).trans h1
  exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.coe_ne_top _)).1 this)

/-- The support of the reduced divisor `∑_{P ∈ T} P` is the union of the `P ∈ T`. -/
private theorem coe_supp_sum_single {Y : Scheme.{0}} (T : Finset (MMP.Mori.PrimeDivisor Y)) :
    ((∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor Y).supp : Set Y) =
      ⋃ P ∈ T, (P.support : Set Y) := by
  classical
  ext y
  rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
  simp only [Set.mem_iUnion, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply,
    Finsupp.single_apply, Finset.sum_ite_eq', exists_prop]
  constructor
  · rintro ⟨E, hE, hy⟩
    exact ⟨E, by by_contra h; simp [h] at hE, hy⟩
  · rintro ⟨E, hE, hy⟩
    exact ⟨E, by simp [hE], hy⟩

/-- The reduced subscheme on `∑_{P ∈ T} P` has image the union of the `P ∈ T`. -/
private theorem range_subschemeι_sum_single {Y : Scheme.{0}}
    (T : Finset (MMP.Mori.PrimeDivisor Y)) :
    Set.range (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor Y).suppIdeal.subschemeι =
      ⋃ P ∈ T, (P.support : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.coe_support_suppIdeal,
    coe_supp_sum_single]

/-- **Components with the two labels meet over every point.** Let `T = ∑ P` be a reduced divisor
on `R` and `φ : T ⟶ W` a morphism over `g : R ⟶ X` whose comorphism is bijective on every open of
`W`. If each component maps into `C₁` or into `C₂`, and the point `x` lies in the image of a
component over `C₁` and of one over `C₂`, then some component over `C₁` and some component over
`C₂` meet over `x`. -/
private theorem exists_mem_image_inter_of_isIso_app {X R : Scheme.{0}} (g : R ⟶ X)
    (hgc : IsClosedMap g.base) (T : Finset (MMP.Mori.PrimeDivisor R)) (W : Closeds X)
    (φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal W).subscheme)
    (hφ : φ ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
      (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g)
    (hiso : ∀ U, IsIso (φ.app U)) (C₁ C₂ : Set X)
    (hlab : ∀ P ∈ T, g.base '' P.support ⊆ C₁ ∨ g.base '' P.support ⊆ C₂)
    {x : X} (h₁ : ∃ P ∈ T, g.base '' P.support ⊆ C₁ ∧ x ∈ g.base '' P.support)
    (h₂ : ∃ Q ∈ T, g.base '' Q.support ⊆ C₂ ∧ x ∈ g.base '' Q.support) :
    ∃ P ∈ T, ∃ Q ∈ T, g.base '' P.support ⊆ C₁ ∧ g.base '' Q.support ⊆ C₂ ∧
      x ∈ g.base '' (P.support ∩ Q.support) := by
  classical
  by_contra H
  push Not at H
  set ιT := (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι with hιT
  set ιW := (Scheme.IdealSheafData.vanishingIdeal W).subschemeι with hιW
  have hrange := range_subschemeι_sum_single T
  have hpt : ∀ a, ιW (φ a) = g (ιT a) := fun a => congrArg (fun h => h.base a) hφ
  have hclP : ∀ P : MMP.Mori.PrimeDivisor R, IsClosed (P.support : Set R) := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  let Bad : Set X := ⋃ P ∈ T, ⋃ Q ∈ T,
    ⋃ (_ : g.base '' P.support ⊆ C₁ ∧ g.base '' Q.support ⊆ C₂),
      g.base '' ((P.support : Set R) ∩ Q.support)
  have hBad : IsClosed Bad :=
    isClosed_biUnion_finset fun P _ => isClosed_biUnion_finset fun Q _ =>
      isClosed_iUnion_of_finite fun _ => hgc _ ((hclP P).inter (hclP Q))
  let UX : X.Opens := ⟨Badᶜ, hBad.isOpen_compl⟩
  let F₁ : Set (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme :=
    ιT ⁻¹' ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C₁), (P.support : Set R)
  let F₂ : Set (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme :=
    ιT ⁻¹' ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C₂), (P.support : Set R)
  have hF : ∀ C : Set X, IsClosed (ιT ⁻¹' ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C),
      (P.support : Set R)) := fun C =>
    (isClosed_biUnion_finset fun P _ => isClosed_iUnion_of_finite fun _ => hclP P).preimage
      ιT.continuous
  have hmemU : ∀ a, φ a ∈ ιW ⁻¹ᵁ UX ↔ g (ιT a) ∉ Bad := fun a => by
    rw [Scheme.Hom.mem_preimage, hpt]; exact Iff.rfl
  obtain ⟨P₁, hP₁, hP₁C, y₁, hy₁, hy₁x⟩ := h₁
  obtain ⟨Q₁, hQ₁, hQ₁C, y₂, hy₂, hy₂x⟩ := h₂
  obtain ⟨a₁, ha₁⟩ : y₁ ∈ Set.range ιT := by
    rw [hrange]; exact Set.mem_biUnion hP₁ hy₁
  obtain ⟨a₂, ha₂⟩ : y₂ ∈ Set.range ιT := by
    rw [hrange]; exact Set.mem_biUnion hQ₁ hy₂
  have hxBad : x ∉ Bad := by
    simp only [Bad, Set.mem_iUnion, not_exists]
    intro P hP Q hQ hPQ
    exact H P hP Q hQ hPQ.1 hPQ.2
  refine false_of_isIso_app φ hiso (ιW ⁻¹ᵁ UX) F₁ F₂ (hF C₁) (hF C₂) ?_ ?_
    (a₁ := a₁) (a₂ := a₂) ?_ ?_ ?_ ?_
  · intro a _
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.1
      (show ιT a ∈ ⋃ P ∈ T, (P.support : Set R) by rw [← hrange]; exact ⟨a, rfl⟩)
    rcases hlab P hP with h | h
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨P, hP, Set.mem_iUnion.2 ⟨h, hyP⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨P, hP, Set.mem_iUnion.2 ⟨h, hyP⟩⟩)
  · intro a ha h1 h2
    obtain ⟨P, hP, h1'⟩ := Set.mem_iUnion₂.1 h1
    obtain ⟨hPC, hyP⟩ := Set.mem_iUnion.1 h1'
    obtain ⟨Q, hQ, h2'⟩ := Set.mem_iUnion₂.1 h2
    obtain ⟨hQC, hyQ⟩ := Set.mem_iUnion.1 h2'
    exact (hmemU a).1 ha (Set.mem_iUnion₂.2 ⟨P, hP, Set.mem_iUnion₂.2 ⟨Q, hQ,
      Set.mem_iUnion.2 ⟨⟨hPC, hQC⟩, ⟨ιT a, ⟨hyP, hyQ⟩, rfl⟩⟩⟩⟩)
  · show ιT a₁ ∈ ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C₁), (P.support : Set R)
    rw [ha₁]; exact Set.mem_iUnion₂.2 ⟨P₁, hP₁, Set.mem_iUnion.2 ⟨hP₁C, hy₁⟩⟩
  · show ιT a₂ ∈ ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C₂), (P.support : Set R)
    rw [ha₂]; exact Set.mem_iUnion₂.2 ⟨Q₁, hQ₁, Set.mem_iUnion.2 ⟨hQ₁C, hy₂⟩⟩
  · exact (hmemU a₁).2 (by rw [ha₁, hy₁x]; exact hxBad)
  · apply ιW.isClosedEmbedding.injective
    rw [hpt, hpt, ha₁, ha₂, hy₁x, hy₂x]

private theorem isReduced_subscheme_sup_of_isSNC {k : Type} [Field k] {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} {D : Divisor Y}
    (hsnc : DivisorWithCoeffs.IsSNC sY D) {E F : MMP.Mori.PrimeDivisor Y} (hE : E ∈ D.support)
    (hF : F ∈ D.support) (hEF : E ≠ F) :
    IsReduced (E.idealSheaf ⊔ F.idealSheaf).subscheme := by
  have key : E.idealSheaf ⊔ F.idealSheaf = Scheme.IdealSheafData.vanishingIdeal
      (E.idealSheaf ⊔ F.idealSheaf).support := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support]
    refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
    rw [MMP.Resolution.stalk_radical, eq_comm, Ideal.radical_eq_iff]
    have hsup : IdealSheafData.stalk (E.idealSheaf ⊔ F.idealSheaf) y =
        IdealSheafData.stalk E.idealSheaf y ⊔ IdealSheafData.stalk F.idealSheaf y := by
      have := MMP.Resolution.stalk_iSup (fun b : Bool => cond b E.idealSheaf F.idealSheaf) y
      simpa [iSup_bool_eq] using this
    rw [hsup]
    by_cases hyE : y ∈ E.support
    · by_cases hyF : y ∈ F.support
      · obtain ⟨N, z, j, hz, hj, hI⟩ := hsnc.2 y
        have hab : j ⟨E, hE, hyE⟩ ≠ j ⟨F, hF, hyF⟩ := fun h =>
          hEF (congrArg Subtype.val (hj h))
        rw [hI ⟨E, hE, hyE⟩, hI ⟨F, hF, hyF⟩]
        have hp := MMP.Resolution.span_image_isPrime_of_isRegularSystemOfParameters hz
          {j ⟨E, hE, hyE⟩, j ⟨F, hF, hyF⟩}
        rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
          Ideal.span_insert] at hp
        exact hp.isRadical
      · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support F hyF, sup_top_eq]
        exact le_top
    · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support E hyE, top_sup_eq]
      exact le_top
  rw [key]
  infer_instance

/-- Restriction of `appLE` along equal morphisms. -/
private theorem appLE_congr_hom {X Y : Scheme.{0}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) (b : Γ(Y, U)) :
    f.appLE U V e b = f'.appLE U V e' b := by
  subst h; rfl

/-- **Integral rational functions on `W` are regular.** Let `D` be a reduced snc divisor on a
smooth variety, with reduced subscheme `T`, and `φ : T ⟶ W` a surjective morphism to an integral
scheme whose comorphism is bijective on every open, such that the generic points of the components
of `D` and of the codimension-two strata of `D` map to the generic point of `W`. Then a rational
function on `W` integral over `Γ(W, U)` is a section over `U`: its pull-backs to the normal
components are regular, agree on the reduced pairwise intersections, glue to a section of `𝒪_T`,
and that section comes from `W`. -/
private theorem exists_germToFunctionField_eq_of_isIntegral_of_isIso_app
    {R : Scheme.{0}} [IsLocallyNoetherian R] {sR : R ⟶ Spec (.of ℂ)} [Smooth sR]
    (hRv : MMP.Mori.IsVariety ℂ sR) {D : Divisor R}
    (hsnc : DivisorWithCoeffs.IsSNC sR D) (hsncD : MMP.Intersection.IsSNCDivisor sR D)
    {Wsch : Scheme.{0}} [IsIntegral Wsch] (φ : D.suppIdeal.subscheme ⟶ Wsch)
    (hiso : ∀ U, IsIso (φ.app U)) (hsurj : Function.Surjective φ.base)
    (hgen : ∀ E ∈ D.support, ∀ a, D.suppIdeal.subschemeι a = E.genericPoint →
      φ a = genericPoint Wsch)
    (hstr : ∀ E ∈ D.support, ∀ F ∈ D.support, E ≠ F → ∀ y ∈ E.support, y ∈ F.support →
      ∃ z, z ∈ E.support ∧ z ∈ F.support ∧ z ⤳ y ∧
        ∀ a, D.suppIdeal.subschemeι a = z → φ a = genericPoint Wsch)
    (U : Wsch.Opens) [Nonempty U] (ψ : Wsch.functionField) (hψ : IsIntegral Γ(Wsch, U) ψ) :
    ∃ a : Γ(Wsch, U), Wsch.germToFunctionField U a = ψ := by
  classical
  set ιT := D.suppIdeal.subschemeι with hιT
  -- the open `U'` of `R` cutting out `φ⁻¹ U`
  obtain ⟨U', hU'⟩ : ∃ U' : R.Opens, ιT ⁻¹ᵁ U' = φ ⁻¹ᵁ U := by
    obtain ⟨t, ht, hts⟩ := ιT.isClosedEmbedding.isInducing.isOpen_iff.1 (φ ⁻¹ᵁ U).isOpen
    exact ⟨⟨t, ht⟩, Opens.ext hts⟩
  have hle : ∀ E : D.support, D.suppIdeal ≤ E.1.idealSheaf := fun E =>
    (MMP.Intersection.suppIdeal_eq_finsetInf D).le.trans (Finset.inf_le E.2)
  let incl : ∀ E : D.support, E.1.idealSheaf.subscheme ⟶ D.suppIdeal.subscheme :=
    fun E => Scheme.IdealSheafData.inclusion (hle E)
  have hincl : ∀ E : D.support, ∀ p, ιT (incl E p) = E.1.idealSheaf.subschemeι p := by
    intro E p
    rw [← Scheme.IdealSheafData.inclusion_subschemeι (hle E)]
    rfl
  haveI : LocallyOfFiniteType sR := hRv.toLocallyOfFiniteType
  have hnor : ∀ E : D.support, IsNormal E.1.idealSheaf.subscheme := by
    intro E
    have hsm := hsncD.2.1 E.1 E.2
    haveI : LocallyOfFinitePresentation (E.1.idealSheaf.subschemeι ≫ sR) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType
        (f := E.1.idealSheaf.subschemeι ≫ sR)).mpr inferInstance
    haveI : Smooth (E.1.idealSheaf.subschemeι ≫ sR) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
    haveI : IsNormal (Spec (.of ℂ)) := isNormal_spec_of_isIntegrallyClosed _
    exact AlgebraicGeometry.isNormal_of_smooth (E.1.idealSheaf.subschemeι ≫ sR)
  have hgenE : ∀ E : D.support, haveI := E.1.integral
      (incl E ≫ φ) (genericPoint E.1.idealSheaf.subscheme) = genericPoint Wsch :=
    fun E => hgen E.1 E.2 _ (hincl E _)
  have hdom : ∀ E : D.support, IsDominant (incl E ≫ φ) := by
    intro E
    haveI := E.1.integral
    refine ⟨dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)⟩
    rw [← (genericPoint_spec Wsch).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hgenE E⟩)
  -- the sections on the components
  have hsec : ∀ E : D.support, ∃ s : Γ(E.1.idealSheaf.subscheme,
      E.1.idealSheaf.subschemeι ⁻¹ᵁ U'),
      (∀ _ : Nonempty (E.1.idealSheaf.subschemeι ⁻¹ᵁ U'),
        haveI := E.1.integral
        haveI := hdom E
        E.1.idealSheaf.subscheme.germToFunctionField _ s =
          AlgebraicGeometry.functionFieldMap (incl E ≫ φ) ψ) ∧
      ∀ (V : E.1.idealSheaf.subscheme.Opens) (hV : V ≤ E.1.idealSheaf.subschemeι ⁻¹ᵁ U')
        (V₀ : Wsch.Opens) [Nonempty V₀] (b : Γ(Wsch, V₀))
        (hVV₀ : V ≤ (incl E ≫ φ) ⁻¹ᵁ V₀),
        Wsch.germToFunctionField V₀ b = ψ →
        E.1.idealSheaf.subscheme.presheaf.map (homOfLE hV).op s =
          (incl E ≫ φ).appLE V₀ V hVV₀ b := by
    intro E
    haveI := E.1.integral
    haveI := hnor E
    haveI := hdom E
    have hpt : ∀ p : E.1.idealSheaf.subscheme, p ∈ E.1.idealSheaf.subschemeι ⁻¹ᵁ U' →
        (incl E ≫ φ) p ∈ U := by
      intro p hp
      have h1 : incl E p ∈ ιT ⁻¹ᵁ U' := by
        rw [Scheme.Hom.mem_preimage, hincl E p]
        exact (Scheme.Hom.mem_preimage _).1 hp
      rw [hU'] at h1
      exact (Scheme.Hom.mem_preimage _).1 h1
    by_cases hne : Nonempty (E.1.idealSheaf.subschemeι ⁻¹ᵁ U')
    · have hmem : ∀ p : (E.1.idealSheaf.subschemeι ⁻¹ᵁ U'),
          ∃ a : E.1.idealSheaf.subscheme.presheaf.stalk p.1,
            algebraMap _ E.1.idealSheaf.subscheme.functionField a =
              AlgebraicGeometry.functionFieldMap (incl E ≫ φ) ψ := by
        intro p
        have hp := hpt p.1 p.2
        haveI : Nonempty ((incl E ≫ φ) ⁻¹ᵁ U) := ⟨⟨p.1, hp⟩⟩
        haveI := IsNormal.stalk_normal (X := E.1.idealSheaf.subscheme) p.1
        refine IsIntegrallyClosed.isIntegral_iff.1 ?_
        obtain ⟨q, hqm, hq⟩ := hψ
        refine ⟨q.map ((E.1.idealSheaf.subscheme.presheaf.germ ((incl E ≫ φ) ⁻¹ᵁ U) p.1 hp).hom.comp
            ((incl E ≫ φ).app U).hom), hqm.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hcomp : (algebraMap (E.1.idealSheaf.subscheme.presheaf.stalk p.1)
            E.1.idealSheaf.subscheme.functionField).comp
              ((E.1.idealSheaf.subscheme.presheaf.germ ((incl E ≫ φ) ⁻¹ᵁ U) p.1 hp).hom.comp
                ((incl E ≫ φ).app U).hom) =
            (AlgebraicGeometry.functionFieldMap (incl E ≫ φ)).comp
              (algebraMap Γ(Wsch, U) Wsch.functionField) := by
          ext c
          show algebraMap _ _ (E.1.idealSheaf.subscheme.presheaf.germ ((incl E ≫ φ) ⁻¹ᵁ U) p.1 hp
            ((incl E ≫ φ).app U c)) =
            AlgebraicGeometry.functionFieldMap (incl E ≫ φ) (Wsch.germToFunctionField U c)
          refine (Scheme.algebraMap_germ_eq_germToFunctionField
            (X := E.1.idealSheaf.subscheme) hp _).trans ?_
          rw [MMP.Spreading.functionFieldMap_germToFunctionField (incl E ≫ φ) U
            ((incl E ≫ φ) ⁻¹ᵁ U) le_rfl c, Scheme.Hom.appLE_eq_app]
        rw [hcomp, ← Polynomial.hom_eval₂, hq, map_zero]
      obtain ⟨s, hs⟩ := exists_germToFunctionField_eq_of_forall_mem_range
        E.1.idealSheaf.subscheme (E.1.idealSheaf.subschemeι ⁻¹ᵁ U')
        (AlgebraicGeometry.functionFieldMap (incl E ≫ φ) ψ) hmem
      refine ⟨s, fun _ => hs, fun V hV V₀ _ b hVV₀ hb => ?_⟩
      by_cases hVne : Nonempty V
      · apply E.1.idealSheaf.subscheme.germToFunctionField_injective V
        rw [TopCat.Presheaf.germ_res_apply]
        change E.1.idealSheaf.subscheme.germToFunctionField _ s = _
        rw [hs, ← hb, MMP.Spreading.functionFieldMap_germToFunctionField (incl E ≫ φ) V₀ V hVV₀ b]
      · have hV0 : V = ⊥ := eq_bot_iff.2 fun x hx => (hVne ⟨⟨x, hx⟩⟩).elim
        subst hV0
        exact Subsingleton.elim _ _
    · refine ⟨0, fun h => (hne h).elim, fun V hV V₀ _ b hVV₀ _ => ?_⟩
      have hV0 : V = ⊥ := eq_bot_iff.2 fun x hx => (hne ⟨⟨x, hV hx⟩⟩).elim
      subst hV0
      exact Subsingleton.elim _ _
  choose s hsgerm hs using hsec
  -- a representative of `ψ` on an open of `W`
  obtain ⟨V₀, hηV₀, b₀, hb₀⟩ := TopCat.Presheaf.germ_exist (x := genericPoint Wsch) Wsch.presheaf ψ
  haveI : Nonempty V₀ := ⟨⟨_, hηV₀⟩⟩
  have hb₀' : Wsch.germToFunctionField V₀ b₀ = ψ := hb₀
  -- compatibility on the pairwise intersections
  have hcompat : ∀ E E' : D.support,
      (Scheme.IdealSheafData.inclusion le_sup_left).appLE
          (E.1.idealSheaf.subschemeι ⁻¹ᵁ U')
          ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U')
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
          (s E) =
        (Scheme.IdealSheafData.inclusion le_sup_right).appLE
          (E'.1.idealSheaf.subschemeι ⁻¹ᵁ U')
          ((E.1.idealSheaf ⊔ E'.1.idealSheaf).subschemeι ⁻¹ᵁ U')
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
          (s E') := by
    intro E E'
    by_cases hEE : E = E'
    · subst hEE; rfl
    have hEE' : E.1 ≠ E'.1 := fun h => hEE (Subtype.ext h)
    set J := E.1.idealSheaf ⊔ E'.1.idealSheaf with hJ
    haveI : IsReduced J.subscheme := isReduced_subscheme_sup_of_isSNC hsnc E.2 E'.2 hEE'
    set iL := Scheme.IdealSheafData.inclusion (le_sup_left : E.1.idealSheaf ≤ J)
    set iR := Scheme.IdealSheafData.inclusion (le_sup_right : E'.1.idealSheaf ≤ J)
    set V := J.subschemeι ⁻¹ᵁ U'
    have hJle : D.suppIdeal ≤ J := (hle E).trans le_sup_left
    set iJ := Scheme.IdealSheafData.inclusion hJle
    have hLJ : iL ≫ incl E = iJ := Scheme.IdealSheafData.inclusion_comp _ _
    have hRJ : iR ≫ incl E' = iJ := Scheme.IdealSheafData.inclusion_comp _ _
    have hιJ : ∀ w, ιT (iJ w) = J.subschemeι w := by
      intro w
      rw [← Scheme.IdealSheafData.inclusion_subschemeι hJle]
      rfl
    -- both sides agree near every point lying over the generic point of `W`
    set N : J.subscheme.Opens := V ⊓ (iJ ≫ φ) ⁻¹ᵁ V₀
    have hside : ∀ (F : D.support) (i : J.subscheme ⟶ F.1.idealSheaf.subscheme)
        (hi : i ≫ incl F = iJ) (hiι : i ≫ F.1.idealSheaf.subschemeι = J.subschemeι)
        (e : V ≤ i ⁻¹ᵁ (F.1.idealSheaf.subschemeι ⁻¹ᵁ U')),
        J.subscheme.presheaf.map (homOfLE (inf_le_left : N ≤ V)).op
          (i.appLE _ V e (s F)) = (iJ ≫ φ).appLE V₀ N inf_le_right b₀ := by
      intro F i hi hiι e
      set VF : F.1.idealSheaf.subscheme.Opens :=
        F.1.idealSheaf.subschemeι ⁻¹ᵁ U' ⊓ (incl F ≫ φ) ⁻¹ᵁ V₀
      have hNVF : N ≤ i ⁻¹ᵁ VF := by
        intro w hw
        refine ⟨e hw.1, ?_⟩
        show (incl F ≫ φ) (i w) ∈ V₀
        have : (incl F ≫ φ) (i w) = (iJ ≫ φ) w := by
          rw [← hi]; rfl
        rw [this]; exact hw.2
      rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
      have h1 : i.appLE (F.1.idealSheaf.subschemeι ⁻¹ᵁ U') N
          (inf_le_left.trans e) (s F) =
          i.appLE VF N hNVF (F.1.idealSheaf.subscheme.presheaf.map
            (homOfLE (inf_le_left : VF ≤ _)).op (s F)) := by
        rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
      rw [h1, hs F VF inf_le_left V₀ b₀ inf_le_right hb₀', ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr_hom (by rw [← Category.assoc, hi]) _ _ _ _ _
    apply eq_of_sub_eq_zero
    apply eq_zero_of_basicOpen_eq_bot
    refine eq_bot_iff.2 fun v hv => ?_
    exfalso
    have hvV : v ∈ V := J.subscheme.basicOpen_le _ hv
    have hJs : Set.range J.subschemeι = E.1.support ∩ E'.1.support := by
      rw [Scheme.IdealSheafData.range_subschemeι, hJ, Scheme.IdealSheafData.support_sup]
      rfl
    have hyJ : J.subschemeι v ∈ E.1.support ∩ E'.1.support := by
      rw [← hJs]; exact ⟨v, rfl⟩
    obtain ⟨z, hzE, hzE', hzy, hzφ⟩ := hstr E.1 E.2 E'.1 E'.2 hEE' _ hyJ.1 hyJ.2
    obtain ⟨ζ, hζ⟩ : z ∈ Set.range J.subschemeι := by
      rw [hJs]; exact ⟨hzE, hzE'⟩
    have hζv : ζ ⤳ v := by
      rw [← J.subschemeι.isClosedEmbedding.isInducing.specializes_iff, hζ]
      exact hzy
    have hζb := hζv.mem_open (J.subscheme.basicOpen _).isOpen hv
    have hζV : ζ ∈ V := J.subscheme.basicOpen_le _ hζb
    have hζN : ζ ∈ N := by
      refine ⟨hζV, ?_⟩
      show φ (iJ ζ) ∈ V₀
      rw [hzφ _ (by rw [hιJ, hζ])]
      exact hηV₀
    have hL := hside E iL hLJ (Scheme.IdealSheafData.inclusion_subschemeι _)
      (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
    have hR := hside E' iR hRJ (Scheme.IdealSheafData.inclusion_subschemeι _)
      (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι])
    have hgerm : J.subscheme.presheaf.germ V ζ hζV
        (iL.appLE _ V (by rw [← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι]) (s E) -
          iR.appLE _ V (by rw [← Scheme.Hom.comp_preimage,
              Scheme.IdealSheafData.inclusion_subschemeι]) (s E')) = 0 := by
      rw [map_sub, ← TopCat.Presheaf.germ_res_apply J.subscheme.presheaf
          (homOfLE (inf_le_left : N ≤ V)) ζ hζN,
        ← TopCat.Presheaf.germ_res_apply J.subscheme.presheaf
          (homOfLE (inf_le_left : N ≤ V)) ζ hζN, hL, hR, sub_self]
    have hζb' : ζ ∈ J.subscheme.basicOpen
        (iL.appLE _ V (by rw [← Scheme.Hom.comp_preimage,
            Scheme.IdealSheafData.inclusion_subschemeι]) (s E) -
          iR.appLE _ V (by rw [← Scheme.Hom.comp_preimage,
              Scheme.IdealSheafData.inclusion_subschemeι]) (s E')) := hζb
    rw [Scheme.mem_basicOpen _ _ _ hζV, hgerm] at hζb'
    exact not_isUnit_zero hζb'
  -- glue
  obtain ⟨t, ht, -⟩ := (MMP.Intersection.IsSNCDivisor.existsUnique_glue hRv hsncD U').1 s hcompat
  haveI := hiso U
  obtain ⟨a, ha⟩ : ∃ a : Γ(Wsch, U),
      φ.app U a = D.suppIdeal.subscheme.presheaf.map (homOfLE hU'.ge).op t :=
    ⟨(inv (φ.app U)) _, by
      rw [← CategoryTheory.comp_apply, IsIso.inv_hom_id, CategoryTheory.id_apply]⟩
  refine ⟨a, ?_⟩
  -- compare on a component through a point over `U`
  obtain ⟨w₀⟩ := ‹Nonempty U›
  obtain ⟨a₀, ha₀⟩ := hsurj w₀.1
  have ha₀U : a₀ ∈ φ ⁻¹ᵁ U := by rw [Scheme.Hom.mem_preimage, ha₀]; exact w₀.2
  have ha₀U' : ιT a₀ ∈ U' := by
    rw [← hU'] at ha₀U; exact (Scheme.Hom.mem_preimage _).1 ha₀U
  have hsuppT : ιT a₀ ∈ (D.suppIdeal.support : Set R) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨a₀, rfl⟩
  rw [DivisorWithCoeffs.coe_support_suppIdeal, SetLike.mem_coe,
    DivisorWithCoeffs.mem_supp_iff] at hsuppT
  obtain ⟨E₀, hE₀D, hE₀⟩ := hsuppT
  have hE₀s : E₀ ∈ D.support := by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]; exact hE₀D
  set E : D.support := ⟨E₀, hE₀s⟩
  obtain ⟨p₀, hp₀⟩ : ιT a₀ ∈ Set.range E.1.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hE₀
  have hp₀a₀ : incl E p₀ = a₀ := ιT.isClosedEmbedding.injective (by rw [hincl, hp₀])
  haveI := E.1.integral
  haveI := hdom E
  have hp₀U : p₀ ∈ (incl E ≫ φ) ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage]; show φ (incl E p₀) ∈ U; rw [hp₀a₀]; exact
        (Scheme.Hom.mem_preimage _).1 ha₀U
  have hp₀U' : p₀ ∈ E.1.idealSheaf.subschemeι ⁻¹ᵁ U' := by
    rw [Scheme.Hom.mem_preimage, hp₀]; exact ha₀U'
  haveI : Nonempty ((incl E ≫ φ) ⁻¹ᵁ U) := ⟨⟨p₀, hp₀U⟩⟩
  haveI : Nonempty (E.1.idealSheaf.subschemeι ⁻¹ᵁ U') := ⟨⟨p₀, hp₀U'⟩⟩
  set Vs : E.1.idealSheaf.subscheme.Opens :=
    E.1.idealSheaf.subschemeι ⁻¹ᵁ U' ⊓ (incl E ≫ φ) ⁻¹ᵁ U
  haveI : Nonempty Vs := ⟨⟨p₀, hp₀U', hp₀U⟩⟩
  have key : (incl E ≫ φ).appLE U Vs inf_le_right a =
      E.1.idealSheaf.subscheme.presheaf.map
        (homOfLE (inf_le_left : Vs ≤ E.1.idealSheaf.subschemeι ⁻¹ᵁ U')).op
        ((incl E).appLE (ιT ⁻¹ᵁ U') (E.1.idealSheaf.subschemeι ⁻¹ᵁ U')
          (by rw [← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]) t) := by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.comp_appLE,
      ConcreteCategory.comp_apply, ha, ← ConcreteCategory.comp_apply]
    exact congrArg (fun f : Γ(D.suppIdeal.subscheme, ιT ⁻¹ᵁ U') ⟶
        Γ(E.1.idealSheaf.subscheme, Vs) => f t)
      (Scheme.Hom.map_appLE (incl E) (V := Vs) _ (homOfLE hU'.ge).op)
  apply (AlgebraicGeometry.functionFieldMap (incl E ≫ φ)).injective
  rw [MMP.Spreading.functionFieldMap_germToFunctionField (incl E ≫ φ) U Vs inf_le_right a, key,
    MMP.Intersection.germToFunctionField_map, ← hsgerm E inferInstance, ← ht E]

/-- On a scheme of dimension at most one every point has codimension at most one. -/
private theorem coheight_le_one_of_topologicalKrullDim_le_one' {Y : Scheme.{0}}
    (hd : topologicalKrullDim Y ≤ 1) (y : Y) : Order.coheight y ≤ 1 := by
  have h : (Order.coheight y : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
    rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
    exact Order.coheight_le_krullDim _
  exact_mod_cast h.trans hd

/-- In dimension at most one a prime divisor is a closed point. -/
private theorem support_eq_singleton_of_topologicalKrullDim_le_one {Y : Scheme.{0}}
    (hd : topologicalKrullDim Y ≤ 1) (Γ : MMP.Mori.PrimeDivisor Y) :
    (Γ.support : Set Y) = {Γ.genericPoint} := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.2 (subset_closure rfl))
  by_contra hne
  have hlt : z < Γ.genericPoint :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.2 (specializes_iff_mem_closure.2 hz))
      (fun h => hne ((Scheme.le_iff_specializes.1 h).antisymm
        (specializes_iff_mem_closure.2 hz)).eq)
  have h1 := Order.coheight_add_one_le hlt
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint Γ] at h1
  have h2 := (h1.trans (coheight_le_one_of_topologicalKrullDim_le_one' hd z))
  exact absurd h2 (by decide)

/-- In dimension at least two, an lc pair has boundary coefficients at most one (Kollár–Mori
2.31(1)): a coefficient above one forces `discrep = -∞`. -/
private theorem coeff_le_one_of_isLcPair_of_two_le {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {d : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (h : IsLcPair sX d K Δ) (hd : 2 ≤ d) (E : MMP.Mori.PrimeDivisor X) :
    Δ.coeff E ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have htot := totalDiscrep_le_neg_coeff h.1.1 (MMP.Positivity.IsPair.exists_isDiscrepancy
    h.1.isPair h.1.2.1 (DivisorOver.ofPrimeDivisor ℂ h.1.1 E))
  have hc : (((-Δ.coeff E : ℚ) : ℝ) : EReal) < ((-1 : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr (by push_cast; exact_mod_cast (by linarith : -Δ.coeff E < -1))
  have h2 := h.2
  rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one h.1 hd
    (htot.trans_lt (hc.trans_eq (by norm_num)))] at h2
  exact ((EReal.bot_lt_coe (-1)).trans_eq (by simp)).not_ge h2

/-- In dimension at most one, every lc centre of a pair is a closed point which is a component
of coefficient one of the boundary. -/
private theorem exists_center_eq_singleton_of_topologicalKrullDim_le_one {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} (hPw : IsPairWith sX n K B)
    (hd : topologicalKrullDim X ≤ 1) (E : DivisorOver ℂ sX) (hE : IsDiscrepancy sX n K B E (-1)) :
    ∃ Γ : MMP.Mori.PrimeDivisor X, B.coeff Γ = 1 ∧ (E.center : Set X) = {Γ.genericPoint} := by
  have hnex : ¬ E.IsExceptional := by
    rw [DivisorOver.isExceptional_iff_two_le_coheight hPw.1]
    intro h
    exact absurd (h.trans (coheight_le_one_of_topologicalKrullDim_le_one' hd _)) (by decide)
  obtain ⟨Γ, hΓc, hΓd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw E hnex
  refine ⟨Γ, by have := hE.eq hΓd; linarith, ?_⟩
  rw [hΓc, support_eq_singleton_of_topologicalKrullDim_le_one hd]

/-- The reduced subscheme on a closed point is normal. -/
private theorem isNormal_subscheme_vanishingIdeal_singleton {Y : Scheme.{0}} (W : Closeds Y) {w : Y}
    (hw : (W : Set Y) = {w}) :
    IsNormal (Scheme.IdealSheafData.vanishingIdeal W).subscheme := by
  have hirr : IsIrreducible (W : Set Y) := by rw [hw]; exact isIrreducible_singleton
  haveI := MMP.Fourfold.isIntegral_subscheme_vanishingIdeal W hirr
  have hsub : ∀ p q : (Scheme.IdealSheafData.vanishingIdeal W).subscheme, p = q := by
    intro p q
    apply (Scheme.IdealSheafData.vanishingIdeal W).subschemeι.isClosedEmbedding.injective
    have hr : ∀ p : (Scheme.IdealSheafData.vanishingIdeal W).subscheme,
        (Scheme.IdealSheafData.vanishingIdeal W).subschemeι p = w := by
      intro p
      have : (Scheme.IdealSheafData.vanishingIdeal W).subschemeι p ∈ (W : Set Y) := by
        rw [← Scheme.IdealSheafData.coe_support_vanishingIdeal,
          ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨p, rfl⟩
      rw [hw] at this
      exact this
    rw [hr, hr]
  refine ⟨fun x => inferInstance, fun x => ?_⟩
  rw [hsub x (genericPoint _)]
  change IsIntegrallyClosed (Scheme.IdealSheafData.vanishingIdeal W).subscheme.functionField
  infer_instance

/-- A component of coefficient one of the crepant boundary is an lc place: its image is an lc
centre. -/
private theorem exists_isDiscrepancy_center_eq_image_of_coeff_eq_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] (g : R ⟶ X)
    (hgc : IsClosedMap g.base) (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
    {BR : QDivisor R} (hcrep : IsCrepantBoundary sX n K B g hR hgb BR)
    {P : MMP.Mori.PrimeDivisor R} (hP : BR.coeff P = 1) :
    ∃ E : DivisorOver ℂ sX, IsDiscrepancy sX n K B E (-1) ∧
      (E.center : Set X) = g.base '' P.support := by
  refine ⟨⟨R, g, hR, hgb, P⟩, by have := hcrep P; rwa [hP] at this, ?_⟩
  rw [DivisorOver.coe_center]
  refine (hgc _ ?_).closure_eq
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure

/-- **Finiteness of lc centres.** On a crepant log resolution with snc boundary of coefficients at
most one, the centre of an lc place is the image of a point lying on as many components as its
codimension, and there are only finitely many such points. -/
private theorem finite_lcCentres_of_isCrepantBoundary
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPw : IsPairWith sX n K B)
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] [NoetherianSpace R]
    (g : R ⟶ X) [IsProper g] (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (hsm : IsSmoothScheme (g ≫ sX))
    {KR : Divisor R} (hKR : KR.IsCanonicalDivisor (g ≫ sX) n) {BR : QDivisor R}
    (hcrep : IsCrepantBoundary sX n K B g hR hgb BR)
    (hBR1 : ∀ P, BR.coeff P ≤ 1) {sbig : Finset (MMP.Mori.PrimeDivisor R)}
    (hsupp : BR.support ⊆ sbig)
    (hsnc : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ))) :
    {Z : IrreducibleCloseds X |
      ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1)}.Finite := by
  classical
  haveI := hgb.isDominant
  have hcr := IsPair.isDiscrepancy_iff_of_crepant hPw.isPair g hR hgb hPw.2.1 hKR (Or.inl hcrep)
  refine ((finite_setOf_coheight_eq_card hsnc).biUnion fun y _ =>
    (show ({Z : IrreducibleCloseds X | (Z : Set X) = closure {g y}}).Subsingleton from
      fun Z₁ h₁ Z₂ h₂ => SetLike.coe_injective (h₁.trans h₂.symm)).finite).subset ?_
  rintro Z ⟨E, rfl, hE⟩
  obtain ⟨E', hE'⟩ := exists_divisorOver_comap_eq hR hgb E
  have hE'd : IsDiscrepancy (g ≫ sX) n KR BR E' (-1) := (hcr.2 E' E hE' (-1)).2 hE
  have hcent : E.f E.E.genericPoint = g (E'.f E'.E.genericPoint) :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hPw.1.1
      (D := E) (D' := compDivisorOver g hR hgb E')
      (by rw [valuation_compDivisorOver]; exact hE')
  refine Set.mem_iUnion₂.2 ⟨E'.f E'.E.genericPoint, ?_, ?_⟩
  · show Order.coheight _ = _
    by_cases hex : E'.IsExceptional
    · obtain ⟨c, T, hc, hT, -, hTc, -, -, hb⟩ :=
        le_isDiscrepancy_of_isSNC hR hsm hKR hsupp hsnc (fun G _ => hBR1 G) E' hex hE'd
      have hsum : 0 ≤ ∑ G ∈ T, (1 - BR.coeff G) :=
        Finset.sum_nonneg fun G _ => sub_nonneg.2 (hBR1 G)
      have hcT : c = T.card := by
        have h1 : (c : ℚ) ≤ T.card := by linarith
        exact le_antisymm (by exact_mod_cast h1) hTc
      rw [← hc, hcT, hT]
    · have hPw' : IsPairWith (g ≫ sX) n KR BR := by
        obtain ⟨-, -, m, hm, hC, -⟩ := hE'd
        exact ⟨hR, hKR, ⟨m, by exact_mod_cast hm.ne', hC⟩⟩
      obtain ⟨Γ, hΓc, hΓd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPw' E' hex
      have h1 : BR.coeff Γ = 1 := by have := hE'd.eq hΓd; linarith
      have hΓs : Γ ∈ sbig := hsupp (by
        rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, h1]; norm_num)
      have hy : E'.f E'.E.genericPoint = Γ.genericPoint := by
        have h2 : IsGenericPoint (E'.f E'.E.genericPoint) (Γ.support : Set R) :=
          hΓc ▸ E'.isGenericPoint_center
        have h3 : IsGenericPoint Γ.genericPoint (Γ.support : Set R) :=
          (AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ).symm
        exact h2.eq h3
      rw [hy, MMP.Mori.PrimeDivisor.coheight_genericPoint Γ]
      have : (sbig.filter fun G => Γ.genericPoint ∈ G.support) = {Γ} := by
        ext G
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨-, hG⟩; exact MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hG
        · intro h; rw [h]; exact ⟨hΓs, MMP.Flips.primeDivisor_genericPoint_mem_support Γ⟩
      rw [this, Finset.card_singleton]; rfl
  · show (E.center : Set X) = closure {g (E'.f E'.E.genericPoint)}
    rw [DivisorOver.center_eq_closure_genericPoint, hcent]

/-- Two components of coefficient one of the crepant boundary meeting at `y` give an lc place
whose centre is the image of a codimension-two stratum through `y`. -/
private theorem exists_isDiscrepancy_center_eq_closure_of_mem_inter
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPw : IsPairWith sX n K B)
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] (g : R ⟶ X)
    (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (hsm : IsSmoothScheme (g ≫ sX))
    {KR : Divisor R} (hKR : KR.IsCanonicalDivisor (g ≫ sX) n) {BR : QDivisor R}
    (hcrep : IsCrepantBoundary sX n K B g hR hgb BR)
    {sbig : Finset (MMP.Mori.PrimeDivisor R)} (hsupp : BR.support ⊆ sbig)
    (hsnc : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)))
    {P Q : MMP.Mori.PrimeDivisor R} (hP : BR.coeff P = 1) (hQ : BR.coeff Q = 1) (hPQ : P ≠ Q)
    {y : R} (hyP : y ∈ P.support) (hyQ : y ∈ Q.support) :
    ∃ z : R, z ∈ P.support ∧ z ∈ Q.support ∧ z ⤳ y ∧ ∃ E : DivisorOver ℂ sX,
      IsDiscrepancy sX n K B E (-1) ∧ (E.center : Set X) = closure {g z} := by
  haveI := hgb.isDominant
  have hmem : ∀ G : MMP.Mori.PrimeDivisor R, BR.coeff G = 1 → G ∈ sbig := fun G hG => hsupp (by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hG]; norm_num)
  have hn : topologicalKrullDim R = n := hKR.topologicalKrullDim_eq
  obtain ⟨D, -, hDP, hDQ, hDy, hDa⟩ :=
    exists_isExceptional_isDiscrepancy_eq_one_sub_sub_of_mem hR hsm hn hsnc (hmem P hP)
      (hmem Q hQ) hPQ hyP hyQ
  have hcr := IsPair.isDiscrepancy_iff_of_crepant hPw.isPair g hR hgb hPw.2.1 hKR (Or.inl hcrep)
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcr.1 hKR D
  have hc1 : c = -1 := by
    have := hDa KR BR hsupp c hc
    rw [hP, hQ] at this; linarith
  refine ⟨D.f D.E.genericPoint, hDP, hDQ, hDy, compDivisorOver g hR hgb D,
    (hcr.2 D _ (valuation_compDivisorOver g hR hgb D) (-1)).1 (hc1 ▸ hc), ?_⟩
  rw [DivisorOver.center_eq_closure_genericPoint]
  rfl

/-- The components of `∑_{P ∈ T} P` are the members of `T`. -/
private theorem support_sum_single {Y : Scheme.{0}} (T : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor Y).support = T := by
  classical
  ext P
  simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- **The intersection of two lc centres**, on a model where `g_* 𝒪_T = 𝒪_{C₁ ∪ C₂}`: every point
of `C₁ ∩ C₂` lies on an lc centre contained in `C₁ ∩ C₂`. -/
private theorem exists_lcCentre_subset_inter_of_isIso_app
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPw : IsPairWith sX n K B) (C₁ C₂ : IrreducibleCloseds X)
    (h12 : ¬ (C₁ : Set X) ⊆ C₂) (h21 : ¬ (C₂ : Set X) ⊆ C₁)
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] (g : R ⟶ X)
    [IsProper g] (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (hsm : IsSmoothScheme (g ≫ sX))
    {KR : Divisor R} (hKR : KR.IsCanonicalDivisor (g ≫ sX) n) {BR : QDivisor R}
    (hcrep : IsCrepantBoundary sX n K B g hR hgb BR)
    {sbig : Finset (MMP.Mori.PrimeDivisor R)} (hsupp : BR.support ⊆ sbig)
    (hsnc : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)))
    (T : Finset (MMP.Mori.PrimeDivisor R)) (hT1 : ∀ P ∈ T, BR.coeff P = 1)
    (W : Closeds X) (hW : (W : Set X) = (C₁ : Set X) ∪ C₂)
    (φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal W).subscheme)
    (hφ : φ ≫ (Scheme.IdealSheafData.vanishingIdeal W).subschemeι =
      (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g)
    (hiso : ∀ U, IsIso (φ.app U)) (hTW : g.base '' (⋃ P ∈ T, (P.support : Set R)) = W)
    {x : X} (hx : x ∈ (C₁ : Set X) ∩ C₂) :
    ∃ Z : IrreducibleCloseds X,
      (∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1)) ∧
        (Z : Set X) ⊆ (C₁ : Set X) ∩ C₂ ∧ x ∈ Z := by
  classical
  have hgc : IsClosedMap g.base := g.isClosedMap
  have hPW : ∀ P ∈ T, g.base '' P.support ⊆ W := fun P hP => by
    rw [← hTW]; exact Set.image_mono (Set.subset_biUnion_of_mem (u := fun P :
        MMP.Mori.PrimeDivisor R =>
      (P.support : Set R)) hP)
  have hirr : ∀ P : MMP.Mori.PrimeDivisor R, IsIrreducible (g.base '' P.support) := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure.image _ g.continuous.continuousOn
  have hlab : ∀ P ∈ T, g.base '' P.support ⊆ C₁ ∨ g.base '' P.support ⊆ C₂ := fun P hP =>
    isPreirreducible_iff_isClosed_union_isClosed.1 (hirr P).isPreirreducible _ _ C₁.isClosed
      C₂.isClosed (hW ▸ hPW P hP)
  have hcov : ∀ (C C' : IrreducibleCloseds X), (W : Set X) = (C : Set X) ∪ C' →
      ¬ (C : Set X) ⊆ C' → x ∈ (C : Set X) →
      ∃ P ∈ T, g.base '' P.support ⊆ C ∧ x ∈ g.base '' P.support := by
    intro C C' hCC hCC' hxC
    let A : Set X := ⋃ P ∈ T, ⋃ (_ : g.base '' P.support ⊆ C), g.base '' P.support
    have hA : IsClosed A := isClosed_biUnion_finset fun P _ =>
      isClosed_iUnion_of_finite fun _ => hgc _
          (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P)
    have hsub : (C : Set X) ⊆ A ∪ C' := by
      intro z hz
      have hzW : z ∈ g.base '' (⋃ P ∈ T, (P.support : Set R)) := by
        rw [hTW, hCC]; exact Or.inl hz
      rw [Set.image_iUnion₂] at hzW
      obtain ⟨P, hP, hzP⟩ := Set.mem_iUnion₂.1 hzW
      have hPW' := hPW P hP
      rw [hCC] at hPW'
      rcases isPreirreducible_iff_isClosed_union_isClosed.1 (hirr P).isPreirreducible _ _ C.isClosed
        C'.isClosed hPW' with h | h
      · exact Or.inl (Set.mem_iUnion₂.2 ⟨P, hP, Set.mem_iUnion.2 ⟨h, hzP⟩⟩)
      · exact Or.inr (h hzP)
    rcases isPreirreducible_iff_isClosed_union_isClosed.1 C.isIrreducible.isPreirreducible _ _ hA
      C'.isClosed hsub with h | h
    · obtain ⟨P, hP, h'⟩ := Set.mem_iUnion₂.1 (h hxC)
      obtain ⟨hPC, hxP⟩ := Set.mem_iUnion.1 h'
      exact ⟨P, hP, hPC, hxP⟩
    · exact absurd h hCC'
  obtain ⟨P, hP, Q, hQ, hPC, hQC, y, ⟨hyP, hyQ⟩, rfl⟩ :=
    exists_mem_image_inter_of_isIso_app g hgc T W φ hφ hiso C₁ C₂ hlab
      (hcov C₁ C₂ hW h12 hx.1) (hcov C₂ C₁ (by rw [hW, Set.union_comm]) h21 hx.2)
  by_cases hPQ : P = Q
  · subst hPQ
    obtain ⟨E, hE, hEc⟩ := exists_isDiscrepancy_center_eq_image_of_coeff_eq_one g hgc hR hgb
      hcrep (hT1 P hP)
    refine ⟨E.center, ⟨E, rfl, hE⟩, ?_, ?_⟩
    · rw [hEc]; exact Set.subset_inter hPC hQC
    · show g y ∈ (E.center : Set X)
      rw [hEc]; exact ⟨y, hyP, rfl⟩
  · obtain ⟨z, hzP, hzQ, hzy, E, hE, hEc⟩ := exists_isDiscrepancy_center_eq_closure_of_mem_inter
      hPw g hR hgb hsm hKR hcrep hsupp hsnc (hT1 P hP) (hT1 Q hQ) hPQ hyP hyQ
    refine ⟨E.center, ⟨E, rfl, hE⟩, ?_, ?_⟩
    · rw [hEc]
      refine closure_minimal (Set.singleton_subset_iff.2 ?_)
        (hgc _ ((MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P).inter
            (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support Q))) |>.trans ?_
      · exact ⟨z, ⟨hzP, hzQ⟩, rfl⟩
      · exact Set.subset_inter ((Set.image_mono Set.inter_subset_left).trans hPC)
          ((Set.image_mono Set.inter_subset_right).trans hQC)
    · show g y ∈ (E.center : Set X)
      rw [hEc]
      exact specializes_iff_mem_closure.1 (hzy.map g.continuous)

/-- The generic point of the reduced subscheme on an irreducible closed set `W` is the generic
point of `W`. -/
private theorem isGenericPoint_subschemeι_genericPoint {Y : Scheme.{0}} (W : Closeds Y)
    [IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal W).subscheme] :
    IsGenericPoint ((Scheme.IdealSheafData.vanishingIdeal W).subschemeι
      (genericPoint (Scheme.IdealSheafData.vanishingIdeal W).subscheme)) (W : Set Y) := by
  have h := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal W).subscheme).image
    (Scheme.IdealSheafData.vanishingIdeal W).subschemeι.continuous
  rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, W.isClosed.closure_eq] at h
  exact h

/-- **A minimal lc centre is normal**, on a model where `g_* 𝒪_T = 𝒪_W`. -/
private theorem isNormal_of_isIso_app
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hPw : IsPairWith sX n K B) (W : IrreducibleCloseds X)
    (hmin : ∀ E : DivisorOver ℂ sX, IsDiscrepancy sX n K B E (-1) →
      (E.center : Set X) ⊆ W → E.center = W)
    {R : Scheme.{0}} [IsIntegral R] [IsLocallyNoetherian R] [IsNormal R] (g : R ⟶ X)
    [IsProper g] (hR : IsNormalVariety ℂ (g ≫ sX)) (hgb : IsBirationalMorphism g)
    (hsm : IsSmoothScheme (g ≫ sX))
    {KR : Divisor R} (hKR : KR.IsCanonicalDivisor (g ≫ sX) n) {BR : QDivisor R}
    (hcrep : IsCrepantBoundary sX n K B g hR hgb BR)
    {sbig : Finset (MMP.Mori.PrimeDivisor R)} (hsupp : BR.support ⊆ sbig)
    (hsnc : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)))
    (T : Finset (MMP.Mori.PrimeDivisor R)) (hT1 : ∀ P ∈ T, BR.coeff P = 1)
    (φ : (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme)
    (hφ : φ ≫ (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subschemeι =
      (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι ≫ g)
    (hiso : ∀ U, IsIso (φ.app U))
    (hTW : g.base '' (⋃ P ∈ T, (P.support : Set R)) = W) :
    IsNormal (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme := by
  classical
  set ιW := (Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subschemeι
  set ιT := (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).suppIdeal.subschemeι
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal (⟨(W : Set X), W.isClosed⟩ : Closeds X)
        W.isIrreducible
  have hgc : IsClosedMap g.base := g.isClosedMap
  have hpt : ∀ a, ιW (φ a) = g (ιT a) := fun a => congrArg (fun h => h.base a) hφ
  have hξ := isGenericPoint_subschemeι_genericPoint (⟨(W : Set X), W.isClosed⟩ : Closeds X)
  -- a point of `T` lying over the generic point of `W` maps to the generic point
  have hover : ∀ a, IsGenericPoint (g (ιT a)) (W : Set X) →
      φ a = genericPoint (Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme := fun a ha =>
    ιW.isClosedEmbedding.injective (by rw [hpt]; exact ha.eq hξ)
  -- the components dominate `W`
  have hPW : ∀ P ∈ T, g.base '' P.support = W := by
    intro P hP
    obtain ⟨E, hE, hEc⟩ := exists_isDiscrepancy_center_eq_image_of_coeff_eq_one g hgc hR hgb
      hcrep (hT1 P hP)
    have hsub : (E.center : Set X) ⊆ W := by
      rw [hEc, ← hTW]
      exact Set.image_mono (Set.subset_biUnion_of_mem (u := fun P : MMP.Mori.PrimeDivisor R =>
        (P.support : Set R)) hP)
    rw [← hEc, hmin E hE hsub]
  have hDsupp := support_sum_single T
  have hgen : ∀ P ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).support, ∀ a, ιT a =
      P.genericPoint →
      φ a = genericPoint (Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme := by
    intro P hP a ha
    rw [hDsupp] at hP
    refine hover a ?_
    rw [ha]
    have h0 : IsGenericPoint P.genericPoint (P.support : Set R) :=
      (AlgebraicGeometry.PrimeDivisor.support_eq_closure P).symm
    have h := h0.image g.continuous
    rwa [(hgc _ (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P)).closure_eq,
        hPW P hP] at h
  have hstr : ∀ P ∈ (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R).support, ∀ Q ∈ (∑ P ∈ T,
      Finsupp.single P (1 : ℤ) : Divisor R).support, P ≠ Q → ∀ y ∈ P.support, y ∈ Q.support →
      ∃ z, z ∈ P.support ∧ z ∈ Q.support ∧ z ⤳ y ∧ ∀ a, ιT a = z →
        φ a = genericPoint (Scheme.IdealSheafData.vanishingIdeal
            (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme := by
    intro P hP Q hQ hPQ y hyP hyQ
    rw [hDsupp] at hP hQ
    obtain ⟨z, hzP, hzQ, hzy, E, hE, hEc⟩ := exists_isDiscrepancy_center_eq_closure_of_mem_inter
      hPw g hR hgb hsm hKR hcrep hsupp hsnc (hT1 P hP) (hT1 Q hQ) hPQ hyP hyQ
    refine ⟨z, hzP, hzQ, hzy, fun a ha => hover a ?_⟩
    have hsub : (E.center : Set X) ⊆ W := by
      rw [hEc, ← hPW P hP]
      exact closure_minimal (Set.singleton_subset_iff.2 ⟨z, hzP, rfl⟩)
        (hgc _ (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P))
    have h := hmin E hE hsub
    rw [ha]
    show closure {g z} = (W : Set X)
    rw [← hEc, h]
  have hsurj : Function.Surjective φ.base := by
    intro w
    have hw : ιW w ∈ (W : Set X) := by
      have : ιW w ∈ Set.range ιW := ⟨w, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    have hw' : ιW w ∈ g.base '' (⋃ P ∈ T, (P.support : Set R)) := by rw [hTW]; exact hw
    obtain ⟨y, hy, hyw⟩ := hw'
    obtain ⟨a, ha⟩ : y ∈ Set.range ιT := by rw [range_subschemeι_sum_single]; exact hy
    exact ⟨a, ιW.isClosedEmbedding.injective (by rw [hpt, ha, hyw])⟩
  -- the snc hypotheses for the components of `T`
  have hTs : T ⊆ sbig := fun P hP => hsupp (by
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hT1 P hP]; norm_num)
  have hsncD' : DivisorWithCoeffs.IsSNC (g ≫ sX) (∑ P ∈ T, Finsupp.single P (1 : ℤ) : Divisor R) :=
    hsnc.of_support_subset (by rw [hDsupp, support_sum_single]; exact hTs)
  have hFl : MMP.Flips.IsSNCDivisor (g ≫ sX) (∑ E ∈ sbig, Finsupp.single E (1 : ℤ)) := by
    refine ⟨fun E => ?_, hsnc.1, fun p _ => hsnc.2 p⟩
    rw [DivisorWithCoeffs.coeff_apply]
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs <;> simp
  have hsncD : MMP.Intersection.IsSNCDivisor (g ≫ sX) (∑ P ∈ T, Finsupp.single P (1 : ℤ) :
      Divisor R) :=
    MMP.Flips.IsSNCDivisor.isSNCDivisor_of_support_subset hFl (fun E => by
      rw [DivisorWithCoeffs.coeff_apply]
      simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
      split_ifs <;> simp) (by rw [hDsupp, support_sum_single]; exact hTs)
  haveI : LocallyOfFiniteType (g ≫ sX) := hR.1.toLocallyOfFiniteType
  haveI : LocallyOfFinitePresentation (g ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := g ≫ sX)).mpr inferInstance
  haveI : Smooth (g ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  -- normality on affine opens
  rw [AlgebraicGeometry.isNormal_iff_forall_affineOpen_normal]
  intro U hU
  letI : IsDomain Γ((Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1) := IsIntegral.component_integral U.1
  let φF : FractionRing Γ((Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1) →+*
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme.functionField :=
    IsFractionRing.lift (g := ((Scheme.IdealSheafData.vanishingIdeal
        (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme.germToFunctionField
      U.1).hom) ((Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme.germToFunctionField_injective U.1)
  have hφF : ∀ a, φF (algebraMap _ (FractionRing _) a) =
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme.germToFunctionField U.1 a :=
    fun a => IsFractionRing.lift_algebraMap _ a
  rw [isIntegrallyClosed_iff (FractionRing Γ((Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1))]
  intro z hz
  have hz' : IsIntegral Γ((Scheme.IdealSheafData.vanishingIdeal
      (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1) (φF z) := by
    change (algebraMap Γ((Scheme.IdealSheafData.vanishingIdeal
        (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1) _).IsIntegralElem (φF z)
    simpa only [show φF.comp (algebraMap Γ((Scheme.IdealSheafData.vanishingIdeal
        (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1) (FractionRing
        Γ((Scheme.IdealSheafData.vanishingIdeal (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme,
        U.1))) =
      algebraMap Γ((Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme, U.1)
          (Scheme.IdealSheafData.vanishingIdeal
          (⟨(W : Set X), W.isClosed⟩ : Closeds X)).subscheme.functionField from by
        ext a; exact hφF a] using RingHom.IsIntegralElem.map hz φF
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_isIntegral_of_isIso_app hR.1 hsncD' hsncD φ
    hiso hsurj hgen hstr U.1 (φF z) hz'
  exact ⟨a, φF.injective ((hφF a).trans ha)⟩

/-- **Lc centres.** Let `(X, B)` be an lc pair, with canonical divisor `K` of dimension `n` and
effective `ℚ`-boundary `B`, on a normal projective variety over `ℂ`, and call `Z` an lc centre if
`Z` is the centre of a divisor `E` over `X` with `a(E, X, B) = -1`. Then the set of lc centres is
finite, the intersection of any two lc centres is the union of the lc centres contained in it, and
every lc centre `W` that contains no other lc centre is normal with its reduced scheme
structure. -/
@[mmp "lem_mmp_lc_bpf_minimal_centre_normal"]
public theorem IsLcPair.finite_lcCentres_and_isNormal_of_minimal
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hproj : IsProjectiveMorphism sX)
    {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (hBeff : B.IsEffective) :
    let lcCentres : Set (IrreducibleCloseds X) :=
      {Z | ∃ E : DivisorOver ℂ sX, E.center = Z ∧ IsDiscrepancy sX n K B E (-1)}
    lcCentres.Finite ∧
      (∀ C₁ ∈ lcCentres, ∀ C₂ ∈ lcCentres,
        ((C₁ : Set X) ∩ C₂) = ⋃ Z ∈ {Z ∈ lcCentres | (Z : Set X) ⊆ (C₁ : Set X) ∩ C₂},
          (Z : Set X)) ∧
      ∀ W ∈ lcCentres, (∀ Z ∈ lcCentres, (Z : Set X) ⊆ W → Z = W) →
        IsNormal (Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩).subscheme := by
  intro lcCentres
  classical
  have hPw : IsPairWith sX n K B := hB.1
  have hX : IsNormalVariety ℂ sX := hB.1.1
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj
  haveI : CompactSpace X :=
    haveI := hX.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  have hsupset : ∀ C₁ C₂ : IrreducibleCloseds X,
      (⋃ Z ∈ {Z ∈ lcCentres | (Z : Set X) ⊆ (C₁ : Set X) ∩ C₂}, (Z : Set X)) ⊆
        (C₁ : Set X) ∩ C₂ := fun C₁ C₂ => Set.iUnion₂_subset fun Z hZ => hZ.2
  by_cases hB1 : ∀ P, B.coeff P ≤ 1
  · -- the model
    have hmodel := fun (W : Closeds X) (S : Set (IrreducibleCloseds X)) hS hW =>
      exists_isIso_app_comp_subschemeι_vanishingIdeal_and_isCrepantBoundary_of_coeff_le_one sX
        hproj hB hBeff hB1 W S hS hW
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨R, _, _, _, g, hR, hgb, -, -, hsm, -, hgp, -, -, -, KR, BR, sbig, hKR, hcrep,
        hBR1, -, hsupp, hsnc⟩ := hmodel ⊥ ∅ (by simp) (by simp)
      haveI : IsProper g := hgp.isProper
      haveI : CompactSpace R :=
        haveI := hR.1.toQuasiCompact
        QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
      haveI : AlgebraicGeometry.IsNoetherian R := {}
      exact finite_lcCentres_of_isCrepantBoundary hPw g hR hgb hsm hKR hcrep hBR1 hsupp hsnc
    · intro C₁ hC₁ C₂ hC₂
      refine Set.Subset.antisymm (fun x hx => ?_) (hsupset C₁ C₂)
      by_cases h12 : (C₁ : Set X) ⊆ C₂
      · exact Set.mem_iUnion₂.2 ⟨C₁, ⟨hC₁, Set.subset_inter le_rfl h12⟩, hx.1⟩
      by_cases h21 : (C₂ : Set X) ⊆ C₁
      · exact Set.mem_iUnion₂.2 ⟨C₂, ⟨hC₂, Set.subset_inter h21 le_rfl⟩, hx.2⟩
      let W : Closeds X := ⟨(C₁ : Set X) ∪ C₂, C₁.isClosed.union C₂.isClosed⟩
      obtain ⟨R, _, _, _, g, hR, hgb, T, φ, hsm, -, hgp, hTW, hφ, hiso, KR, BR, sbig, hKR,
        hcrep, -, hT1, hsupp, hsnc⟩ := hmodel W {C₁, C₂}
        (by rintro Z (rfl | rfl); exacts [hC₁, hC₂]) (by simp [W])
      haveI : IsProper g := hgp.isProper
      obtain ⟨Z, hZ, hZsub, hxZ⟩ := exists_lcCentre_subset_inter_of_isIso_app hPw C₁ C₂ h12 h21
        g hR hgb hsm hKR hcrep hsupp hsnc T hT1 W rfl φ hφ hiso hTW hx
      exact Set.mem_iUnion₂.2 ⟨Z, ⟨hZ, hZsub⟩, hxZ⟩
    · intro W hW hmin
      obtain ⟨R, _, _, _, g, hR, hgb, T, φ, hsm, -, hgp, hTW, hφ, hiso, KR, BR, sbig, hKR,
        hcrep, -, hT1, hsupp, hsnc⟩ := hmodel ⟨(W : Set X), W.isClosed⟩ {W}
        (by rintro Z rfl; exact hW) (by simp)
      haveI : IsProper g := hgp.isProper
      exact isNormal_of_isIso_app hPw W (fun E hE hsub => hmin _ ⟨E, rfl, hE⟩ hsub) g hR hgb hsm
        hKR hcrep hsupp hsnc T hT1 φ hφ hiso hTW
  · -- the curve case
    have hn : n ≤ 1 := by
      by_contra h
      exact hB1 fun P => coeff_le_one_of_isLcPair_of_two_le hB (by omega) P
    have hd : topologicalKrullDim X ≤ 1 := by
      rw [hB.1.2.1.topologicalKrullDim_eq]; exact_mod_cast hn
    have hpt : ∀ Z ∈ lcCentres, ∃ Γ : MMP.Mori.PrimeDivisor X, B.coeff Γ = 1 ∧
        (Z : Set X) = {Γ.genericPoint} := by
      rintro Z ⟨E, rfl, hE⟩
      exact exists_center_eq_singleton_of_topologicalKrullDim_le_one hPw hd E hE
    refine ⟨?_, ?_, ?_⟩
    · refine (B.support.finite_toSet.biUnion fun Γ _ =>
        (show ({Z : IrreducibleCloseds X | (Z : Set X) = {Γ.genericPoint}}).Subsingleton from
          fun Z₁ h₁ Z₂ h₂ => SetLike.coe_injective (h₁.trans h₂.symm)).finite).subset ?_
      intro Z hZ
      obtain ⟨Γ, hΓ, hZΓ⟩ := hpt Z hZ
      refine Set.mem_iUnion₂.2 ⟨Γ, ?_, hZΓ⟩
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hΓ]
      norm_num
    · intro C₁ hC₁ C₂ hC₂
      refine Set.Subset.antisymm (fun x hx => ?_) (hsupset C₁ C₂)
      obtain ⟨Γ, -, hΓ⟩ := hpt C₁ hC₁
      have hsub : (C₁ : Set X) ⊆ C₂ := by
        rw [hΓ, Set.singleton_subset_iff]
        have := hx.1; rw [hΓ] at this; rw [← this]; exact hx.2
      exact Set.mem_iUnion₂.2 ⟨C₁, ⟨hC₁, Set.subset_inter le_rfl hsub⟩, hx.1⟩
    · intro W hW _
      obtain ⟨Γ, -, hΓ⟩ := hpt W hW
      exact isNormal_subscheme_vanishingIdeal_singleton _ hΓ

end MMP.Mori
