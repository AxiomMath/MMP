module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Threefold.CrepantTerminalModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.TerminalComparisonModels
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective

/-!
# Finiteness for convergent small klt weak models

Let `X` be a normal projective `ℚ`-factorial complex threefold over a projective variety `S`,
and let `B_i → B` be a convergent sequence of effective real boundaries on `X` supported on
one finite set of prime divisors, with `(X, B)` klt. Suppose that every `(X, B_i)` has a
projective `ℚ`-factorial nef weak model `φ_i : X ⤏ X_i` over `S` which is an isomorphism in
codimension one. Then the nef models `(X_i, (φ_i)_* B_i)` fall into finitely many equivalence
classes: there are finitely many indices `j` such that every `X_i` is equivalent, through
`φ_j ∘ φ_i⁻¹`, to one of the `X_j`.

## Main results

* `MMP.Fourfold.exists_finset_isNefModelEquivalent_of_tendsto`.

## Implementation notes

The weak model `X_i` carries the canonical divisor `(φ_i)_* K_X` and the boundary
`(φ_i)_* B_i`, as in `MMP.Fourfold.IsNefWeakModel`. Convergence `B_i → B` is coefficientwise;
since all the `B_i` are supported on one finite set, this is convergence in the
finite-dimensional real space of divisors on that set. Isomorphism in codimension one means
that neither `φ_i` nor `φ_i⁻¹` contracts a prime divisor; the second half is part of
`MMP.Fourfold.IsNefWeakModel`. The comparison map `X_i ⤏ X_j` is the composite
`φ_j ∘ φ_i⁻¹`, written through partial isomorphisms representing `φ_i` and `φ_j`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

universe u

section

namespace Proof_thm_fourfold_convergent_klt_weak_models_finite

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Partial isomorphisms and composition of rational maps -/

section PartialIso

variable {X Y Z : Scheme.{u}}

private theorem isoOfLE_inv_ι' {U V : X.Opens} (h : U ≤ V) :
    (Scheme.Opens.isoOfLE h).inv ≫ (V.ι ⁻¹ᵁ U).ι = X.homOfLE h := by
  rw [← cancel_mono V.ι]
  simp

private theorem restrictSource_iso_hom_ι (e : X.PartialIso Y) (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ e.source) :
    (e.restrictSource U hU hU').iso.hom ≫ (e.restrictSource U hU hU').target.ι =
      X.homOfLE hU' ≫ e.iso.hom ≫ e.target.ι := by
  simp [Scheme.PartialIso.restrictSource, reassoc_of% isoOfLE_inv_ι']

private theorem restrictSource_target_le (e : X.PartialIso Y) (U : X.Opens) (hU : Dense (U : Set X))
    (hU' : U ≤ e.source) : (e.restrictSource U hU hU').target ≤ e.target := by
  change e.target.ι ''ᵁ _ ≤ e.target
  exact (Scheme.Hom.image_le_opensRange _ _).trans (by simp)

private theorem restrictSource_iso_hom_homOfLE (e : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ e.source) :
    (e.restrictSource U hU hU').iso.hom ≫ Y.homOfLE (restrictSource_target_le e U hU hU') =
      X.homOfLE hU' ≫ e.iso.hom := by
  refine (cancel_mono e.target.ι).1 ?_
  exact (Category.assoc _ _ _).trans ((congrArg _ (Scheme.homOfLE_ι _ _)).trans
    ((restrictSource_iso_hom_ι e U hU hU').trans (Category.assoc _ _ _).symm))

private theorem restrictTarget_source_le (e : X.PartialIso Y) (V : Y.Opens) (hV : Dense (V : Set Y))
    (hV' : V ≤ e.target) : (e.restrictTarget V hV hV').source ≤ e.source :=
  restrictSource_target_le e.symm V hV hV'

private theorem restrictTarget_iso_hom_ι (e : X.PartialIso Y) (V : Y.Opens) (hV : Dense (V : Set Y))
    (hV' : V ≤ e.target) :
    (e.restrictTarget V hV hV').iso.hom ≫ V.ι =
      X.homOfLE (restrictTarget_source_le e V hV hV') ≫ e.iso.hom ≫ e.target.ι := by
  have h2 := restrictSource_iso_hom_homOfLE e.symm V hV hV'
  change (e.symm.restrictSource V hV hV').iso.inv ≫ V.ι = _
  refine (Iso.inv_comp_eq _).2 ?_
  refine Eq.trans ?_ ((reassoc_of% h2) (e.iso.hom ≫ e.target.ι)).symm
  exact (by simp : V.ι = Y.homOfLE hV' ≫ e.iso.inv ≫ e.iso.hom ≫ e.target.ι)

private theorem isDominant_toPartialMap_hom (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

private theorem comp_toRationalMap_eq {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

private theorem toRationalMap_trans'_eq [IsIntegral X] [Nonempty Y] (f : X.PartialIso Y)
    (g : Y.PartialIso Z) (F : X.PartialIso Y) (G : Y.PartialIso Z) (e : F.target = G.source)
    (hFs : F.source ≤ f.source) (hGs : G.source ≤ g.source)
    (hF : F.iso.hom ≫ F.target.ι = X.homOfLE hFs ≫ f.iso.hom ≫ f.target.ι)
    (hG : G.iso.hom ≫ G.target.ι = Y.homOfLE hGs ≫ g.iso.hom ≫ g.target.ι) :
    haveI := isDominant_toPartialMap_hom f
    (F.trans' G e).toRationalMap = f.toRationalMap.comp g.toRationalMap := by
  haveI := isDominant_toPartialMap_hom f
  have hFs' : F.source ≤ f.toPartialMap.domain := hFs
  have hGs' : G.source ≤ g.toPartialMap.domain := hGs
  rw [comp_toRationalMap_eq f.toPartialMap g.toPartialMap (O := F.source) F.dense_source hFs'
    (F.iso.hom ≫ (Y.isoOfEq e).hom ≫ Y.homOfLE hGs') (by
      rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι]
      exact hF)]
  change (F.trans' G e).toPartialMap.toRationalMap = _
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change (F.iso.hom ≫ (Y.isoOfEq e).hom ≫ G.iso.hom) ≫ G.target.ι =
    (X.isoOfEq rfl).hom ≫ ((F.iso.hom ≫ (Y.isoOfEq e).hom ≫ Y.homOfLE hGs') ≫
      g.iso.hom ≫ g.target.ι)
  simp [hG]
  rfl

private theorem toRationalMap_trans [IsIntegral X] [Nonempty Y] (f : X.PartialIso Y)
    (g : Y.PartialIso Z) [f.toRationalMap.IsDominant] :
    (f.trans g).toRationalMap = f.toRationalMap.comp g.toRationalMap := by
  have hV := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  haveI := isDominant_toPartialMap_hom f
  exact toRationalMap_trans'_eq f g _ _ rfl (restrictTarget_source_le f _ hV inf_le_left)
    inf_le_right (restrictTarget_iso_hom_ι f _ hV inf_le_left)
    (restrictSource_iso_hom_ι g _ hV inf_le_right)

private theorem isDominant_toRationalMap (e : X.PartialIso Y) : e.toRationalMap.IsDominant := by
  have := isDominant_toPartialMap_hom e
  infer_instance

private theorem isDominant_of_isBirational {X Y : Scheme.{u}} {φ : X.RationalMap Y}
    (hφ : RationalMap.IsBirational φ) : φ.IsDominant := by
  obtain ⟨e, rfl⟩ := hφ
  have := isDominant_toPartialMap_hom e
  infer_instance

private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- A birational map followed by its inverse is the identity. -/
private theorem comp_eq_id_of_isInverse {X Y : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    {f : X.RationalMap Y} [f.IsDominant] {h : Y.RationalMap X}
    (H : RationalMap.IsInverse f h) : f.comp h = Scheme.RationalMap.id X := by
  obtain ⟨e, rfl, rfl⟩ := H
  have := isDominant_toPartialMap_hom e
  rw [comp_toRationalMap_eq e.toPartialMap e.symm.toPartialMap (O := e.source) e.dense_source le_rfl
    e.iso.hom (by
      change e.iso.hom ≫ e.target.ι = X.homOfLE le_rfl ≫ e.iso.hom ≫ e.target.ι
      rw [Scheme.homOfLE_rfl, Category.id_comp])]
  have : (⟨e.source, e.dense_source, e.iso.hom ≫ e.symm.toPartialMap.hom⟩ : X.PartialMap X) =
      ⟨e.source, e.dense_source, e.source.ι ≫ 𝟙 X⟩ := by
    congr 1
    change e.iso.hom ≫ e.iso.inv ≫ e.source.ι = _
    simp
  exact (congrArg Scheme.PartialMap.toRationalMap this).trans (toRationalMap_ι_comp _ (𝟙 X))

/-- The composite `e⁻¹ ∘ e` of a partial isomorphism with its inverse represents the identity. -/
private theorem toRationalMap_symm_trans_self [IsIntegral X] [Nonempty Y] (e : Y.PartialIso X) :
    (e.symm.trans e).toRationalMap = Scheme.RationalMap.id X := by
  haveI := isDominant_toRationalMap e.symm
  rw [toRationalMap_trans]
  exact comp_eq_id_of_isInverse ⟨e.symm, rfl, rfl⟩

private theorem comp_eq_comp_of_eq {X Y Z : Scheme.{u}} [IrreducibleSpace X] [Nonempty Y]
    {f f' : X.RationalMap Y} [f.IsDominant] [f'.IsDominant] (h : f = f') (g : Y.RationalMap Z) :
    f.comp g = f'.comp g := by
  subst h; rfl

/-- If `e ∘ k = id`, then `k` is the rational map of `e⁻¹`. -/
private theorem symm_toRationalMap_eq_of_comp_eq_id {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (e : X.PartialIso Y) {k : Y.RationalMap X}
    [e.toRationalMap.IsDominant] (hk : e.toRationalMap.comp k = Scheme.RationalMap.id X) :
    e.symm.toRationalMap = k := by
  haveI := isDominant_toRationalMap e.symm
  haveI := isDominant_toRationalMap e.symm.symm
  calc e.symm.toRationalMap = e.symm.toRationalMap.comp (Scheme.RationalMap.id X) :=
        (Scheme.RationalMap.comp_id _).symm
    _ = e.symm.toRationalMap.comp (e.toRationalMap.comp k) := by rw [hk]
    _ = (e.symm.toRationalMap.comp e.toRationalMap).comp k :=
        (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id Y).comp k :=
      comp_eq_comp_of_eq (comp_eq_id_of_isInverse ⟨e.symm, rfl, rfl⟩) k
    _ = k := Scheme.RationalMap.id_comp k

/-- **Transport of partial isomorphisms along a birational morphism.** If `e₁`, `e₂` represent
`φ₁ ∘ h`, `φ₂ ∘ h` for a birational morphism `h : Y ⟶ X`, then there are partial isomorphisms
`f₁`, `f₂` representing `φ₁`, `φ₂` with `f₂ ∘ f₁⁻¹ = e₂ ∘ e₁⁻¹` as rational maps. -/
private theorem exists_partialIso_trans_eq {X Y Z₁ Z₂ : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z₁] [IsIntegral Z₂] (h : Y ⟶ X) [IsDominant h]
    (hh : ∃ eh : Y.PartialIso X, eh.toRationalMap = h.toRationalMap)
    (φ₁ : X.RationalMap Z₁) (φ₂ : X.RationalMap Z₂) (e₁ : Y.PartialIso Z₁)
    (e₂ : Y.PartialIso Z₂) (he₁ : e₁.toRationalMap = h.toRationalMap.comp φ₁)
    (he₂ : e₂.toRationalMap = h.toRationalMap.comp φ₂) :
    ∃ (f₁ : X.PartialIso Z₁) (f₂ : X.PartialIso Z₂), f₁.toRationalMap = φ₁ ∧
      f₂.toRationalMap = φ₂ ∧
        (f₁.symm.trans f₂).toRationalMap = (e₁.symm.trans e₂).toRationalMap := by
  obtain ⟨eh, heh⟩ := hh
  haveI := isDominant_toRationalMap eh
  haveI := isDominant_toRationalMap eh.symm
  haveI := isDominant_toRationalMap eh.symm.symm
  haveI := isDominant_toRationalMap e₁
  haveI := isDominant_toRationalMap e₁.symm
  haveI := isDominant_toRationalMap e₁.symm.symm
  haveI := isDominant_toRationalMap e₂
  have hcomp : ∀ {W : Scheme.{u}} (e : Y.PartialIso W) (φ : X.RationalMap W),
      e.toRationalMap = h.toRationalMap.comp φ → (eh.symm.trans e).toRationalMap = φ := by
    intro W e φ he
    have h1 : eh.symm.toRationalMap.comp eh.toRationalMap = Scheme.RationalMap.id X :=
      comp_eq_id_of_isInverse ⟨eh.symm, rfl, rfl⟩
    rw [toRationalMap_trans, he, ← comp_eq_comp_of_eq heh φ, ← Scheme.RationalMap.comp_assoc]
    simp only [h1, Scheme.RationalMap.id_comp]
  refine ⟨eh.symm.trans e₁, eh.symm.trans e₂, hcomp e₁ φ₁ he₁, hcomp e₂ φ₂ he₂, ?_⟩
  haveI := isDominant_toRationalMap (eh.symm.trans e₁)
  haveI := isDominant_toRationalMap (eh.symm.trans e₁).symm
  haveI := isDominant_toRationalMap (e₁.symm.trans eh)
  have he₁e : e₁.toRationalMap.comp e₁.symm.toRationalMap = Scheme.RationalMap.id Y :=
    comp_eq_id_of_isInverse ⟨e₁, rfl, rfl⟩
  have hehe : eh.toRationalMap.comp eh.symm.toRationalMap = Scheme.RationalMap.id Y :=
    comp_eq_id_of_isInverse ⟨eh, rfl, rfl⟩
  have hehe' : eh.symm.toRationalMap.comp eh.toRationalMap = Scheme.RationalMap.id X :=
    comp_eq_id_of_isInverse ⟨eh.symm, rfl, rfl⟩
  have hsymm : (eh.symm.trans e₁).symm.toRationalMap = (e₁.symm.trans eh).toRationalMap := by
    refine symm_toRationalMap_eq_of_comp_eq_id _ ?_
    calc (eh.symm.trans e₁).toRationalMap.comp (e₁.symm.trans eh).toRationalMap
        = (eh.symm.toRationalMap.comp e₁.toRationalMap).comp
            (e₁.symm.toRationalMap.comp eh.toRationalMap) := by
          simp only [toRationalMap_trans]
      _ = eh.symm.toRationalMap.comp ((e₁.toRationalMap.comp e₁.symm.toRationalMap).comp
            eh.toRationalMap) := by
          simp only [Scheme.RationalMap.comp_assoc]
      _ = Scheme.RationalMap.id X := by
          simp only [he₁e, Scheme.RationalMap.id_comp, hehe']
  calc ((eh.symm.trans e₁).symm.trans (eh.symm.trans e₂)).toRationalMap
      = (eh.symm.trans e₁).symm.toRationalMap.comp (eh.symm.trans e₂).toRationalMap :=
        toRationalMap_trans _ _
    _ = (e₁.symm.trans eh).toRationalMap.comp (eh.symm.trans e₂).toRationalMap :=
        comp_eq_comp_of_eq hsymm _
    _ = (e₁.symm.toRationalMap.comp eh.toRationalMap).comp
          (eh.symm.toRationalMap.comp e₂.toRationalMap) := by
        simp only [toRationalMap_trans]
    _ = e₁.symm.toRationalMap.comp ((eh.toRationalMap.comp eh.symm.toRationalMap).comp
          e₂.toRationalMap) := by
        simp only [Scheme.RationalMap.comp_assoc]
    _ = (e₁.symm.trans e₂).toRationalMap := by
        simp only [hehe, Scheme.RationalMap.id_comp, toRationalMap_trans]

end PartialIso

/-! ### Finitely many classes from convergent subsequences -/

/-- A relation `R` on `ℕ` which is reflexive and such that every subsequence has a further
subsequence all of whose terms are `R`-related to finitely many of its terms has a finite set of
representatives: every `i` is `R`-related to some member of a finite set. -/
private theorem exists_finset_of_forall_strictMono {R : ℕ → ℕ → Prop} (hrefl : ∀ i, R i i)
    (hsub : ∀ σ : ℕ → ℕ, StrictMono σ → ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∃ J : Finset ℕ, ∀ n, ∃ m ∈ J, R (σ (τ n)) (σ (τ m))) :
    ∃ F : Finset ℕ, ∀ i, ∃ j ∈ F, R i j := by
  classical
  by_cases hinf : ∀ F : Finset ℕ, {i | ∀ j ∈ F, ¬ R i j}.Infinite
  · exfalso
    choose g hg using fun (F : Finset ℕ) (N : ℕ) => (hinf F).exists_gt N
    let P : ℕ → Finset ℕ := fun n => Nat.rec ∅ (fun _ Q => insert (g Q (Q.sup id)) Q) n
    let a : ℕ → ℕ := fun n => g (P n) ((P n).sup id)
    have hPsucc : ∀ n, P (n + 1) = insert (a n) (P n) := fun n => rfl
    have hmem : ∀ m n, m < n → a m ∈ P n := by
      intro m n hmn
      induction n with
      | zero => exact absurd hmn (Nat.not_lt_zero _)
      | succ n ih =>
        rw [hPsucc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h | h
        · exact Finset.mem_insert_of_mem (ih h)
        · exact h ▸ Finset.mem_insert_self _ _
    have hmono : StrictMono a := by
      intro m n hmn
      exact (Finset.le_sup (f := id) (hmem m n hmn)).trans_lt (hg (P n) ((P n).sup id)).2
    have hbad : ∀ m n, m < n → ¬ R (a n) (a m) := fun m n hmn =>
      (hg (P n) ((P n).sup id)).1 _ (hmem m n hmn)
    obtain ⟨τ, hτ, J, hJ⟩ := hsub a hmono
    obtain ⟨m, hmJ, hR⟩ := hJ (J.sup id + 1)
    exact hbad _ _ (hτ (Nat.lt_succ_of_le (Finset.le_sup (f := id) hmJ))) hR
  · push Not at hinf
    obtain ⟨F₀, hF₀⟩ := hinf
    have hfin : {i | ∀ j ∈ F₀, ¬ R i j}.Finite := hF₀
    refine ⟨F₀ ∪ hfin.toFinset, fun i => ?_⟩
    by_cases hi : ∀ j ∈ F₀, ¬ R i j
    · exact ⟨i, Finset.mem_union_right _ (hfin.mem_toFinset.mpr hi), hrefl i⟩
    · push Not at hi
      obtain ⟨j, hj, hR⟩ := hi
      exact ⟨j, Finset.mem_union_left _ hj, hR⟩

/-! ### Reflexivity of the equivalence of nef models -/

/-- A nef weak model is equivalent to itself, through `e⁻¹ ∘ e` for any partial isomorphism `e`
representing it. -/
private theorem exists_isNefModelEquivalent_self {X S Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ]
    {πX : X ⟶ S} {πZ : Z ⟶ S} {K : Divisor X} {B : RDivisor X} {φ : X.RationalMap Z}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hφ : IsNefWeakModel sX sZ sS πX πZ K B φ) :
    ∃ (e e' : X.PartialIso Z), e.toRationalMap = φ ∧ e'.toRationalMap = φ ∧
      IsNefModelEquivalent sZ sZ sS πZ πZ
        (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)
        (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)
        (e.symm.trans e').toRationalMap := by
  obtain ⟨e, he⟩ := hφ.isBirational
  haveI : IsSeparated sS := (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
  haveI := isDominant_of_isBirational hφ.isBirational
  refine ⟨e, e, he, he, ?_⟩
  refine (IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent hφ hφ).2 _ ?_
  rw [toRationalMap_symm_trans_self, Scheme.RationalMap.comp_id]

/-! ### Subsequences -/

/-- A sequence in a finite type is constant along a subsequence. -/
private theorem exists_strictMono_eq_of_finite {β : Type*} [Finite β] (f : ℕ → β) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ b, ∀ n, f (τ n) = b := by
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber f
  have hs : (Set.ofPred fun n => f n = b).Infinite := Set.infinite_coe_iff.mp hb
  exact ⟨Nat.nth fun n => f n = b, Nat.nth_strictMono hs, b, Nat.nth_mem_of_infinite hs⟩

/-! ### Real divisors on a `ℚ`-factorial variety -/

section RDivisors

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- If a positive multiple of every prime divisor is Cartier, every `ℝ`-divisor is `ℝ`-Cartier:
`D = ∑_P (d_P / m_P) (m_P P)` with `m_P P` Cartier. -/
private theorem isRCartier_of_forall_isCartier_nsmul_single
    (hm : ∀ P : MMP.Mori.PrimeDivisor X, ∃ m : ℕ, 0 < m ∧
      Divisor.IsCartier ((m : ℤ) • (Finsupp.single P 1 : Divisor X))) (D : RDivisor X) :
    RDivisor.IsRCartier D := by
  classical
  choose m hm hmC using hm
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i).1 1, fun i => hmC _,
    fun Γ => ?_⟩
  change D Γ = _
  have key : ∀ P : MMP.Mori.PrimeDivisor X, D P / (m P : ℝ) *
      ((DivisorWithCoeffs.coeff (((m P : ℕ) : ℤ) • (Finsupp.single P (1 : ℤ)) : Divisor X) Γ :
        ℤ) : ℝ) =
        if P = Γ then D P else 0 := by
    intro P
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp [hm0]
  simp_rw [key]
  rw [e.symm.sum_comp (fun x : D.support => if x.1 = Γ then D x.1 else 0),
    Finset.sum_coe_sort D.support (fun x => if x = Γ then D x else 0)]
  simp only [Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact not_not.mp h

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial (hQ : IsQFactorial sX) (D : RDivisor X) :
    RDivisor.IsRCartier D :=
  isRCartier_of_forall_isCartier_nsmul_single (fun P => hQ.2 _) D

/-- On a smooth variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isSmoothScheme (hsm : MMP.Mori.IsSmoothScheme sX) (D : RDivisor X) :
    RDivisor.IsRCartier D :=
  isRCartier_of_forall_isCartier_nsmul_single
    (fun P => ⟨1, one_pos, by simpa using MMP.Fourfold.isCartier_of_isSmoothScheme hsm _⟩) D

/-- An `ℝ`-Cartier divisor is a real combination of Cartier divisors in the sense of
`MMP.Flips.IsCartierCombination`. -/
private theorem isCartierCombination_of_isRCartier {D : RDivisor X} (hD : RDivisor.IsRCartier D) :
    MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := hD
  refine ⟨m, r, C, hC, Finsupp.ext fun Γ => ?_⟩
  rw [← DivisorWithCoeffs.coeff_apply, hD Γ, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, ← DivisorWithCoeffs.coeff_apply (D := DivisorWithCoeffs.mapCoeffs _ _ _),
    DivisorWithCoeffs.coeff_mapCoeffs, smul_eq_mul]

/-- An `ℝ`-Cartier divisor has a pull-back along every dominant morphism from a quasi-compact
normal integral scheme. -/
private theorem exists_isRCartierPullback_of_isRCartier {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ X) [IsDominant f]
    {D : RDivisor X} (hD : RDivisor.IsRCartier D) :
    ∃ G : RDivisor Y, MMP.Flips.IsRCartierPullback f D G :=
  (MMP.Flips.existsUnique_isRCartierPullback f (isCartierCombination_of_isRCartier hD)).exists

/-- **Adding an `ℝ`-Cartier divisor to the boundary.** If `a = a(E, X, B)` and `G = f^*L` is a
pull-back of an `ℝ`-Cartier divisor `L` to the model of `E`, then
`a(E, X, B + L) = a - coeff_E G`. -/
private theorem isLogDiscrepancy_add {n : ℕ} {B L : RDivisor X} {E : DivisorOver k sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n B E a) {G : RDivisor E.Y}
    (hG : haveI := E.isLocallyNoetherian; haveI := E.isNormal
      MMP.Flips.IsRCartierPullback E.f L G) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + L) E (a - G.coeff E.E) := by
  have := E.isLocallyNoetherian
  have := E.isNormal
  obtain ⟨hX, hp, ω, hω0, hK, m, r, C, C', hC, hrel, hpb, rfl⟩ := h
  obtain ⟨m', r', L₀, L₀', hL₀, rfl, hpb', rfl⟩ := hG
  refine ⟨hX, hp, ω, hω0, hK, m + m', Fin.append r r', Fin.append C L₀, Fin.append C' L₀', ?_,
    fun Γ => ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hC i
    · simpa using hL₀ i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, DivisorWithCoeffs.coeff_add,
      MMP.Fourfold.coeff_sum_smul_toRDivisor, ← hrel Γ]
    ring
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hpb i
    · obtain ⟨hB, hp⟩ := hpb' i
      exact ⟨by simpa using hB, by simpa using hp⟩
  · rw [Fin.sum_univ_add, MMP.Fourfold.coeff_sum_smul_toRDivisor]
    simp only [Fin.append_left, Fin.append_right]
    ring

/-- A divisor over `X` carrying a log discrepancy has a proper, hence quasi-compact, model; an
`ℝ`-Cartier divisor on `X` pulls back to it, effectively if it is effective. -/
private theorem exists_isRCartierPullback_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {E : DivisorOver k sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B E a)
    {L : RDivisor X} (hL : RDivisor.IsRCartier L) :
    haveI := E.isLocallyNoetherian; haveI := E.isNormal
    ∃ G : RDivisor E.Y, MMP.Flips.IsRCartierPullback E.f L G ∧ (0 ≤ L → 0 ≤ G) := by
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isIntegral
  have := E.isDominant
  have hX := h.1
  have : IsProper E.f := h.2.1
  have : CompactSpace X := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  obtain ⟨m, r, C, hC, hcoeff⟩ := id hL
  choose C' hC' using fun j => (hC j).exists_isPullback
    (map_componentGenericPoint_notMem_supp_of_isDominant E.f (C j))
  have hG : MMP.Flips.IsRCartierPullback E.f L (∑ j, r j • Divisor.toRDivisor (C' j)) := by
    refine ⟨m, r, C, C', hC, ?_, fun j => ⟨_, hC' j⟩, rfl⟩
    ext P
    rw [hcoeff P, MMP.Fourfold.coeff_sum_smul_toRDivisor]
  exact ⟨_, hG, fun h0 => (MMP.Fourfold.isEffective_of_isRCartierPullback E.f hL h0).2 _ hG⟩

end RDivisors

/-! ### The crepant canonical divisor of the terminal model -/

/-- **A crepant canonical divisor.** On the crepant model `h : Y ⟶ X` of `(X, B)`, with crepant
boundary `B_Y` (`a(F, X, B) = 1 - coeff_F B_Y` for the primes `F` of `Y`), there is a canonical
divisor `K_Y` with `h_* K_Y = K_X` and `B_Y = h^*(K_X + B) - K_Y`. -/
private theorem exists_isCanonicalDivisor_crepant {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 3) {B₀ : RDivisor X} {h : Y ⟶ X} (hh : IsBirationalMorphism h)
    (hY : IsNormalVariety ℂ (h ≫ sX)) (hhp : IsProjectiveMorphism h) {BY : RDivisor Y}
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y,
      MMP.Intersection.IsLogDiscrepancy sX 3 B₀ ⟨Y, h, hY, hh, F⟩ (1 - BY.coeff F))
    {GX : RDivisor Y}
    (hGX : MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor K B₀) GX) :
    ∃ KY : Divisor Y, KY.IsCanonicalDivisor (h ≫ sX) 3 ∧
      RationalMap.transformDivisor h.toRationalMap KY = K ∧
      ∀ P, BY.coeff P = GX.coeff P - (KY.coeff P : ℝ) := by
  haveI := hY.1
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  haveI : IsDominant h := hh.isDominant
  haveI : CompactSpace X := hX.toQuasiCompact.compactSpace_of_compactSpace
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  haveI : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (h ≫ sX) := hY.1.toLocallyOfFiniteType
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hdimY : topologicalKrullDim Y = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (h ≫ sX) hh).symm.trans
      hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (h ≫ sX) hY hdimY
  obtain ⟨KY, hKY, hKYK⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hXn hY hh hK hK₀
  obtain ⟨ω, hω0, hωK, hωKY⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn hY hh hK hKY hKYK
  refine ⟨KY, hKY, hKYK, fun P => ?_⟩
  obtain ⟨m, r, L, L', hLc, hD, hL', rfl⟩ := hGX
  have hld : MMP.Intersection.IsLogDiscrepancy sX 3 B₀ ⟨Y, h, hY, hh, P⟩
      (1 + (KY.coeff P : ℝ) - ∑ j, r j * ((L' j).coeff P : ℝ)) := by
    refine ⟨hXn, inferInstance, ω, hω0, ⟨K, hK, fun Γ => ?_⟩, m, r, L, L', hLc, fun Γ => ?_, hL',
      ?_⟩
    · rw [← hωK, coeff_divisorOfForm]
    · have h1 := congrArg (fun D : RDivisor X => D.coeff Γ) hD
      simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
        MMP.Fourfold.coeff_sum_smul_toRDivisor] at h1
      rw [← h1, ← hωK]
      congr 1
    · rw [← hωKY, coeff_divisorOfForm]
      rfl
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hBY P) hld
  rw [MMP.Fourfold.coeff_sum_smul_toRDivisor]
  linarith

/-! ### Lowering a terminal boundary -/

/-- **Lowering an effective boundary keeps a pair terminal.** On a `ℚ`-factorial variety, if
`(Y, B)` is real terminal and `0 ≤ C ≤ B`, then `(Y, C)` is real terminal. -/
private theorem isRealTerminalPair_of_le {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (hYq : IsQFactorial sY) {B C : RDivisor Y}
    (hB : IsRealTerminalPair sY B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hCB : ∀ P, C.coeff P ≤ B.coeff P) :
    IsRealTerminalPair sY C := by
  obtain ⟨⟨hYn, hBc, ⟨n, K, hK, -⟩, -⟩, hBt⟩ := hB
  have hlog : ∀ (m : ℕ) (E : DivisorOver ℂ sY) (a : ℝ), E.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sY m C E a → 1 < a := by
    intro m E a hE ha
    obtain ⟨G, hG, hG0⟩ := exists_isRCartierPullback_of_isLogDiscrepancy ha
      (isRCartier_of_isQFactorial hYq (B - C))
    have hBC : 0 ≤ B - C := fun P => by
      change (0 : ℝ) ≤ (B - C) P
      rw [Finsupp.sub_apply, ← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
        sub_nonneg]
      exact hCB P
    have h1 := hBt m E _ hE (by simpa only [add_sub_cancel] using isLogDiscrepancy_add ha hG)
    have h2 : 0 ≤ G.coeff E.E := hG0 hBC E.E
    linarith
  refine ⟨⟨hYn, fun P hP => ?_, ⟨n, K, hK, isRCartier_of_isQFactorial hYq _⟩,
    fun m E a hE ha => (hlog m E a hE ha).le⟩, hlog⟩
  have hpos : 0 < C.coeff P := lt_of_le_of_ne (hC0 P) (Ne.symm hP)
  have hB0 : B.coeff P ≠ 0 := (lt_of_lt_of_le hpos (hCB P)).ne'
  exact ⟨hpos, (hCB P).trans_lt (hBc P hB0).2⟩

/-! ### Generic points, strict transforms and composites -/

section GenericPoints

open MMP

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The local ring of a normal locally noetherian integral scheme at a point of coheight at most
one is a valuation ring (a field or a discrete valuation ring). -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : Order.coheight x ≤ 1) :
    ValuationRing (X.presheaf.stalk x) := by
  rcases lt_or_eq_of_le hx with h | h
  · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have hx' : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    have hgx : genericPoint X = x := (hgen.antisymm hx').eq
    subst hgx
    have : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
    letI := this.toField
    infer_instance
  · have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]; rfl
    have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
    have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
    have := h1.choose_spec
    infer_instance

/-- **The point over a codimension-one point.** Let `f : X ⟶ Y` be a separated dominant morphism
of normal integral schemes inducing an isomorphism of function fields, and `y ∈ Y` a point of
coheight at most one. Then `f` induces an isomorphism of local rings at every point over `y`, and
two points over `y` coincide. -/
private theorem isIso_stalkMap_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : Order.coheight (f x) ≤ 1) :
    IsIso (f.stalkMap x) := by
  have := valuationRing_stalk_of_coheight_le_one hx
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  have : IsIso (f.stalkMap x₂) :=
    isIso_stalkMap_of_coheight_le_one f hf (by rw [h]; exact hx)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- Two partial maps with the same domain representing the same rational map to a separated
scheme are equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]

private theorem mem_irreducibleComponent' {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (g ≫ f)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent'
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent' (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- `(g ∘ f) ∘ q = (q ∘ g) ∘ f` for dominant `f`, `g` and a morphism `q`. -/
private theorem comp_compHom {X Y Z T : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [Nonempty Y] [Nonempty Z] (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) [g.IsDominant] (q : Z ⟶ T) :
    (f.comp g).compHom q = f.comp (g.compHom q) := by
  rw [← Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_assoc,
    Scheme.RationalMap.comp_toRationalMap]

/-- A rational map `Y ⤏ V` inverse to a proper morphism `p : V ⟶ Y` is defined at the generic
point of every prime divisor of `Y`. -/
private theorem exists_rep_mem_domain {Y V : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p] {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ g : Y.PartialMap V, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
  have hhp := compHom_eq_of_isInverse hinv
  obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Y) p h hhp
      (Q.coheight_genericPoint.le))
  exact ⟨g, hg', hg⟩

/-- A representative of the inverse of a morphism `p`, defined at a point `y`, sends `y` to a point
over `y`. -/
private theorem apply_rep_eq_of_isInverse {Y V : Scheme.{u}} [IsReduced Y] [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) {g : Y.PartialMap V}
    (hg : g.toRationalMap = h) {y : Y} (hy : y ∈ g.domain) : p (g.hom ⟨y, hy⟩) = y := by
  have he : g.hom ≫ p = g.domain.ι ≫ 𝟙 Y :=
    hom_eq_of_toRationalMap_eq g.dense_domain <| by
      rw [toRationalMap_ι_comp]
      change (g.compHom p).toRationalMap = _
      rw [Scheme.RationalMap.compHom_toRationalMap, hg, compHom_eq_of_isInverse hinv]
  calc p (g.hom ⟨y, hy⟩) = (g.hom ≫ p) ⟨y, hy⟩ := (Scheme.Hom.comp_apply _ _ _).symm
    _ = y := by rw [he]; simp

/-- **The point over a source prime.** Let `p : V ⟶ Y` be proper with inverse `h`, and
`q : V ⟶ T` with `q ∘ h = φ`. If `φ_* R = P`, then the image under `h` of `η_R` is a point of `V`
lying over `η_R` and over `η_P`. -/
private theorem exists_apply_eq_genericPoint {Y V T : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p]
    {q : V ⟶ T} {h : Y.RationalMap V} {φ : Y.RationalMap T}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (hq : h.compHom q = φ)
    {R : MMP.Mori.PrimeDivisor Y} {P : MMP.Mori.PrimeDivisor T}
    (hR : MMP.Mori.RationalMap.transformPrimeDivisor φ R = some P) :
    ∃ w : V, q w = P.genericPoint ∧ p w = R.genericPoint := by
  obtain ⟨g, hg, hRg⟩ := exists_rep_mem_domain hinv R
  refine ⟨g.hom ⟨R.genericPoint, hRg⟩,
    (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hR (g.compHom q)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg, hq]) hRg).symm,
    apply_rep_eq_of_isInverse hinv hg hRg⟩

private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact Oai4C1.Negativity.withBot_add_two_le_iff h

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- **Transforms along `q ∘ p⁻¹`.** Let `p : V ⟶ Y` be proper with inverse `h`, and `q : V ⟶ T`,
with `p`, `q` dominant and separated, inducing isomorphisms of function fields. If a prime divisor
`E` of `V` lies over prime divisors `P` of `Y` and `F` of `T`, then `F` is the
transform of `P`, and of no other prime divisor of `Y`, under `q ∘ p⁻¹`. -/
private theorem transformPrimeDivisor_compHom_eq_some {Y V T : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (V ↘ ⊤_ Scheme)]
    [IsSeparated (T ↘ ⊤_ Scheme)] {p : V ⟶ Y}
    [IsProper p] [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) {q : V ⟶ T}
    [IsSeparated q] [IsDominant q] (hq : Function.Bijective (functionFieldMap q))
    {h : Y.RationalMap V} (hinv : RationalMap.IsInverse p.toRationalMap h)
    {P : MMP.Mori.PrimeDivisor Y} {E : MMP.Mori.PrimeDivisor V} {F : MMP.Mori.PrimeDivisor T}
    (hEP : p E.genericPoint = P.genericPoint) (hEF : q E.genericPoint = F.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) P = some F ∧
      ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) P' = some F → P' = P := by
  obtain ⟨g, hg, hP⟩ := exists_rep_mem_domain hinv P
  have hx : E.genericPoint = g.hom ⟨P.genericPoint, hP⟩ :=
    eq_of_apply_eq_of_coheight_le_one p hp ((apply_rep_eq_of_isInverse hinv hg hP).trans hEP.symm)
      (by rw [hEP]; exact P.coheight_genericPoint.le)
  refine ⟨transformPrimeDivisor_eq_some_of_genericPoint_eq (g.compHom q)
      (by rw [Scheme.RationalMap.compHom_toRationalMap, hg]) hP ?_, fun P' hP' => ?_⟩
  · change F.genericPoint = q (g.hom ⟨P.genericPoint, hP⟩)
    rw [← hx, hEF]
  · obtain ⟨w', hw'q, hw'p⟩ := exists_apply_eq_genericPoint hinv rfl hP'
    have hw : E.genericPoint = w' := eq_of_apply_eq_of_coheight_le_one q hq (hw'q.trans hEF.symm)
      (by rw [hEF]; exact F.coheight_genericPoint.le)
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hw'p.symm.trans (hw ▸ hEP))

/-- **Pulling a pull-back back once more.** If `D = g^*M` is an `ℝ`-Cartier pull-back and `f` is
dominant from a quasi-compact normal integral scheme, then `f^*D` is a pull-back of `M` along
`f ≫ g`. -/
private theorem exists_isRCartierPullback_comp_and {V W Z : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      MMP.Flips.IsRCartierPullback f D G := by
  obtain ⟨m, r, L, L', hLc, hM, hpb, rfl⟩ := hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  let L'' : Fin m → Divisor V := fun j =>
    (L' j).pullback (hL'c j) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  have hL'' : ∀ j, (L' j).IsPullback f
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  exact ⟨∑ j, r j • Divisor.toRDivisor (L'' j), ⟨m, r, L, L'', hLc, hM, fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) _,
      isPullback_comp (hpb j).2 (hL'' j) _⟩, rfl⟩,
    ⟨m, r, L', L'', hL'c, rfl, fun j => ⟨_, hL'' j⟩, rfl⟩⟩

/-- Two morphisms from a reduced scheme to a separated scheme with the same rational map are
equal. -/
private theorem hom_eq_of_toRationalMap_eq' {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {f g : X ⟶ Y} (h : f.toRationalMap = g.toRationalMap) :
    f = g := by
  have h1 := hom_eq_of_toRationalMap_eq (U := ⊤) dense_univ
    ((toRationalMap_ι_comp dense_univ f).trans (h.trans (toRationalMap_ι_comp dense_univ g).symm))
  haveI : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  exact (cancel_epi (⊤ : X.Opens).ι).1 h1

/-- The rational map of a morphism followed by a morphism is the rational map of the composite. -/
private theorem toRationalMap_compHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  change (f.toPartialMap.toRationalMap).compHom g = (f ≫ g).toPartialMap.toRationalMap
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom]

/-- If a prime divisor `E` of `V` lies over a prime divisor `P` of `Y`, for a proper birational
morphism `p : V ⟶ Y` with inverse `h`, then `h_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_isInverse {Y V : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral V] [IsSeparated (Y ↘ ⊤_ Scheme)]
    [IsSeparated (V ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p] [IsDominant p]
    (hp : Function.Bijective (functionFieldMap p)) {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) {P : MMP.Mori.PrimeDivisor Y}
    {E : MMP.Mori.PrimeDivisor V} (hEP : p E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor h P = some E := by
  obtain ⟨g, hg, hP⟩ := exists_rep_mem_domain hinv P
  exact transformPrimeDivisor_eq_some_of_genericPoint_eq g hg hP
    (eq_of_apply_eq_of_coheight_le_one p hp ((apply_rep_eq_of_isInverse hinv hg hP).trans hEP.symm)
      (by rw [hEP]; exact P.coheight_genericPoint.le))

end GenericPoints

/-- If `hW` is inverse to `p` and `h₀` inverse to `p₀`, with `g₀ ≫ p₀ = p ≫ h` and
`q₀ ∘ h₀ = φ`, then `(g₀ ≫ q₀) ∘ hW = φ ∘ h`. -/
private theorem compHom_comp_eq_of_comp_eq_id {Y W W₀ X Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral W] [IsIntegral W₀] [IsIntegral X] [IsIntegral Z] {p : W ⟶ Y} {h : Y ⟶ X}
    {g₀ : W ⟶ W₀} {p₀ : W₀ ⟶ X} {q₀ : W₀ ⟶ Z} [IsDominant p] [IsDominant h] [IsDominant g₀]
    [IsDominant p₀] {hW : Y.RationalMap W} [hW.IsDominant] {h₀ : X.RationalMap W₀}
    [h₀.IsDominant] {φ : X.RationalMap Z}
    (hpinv : hW.comp p.toRationalMap = Scheme.RationalMap.id Y)
    (hp₀inv : p₀.toRationalMap.comp h₀ = Scheme.RationalMap.id W₀) (hcomm : g₀ ≫ p₀ = p ≫ h)
    (hh₀ : h₀.compHom q₀ = φ) :
    hW.compHom (g₀ ≫ q₀) = h.toRationalMap.comp φ := by
  have hk : (hW.comp g₀.toRationalMap).comp p₀.toRationalMap = h.toRationalMap := by
    rw [Scheme.RationalMap.comp_toRationalMap, comp_compHom, toRationalMap_compHom, hcomm,
      ← toRationalMap_compHom, ← comp_compHom, hpinv, Scheme.RationalMap.id_compHom]
  have h1 : hW.compHom g₀ = h.toRationalMap.comp h₀ := by
    calc hW.compHom g₀ = hW.comp g₀.toRationalMap :=
          (Scheme.RationalMap.comp_toRationalMap _ _).symm
      _ = (hW.comp g₀.toRationalMap).comp (Scheme.RationalMap.id W₀) :=
          (Scheme.RationalMap.comp_id _).symm
      _ = (hW.comp g₀.toRationalMap).comp (p₀.toRationalMap.comp h₀) := by rw [hp₀inv]
      _ = ((hW.comp g₀.toRationalMap).comp p₀.toRationalMap).comp h₀ :=
          (Scheme.RationalMap.comp_assoc _ _ _).symm
      _ = h.toRationalMap.comp h₀ := comp_eq_comp_of_eq hk h₀
  calc hW.compHom (g₀ ≫ q₀) = (hW.compHom g₀).compHom q₀ :=
        (Oai4C1.Main.compHom_compHom _ _ _).symm
    _ = (h.toRationalMap.comp h₀).compHom q₀ := by rw [h1]
    _ = h.toRationalMap.comp (h₀.compHom q₀) := comp_compHom _ _ _
    _ = h.toRationalMap.comp φ := by rw [hh₀]

/-- If `h₀` is inverse to `p₀` and `q₀ ∘ h₀ = φ` lies over `πX` through `πZ`, then
`p₀ ≫ πX = q₀ ≫ πZ`. -/
private theorem comp_eq_comp_of_comp_eq_id {W₀ X Z S : Scheme.{0}} [IsIntegral W₀]
    [IsIntegral X] [IsIntegral Z] [IsSeparated (S ↘ ⊤_ Scheme)] {p₀ : W₀ ⟶ X} {q₀ : W₀ ⟶ Z}
    [IsDominant p₀] {πX : X ⟶ S} {πZ : Z ⟶ S} {h₀ : X.RationalMap W₀} [h₀.IsDominant]
    {φ : X.RationalMap Z} (hp₀inv : p₀.toRationalMap.comp h₀ = Scheme.RationalMap.id W₀)
    (hh₀ : h₀.compHom q₀ = φ) (hov : φ.compHom πZ = πX.toRationalMap) :
    p₀ ≫ πX = q₀ ≫ πZ := by
  apply hom_eq_of_toRationalMap_eq'
  calc (p₀ ≫ πX).toRationalMap = p₀.toRationalMap.compHom πX := (toRationalMap_compHom _ _).symm
    _ = p₀.toRationalMap.comp πX.toRationalMap :=
        (Scheme.RationalMap.comp_toRationalMap _ _).symm
    _ = p₀.toRationalMap.comp ((h₀.compHom q₀).compHom πZ) := by rw [hh₀, hov]
    _ = p₀.toRationalMap.comp (h₀.compHom (q₀ ≫ πZ)) := by rw [Oai4C1.Main.compHom_compHom]
    _ = (p₀.toRationalMap.comp h₀).compHom (q₀ ≫ πZ) := (comp_compHom _ _ _).symm
    _ = (q₀ ≫ πZ).toRationalMap := by rw [hp₀inv, Scheme.RationalMap.id_compHom]

/-! ### The comparison boundaries on the terminal model -/

/-- **The comparison boundary on a crepant model.** Let `h : Y ⟶ X` be a projective birational
morphism from a `ℚ`-factorial variety, with `h_* K_Y = K_X`, and let `φ : X ⤏ Z` be a small nef
weak model of `(X, B)`. On a common resolution `p : W ⟶ Y`, `q : W ⟶ Z` let
`Γ = p_* q^*(K_Z + B_Z)`. Then `Γ ≤ h^*(K_X + B)`, and for the boundary `C` with coefficients
`max(Γ - K_Y, 0)` the map `φ ∘ h : Y ⤏ Z` is a nef weak model of `(Y, C)` with the same target
pair, whose comparison divisor vanishes along every prime with positive coefficient in `C`. -/
private theorem exists_comparisonBoundary
    {X S Y Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [QuasiCompact sZ]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 3) (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {πX : X ⟶ S}
    {πZ : Z ⟶ S} {h : Y ⟶ X} [IsDominant h] (hh : IsBirationalMorphism h)
    (hYq : IsQFactorial (h ≫ sX)) (hhp : IsProjectiveMorphism h) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (h ≫ sX) 3)
    (hKYK : RationalMap.transformDivisor h.toRationalMap KY = K) {B : RDivisor X} (hB : 0 ≤ B)
    {φ : X.RationalMap Z} (hφ : IsNefWeakModel sX sZ sS πX πZ K B φ)
    (hsmall : ∀ P : MMP.Mori.PrimeDivisor X, ¬ RationalMap.IsExceptional φ P) {GX : RDivisor Y}
    (hGX : MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor K B) GX) :
    ∃ Γ : RDivisor Y, (∀ P, Γ.coeff P ≤ GX.coeff P) ∧
      ∀ C : RDivisor Y, (∀ P, C.coeff P = max (Γ.coeff P - KY.coeff P) 0) →
        IsNefWeakModel (h ≫ sX) sZ sS (h ≫ πX) πZ KY C (h.toRationalMap.comp φ) ∧
        RationalMap.transformDivisor (h.toRationalMap.comp φ) KY =
          RationalMap.transformDivisor φ K ∧
        RationalMap.transformDivisor (h.toRationalMap.comp φ) C =
          RationalMap.transformDivisor φ B ∧
        ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (hW : Y.RationalMap W),
          MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ (h ≫ sX) = sW ∧
            q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
            IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
            MMP.Mori.RationalMap.IsInverse p.toRationalMap hW ∧
            hW.compHom q = h.toRationalMap.comp φ ∧
            ∃ GY GZ : RDivisor W,
              MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KY C) GY ∧
              MMP.Flips.IsRCartierPullback q
                (MMP.Flips.logCanonicalDivisor
                  (MMP.Mori.RationalMap.transformDivisor (h.toRationalMap.comp φ) KY)
                  (MMP.Mori.RationalMap.transformDivisor (h.toRationalMap.comp φ) C)) GZ ∧
              ∀ P, 0 < C.coeff P → ∃ P' : MMP.Mori.PrimeDivisor W,
                MMP.Mori.RationalMap.transformPrimeDivisor hW P = some P' ∧
                  (GY - GZ).coeff P' = 0 := by
  classical
  /- Instances on `X`, `Y`, `Z`. -/
  have hXn : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hYn : IsNormalVariety ℂ (h ≫ sX) := hYq.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.toIsVariety
  haveI : AlgebraicGeometry.IsVariety ℂ (h ≫ sX) := hYn.1
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  haveI : CompactSpace X := hX.toQuasiCompact.compactSpace_of_compactSpace
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  have hZn := hφ.isNormalVariety_target
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_toTerminal sX
  haveI : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_toTerminal (h ≫ sX)
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal sZ
  have hhbij := hh.functionFieldMap_bijective
  /- The resolution of the weak model `φ`. -/
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀v, hW₀sm, hp₀s, hq₀s, hp₀p, hq₀p, hp₀b, hq₀b, hinv₀,
    hh₀, GX₀, GZ₀, hGX₀, hGZ₀, hGeff₀, -⟩ := hφ.exists_resolution
  haveI : AlgebraicGeometry.IsVariety ℂ sW₀ := hW₀v
  haveI : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀p
  haveI : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀p
  haveI : IsDominant p₀ := hp₀b.isDominant
  haveI : IsDominant q₀ := hq₀b.isDominant
  haveI : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace sW₀
  have hW₀n : IsNormalVariety ℂ (p₀ ≫ sX) := by rw [hp₀s]; exact ⟨hW₀v, inferInstance⟩
  have hp₀bij := hp₀b.functionFieldMap_bijective
  have hq₀bij := hq₀b.functionFieldMap_bijective
  /- A smooth projective common model `W` of `Y` and `W₀` over `X`. -/
  let Xs : Bool → Scheme.{0} := fun b => cond b W₀ Y
  let fs : ∀ b, Xs b ⟶ X := fun b => Bool.rec (motive := fun b => Xs b ⟶ X) h p₀ b
  haveI : ∀ b, IsProper (fs b) := fun b => by
    cases b
    · exact (inferInstance : IsProper h)
    · exact (inferInstance : IsProper p₀)
  obtain ⟨W, w, hWn, hwb, g, hWsm, hwp, hg, -, hWproj⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX fs
      (fun b => by cases b; exacts [hh, hp₀b]) (fun b => by cases b; exacts [hYn, hW₀n])
      (κ := Empty) Empty.elim (fun j => j.elim)
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sX) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sX)
  haveI : QuasiCompact (w ≫ sX) := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ sX)
  let p : W ⟶ Y := g false
  let g₀ : W ⟶ W₀ := g true
  have hpw : p ≫ h = w := (hg false).1
  have hgw : g₀ ≫ p₀ = w := (hg true).1
  have hpp : IsProjectiveMorphism p := (hg false).2.1
  have hpb : IsBirationalMorphism p := (hg false).2.2
  have hg₀p : IsProjectiveMorphism g₀ := (hg true).2.1
  have hg₀b : IsBirationalMorphism g₀ := (hg true).2.2
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  haveI : IsDominant p := hpb.isDominant
  haveI : IsProper g₀ := isProper_of_isProjectiveMorphism g₀ hg₀p
  haveI : IsDominant g₀ := hg₀b.isDominant
  let q : W ⟶ Z := g₀ ≫ q₀
  have hqp : IsProjectiveMorphism q := IsProjectiveMorphism.comp hg₀p hq₀p
  have hqb : IsBirationalMorphism q := Oai4C1.CommonModel.isBirationalMorphism_comp hg₀b hq₀b
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hqp
  haveI : IsDominant q := hqb.isDominant
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hps : p ≫ (h ≫ sX) = w ≫ sX := by rw [← Category.assoc, hpw]
  have hqs : q ≫ sZ = w ≫ sX := by
    change (g₀ ≫ q₀) ≫ sZ = w ≫ sX
    rw [Category.assoc, hq₀s, ← hp₀s, ← Category.assoc, hgw]
  have hWnp : IsNormalVariety ℂ (p ≫ (h ≫ sX)) := by rw [hps]; exact hWn
  obtain ⟨hW, hWinv⟩ := hpb.exists_isInverse
  /- The pull-backs to `W`. -/
  obtain ⟨GZ, hGZq, hGZg⟩ := exists_isRCartierPullback_comp_and g₀ q₀ hGZ₀
  obtain ⟨GXW, hGXWw, hGXWg⟩ := exists_isRCartierPullback_comp_and g₀ p₀ hGX₀
  obtain ⟨GXW', hGXW'w, hGXW'p⟩ := exists_isRCartierPullback_comp_and p h hGX
  have hGXWeq : GXW = GXW' := by
    haveI : IsDominant w := hwb.isDominant
    rw [hgw] at hGXWw
    rw [hpw] at hGXW'w
    exact MMP.Flips.IsRCartierPullback.eq w hGXWw hGXW'w
  have hGeff : 0 ≤ GXW - GZ := by
    have hpb' : MMP.Flips.IsRCartierPullback g₀ (GX₀ - GZ₀) (GXW - GZ) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℝ GZ₀, ← neg_one_smul ℝ GZ]
      exact isRCartierPullback_add hGXWg (isRCartierPullback_smul _ hGZg)
    exact (MMP.Fourfold.isEffective_of_isRCartierPullback g₀
      (isRCartier_of_isSmoothScheme hW₀sm _) (fun P => hGeff₀ P)).2 _ hpb'
  /- Strict transforms on `W` and on `Y`. -/
  choose sP hsPp hsPiso hsPtr using fun P : MMP.Mori.PrimeDivisor Y =>
    (MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hYn hWnp hpb P :
      ∃ E : MMP.Mori.PrimeDivisor W, p E.genericPoint = P.genericPoint ∧
        IsIso (p.stalkMap E.genericPoint) ∧ ∀ {R : Type} [AddCommMonoid R]
          (D : DivisorWithCoeffs R W), RationalMap.transformDivisor (X := W) p.toRationalMap D P =
            D E)
  choose sY hsYp hsYiso hsYtr using fun Q : MMP.Mori.PrimeDivisor X =>
    (MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hXn hYn hh Q :
      ∃ E : MMP.Mori.PrimeDivisor Y, h E.genericPoint = Q.genericPoint ∧
        IsIso (h.stalkMap E.genericPoint) ∧ ∀ {R : Type} [AddCommMonoid R]
          (D : DivisorWithCoeffs R Y), RationalMap.transformDivisor (X := Y) h.toRationalMap D Q =
            D E)
  refine ⟨RationalMap.transformDivisor p.toRationalMap GZ, fun P => ?_, fun C hC => ?_⟩
  · haveI := hsPiso P
    rw [DivisorWithCoeffs.coeff_apply, hsPtr P GZ, ← DivisorWithCoeffs.coeff_apply,
      ← MMP.Fourfold.coeff_eq_of_isRCartierPullback (sP P) P (hsPp P) hGXW'p, ← hGXWeq]
    have := hGeff (sP P)
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply, sub_nonneg] at this
    exact this
  · /- The source primes of the primes of `Z`. -/
    have hZpr : ∀ F : MMP.Mori.PrimeDivisor Z, ∃ Q : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F ∧
        ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
          MMP.Mori.RationalMap.transformDivisor φ D F = D Q := by
      intro F
      obtain ⟨Q, hQ⟩ : ∃ Q, MMP.Mori.RationalMap.transformPrimeDivisor φ Q = some F := by
        have := hφ.not_isInverseExceptional F
        simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
      refine ⟨Q, hQ, fun D => ?_⟩
      refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hQ (fun Q' hQ' => ?_) D
      obtain ⟨x, hxq, hxp⟩ := exists_apply_eq_genericPoint hinv₀ hh₀ hQ
      obtain ⟨x', hxq', hxp'⟩ := exists_apply_eq_genericPoint hinv₀ hh₀ hQ'
      have hxx : x = x' := eq_of_apply_eq_of_coheight_le_one q₀ hq₀bij (hxq'.trans hxq.symm)
        (by rw [hxq]; exact F.coheight_genericPoint.le)
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hxp'.symm.trans (hxx ▸ hxp))
    choose QF hQF hQFtr using hZpr
    /- The strict transform on `W` of the source prime of `F` lies over `F`. -/
    have hV1 : ∀ F : MMP.Mori.PrimeDivisor Z,
        q (sP (sY (QF F))).genericPoint = F.genericPoint := by
      intro F
      obtain ⟨x, hxq, hxp⟩ := exists_apply_eq_genericPoint hinv₀ hh₀ (hQF F)
      have h1 : p₀ (g₀ (sP (sY (QF F))).genericPoint) = p₀ x := by
        rw [← Scheme.Hom.comp_apply, hgw, ← hpw, Scheme.Hom.comp_apply, hsPp, hsYp, hxp]
      have h2 : x = g₀ (sP (sY (QF F))).genericPoint :=
        eq_of_apply_eq_of_coheight_le_one p₀ hp₀bij h1
          (by rw [hxp]; exact (QF F).coheight_genericPoint.le)
      change q₀ (g₀ (sP (sY (QF F))).genericPoint) = F.genericPoint
      rw [← h2, hxq]
    /- The map `φ ∘ h` is `q ∘ p⁻¹`. -/
    haveI : hW.IsDominant := isDominant_of_isBirational hWinv.isBirational_inverse
    haveI : h₀.IsDominant := isDominant_of_isBirational hinv₀.isBirational_inverse
    have hpinv : hW.comp p.toRationalMap = Scheme.RationalMap.id Y :=
      comp_eq_id_of_isInverse hWinv.symm
    have hp₀inv : p₀.toRationalMap.comp h₀ = Scheme.RationalMap.id W₀ :=
      comp_eq_id_of_isInverse hinv₀
    have hV4 : hW.compHom q = h.toRationalMap.comp φ :=
      compHom_comp_eq_of_comp_eq_id hpinv hp₀inv (hgw.trans hpw.symm) hh₀
    /- The transforms along `φ ∘ h`. -/
    haveI : IsSeparated (w ≫ sX) := hWn.1.toIsSeparated
    haveI : IsSeparated (W ↘ ⊤_ Scheme) := isSeparated_toTerminal (w ≫ sX)
    have hψF : ∀ F : MMP.Mori.PrimeDivisor Z,
        MMP.Mori.RationalMap.transformPrimeDivisor (h.toRationalMap.comp φ) (sY (QF F)) = some F ∧
        ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor (h.toRationalMap.comp φ) P' = some F →
          P' = sY (QF F) := by
      intro F
      rw [← hV4]
      exact transformPrimeDivisor_compHom_eq_some hpbij hqbij hWinv (hsPp _) (hV1 F)
    have hψtr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Y)
        (F : MMP.Mori.PrimeDivisor Z),
        MMP.Mori.RationalMap.transformDivisor (h.toRationalMap.comp φ) D F = D (sY (QF F)) :=
      fun D F => MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (hψF F).1 (hψF F).2 D
    have hKYQ : ∀ Q, KY (sY Q) = K Q := fun Q => by
      have := hsYtr Q KY
      rw [hKYK] at this
      exact this.symm
    have hΓF : ∀ F : MMP.Mori.PrimeDivisor Z,
        (RationalMap.transformDivisor p.toRationalMap GZ).coeff (sY (QF F)) =
          (K.coeff (QF F) : ℝ) + B.coeff (QF F) := by
      intro F
      haveI : IsIso (q.stalkMap (sP (sY (QF F))).genericPoint) :=
        isIso_stalkMap_of_coheight_le_one q hqbij
          (by rw [hV1 F]; exact F.coheight_genericPoint.le)
      rw [DivisorWithCoeffs.coeff_apply, hsPtr, ← DivisorWithCoeffs.coeff_apply,
        MMP.Fourfold.coeff_eq_of_isRCartierPullback (f := q) _ F (hV1 F) hGZq]
      simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add]
      change ((RationalMap.transformDivisor φ K F : ℤ) : ℝ) +
        RationalMap.transformDivisor φ B F = _
      rw [hQFtr, hQFtr]
      rfl
    have hbF : ∀ F : MMP.Mori.PrimeDivisor Z,
        (RationalMap.transformDivisor p.toRationalMap GZ).coeff (sY (QF F)) -
          (KY.coeff (sY (QF F)) : ℝ) = B.coeff (QF F) := by
      intro F
      rw [hΓF, DivisorWithCoeffs.coeff_apply KY, hKYQ, DivisorWithCoeffs.coeff_apply K]
      ring
    have hCF : ∀ F : MMP.Mori.PrimeDivisor Z, C.coeff (sY (QF F)) = B.coeff (QF F) := fun F => by
      rw [hC, hbF, max_eq_left (show (0 : ℝ) ≤ B.coeff (QF F) from hB (QF F))]
    have hT1 : RationalMap.transformDivisor (h.toRationalMap.comp φ) KY =
        RationalMap.transformDivisor φ K := Finsupp.ext fun F => by
      rw [hψtr, hQFtr, hKYQ]
    have hT2 : RationalMap.transformDivisor (h.toRationalMap.comp φ) C =
        RationalMap.transformDivisor φ B := Finsupp.ext fun F => by
      rw [hψtr, hQFtr]
      exact hCF F
    /- The comparison divisor on `W`. -/
    obtain ⟨GY, hGY⟩ := exists_isRCartierPullback_of_isRCartier p
      (isRCartier_of_isQFactorial hYq (MMP.Flips.logCanonicalDivisor KY C))
    have hGYc : ∀ P, (GY - GZ).coeff (sP P) = (KY.coeff P : ℝ) + C.coeff P -
        (RationalMap.transformDivisor p.toRationalMap GZ).coeff P := by
      intro P
      haveI := hsPiso P
      rw [DivisorWithCoeffs.coeff_sub,
        MMP.Fourfold.coeff_eq_of_isRCartierPullback (sP P) P (hsPp P) hGY]
      simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add]
      rw [DivisorWithCoeffs.coeff_apply (RationalMap.transformDivisor _ GZ), hsPtr,
        ← DivisorWithCoeffs.coeff_apply]
      rfl
    have hpush : 0 ≤ RationalMap.transformDivisor p.toRationalMap (GY - GZ) := fun P => by
      change (0 : ℝ) ≤ RationalMap.transformDivisor p.toRationalMap (GY - GZ) P
      rw [hsPtr, ← DivisorWithCoeffs.coeff_apply, hGYc, hC P]
      linarith [le_max_left ((RationalMap.transformDivisor p.toRationalMap GZ).coeff P -
        (KY.coeff P : ℝ)) 0]
    /- The structure morphisms to `S`. -/
    haveI : IsSeparated sS :=
      (instIsProperVarietyOfIsProjectiveVariety ℂ sS).toIsProper.toIsSeparated
    haveI : IsSeparated (S ↘ ⊤_ Scheme) := isSeparated_toTerminal sS
    have hp₀q₀ : p₀ ≫ πX = q₀ ≫ πZ := comp_eq_comp_of_comp_eq_id hp₀inv hh₀ hφ.isOver
    have hpq : p ≫ (h ≫ πX) = q ≫ πZ := by
      change p ≫ h ≫ πX = (g₀ ≫ q₀) ≫ πZ
      rw [← Category.assoc, hpw, ← hgw, Category.assoc, hp₀q₀, Category.assoc]
    /- Effectivity of the comparison. -/
    have hYp : MMP.Mori.IsProjectiveVariety ℂ (h ≫ sX) :=
      (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hYn.1, IsProjectiveMorphism.comp hhp
        ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2⟩
    have hWpv : MMP.Mori.IsProjectiveVariety ℂ (w ≫ sX) := hWproj hX
    have hGYZ : 0 ≤ GY - GZ :=
      MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (w ≫ sX) (h ≫ sX) sZ hWn hWpv hYn
        hYp hZn hφ.isProjectiveVariety_target (h ≫ πX) πZ p q hps hqs hpq hpp hpb hqp hqb
        (isCartierCombination_of_isRCartier (isRCartier_of_isQFactorial hYq _))
        hφ.isRelativelyNef hGY hGZq hpush
    /- The comparison is supported on `q`-exceptional primes. -/
    haveI : AlgebraicGeometry.IsVariety ℂ (w ≫ sX) := hWn.1
    have hdimZ : topologicalKrullDim Z = 3 := by
      rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (w ≫ sX) hqb,
        ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (w ≫ sX) hwb]
      exact hK.topologicalKrullDim_eq
    haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
    have hqnv : IsNormalVariety ℂ (q ≫ sZ) := by rw [hqs]; exact hWn
    have hexc : ∀ G : MMP.Mori.PrimeDivisor W, (GY - GZ).coeff G ≠ 0 →
        MMP.Flips.IsExceptionalPrimeDivisor sZ q G := by
      intro G hG
      by_contra hne
      have hco : Order.coheight (q G.genericPoint) ≤ 1 := by
        by_contra h2
        have h2' : 2 ≤ Order.coheight (q G.genericPoint) := by
          have := Order.add_one_le_of_lt (not_le.mp h2)
          simpa [one_add_one_eq_two] using this
        exact hne ⟨hqnv, hqb, inferInstance, (isExceptional_iff_two_le_coheight hdimZ
          (MMP.Flips.ProperDivisorOver.mk ⟨W, q, hqnv, hqb, G⟩ inferInstance)).mpr h2'⟩
      rcases eq_or_lt_of_le hco with h1 | h0
      · have hF := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1
        set F := AlgebraicGeometry.PrimeDivisor.ofCoheightOne (q G.genericPoint) h1
        have hGE : G = sP (sY (QF F)) := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_apply_eq_of_coheight_le_one q hqbij ((hV1 F).trans hF) hco)
        apply hG
        rw [hGE, hGYc, hCF]
        linarith [hbF F]
      · have h0' : Order.coheight (q G.genericPoint) = 0 := ENat.lt_one_iff_eq_zero.mp h0
        have hmax : IsMax (q G.genericPoint) := Order.coheight_eq_zero.mp h0'
        have hgen : genericPoint Z ⤳ q G.genericPoint := (genericPoint_spec Z).specializes trivial
        have hx' : q G.genericPoint ⤳ genericPoint Z :=
          hmax (show q G.genericPoint ≤ genericPoint Z from hgen)
        have hgx : genericPoint Z = q G.genericPoint := (hgen.antisymm hx').eq
        have hq1 : q (genericPoint W) = genericPoint Z :=
          MMP.Positivity.map_genericPoint_eq_of_isDominant q
        have hGW : G.genericPoint = genericPoint W :=
          eq_of_apply_eq_of_coheight_le_one q hqbij (hq1.trans hgx) hco
        have hc1 := G.coheight_genericPoint
        have hc0 : Order.coheight (genericPoint W) = 0 :=
          Order.coheight_eq_zero.mpr fun y _ => (genericPoint_spec W).specializes (Set.mem_univ y)
        rw [hGW, hc0] at hc1
        exact zero_ne_one hc1
    /- The nef weak model `φ ∘ h` of `(Y, C)`. -/
    obtain ⟨eh, heh⟩ := id hh
    obtain ⟨e₀, he₀⟩ := hφ.isBirational
    haveI := isDominant_toRationalMap eh
    have hψbir : MMP.Mori.RationalMap.IsBirational (h.toRationalMap.comp φ) :=
      ⟨eh.trans e₀, by rw [toRationalMap_trans, ← he₀]; exact comp_eq_comp_of_eq heh _⟩
    haveI : φ.IsDominant := isDominant_of_isBirational hφ.isBirational
    have hψover : MMP.Flips.RationalMap.IsOver (h ≫ πX) πZ (h.toRationalMap.comp φ) := by
      change (h.toRationalMap.comp φ).compHom πZ = (h ≫ πX).toRationalMap
      rw [comp_compHom, (hφ.isOver : φ.compHom πZ = πX.toRationalMap),
        Scheme.RationalMap.comp_toRationalMap, toRationalMap_compHom]
    have hNWM : IsNefWeakModel (h ≫ sX) sZ sS (h ≫ πX) πZ KY C (h.toRationalMap.comp φ) :=
      { isNormalVariety_source := hYn
        isProjectiveVariety_source := hYp
        comp_eq_source := by rw [Category.assoc, hφ.comp_eq_source]
        isCanonicalDivisor := ⟨3, hKY⟩
        isCartierCombination :=
          isCartierCombination_of_isRCartier (isRCartier_of_isQFactorial hYq _)
        isNormalVariety_target := hφ.isNormalVariety_target
        isProjectiveVariety_target := hφ.isProjectiveVariety_target
        comp_eq_target := hφ.comp_eq_target
        isBirational := hψbir
        isOver := hψover
        not_isInverseExceptional := fun F hF => hF (sY (QF F)) (hψF F).1
        isRelativelyNef := by rw [hT1, hT2]; exact hφ.isRelativelyNef
        exists_resolution := ⟨W, inferInstance, inferInstance, inferInstance, w ≫ sX, p, q, hW,
          hWn.1, hWsm, hps, hqs, hpp, hqp, hpb, hqb, hWinv, hV4, GY, GZ, hGY,
          by rw [hT1, hT2]; exact hGZq, fun P => hGYZ P, hexc⟩ }
    refine ⟨hNWM, hT1, hT2, W, inferInstance, inferInstance, inferInstance, w ≫ sX, p, q, hW,
      hWn.1, hWsm, hps, hqs, hpp, hqp, hpb, hqb, hWinv, hV4, GY, GZ, hGY,
      by rw [hT1, hT2]; exact hGZq, fun P hP => ⟨sP P,
        transformPrimeDivisor_eq_some_of_isInverse hpbij hWinv (hsPp P), ?_⟩⟩
    rw [hGYc]
    have h1 := hC P
    have h2 : 0 < (RationalMap.transformDivisor p.toRationalMap GZ).coeff P -
        (KY.coeff P : ℝ) := by
      rw [h1] at hP
      by_contra hle
      push Not at hle
      rw [max_eq_right hle] at hP
      exact lt_irrefl _ hP
    rw [h1, max_eq_left h2.le]
    ring

/-! ### The convergent subsequence -/

/-- The coefficients of `∑_{P ∈ A} x_P P`. -/
private theorem coeff_sum_single_subtype {Y : Scheme.{0}} [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    {A : Finset (MMP.Mori.PrimeDivisor Y)} (x : A → ℝ) (P : MMP.Mori.PrimeDivisor Y) :
    (∑ Q : A, Finsupp.single Q.1 (x Q) : RDivisor Y).coeff P =
      if hP : P ∈ A then x ⟨P, hP⟩ else 0 := by
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  split_ifs with hP
  · rw [Finset.sum_eq_single ⟨P, hP⟩ (fun Q _ hQ => by
        rw [Finsupp.single_apply, if_neg fun h => hQ (Subtype.ext h)])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  · exact Finset.sum_eq_zero fun Q _ => by
      rw [Finsupp.single_apply,
        if_neg fun h : (Q : MMP.Mori.PrimeDivisor Y) = P => hP (h ▸ Q.2)]

/-- For boundaries `B, B₀` supported on `T`, `K + B = (K + B₀) + ∑_{Q ∈ T} (b_Q - b₀_Q) Q`. -/
private theorem logCanonicalDivisor_eq_add_sum {X : Scheme.{0}} {K : Divisor X}
    {B B₀ : RDivisor X} {T : Finset (MMP.Mori.PrimeDivisor X)}
    (hoff : ∀ P, P ∉ T → B.coeff P = 0) (hoff₀ : ∀ P, P ∉ T → B₀.coeff P = 0) :
    MMP.Flips.logCanonicalDivisor K B = MMP.Flips.logCanonicalDivisor K B₀ +
      ∑ Q ∈ T, (B.coeff Q - B₀.coeff Q) • Finsupp.single Q (1 : ℝ) := by
  classical
  refine Finsupp.ext fun P => ?_
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply]
  simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add]
  rw [DivisorWithCoeffs.coeff_apply (∑ Q ∈ T, _), Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq']
  split_ifs with hP
  · ring
  · rw [hoff P hP, hoff₀ P hP]
    ring

/-- **The geometric core.** Under the hypotheses of the theorem, some subsequence of the nef models
has all its terms equivalent to finitely many of its terms. -/
private theorem exists_strictMono_finset_isNefModelEquivalent
    {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (πX : X ⟶ S) (hπX : πX ≫ sS = sX)
    (B : ℕ → RDivisor X) (B₀ : RDivisor X) (hB : ∀ i, 0 ≤ B i)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (hT : ∀ i, (B i).support ⊆ T)
    (hlim : ∀ P, Tendsto (fun i ↦ (B i).coeff P) atTop (𝓝 (B₀.coeff P)))
    (hklt : IsRealKltPair sX B₀)
    (Z : ℕ → Scheme.{0}) [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, X.RationalMap (Z i))
    (hφ : ∀ i, IsNefWeakModel sX (sZ i) sS πX (πZ i) K (B i) (φ i))
    (hZq : ∀ i, IsQFactorial (sZ i))
    (hsmall : ∀ i (P : MMP.Mori.PrimeDivisor X), ¬ RationalMap.IsExceptional (φ i) P) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ J : Finset ℕ, ∀ n, ∃ m ∈ J,
      ∃ (eᵢ : X.PartialIso (Z (τ n))) (eⱼ : X.PartialIso (Z (τ m))),
        eᵢ.toRationalMap = φ (τ n) ∧ eⱼ.toRationalMap = φ (τ m) ∧
        IsNefModelEquivalent (sZ (τ n)) (sZ (τ m)) sS (πZ (τ n)) (πZ (τ m))
          (RationalMap.transformDivisor (φ (τ n)) K)
          (RationalMap.transformDivisor (φ (τ n)) (B (τ n)))
          (RationalMap.transformDivisor (φ (τ m)) K)
          (RationalMap.transformDivisor (φ (τ m)) (B (τ m)))
          (eᵢ.symm.trans eⱼ).toRationalMap := by
  classical
  have hdim : topologicalKrullDim X = 3 := hK.topologicalKrullDim_eq
  have hBc : ∀ i P, 0 ≤ (B i).coeff P := fun i P => hB i P
  have hB₀ : ∀ P, 0 ≤ B₀.coeff P := fun P => ge_of_tendsto' (hlim P) fun i => hBc i P
  have hoff : ∀ i P, P ∉ T → (B i).coeff P = 0 := fun i P hP =>
    Finsupp.notMem_support_iff.mp fun h => hP (hT i h)
  have hoff₀ : ∀ P, P ∉ T → B₀.coeff P = 0 := fun P hP =>
    tendsto_nhds_unique (hlim P) (by simp [hoff _ P hP])
  /- The crepant terminal model `h : Y ⟶ X`. -/
  obtain ⟨Y, _, _, _, h, hh, hYq, BY, hhp, hBY0, hBYld, hBYt⟩ :=
    IsRealKltPair.exists_isRealTerminalPair_crepant hX hdim hB₀ hklt
  haveI : IsDominant h := hh.isDominant
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhp
  haveI : CompactSpace X := hX.toQuasiCompact.compactSpace_of_compactSpace
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  have hRC := isRCartier_of_isQFactorial hXq
  obtain ⟨GX₀, hGX₀⟩ :=
    exists_isRCartierPullback_of_isRCartier h (hRC (MMP.Flips.logCanonicalDivisor K B₀))
  choose GQ hGQ using fun Q : MMP.Mori.PrimeDivisor X =>
    exists_isRCartierPullback_of_isRCartier h (hRC (Finsupp.single Q 1))
  obtain ⟨KY, hKY, hKYK, hBYeq⟩ := exists_isCanonicalDivisor_crepant hX hK hh hYq.1 hhp hBYld hGX₀
  /- The pull-backs `h^*(K_X + B_i)`. -/
  let GX : ℕ → RDivisor Y := fun i => GX₀ + ∑ Q ∈ T, ((B i).coeff Q - B₀.coeff Q) • GQ Q
  have hGX : ∀ i,
      MMP.Flips.IsRCartierPullback h (MMP.Flips.logCanonicalDivisor K (B i)) (GX i) := by
    intro i
    rw [logCanonicalDivisor_eq_add_sum (hoff i) hoff₀]
    exact isRCartierPullback_add hGX₀
      (isRCartierPullback_sum _ _ _ fun Q _ => isRCartierPullback_smul _ (hGQ Q))
  have hGXc : ∀ i P, (GX i).coeff P - KY.coeff P =
      BY.coeff P + ∑ Q ∈ T, ((B i).coeff Q - B₀.coeff Q) * (GQ Q).coeff P := by
    intro i P
    have := hBYeq P
    simp only [GX, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have hu_lim : ∀ P, Tendsto (fun i => (GX i).coeff P - KY.coeff P) atTop (𝓝 (BY.coeff P)) := by
    intro P
    simp_rw [hGXc]
    have : Tendsto (fun i => ∑ Q ∈ T, ((B i).coeff Q - B₀.coeff Q) * (GQ Q).coeff P) atTop
        (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ Q ∈ T, (0 : ℝ) * (GQ Q).coeff P by simp]
      refine tendsto_finset_sum _ fun Q _ => Tendsto.mul_const _ ?_
      simpa using (hlim Q).sub_const (B₀.coeff Q)
    simpa using this.const_add (BY.coeff P)
  let A : Finset (MMP.Mori.PrimeDivisor Y) := BY.support ∪ T.biUnion fun Q => (GQ Q).support
  have hu_off : ∀ i P, P ∉ A → (GX i).coeff P - KY.coeff P = 0 := by
    intro i P hP
    rw [hGXc]
    simp only [A, Finset.mem_union, Finset.mem_biUnion, not_or, not_exists, not_and,
      Finsupp.mem_support_iff, not_not] at hP
    rw [DivisorWithCoeffs.coeff_apply, hP.1, zero_add]
    exact Finset.sum_eq_zero fun Q hQ => by
      rw [DivisorWithCoeffs.coeff_apply (GQ Q), hP.2 Q hQ, mul_zero]
  /- The comparison boundaries. -/
  choose Γ hΓle hΓ using fun i => exists_comparisonBoundary hX hXq hK hS hh hYq hhp hKY hKYK
    (hB i) (hφ i) (hsmall i) (hGX i)
  let b : ℕ → MMP.Mori.PrimeDivisor Y → ℝ := fun i P => (Γ i).coeff P - KY.coeff P
  have hb_le : ∀ i P, b i P ≤ (GX i).coeff P - KY.coeff P := fun i P =>
    sub_le_sub_right (hΓle i P) _
  have hb_off : ∀ i P, P ∉ A → b i P ≤ 0 := fun i P hP => (hb_le i P).trans (hu_off i P hP).le
  /- A subsequence with a fixed positive support. -/
  obtain ⟨τ₁, hτ₁, S₀, hS₀⟩ :=
    exists_strictMono_eq_of_finite
      (fun i => ((Finset.univ : Finset A).filter fun P : A => 0 < b i P : Finset A))
  /- A further subsequence along which the coefficients converge. -/
  let c : ℕ → A → ℝ := fun n P => max (b (τ₁ n) P) 0
  have hc_bdd : Bornology.IsBounded (Set.range c) := by
    choose M hM using fun P : A => (hu_lim P.1).bddAbove_range
    refine isBounded_iff_forall_norm_le.2 ⟨∑ P : A, max (M P) 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)).2
      fun P => ?_
    have h1 : c n P ≤ max (M P) 0 := max_le_max ((hb_le _ _).trans (hM P ⟨τ₁ n, rfl⟩)) le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact h1.trans (Finset.single_le_sum (f := fun P => max (M P) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ P))
  obtain ⟨c₀, -, τ₂, hτ₂, hc⟩ := tendsto_subseq_of_bounded hc_bdd (fun n => Set.mem_range_self n)
  let D : (A → ℝ) → RDivisor Y := fun x => ∑ P : A, Finsupp.single P.1 (x P)
  have hDc : ∀ (x : A → ℝ) (P : MMP.Mori.PrimeDivisor Y),
      (D x).coeff P = if hP : P ∈ A then x ⟨P, hP⟩ else 0 := coeff_sum_single_subtype
  have hcoord : ∀ P : A, Tendsto (fun n => c (τ₂ n) P) atTop (𝓝 (c₀ P)) := fun P =>
    tendsto_pi_nhds.1 hc P
  have hc₀le : ∀ P, (D c₀).coeff P ≤ BY.coeff P := by
    intro P
    rw [hDc]
    split_ifs with hP
    · have ht := ((hu_lim P).comp (hτ₁.comp hτ₂).tendsto_atTop).max
        (tendsto_const_nhds (x := (0 : ℝ)))
      rw [max_eq_left (hBY0 P)] at ht
      exact le_of_tendsto_of_tendsto' (hcoord ⟨P, hP⟩) ht fun n => max_le_max (hb_le _ _) le_rfl
    · exact hBY0 P
  have hc₀0 : ∀ P, 0 ≤ (D c₀).coeff P := by
    intro P
    rw [hDc]
    split_ifs with hP
    · exact ge_of_tendsto' (hcoord ⟨P, hP⟩) fun n => le_max_right _ _
    · exact le_rfl
  have hterm : IsRealTerminalPair (h ≫ sX) (D c₀) := isRealTerminalPair_of_le hYq hBYt hc₀0 hc₀le
  /- Terminality persists near the limit. -/
  have hYp : MMP.Mori.IsProjectiveVariety ℂ (h ≫ sX) :=
    (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hYq.1.1, IsProjectiveMorphism.comp hhp
      ((MMP.Mori.isProjectiveVariety_iff ℂ sX).mp hX).2⟩
  have hYqp : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ (h ≫ sX) :=
    IsProjectiveVariety.isQuasiProjectiveVariety ℂ _
  have hopen := (eventually_isRealKltPair_and_isRealTerminalPair (h ≫ sX) hYqp hYq
    (fun P : A => P.1) c₀).2 hterm
  have hev : ∀ᶠ n in atTop, IsRealTerminalPair (h ≫ sX) (D (c (τ₂ n))) :=
    (tendsto_nhdsWithin_iff.2 ⟨hc, Eventually.of_forall fun n =>
      Set.mem_Ici.2 fun P => le_max_right _ _⟩).eventually
      hopen
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let τ : ℕ → ℕ := fun n => τ₁ (τ₂ (n + N))
  have hτ : StrictMono τ := hτ₁.comp (hτ₂.comp fun a b hab => Nat.add_lt_add_right hab N)
  let C' : ℕ → RDivisor Y := fun n => D (c (τ₂ (n + N)))
  have hC'c : ∀ n P, (C' n).coeff P = max ((Γ (τ n)).coeff P - KY.coeff P) 0 := by
    intro n P
    rw [hDc]
    split_ifs with hP
    · rfl
    · exact (max_eq_right (hb_off _ P hP)).symm
  let F : Finset (MMP.Mori.PrimeDivisor Y) := S₀.map (Function.Embedding.subtype _)
  have hF : ∀ n P, P ∈ F ↔ 0 < (C' n).coeff P := by
    intro n P
    rw [hC'c n P, lt_max_iff, or_iff_left (lt_irrefl 0)]
    simp only [F, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rw [← hS₀ (τ₂ (n + N))] at hQ
      exact (Finset.mem_filter.1 hQ).2
    · intro hb
      have hP : P ∈ A := Classical.byContradiction fun hP => (hb_off _ P hP).not_gt hb
      refine ⟨⟨P, hP⟩, ?_, rfl⟩
      rw [← hS₀ (τ₂ (n + N))]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
  have hlimC : ∀ P, Tendsto (fun n => (C' n).coeff P) atTop (𝓝 ((D c₀).coeff P)) := by
    intro P
    simp only [C', hDc]
    split_ifs with hP
    · exact (hcoord ⟨P, hP⟩).comp (tendsto_add_atTop_nat N)
    · exact tendsto_const_nhds
  have hdimY : topologicalKrullDim Y = 3 := hKY.topologicalKrullDim_eq
  obtain ⟨J, hJ⟩ := finite_isNefModelEquivalent_of_tendsto_isRealTerminalPair (πY := h ≫ πX)
    hYp hYq hdimY hS (by rw [Category.assoc, hπX]) KY F C' (D c₀)
    (fun n => hN _ (Nat.le_add_left N n)) hterm hF hlimC (Z := fun n => Z (τ n))
    (fun n => sZ (τ n)) (fun n => πZ (τ n)) (fun n => h.toRationalMap.comp (φ (τ n)))
    (fun n => ((hΓ (τ n)) (C' n) (hC'c n)).1) (fun n => hZq (τ n))
    (fun n => by
      obtain ⟨-, -, -, W, i1, i2, i3, sW, p, q, hW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, GY, GZ,
        hGY, hGZ, hzero⟩ := (hΓ (τ n)) (C' n) (hC'c n)
      exact ⟨W, i1, i2, i3, sW, p, q, hW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, GY, GZ, hGY,
        hGZ, fun P hP => hzero P ((hF n P).1 hP)⟩)
  refine ⟨τ, hτ, J, fun n => ?_⟩
  obtain ⟨m, hm, eY, eY', heY, heY', hequiv⟩ := hJ n
  obtain ⟨f₁, f₂, hf₁, hf₂, htrans⟩ := exists_partialIso_trans_eq h hh (φ (τ n)) (φ (τ m)) eY eY'
    heY heY'
  refine ⟨m, hm, f₁, f₂, hf₁, hf₂, ?_⟩
  obtain ⟨-, hK₁, hB₁, -⟩ := (hΓ (τ n)) (C' n) (hC'c n)
  obtain ⟨-, hK₂, hB₂, -⟩ := (hΓ (τ m)) (C' m) (hC'c m)
  rw [htrans, ← hK₁, ← hB₁, ← hK₂, ← hB₂]
  exact hequiv

private theorem solution
    {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (πX : X ⟶ S) (hπX : πX ≫ sS = sX)
    (B : ℕ → RDivisor X) (B₀ : RDivisor X) (hB : ∀ i, 0 ≤ B i)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (hT : ∀ i, (B i).support ⊆ T)
    (hlim : ∀ P, Tendsto (fun i ↦ (B i).coeff P) atTop (𝓝 (B₀.coeff P)))
    (hklt : IsRealKltPair sX B₀)
    (Z : ℕ → Scheme.{0}) [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, X.RationalMap (Z i))
    (hφ : ∀ i, IsNefWeakModel sX (sZ i) sS πX (πZ i) K (B i) (φ i))
    (hZq : ∀ i, IsQFactorial (sZ i))
    (hsmall : ∀ i (P : MMP.Mori.PrimeDivisor X), ¬ RationalMap.IsExceptional (φ i) P) :
    ∃ F : Finset ℕ, ∀ i, ∃ j ∈ F, ∃ (eᵢ : X.PartialIso (Z i)) (eⱼ : X.PartialIso (Z j)),
      eᵢ.toRationalMap = φ i ∧ eⱼ.toRationalMap = φ j ∧
      IsNefModelEquivalent (sZ i) (sZ j) sS (πZ i) (πZ j)
        (RationalMap.transformDivisor (φ i) K) (RationalMap.transformDivisor (φ i) (B i))
        (RationalMap.transformDivisor (φ j) K) (RationalMap.transformDivisor (φ j) (B j))
        (eᵢ.symm.trans eⱼ).toRationalMap := by
  refine exists_finset_of_forall_strictMono (fun i => exists_isNefModelEquivalent_self hS (hφ i))
    fun σ hσ => ?_
  exact exists_strictMono_finset_isNefModelEquivalent hX hXq hK hS πX hπX (fun n => B (σ n)) B₀
    (fun n => hB (σ n)) T (fun n => hT (σ n))
    (fun P => (hlim P).comp hσ.tendsto_atTop) hklt (fun n => Z (σ n)) (fun n => sZ (σ n))
    (fun n => πZ (σ n)) (fun n => φ (σ n)) (fun n => hφ (σ n)) (fun n => hZq (σ n))
    (fun n => hsmall (σ n))

end Proof_thm_fourfold_convergent_klt_weak_models_finite

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology

namespace MMP.Fourfold

open MMP.Mori

/-- **Finiteness for convergent small klt weak models.** Let `X` be a normal projective
`ℚ`-factorial complex threefold with canonical divisor `K`, over a projective variety `S` by
`πX`. Let `B i` be effective real boundaries on `X` supported on a fixed finite set `T` of prime
divisors and converging coefficientwise to `B`, with `(X, B)` klt. Suppose that for every `i`,
`φ i : X ⤏ Z i` is a nef weak model of `(X, B i)` over `S`, with `Z i` `ℚ`-factorial, and that
`φ i` contracts no prime divisor of `X` (so that it is an isomorphism in codimension one).
Then there is a finite set `F` of indices such that every nef model
`(Z i, (φ i)_* K + (φ i)_* (B i))` is equivalent (`MMP.Fourfold.IsNefModelEquivalent`), through
`φ j ∘ (φ i)⁻¹`, to `(Z j, (φ j)_* K + (φ j)_* (B j))` for some `j ∈ F`. -/
@[mmp "thm_fourfold_convergent_klt_weak_models_finite"]
public theorem exists_finset_isNefModelEquivalent_of_tendsto
    {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXq : IsQFactorial sX)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (πX : X ⟶ S) (hπX : πX ≫ sS = sX)
    (B : ℕ → RDivisor X) (B₀ : RDivisor X) (hB : ∀ i, 0 ≤ B i)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (hT : ∀ i, (B i).support ⊆ T)
    (hlim : ∀ P, Tendsto (fun i ↦ (B i).coeff P) atTop (𝓝 (B₀.coeff P)))
    (hklt : IsRealKltPair sX B₀)
    (Z : ℕ → Scheme.{0}) [∀ i, IsIntegral (Z i)] [∀ i, IsLocallyNoetherian (Z i)]
    [∀ i, IsNormal (Z i)] (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) [∀ i, QuasiCompact (sZ i)]
    (πZ : ∀ i, Z i ⟶ S) (φ : ∀ i, X.RationalMap (Z i))
    (hφ : ∀ i, IsNefWeakModel sX (sZ i) sS πX (πZ i) K (B i) (φ i))
    (hZq : ∀ i, IsQFactorial (sZ i))
    (hsmall : ∀ i (P : MMP.Mori.PrimeDivisor X), ¬ RationalMap.IsExceptional (φ i) P) :
    ∃ F : Finset ℕ, ∀ i, ∃ j ∈ F, ∃ (eᵢ : X.PartialIso (Z i)) (eⱼ : X.PartialIso (Z j)),
      eᵢ.toRationalMap = φ i ∧ eⱼ.toRationalMap = φ j ∧
      IsNefModelEquivalent (sZ i) (sZ j) sS (πZ i) (πZ j)
        (RationalMap.transformDivisor (φ i) K) (RationalMap.transformDivisor (φ i) (B i))
        (RationalMap.transformDivisor (φ j) K) (RationalMap.transformDivisor (φ j) (B j))
        (eᵢ.symm.trans eⱼ).toRationalMap :=
  Proof_thm_fourfold_convergent_klt_weak_models_finite.solution hX hXq hK hS πX hπX B B₀ hB T hT
    hlim hklt Z sZ πZ φ hφ hZq hsmall

end MMP.Fourfold
