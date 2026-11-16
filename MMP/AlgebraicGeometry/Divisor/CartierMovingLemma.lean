module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.NineClauses
public import MMP.AlgebraicGeometry.Modules.FiniteLocallyFreeRankOne
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafInvertible
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackEffective
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullbackSheaf
public import MMP.AlgebraicGeometry.Divisor.InvertibleSheafOfEffective

/-!
# Moving a Cartier divisor off finitely many points

Let `Y` be a projective variety over an infinite field and `H` a Cartier divisor on `Y`. For any
finite set `S ⊆ Y` there are effective Cartier divisors `A`, `B` with `𝒪(H) ≅ 𝒪(A - B)` whose
supports miss `S`: for an ample `L` and `n ≫ 0` the sheaves `𝒪(H) ⊗ L^{⊗ n}` and `L^{⊗ n}` are
globally generated ([Stacks, Tag 01Q3]); the global sections vanishing at a point form a proper
subspace, so a section avoids all of `S`, and `A`, `B` are the divisors of two such sections.

If the image of the generic point of an integral scheme `X'` under `f : X' ⟶ Y` lies outside
`Supp A ∪ Supp B`, then `f^*𝒪(H) ≅ 𝒪(f^*A - f^*B)` with `f^*A`, `f^*B` effective.

For a curve-image component `E` of a curve-and-point exceptional model `r : Z ⟶ Y`, the image
`T = r(E)` is a curve, and for an open `U` meeting `T` the set `T ∖ U` is finite and consists of
closed points. Taking `S` to be `T ∖ U` together with the generic point of `T` gives
`(r|_E)^*𝒪(H_Y) ≅ 𝒪(D₁ - D₂)` with `D₁`, `D₂` effective and supported over closed points of
`U ∩ T`.

## Main results

* `MMP.Fourfold.isClosed_singleton_of_isGenericPoint_of_ne`,
  `MMP.Fourfold.finite_diff_of_isGenericPoint`: the points of a closed set of dimension at most
  one, other than its generic point, are closed, and finitely many of them lie outside an open
  set containing the generic point.
* `MMP.Fourfold.exists_forall_mem_nvOpen_of_isGeneratedByGlobalSections`: a globally generated
  invertible module over an infinite field has a section not vanishing on a given finite set.
* `MMP.Fourfold.exists_isEffective_nonempty_sheaf_iso_of_mem_nvOpen`: the divisor of a section.
* `MMP.Fourfold.exists_isEffective_nonempty_sheaf_iso_sub_disjoint`: the moving lemma.
* `MMP.Fourfold.exists_isEffective_nonempty_pullback_sheaf_iso_sub`: its pull-back.
* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_isEffective_iso_pullback_sheaf_sub`: the
  statement for a curve-and-point exceptional model.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

public section

open AlgebraicGeometry CategoryTheory Opposite MMP

namespace MMP.Fourfold

section Topology

variable {X : Type*} [TopologicalSpace X] [T0Space X]

/-- In a space whose closed subset `T` has the generic point `η` and dimension at most one, every
point of `T` other than `η` is closed. -/
theorem isClosed_singleton_of_isGenericPoint_of_ne {T : Set X} {η : X} (hη : IsGenericPoint η T)
    (hdim : topologicalKrullDim T ≤ 1) {y : X} (hy : y ∈ T) (hne : y ≠ η) :
    IsClosed ({y} : Set X) := by
  by_contra hcl
  obtain ⟨w, hw, hwy⟩ : ∃ w ∈ closure ({y} : Set X), w ≠ y := by
    by_contra! h
    exact hcl (closure_subset_iff_isClosed.mp fun w hw => by rw [h w hw]; rfl)
  have hTc : IsClosed T := hη.def ▸ isClosed_closure
  have hwT : w ∈ T := closure_minimal (Set.singleton_subset_iff.mpr hy) hTc hw
  have hηT : η ∈ T := hη.mem
  let cl : T → TopologicalSpace.IrreducibleCloseds T := fun a =>
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ a b : T, (b : X) ⤳ a → (a : X) ≠ b → cl a < cl b := by
    intro a b h hab
    have h₁ : b ⤳ a := Topology.IsInducing.subtypeVal.specializes_iff.mp h
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp h₁) fun he => hab ?_
    have h₂ : a ⤳ b := by
      rw [specializes_iff_closure_subset]
      exact (congrArg (fun Z : TopologicalSpace.IrreducibleCloseds T => (Z : Set T)) he).ge
    exact congrArg Subtype.val (h₂.antisymm h₁).eq
  have h1 : cl ⟨w, hwT⟩ < cl ⟨y, hy⟩ :=
    hlt _ _ (specializes_iff_mem_closure.mpr hw) hwy
  have h2 : cl ⟨y, hy⟩ < cl ⟨η, hηT⟩ :=
    hlt _ _ (specializes_iff_mem_closure.mpr (hη.def ▸ hy)) hne
  let p : LTSeries (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨2, ![cl ⟨w, hwT⟩, cl ⟨y, hy⟩, cl ⟨η, hηT⟩], fun i => by
      fin_cases i
      · exact h1
      · exact h2⟩
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim p).trans hdim
  exact absurd this (by decide)

/-- In a noetherian quasi-sober space, a closed set `T` of dimension at most one with generic
point `η` meets the complement of an open `U ∋ η` in finitely many points. -/
theorem finite_diff_of_isGenericPoint [QuasiSober X] [TopologicalSpace.NoetherianSpace X]
    {T : Set X} {η : X} (hη : IsGenericPoint η T) (hdim : topologicalKrullDim T ≤ 1)
    {U : Set X} (hU : IsOpen U) (hηU : η ∈ U) : (T \ U).Finite := by
  have hTc : IsClosed T := hη.def ▸ isClosed_closure
  obtain ⟨S, hSf, hScl, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (hTc.sdiff hU)
  rw [hS]
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  have hzTU : z ∈ T \ U := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
  rw [← hz.def, (isClosed_singleton_of_isGenericPoint_of_ne hη hdim hzTU.1
    fun h => hzTU.2 (h ▸ hηU)).closure_eq]
  exact Set.finite_singleton z

end Topology

universe u

section Sections

open Stacks.NonvanishingSpelling

/-- **A section avoiding finitely many points.** On a scheme over an infinite field `k`, a
globally generated invertible module `M` has a global section not vanishing at any point of a
given finite set. -/
theorem exists_forall_mem_nvOpen_of_isGeneratedByGlobalSections {k : Type u} [Field k]
    [Infinite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (hM : SheafOfModules.IsGeneratedByGlobalSections M)
    {S : Set X} (hS : S.Finite) :
    ∃ s : Γ(M, ⊤), ∀ y ∈ S, y ∈ Stacks.ProjectiveFromSections.nvOpen M s := by
  classical
  obtain ⟨g⟩ := hM
  have : Finite S := hS.to_subtype
  let V := Stacks.Bertini.globalSections k f M
  let p : S → Submodule k V := fun y =>
    { carrier := {v | y.1 ∉ Stacks.ProjectiveFromSections.nvOpen M (show Γ(M, ⊤) from v)}
      add_mem' := fun {a b} ha hb => by
        refine (Stacks.Chow.BertiniChain.notMem_nvOpen_iff M
          ((show Γ(M, ⊤) from a) + (show Γ(M, ⊤) from b)) y.1).2 ?_
        rw [map_add]
        exact Submodule.add_mem _ ((Stacks.Chow.BertiniChain.notMem_nvOpen_iff M _ y.1).1 ha)
          ((Stacks.Chow.BertiniChain.notMem_nvOpen_iff M _ y.1).1 hb)
      zero_mem' := by
        refine (Stacks.Chow.BertiniChain.notMem_nvOpen_iff M (0 : Γ(M, ⊤)) y.1).2 ?_
        rw [map_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun c v hv => by
        refine (Stacks.Chow.BertiniChain.notMem_nvOpen_iff M (show Γ(M, ⊤) from c • v) y.1).2 ?_
        exact Stacks.StalkwiseGeneration.mem_of_Γgerm_smul M y.1
          (show Γ(X, ⊤) from Stacks.Bertini.baseRingHom k f c) (show Γ(M, ⊤) from v) _
          ((Stacks.Chow.BertiniChain.notMem_nvOpen_iff M _ y.1).1 hv) }
  have hp : ∀ y, p y ≠ ⊤ := by
    intro y htop
    obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing M g y.1
    have hmem : (show V from (g.s i).eval (op ⊤)) ∈ p y := htop ▸ Submodule.mem_top
    exact hmem hi
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨v, fun y hy => ?_⟩
  by_contra h
  exact hv ⟨y, hy⟩ h

/-- **The divisor of a section.** A global section of an invertible module `M` on an integral
scheme which does not vanish at some point is the canonical section of an effective Cartier
divisor `D` with `𝒪(D) ≅ M`, whose support misses the nonvanishing locus of the section. -/
theorem exists_isEffective_nonempty_sheaf_iso_of_mem_nvOpen {X : Scheme.{u}} [IsIntegral X]
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (s : Γ(M, ⊤)) {x₀ : X}
    (hx₀ : x₀ ∈ Stacks.ProjectiveFromSections.nvOpen M s) :
    ∃ D : X.CartierDivisor, MMP.Intersection.IsEffective D ∧
      Nonempty (MMP.CartierDivisor.sheaf D ≅ M) ∧
      ∀ x ∈ Stacks.ProjectiveFromSections.nvOpen M s, x ∉ MMP.Intersection.cartierSupport D := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  set t := Stacks.SheafOfModules.sectionsOfTop M s with ht
  have hevaltop : t.eval (op ⊤) = s := Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne : t.eval (op ⊤) ≠ 0 := by
    rw [hevaltop]
    rintro rfl
    refine (Stacks.Chow.BertiniChain.notMem_nvOpen_iff M 0 x₀).2 ?_ hx₀
    rw [map_zero]
    exact Submodule.zero_mem _
  have hreg := isRegularSection_of_eval_top_ne_zero _ _ hne
  have hZc := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme M t hne
  obtain ⟨D, hD, hDZ⟩ :=
    (MMP.CartierDivisor.isEffectiveCartierDivisor_iff_exists_subscheme_eq _).1 hZc
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme X M t hreg).exists
  refine ⟨D, hD, ⟨MMP.CartierDivisor.sheafIsoInvertibleSheaf D hD ≪≫
    eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hDZ) ≪≫ e⟩, fun x hx hxD => ?_⟩
  have h1 := MMP.CartierDivisor.coe_support_subscheme hD
  rw [hDZ] at h1
  have hxZ : x ∈ ((zeroScheme X M (t.eval (op ⊤))).support : Set X) := h1 ▸ hxD
  have hxnv :=
    (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_sectionsOfTop_iff'
      M s x).1 hx
  rw [← ht, hcompl] at hxnv
  exact hxnv hxZ

end Sections

section Moving

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat
  MMP.CartierDivisor.isInvertible_sheaf
  Stacks.SheafInternalHom.schemeMonoidalCategory

/-- **Moving a Cartier divisor off finitely many points.** On a projective variety `Y` over an
infinite field, every Cartier divisor `H` satisfies `𝒪(H) ≅ 𝒪(A - B)` for effective Cartier
divisors `A`, `B` whose supports miss a given finite set `S`. -/
theorem exists_isEffective_nonempty_sheaf_iso_sub_disjoint {k : Type u} [Field k] [Infinite k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k sY)
    (H : Y.CartierDivisor) {S : Set Y} (hS : S.Finite) :
    ∃ A B : Y.CartierDivisor, MMP.Intersection.IsEffective A ∧ MMP.Intersection.IsEffective B ∧
      Nonempty (CartierDivisor.sheaf H ≅ CartierDivisor.sheaf (A - B)) ∧
      Disjoint S (MMP.Intersection.cartierSupport A) ∧
      Disjoint S (MMP.Intersection.cartierSupport B) := by
  have : IsIntegral Y := hY.toIsIntegral
  obtain ⟨L, hLi, hLa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hY
  have hL : Stacks.Ample.IsAmple Y L := (Stacks.AmpleBridge.isAmple_iff_isAmple Y L).mpr hLa
  have hgen :=
    (Stacks.AmpleCharacterization.quasiSeparatedSpace_and_isGeneratedByGlobalSections_of_isAmple
      L hL).2
  obtain ⟨n₁, hn₁⟩ := hgen (MMP.CartierDivisor.sheaf H) inferInstance
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  obtain ⟨n₂, hn₂⟩ := hgen (MMP.CartierDivisor.sheaf (0 : Y.CartierDivisor)) inferInstance
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  set n := max n₁ n₂
  set P := Stacks.Ample.tensorPowModule Y L n
  have hS' : (insert (genericPoint Y) S).Finite := hS.insert _
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 P :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have := Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj (CartierDivisor.sheaf H) P
  have := Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj
    (MMP.CartierDivisor.sheaf (0 : Y.CartierDivisor)) P
  obtain ⟨s₁, hs₁⟩ := exists_forall_mem_nvOpen_of_isGeneratedByGlobalSections sY
    _ (hn₁ n (le_max_left _ _)) hS'
  obtain ⟨s₂, hs₂⟩ := exists_forall_mem_nvOpen_of_isGeneratedByGlobalSections sY
    _ (hn₂ n (le_max_right _ _)) hS'
  obtain ⟨A, hA, ⟨eA⟩, hAs⟩ := exists_isEffective_nonempty_sheaf_iso_of_mem_nvOpen _ s₁
    (hs₁ _ (Set.mem_insert _ _))
  obtain ⟨B, hB, ⟨eB⟩, hBs⟩ := exists_isEffective_nonempty_sheaf_iso_of_mem_nvOpen _ s₂
    (hs₂ _ (Set.mem_insert _ _))
  obtain ⟨C, ⟨eC⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf P
  have h₁ : MMP.Intersection.LinearlyEquivalent (H + C) A :=
    MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso
      ((MMP.CartierDivisorSheaf.sheafMulIso H C).symm ≪≫
        MMP.CartierDivisorSheaf.tensorIso (Iso.refl _) eC.symm ≪≫
        ((Stacks.SheafInternalHom.tensorLeftIso Y.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
          (CartierDivisor.sheaf H)).app P).symm ≪≫
        eA.symm)
  have h₂ : MMP.Intersection.LinearlyEquivalent (0 + C) B :=
    MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso
      ((MMP.CartierDivisorSheaf.sheafMulIso 0 C).symm ≪≫
        MMP.CartierDivisorSheaf.tensorIso (Iso.refl _) eC.symm ≪≫
        ((Stacks.SheafInternalHom.tensorLeftIso Y.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)
            (MMP.CartierDivisor.sheaf (0 : Y.CartierDivisor))).app P).symm ≪≫
        eB.symm)
  have h : MMP.Intersection.LinearlyEquivalent H (A - B) := by
    unfold MMP.Intersection.LinearlyEquivalent
    convert (MMP.Intersection.principalSubgroup Y).sub_mem h₁ h₂ using 1
    abel
  refine ⟨A, B, hA, hB, (MMP.CartierDivisor.nonempty_sheaf_iso_iff H (A - B)).2 h, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun x hx => hAs x (hs₁ x (Set.mem_insert_of_mem _ hx))
  · exact Set.disjoint_left.mpr fun x hx => hBs x (hs₂ x (Set.mem_insert_of_mem _ hx))

/-- **Pulling back a difference of effective divisors.** Let `f : X' ⟶ X` be a morphism of
integral schemes and `𝒪(H) ≅ 𝒪(A - B)` with `A`, `B` effective and the image of the generic
point of `X'` outside `Supp A ∪ Supp B`. Then `f^*𝒪(H) ≅ 𝒪(f^*A - f^*B)`, with `f^*A`, `f^*B`
effective and supported over `Supp A`, `Supp B`. -/
theorem exists_isEffective_nonempty_pullback_sheaf_iso_sub {X X' : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] (f : X' ⟶ X) {H A B : X.CartierDivisor}
    (hA : MMP.Intersection.IsEffective A) (hB : MMP.Intersection.IsEffective B)
    (he : Nonempty (CartierDivisor.sheaf H ≅ CartierDivisor.sheaf (A - B)))
    (hfA : f (genericPoint X') ∉ MMP.Intersection.cartierSupport A)
    (hfB : f (genericPoint X') ∉ MMP.Intersection.cartierSupport B) :
    ∃ (D₁ D₂ : X'.CartierDivisor), MMP.Intersection.IsEffective D₁ ∧
      MMP.Intersection.IsEffective D₂ ∧
      Nonempty
          ((Scheme.Modules.pullback f).obj (CartierDivisor.sheaf H)
              ≅ CartierDivisor.sheaf (D₁ - D₂)) ∧
      MMP.Intersection.cartierSupport D₁ ⊆ f ⁻¹' MMP.Intersection.cartierSupport A ∧
      MMP.Intersection.cartierSupport D₂ ⊆ f ⁻¹' MMP.Intersection.cartierSupport B := by
  obtain ⟨e⟩ := he
  have hA' := (MMP.CartierDivisor.genericPoint_notMem_cartierSupport_iff f A).1 hfA
  have hB' := (MMP.CartierDivisor.genericPoint_notMem_cartierSupport_iff f B).1 hfB
  set A' := MMP.CartierDivisor.pullback f A hA'
  set B' := MMP.CartierDivisor.pullback f B hB'
  have hHB : MMP.Intersection.LinearlyEquivalent (H + B) A := by
    have := MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso e
    unfold MMP.Intersection.LinearlyEquivalent at this ⊢
    convert this using 1
    abel
  obtain ⟨eHB⟩ := (MMP.CartierDivisor.nonempty_sheaf_iso_iff (H + B) A).2 hHB
  obtain ⟨G, ⟨eG⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
    ((Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf H))
  have h : MMP.Intersection.LinearlyEquivalent (G + B') A' :=
    MMP.CartierDivisor.linearlyEquivalent_of_sheaf_iso
      ((MMP.CartierDivisorSheaf.sheafMulIso G B').symm ≪≫
        MMP.CartierDivisorSheaf.tensorIso eG.symm (MMP.CartierDivisor.pullbackSheafIso f B hB') ≪≫
        (Stacks.Chow.pullbackTensorObjIso f (CartierDivisor.sheaf H)
          (CartierDivisor.sheaf B)).symm ≪≫
        (Scheme.Modules.pullback f).mapIso (MMP.CartierDivisorSheaf.sheafMulIso H B ≪≫ eHB) ≪≫
        (MMP.CartierDivisor.pullbackSheafIso f A hA').symm)
  have hGs : MMP.Intersection.LinearlyEquivalent G (A' - B') := by
    unfold MMP.Intersection.LinearlyEquivalent at h ⊢
    convert h using 1
    abel
  obtain ⟨eGs⟩ := (MMP.CartierDivisor.nonempty_sheaf_iso_iff G (A' - B')).2 hGs
  exact ⟨A', B', MMP.CartierDivisor.isEffective_pullback f hA hA',
    MMP.CartierDivisor.isEffective_pullback f hB hB', ⟨eG ≪≫ eGs⟩,
    MMP.CartierDivisor.cartierSupport_pullback_subset f A hA',
    MMP.CartierDivisor.cartierSupport_pullback_subset f B hB'⟩

end Moving

section Model

open scoped MMP.SubschemeOver
open MMP.Mori

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat
  MMP.CartierDivisor.isInvertible_sheaf

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

omit [IsComplexScheme Z] in
/-- The pull-back of a Cartier divisor of `Y` to a curve-image component `E` of a curve-and-point
exceptional model is a difference of effective Cartier divisors supported over closed points of
any open `U` meeting the curve `r(E)`. -/
theorem IsCurvePointExceptionalModel.exists_isEffective_iso_pullback_sheaf_sub
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) (E : F.support)
    (hE : topologicalKrullDim (r.base '' (E.1.support : Set Z)) = 1)
    (HY : Y.CartierDivisor) (U : Y.Opens)
    (hU : ((U : Set Y) ∩ r.base '' (E.1.support : Set Z)).Nonempty) :
    ∃ (D₁ D₂ : E.1.idealSheaf.subscheme.CartierDivisor) (h₁ : MMP.Intersection.IsEffective D₁)
      (h₂ : MMP.Intersection.IsEffective D₂),
      Nonempty ((Scheme.Modules.pullback (E.1.idealSheaf.subschemeι ≫ r)).obj
          (MMP.CartierDivisor.sheaf HY) ≅ MMP.CartierDivisor.sheaf (D₁ - D₂)) ∧
      ∀ x, (x ∈ (MMP.CartierDivisor.subscheme D₁ h₁).support ∨
          x ∈ (MMP.CartierDivisor.subscheme D₂ h₂).support) →
        (E.1.idealSheaf.subschemeι ≫ r).base x ∈ U ∧
          IsClosed {(E.1.idealSheaf.subschemeι ≫ r).base x} := by
  have := E.1.integral
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sY := hr.isProjectiveVariety
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := {}
  set f := E.1.idealSheaf.subschemeι ≫ r with hf
  set T := r.base '' (E.1.support : Set Z)
  have hrange : Set.range f.base = T := by
    rw [hf, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι]
  have hTc : IsClosed T := by
    have : IsProper r := isProper_of_isProjectiveMorphism r hr.isResolution.2.2.2.1
    exact r.isClosedMap _ E.1.idealSheaf.support.isClosed
  set η := f.base (genericPoint E.1.idealSheaf.subscheme) with hη
  have hgen : IsGenericPoint η T := by
    change closure {η} = T
    refine subset_antisymm (closure_minimal (Set.singleton_subset_iff.mpr
      (hrange ▸ Set.mem_range_self _)) hTc) ?_
    rw [← hrange, ← Set.image_univ, ← (genericPoint_spec E.1.idealSheaf.subscheme).def]
    exact (image_closure_subset_closure_image f.base.hom.continuous).trans (by simp [hη])
  have hηU : η ∈ (U : Set Y) := by
    obtain ⟨y, hyU, hyT⟩ := hU
    exact (specializes_iff_mem_closure.mpr (hgen.def ▸ hyT)).mem_open U.isOpen hyU
  have hS : (insert η (T \ (U : Set Y))).Finite :=
    (finite_diff_of_isGenericPoint hgen hE.le U.isOpen hηU).insert η
  obtain ⟨A, B, hA, hB, e, hAS, hBS⟩ :=
    exists_isEffective_nonempty_sheaf_iso_sub_disjoint hr.isProjectiveVariety HY hS
  obtain ⟨D₁, D₂, h₁, h₂, e', hD₁, hD₂⟩ :=
    exists_isEffective_nonempty_pullback_sheaf_iso_sub f hA hB e
      (Set.disjoint_left.mp hAS (Set.mem_insert _ _))
      (Set.disjoint_left.mp hBS (Set.mem_insert _ _))
  have key : ∀ x, f.base x ∉ insert η (T \ (U : Set Y)) →
      f.base x ∈ U ∧ IsClosed {f.base x} := by
    intro x hx
    have hxT : f.base x ∈ T := hrange ▸ Set.mem_range_self x
    refine ⟨by_contra fun h => hx (Set.mem_insert_of_mem _ ⟨hxT, h⟩), ?_⟩
    exact isClosed_singleton_of_isGenericPoint_of_ne hgen hE.le hxT
      fun h => hx (h ▸ Set.mem_insert _ _)
  refine ⟨D₁, D₂, h₁, h₂, e', fun x hx => key x ?_⟩
  rcases hx with hx | hx
  · have hx' : x ∈ MMP.Intersection.cartierSupport D₁ := by
      rw [← MMP.CartierDivisor.coe_support_subscheme h₁]
      exact hx
    exact fun h => Set.disjoint_left.mp hAS h (hD₁ hx')
  · have hx' : x ∈ MMP.Intersection.cartierSupport D₂ := by
      rw [← MMP.CartierDivisor.coe_support_subscheme h₂]
      exact hx
    exact fun h => Set.disjoint_left.mp hBS h (hD₂ hx')

end Model

end MMP.Fourfold
