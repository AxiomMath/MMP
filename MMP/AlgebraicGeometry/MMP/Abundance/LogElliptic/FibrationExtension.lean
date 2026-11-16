module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.ChowClosure
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.ContractedDivisorConnected
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# The elliptic fibration extends to all of `X`

Let `(X, Δ_X)` satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`),
with `f_U : U ⟶ Z` a log elliptic fiber space on a nonempty open `U ⊆ X` as in (15.4.3), and
suppose that no prime divisor of `X` is `(K_X + Δ_X)`-trivially connected
(`MMP.Flips.IsTriviallyConnected`). Then, after shrinking `Z` to a nonempty open `Z₀`, the
fibration `f_U` extends to a morphism `f : X ⟶ Z̄` onto a normal projective surface `Z̄`
containing `Z₀` as an open subset, with `f_* 𝒪_X = 𝒪_{Z̄}` and all fibres connected of pure
dimension one.

## Main results

* `MMP.Flips.exists_extension_of_forall_not_isTriviallyConnected`: the extension `f : X ⟶ Z̄`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field `k` of
characteristic zero, as for `MMP.Flips.not_dense_image_of_isTriviallyConnected`. A prime divisor
`D` of `X` is the divisor `1 · D` (`Finsupp.single D 1`). The inclusion `Z₀ ⊆ Z̄` is an open
immersion `j : Z₀ ⟶ Z̄` over `k`, and `f = f_U` on `f_U⁻¹(Z₀)` is the equality of the two
morphisms `f_U⁻¹(Z₀) ⟶ Z̄`. `f` being a proper morphism of varieties over `k` with
`f_* 𝒪_X = 𝒪_{Z̄}` is `MMP.Flips.IsContraction`; a surface is a variety of dimension two. The
fibres are the subspaces `f⁻¹(z)` for all points `z ∈ Z̄`, and pure dimension one means every
irreducible component has dimension one.

The proof follows the source. Let `(Z₀, Z̄, Ū)` be a Chow closure of `f_U`, with projections
`g : Ū ⟶ Z̄` and `u : Ū ⟶ X`. A prime divisor `F` in the exceptional set of `u` has `u(F)`
inside the complement of the biregular locus of `u`, of codimension at least two, so
`dim u(F) ≤ 1` and `F` would give a trivially connected prime divisor of `X`; hence `u` is an
isomorphism and `f = g ∘ u⁻¹`. Over an affine open of `Z₀`, `f` is `f_U`, so the finite part of
its Stein factorization is birational onto the normal `Z̄`, hence an isomorphism, and
`f_* 𝒪_X = 𝒪_{Z̄}`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Thm. 15.10
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

universe u

namespace MMP.Flips

open MMP.Mori

/-- A nonempty closed subset of pure codimension one of a locally Noetherian scheme contains a
point of coheight one. -/
private theorem exists_mem_coheight_eq_one_of_isPureCodimOne {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {S : Closeds Y} (hS : IsPureCodimOne S) (hne : (S : Set Y).Nonempty) :
    ∃ x ∈ (S : Set Y), Order.coheight x = 1 := by
  obtain ⟨x, hxS, hmin⟩ :=
    (InvImage.wf (Order.coheight : Y → ℕ∞) wellFounded_lt).has_min (S : Set Y) hne
  refine ⟨x, hxS, ?_⟩
  have hfin : ∀ y : Y, Order.coheight y < ⊤ := fun y => by
    have h := ringKrullDim_lt_top (R := Y.presheaf.stalk y)
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_lt_coe.mp h
  let e := irreducibleSetEquivPoints (α := Y)
  have hW : ∀ y : Y, e.symm y = IrreducibleCloseds.closureSingleton y := fun _ => rfl
  rw [← codimension_closureSingleton, ← hW]
  refine hS _ ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {x} ⊆ (S : Set Y)
    exact S.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxS)
  · have h1 : x ≤ e W' := by simpa using e.monotone hle
    have hx' : e W' ∈ (S : Set Y) := by
      refine hW' ?_
      have : e W' ∈ (IrreducibleCloseds.closureSingleton (e W') : Set Y) := subset_closure rfl
      rwa [← hW, e.symm_apply_apply] at this
    by_contra hn
    have hn' : ¬ e W' ≤ x := fun h => hn (by simpa using e.symm.monotone h)
    exact hmin _ hx' (Order.coheight_strictAnti (lt_of_le_not_ge h1 hn') (hfin _))

/-- In `WithBot ℕ∞`, `a + c = 3` with `2 ≤ c` forces `a ≤ 1`. -/
private theorem le_one_of_add_eq_three {a : WithBot ℕ∞} {c : ℕ∞} (h : a + c = 3) (hc : 2 ≤ c) :
    a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe n =>
    have h' : n + c = 3 := WithBot.coe_injective (by rwa [WithBot.coe_add])
    have h2 : n + 2 ≤ 3 := h' ▸ add_le_add le_rfl hc
    induction n using ENat.recTopCoe with
    | top => simp at h2
    | coe m =>
      have : m + 2 ≤ 3 := by exact_mod_cast h2
      exact_mod_cast (show m ≤ 1 by omega)

/-- A homeomorphism carries a subset all of whose irreducible components have dimension `n` to
one with the same property. -/
private theorem forall_mem_irreducibleComponents_image {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) {A : Set α} {n : WithBot ℕ∞}
    (hA : ∀ Y ∈ irreducibleComponents A, topologicalKrullDim Y = n) :
    ∀ Y ∈ irreducibleComponents (e '' A), topologicalKrullDim Y = n := by
  intro Y hY
  let h := e.image A
  have hY' : h ⁻¹' Y ∈ irreducibleComponents A :=
    preimage_mem_irreducibleComponents hY h.isOpenEmbedding
      (by simpa [h.range_coe] using hY.1.nonempty)
  rw [← hA _ hY', ← h.image_symm]
  exact IsHomeomorph.topologicalKrullDim_eq _ (h.symm.image Y).isHomeomorph

/-- A morphism from a reduced scheme whose image lies in the support of an ideal sheaf `I`
kills `I`. -/
private theorem le_ker_of_range_subset {Y T : Scheme.{u}} [IsReduced Y] (φ : Y ⟶ T)
    (I : T.IdealSheafData) (h : Set.range φ ⊆ I.support) : I ≤ φ.ker := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
  intro x hx
  refine closure_minimal ?_ I.support.isClosed hx
  rintro _ ⟨y, -, rfl⟩
  exact h ⟨y, rfl⟩

/-- **The Chow family is an isomorphism** (FA, proof of 15.10). If no prime divisor of `X` is
`(K_X + Δ_X)`-trivially connected, the projection `u : Ū ⟶ X` of a Chow closure is an
isomorphism. -/
private theorem isIso_snd_of_isChowClosure {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX] {U : X.Opens}
    {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
    {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}
    (hC : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    (hD : ∀ D : Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1)) :
    IsIso (Ubar.subschemeι ≫ pullback.snd sZbar sX) := by
  have := hC.isIntegral
  obtain ⟨hproj, hbir, hsurj, -, -, -⟩ := hC.isProjectiveMorphism_snd
  set u := Ubar.subschemeι ≫ pullback.snd sZbar sX
  have hA := hC.satisfiesAbundanceAssumptions
  have hXv : AlgebraicGeometry.IsVariety k sX :=
    ((Mori.isProjectiveVariety_iff k sX).mp hA.isProjectiveVariety).1
  have : IsProper u := isProper_of_isProjectiveMorphism u hproj
  have hUv : AlgebraicGeometry.IsVariety k (u ≫ sX) := ⟨⟩
  have : IsLocallyNoetherian Ubar.subscheme := LocallyOfFiniteType.isLocallyNoetherian (u ≫ sX)
  have hEx : ∀ y, y ∉ (Mori.exceptionalSet u : Set Ubar.subscheme) := by
    intro y hy
    obtain ⟨x, hxEx, hx1⟩ := exists_mem_coheight_eq_one_of_isPureCodimOne
      (isPureCodimOne_exceptionalSet_of_isQFactorial sX (u ≫ sX) hA.isQFactorial hUv u rfl hproj
        hbir) ⟨y, hy⟩
    let F : Mori.PrimeDivisor Ubar.subscheme := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
    have himg : u.base '' F.support = closure {u x} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
        ← u.isClosedMap.closure_image_eq_of_continuous u.continuous, Set.image_singleton]
    have hco : 2 ≤ Order.coheight (u x) := le_closedsCodimension_iff_le_coheight.mp
      (two_le_closedsCodimension_compl_biregularLocus sX u hbir) (u x) hxEx
    exact (hC.exists_isTriviallyConnected_of_dim_image_le_one F (by
      rw [himg]
      exact le_one_of_add_eq_three
        ((topologicalKrullDim_closure_singleton_add_coheight sX (u x)).trans hA.dim_eq) hco)).elim
      hD
  have htop : biregularLocus u = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, rfl⟩ := u.surjective x
    exact of_not_not (hEx y)
  exact (isBiregular_top_iff u).mp (htop ▸ isBiregular_biregularLocus u)

/-- **The graph of `f_U` lies in the Chow closure.** Over `Z₀`, the graph
`f_U⁻¹(Z₀) ⟶ Z̄ ×ₖ X` of `f_U` factors through `Ū`, compatibly with both projections. -/
private theorem exists_lift_chowGraph {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX] {U : X.Opens}
    {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
    {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}
    (hC : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    ∃ Γ' : (fU ⁻¹ᵁ Z₀).toScheme ⟶ Ubar.subscheme,
      Γ' ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX = (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ∧
      Γ' ≫ Ubar.subschemeι ≫ pullback.fst sZbar sX = (fU ∣_ Z₀) ≫ j := by
  set Γ := chowGraph hC.isLogEllipticFiberSpace.isContraction.comp_eq hC.comp_eq
  have hΓ : Γ.ker ≥ Ubar := by
    refine le_ker_of_range_subset Γ Ubar ?_
    rw [← hC.image_preimage_eq, ← Scheme.IdealSheafData.range_subschemeι]
    exact Set.image_subset_range _ _
  refine ⟨IsClosedImmersion.lift Ubar.subschemeι Γ
    (by rwa [Scheme.IdealSheafData.ker_subschemeι]), ?_, ?_⟩ <;>
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  exacts [pullback.lift_snd _ _ _, pullback.lift_fst _ _ _]

/-- **Zariski's main theorem in the form `f_* 𝒪_X = 𝒪_Y`.** A proper morphism `f : X ⟶ Y` from a
normal variety to a normal variety which is an isomorphism on sections over one affine open `V`
with nonempty preimage is an isomorphism on sections over every open. -/
private theorem isIso_app_of_isIso_app_isAffineOpen {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hY : AlgebraicGeometry.IsVariety k sY) [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) {V : Y.Opens} (hV : IsAffineOpen V)
    (hne : ((f ⁻¹ᵁ V : X.Opens) : Set X).Nonempty) (hfV : IsIso (f.app V)) (T : Y.Opens) :
    IsIso (f.app T) := by
  obtain ⟨W, h, κ, ⟨hS⟩, -, -, hiso, -, hfin, hWn⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety sX sY hX hY f hf
  have hcomp : h ≫ κ = f := hS.comp
  have : IsIntegral W := hWn.1.toIsIntegral
  have hκV : IsIso (κ.app V) := by
    have hκ : IsIso ((h ≫ κ).app V) := by rwa [hcomp]
    rw [Scheme.Hom.comp_app] at hκ
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hiso (κ ⁻¹ᵁ V)) hκ
  have : IsIso (κ ∣_ V) := (isIso_morphismRestrict_iff_isIso_app κ hV).mpr hκV
  obtain ⟨x, hx⟩ := hne
  have hx' : κ (h x) ∈ V := by rwa [← Scheme.Hom.comp_apply, hcomp]
  have hb := isBirationalMorphism_of_isIso_resLE κ (κ ⁻¹ᵁ V) V ⟨h x, hx'⟩ ⟨_, hx'⟩ le_rfl
    (by rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance)
  have : IsIso κ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso κ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).2 hfin
  rw [← hcomp, Scheme.Hom.comp_app]
  exact IsIso.comp_isIso' inferInstance (hiso (κ ⁻¹ᵁ T))

/-- Through the isomorphism `u : Ū ⟶ X`, the morphism `g ∘ u⁻¹ : X ⟶ Z̄` restricts to `f_U` on
`f_U⁻¹(Z₀)`. -/
private theorem comp_inv_snd_comp_fst_eq_of_isChowClosure
    {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX] {U : X.Opens}
    {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
    {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}
    (hC : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    [IsIso (Ubar.subschemeι ≫ pullback.snd sZbar sX)] :
    (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ≫ inv (Ubar.subschemeι ≫ pullback.snd sZbar sX) ≫ Ubar.subschemeι ≫
      pullback.fst sZbar sX = (fU ∣_ Z₀) ≫ j := by
  obtain ⟨Γ', h1, h2⟩ := exists_lift_chowGraph hC
  rw [← Category.assoc, ← h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]

/-- When the projection `u : Ū ⟶ X` of a Chow closure is an isomorphism, `g ∘ u⁻¹ : X ⟶ Z̄` is a
contraction. -/
private theorem isContraction_inv_snd_comp_fst_of_isChowClosure
    {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX] {U : X.Opens}
    {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
    {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
    {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}
    (hC : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar)
    [IsIso (Ubar.subschemeι ≫ pullback.snd sZbar sX)] :
    IsContraction k sZbar sX
      (inv (Ubar.subschemeι ≫ pullback.snd sZbar sX) ≫ Ubar.subschemeι ≫
        pullback.fst sZbar sX) := by
  have hgraph := comp_inv_snd_comp_fst_eq_of_isChowClosure hC
  have := hC.isIntegral
  have := hC.isOpenImmersion
  obtain ⟨-, -, -, -, hrange, -⟩ := hC.isProjectiveMorphism_snd
  set ι := Ubar.subschemeι
  set g := ι ≫ pullback.fst sZbar sX with hg
  set u := ι ≫ pullback.snd sZbar sX with hu
  set f := inv u ≫ g with hf
  have hgu : u ≫ f = g := by simp [hf]
  have hgu' (y : Ubar.subscheme) : f (u y) = g y := by rw [← Scheme.Hom.comp_apply, hgu]
  obtain ⟨hXv, hXp⟩ :=
    (Mori.isProjectiveVariety_iff k sX).mp hC.satisfiesAbundanceAssumptions.isProjectiveVariety
  have : IsProper sX := isProper_of_isProjectiveMorphism _ hXp
  have hZv : AlgebraicGeometry.IsVariety k sZbar := hC.isNormalVariety.1
  have : IsNormal Zbar := hC.isNormalVariety.2
  have hfs : f ≫ sZbar = sX := by
    rw [hf, Category.assoc, hg, Category.assoc, pullback.condition, ← Category.assoc ι, ← hu,
      IsIso.inv_hom_id_assoc]
  have : IsProper (f ≫ sZbar) := hfs ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZbar
  obtain ⟨z₀, hz₀⟩ := hC.nonempty
  obtain ⟨V, hVa, hzV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Zbar.isBasis_affineOpens)
      (show j ⟨z₀, hz₀⟩ ∈ j.opensRange from ⟨_, rfl⟩)
  have hψ : f ⁻¹ᵁ V ≤ ((fU ⁻¹ᵁ Z₀).ι ≫ U.ι).opensRange := by
    intro x hx
    obtain ⟨y, rfl⟩ := (Scheme.homeoOfIso (asIso u)).surjective x
    have hy : y ∈ g ⁻¹ᵁ j.opensRange := (hgu' y ▸ hVle hx : g y ∈ j.opensRange)
    have hmem : u y ∈ Set.range ((g ⁻¹ᵁ j.opensRange).ι ≫ u).base := ⟨⟨y, hy⟩, rfl⟩
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    rwa [hrange] at hmem
  have hφ (T : Z₀.toScheme.Opens) : IsIso ((fU ∣_ Z₀).app T) := by
    rw [morphismRestrict_app]
    exact IsIso.comp_isIso' (hC.isLogEllipticFiberSpace.isContraction.isIso_app (Z₀.ι ''ᵁ T))
      (by rw [eqToHom_op, eqToHom_map]; exact instIsIsoEqToHom _)
  have hfV : IsIso (f.app V) := by
    have hL : IsIso ((((fU ⁻¹ᵁ Z₀).ι ≫ U.ι) ≫ f).app V) := by
      rw [Category.assoc, hgraph, Scheme.Hom.comp_app]
      exact IsIso.comp_isIso' (Scheme.Hom.isIso_app j V hVle) (hφ (j ⁻¹ᵁ V))
    rw [Scheme.Hom.comp_app] at hL
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (Scheme.Hom.isIso_app ((fU ⁻¹ᵁ Z₀).ι ≫ U.ι) _ hψ) hL
  have hne : ((f ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := (hC.isConnected_fiber (j ⟨z₀, hz₀⟩)).nonempty
    exact ⟨u y, show f (u y) ∈ V by rw [hgu', (hy : g y = _)]; exact hzV⟩
  exact ⟨hZv, hXv, hfs, inferInstance,
    isIso_app_of_isIso_app_isAffineOpen ⟨hXv, inferInstance⟩ hZv f hfs hVa hne hfV⟩

/-- **The elliptic fibration extends** (FA Thm. 15.10). Let `(X, Δ_X)`, with `K_X` a canonical
divisor, satisfy the assumptions of 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over an
algebraically closed field `k` of characteristic zero, let `f_U : U ⟶ Z` be a log elliptic fiber
space on a nonempty open `U ⊆ X` as in (15.4.3), and suppose no prime divisor of `X` is
`(K_X + Δ_X)`-trivially connected (`MMP.Flips.IsTriviallyConnected`). Then there are a normal
projective surface `Z̄` over `k`, a nonempty open `Z₀ ⊆ Z` with an open immersion `j : Z₀ ⟶ Z̄`
over `k`, and a morphism `f : X ⟶ Z̄` over `k` with `f_* 𝒪_X = 𝒪_{Z̄}`
(`MMP.Flips.IsContraction`), all of whose fibres are connected of pure dimension one, such that
`f = f_U` on `f_U⁻¹(Z₀)`. -/
@[mmp "thm_fa15_elliptic_fibration_extends"]
public theorem exists_extension_of_forall_not_isTriviallyConnected
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU)
    (hD : ∀ D : Mori.PrimeDivisor X, ¬ IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (Zbar : Scheme.{u}) (sZbar : Zbar ⟶ Spec (.of k)) (Z₀ : Z.Opens)
      (j : Z₀.toScheme ⟶ Zbar) (f : X ⟶ Zbar),
      IsNormalVariety k sZbar ∧ Mori.IsProjectiveVariety k sZbar ∧
      topologicalKrullDim Zbar = 2 ∧
      (Z₀ : Set Z).Nonempty ∧ IsOpenImmersion j ∧ j ≫ sZbar = Z₀.ι ≫ sZ ∧
      IsContraction k sZbar sX f ∧
      (∀ z : Zbar, _root_.IsConnected (f.base ⁻¹' {z})) ∧
      (∀ z : Zbar, ∀ Y ∈ irreducibleComponents (f.base ⁻¹' {z}), topologicalKrullDim Y = 1) ∧
      (fU ⁻¹ᵁ Z₀).ι ≫ U.ι ≫ f = (fU ∣_ Z₀) ≫ j := by
  obtain ⟨⟨Z₀, Zbar, sZbar, j, Ubar, hC⟩, hdim⟩ :=
    exists_isChowClosure_and_dim_eq_two sX h U hU sZ fU hfU
  have : IsIso (Ubar.subschemeι ≫ pullback.snd sZbar sX) := isIso_snd_of_isChowClosure hC hD
  have hcon := isContraction_inv_snd_comp_fst_of_isChowClosure hC
  have hgraph := comp_inv_snd_comp_fst_eq_of_isChowClosure hC
  set ι := Ubar.subschemeι
  set g := ι ≫ pullback.fst sZbar sX
  set u := ι ≫ pullback.snd sZbar sX
  set f := inv u ≫ g with hf
  have hgu : u ≫ f = g := by simp [hf]
  have hgu' (y : Ubar.subscheme) : f (u y) = g y := by rw [← Scheme.Hom.comp_apply, hgu]
  let e : Ubar.subscheme ≃ₜ X := Scheme.homeoOfIso (asIso u)
  have hfib (z : Zbar) : f.base ⁻¹' {z} = e '' (g.base ⁻¹' {z}) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, e.injective.mem_set_image]
    change f (u y) = z ↔ g y = z
    rw [hgu']
  refine ⟨Zbar, sZbar, Z₀, j, f, hC.isNormalVariety, hC.isProjectiveVariety, hdim _ _ _ _ _ hC,
    hC.nonempty, hC.isOpenImmersion, hC.comp_eq, hcon, fun z => ?_, fun z => ?_, hgraph⟩
  · rw [hfib z]
    exact (hC.isConnected_fiber z).image _ e.continuous.continuousOn
  · rw [hfib z]
    exact forall_mem_irreducibleComponents_image e (hC.dim_fiber z)

end MMP.Flips
