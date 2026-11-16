module
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.Blowup.HypersurfaceTransform
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.OnePlusBInvariance
public import MMP.AlgebraicGeometry.Resolution.TransformRestriction
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Dimension.ResidueTrdeg
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus

/-!
# Maximal contact along blow-up sequences, and maximal coefficient ideals

Results from Kollár's *Lectures on resolution of singularities*, 3.62–3.101, on hypersurfaces
of maximal contact along smooth blow-up sequences and on maximal coefficient ideals.

## Étale equivalent blow-up sequences: the centres agree

Let `X` be a separated, smooth, equidimensional scheme of finite type over a field `k` of
characteristic `0`, every irreducible component of positive dimension, `I` an ideal sheaf
nonzero at the generic points with `m = maxord I ≥ 1`, and `𝐁 = (X_i, Z_i)`, `𝐁' = (X'_i, Z'_i)`
smooth blow-up sequences of order `m` starting with `(X, I)`, étale equivalent through
`ψ, ψ' : U → X` (`MMP.Resolution.IsEtaleChartPair` and `ψ^*𝐁 = ψ'^*𝐁'`). Write `U_i` for the
`i`-th scheme of the common pull-back, `ψ_i, ψ'_i : U_i → X_i` for the lifts of `ψ, ψ'`, and
`M_i = (Π^U_i)⁻¹_*(D^{m-1}(ψ^*I), 1)` for the iterated birational transform of the maximal
contact ideal of `ψ^*I` with marking `1`. If the first `i` centres agree, so that `X_i = X'_i`,
and `(ψ_i, ψ'_i)^*I_Δ ⊆ M_i`, `I_Δ` the ideal of the diagonal of `X_i ×_k X_i`, then also
`Z_i = Z'_i`.

The common first `i` steps are a blow-up sequence `C` with `𝐁.truncate i = C = 𝐁'.truncate i`;
then `X_i = C.target`, `ψ_i = C.pullbackHom ψ` and `ψ'_i = C.pullbackHom ψ'`. The two pull-backs
`C.pullback ψ` and `C.pullback ψ'` are equal (both are the first `i` steps of `ψ^*𝐁 = ψ'^*𝐁'`),
and `ψ'_i` is read on `U_i = (C.pullback ψ).target` through that equality. The hypothesis on
the diagonal is stated for every such equality and every proof that `ψ_i, ψ'_i` agree over `k`;
both are propositions that hold, so this is the source's hypothesis. The conclusion
`𝐁.truncate (i + 1) = 𝐁'.truncate (i + 1)` is `Z_i = Z'_i` given the agreement of the earlier
centres.

## Main results

* `MMP.Resolution.ClosedBlowupSequence.truncate_succ_eq_of_isEtaleChartPair`: under these
  hypotheses the first `i + 1` steps of `𝐁` and `𝐁'` agree.
* `MMP.Resolution.ClosedBlowupSequence.IsOrderGePlainSeq.ker_restrictHom_le_of_le_higherDerivativeIdeal`
* `MMP.Resolution.isHypersurfaceOfMaximalContact_of_le_maximalContactIdeal`
* `MMP.Resolution.formalUniqueness_of_le_maximalContactIdeal`
* `MMP.Resolution.ClosedBlowupSequence.higherLogDerivativeIdeal_derivedTransformJ_le`
* `MMP.Resolution.ClosedBlowupSequence.IsOrderGePlainSeq.restrict`
* `MMP.Resolution.multAt_maximalCoefficientIdeal`: `ord_x W_s(I) = s` if `ord_x I = m`, and
  `ord_x W_s(I) = 0` if `ord_x I < m`.
* `MMP.Resolution.Kollar.derivativeIdeal_maximalCoefficientIdeal_succ`
* `MMP.Resolution.Kollar.isDBalanced_maximalCoefficientIdeal`

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution
open ClosedBlowupSequence

variable {k : Type u} [Field k]

namespace Proof_lem_kr3d_etale_equivalent_sequences_centers_agree

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Append one blow-up, along `Z ⊆ X_r`, to a blow-up sequence. -/
private noncomputable def snoc : {X : Scheme.{u}} → (C : ClosedBlowupSequence X) →
    C.target.IdealSheafData → ClosedBlowupSequence X
  | _, .nil _, Z => .cons Z (.nil _)
  | _, .cons Z' C, Z => .cons Z' (snoc C Z)

private theorem snoc_injective {X : Scheme.{u}} (C : ClosedBlowupSequence X)
    {Z Z' : C.target.IdealSheafData} (h : snoc C Z = snoc C Z') : Z = Z' := by
  induction C with
  | nil X => exact (cons_eq_cons_iff.1 h).1
  | cons Z₀ C ih => exact ih (eq_of_heq (cons_eq_cons_iff.1 h).2)

private theorem exists_truncate_succ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (i : ℕ)
    (hi : i < B.length) : ∃ Z, B.truncate (i + 1) = snoc (B.truncate i) Z := by
  induction B generalizing i with
  | nil X => exact absurd hi (Nat.not_lt_zero _)
  | cons Z B ih =>
    cases i with
    | zero =>
      refine ⟨Z, ?_⟩
      change cons Z (B.truncate 0) = cons Z (.nil _)
      rw [Kollar.truncate_zero]
    | succ i =>
      obtain ⟨W, hW⟩ := ih i (Nat.lt_of_succ_lt_succ hi)
      exact ⟨W, by change cons Z (B.truncate (i + 1)) = cons Z (snoc (B.truncate i) W); rw [hW]⟩

private theorem pullback_snoc {X Y : Scheme.{u}} (C : ClosedBlowupSequence X)
    (Z : C.target.IdealSheafData) (h : Y ⟶ X) :
    (snoc C Z).pullback h = snoc (C.pullback h) (Z.comap (C.pullbackHom h)) := by
  induction C generalizing Y with
  | nil X => rfl
  | cons Z₀ C ih =>
    exact congrArg (cons _) (ih Z _)

private theorem length_pullback {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) :
    (B.pullback h).length = B.length := by
  induction B generalizing Y with
  | nil X => rfl
  | cons Z B ih => exact congrArg (· + 1) (ih _)

private theorem isOrderMPlainSeq_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ) (hB : B.IsOrderMPlainSeq s I m)
    (j : ℕ) : (B.truncate j).IsOrderMPlainSeq s I m := by
  induction B generalizing j with
  | nil X => exact hB
  | cons Z B ih =>
    cases j with
    | zero => exact ⟨hB.1, hB.2.1⟩
    | succ j => exact ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2.1, ih _ _ hB.2.2.2.2.2 j⟩

private theorem isSmoothScheme_of_isOrderMPlainSeq_snoc {X : Scheme.{u}}
    (C : ClosedBlowupSequence X) (Z : C.target.IdealSheafData) (s : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (m : ℕ) (h : (snoc C Z).IsOrderMPlainSeq s I m) :
    MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ C.toBase ≫ s) := by
  induction C with
  | nil X =>
    have e : (nil X).toBase ≫ s = s := Category.id_comp s
    have := h.2.2.1
    rwa [← e] at this
  | cons Z₀ C ih =>
    have e : (cons Z₀ C).toBase ≫ s = C.toBase ≫ blowUpToBase Z₀ ≫ s := Category.assoc _ _ _
    rw [e]
    exact ih _ _ _ h.2.2.2.2.2

private theorem isOrderGePlainSeq_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (hB : B.IsOrderGePlainSeq s a)
    (j : ℕ) : (B.truncate j).IsOrderGePlainSeq s a := by
  induction B generalizing j with
  | nil X => exact hB
  | cons Z B ih =>
    cases j with
    | zero => exact ⟨hB.1, hB.2.1⟩
    | succ j => exact ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2.1, ih _ _ hB.2.2.2.2.2 j⟩

private theorem isOrderGePlainSeq_snoc {X : Scheme.{u}}
    (C : ClosedBlowupSequence X) (Z : C.target.IdealSheafData) (s : X ⟶ Spec (.of k))
    (a : MarkedIdeal X) (h : (snoc C Z).IsOrderGePlainSeq s a) :
    MMP.Mori.IsSmoothScheme (C.toBase ≫ s) ∧ MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ C.toBase ≫ s) ∧
      OrderAlongGE (C.markedTransform a).I (Z.support : Set C.target) a.m := by
  induction C with
  | nil X =>
    have e : (nil X).toBase ≫ s = s := Category.id_comp s
    rw [e]
    exact ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩
  | cons Z₀ C ih =>
    have e : (cons Z₀ C).toBase ≫ s = C.toBase ≫ blowUpToBase Z₀ ≫ s := Category.assoc _ _ _
    rw [e]
    exact ih _ _ _ h.2.2.2.2.2

/-- An ideal sheaf of order `≥ 1` along a smooth closed subscheme of a smooth scheme vanishes on
it. -/
private theorem support_subset_of_orderAlongGE_one {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    (hY : MMP.Mori.IsSmoothScheme s) (Z : Y.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (J : Y.IdealSheafData)
    (hJ : OrderAlongGE J (Z.support : Set Y) 1) :
    (Z.support : Set Y) ⊆ J.support := by
  intro x hx
  have h1 := stalk_le_pow_of_orderAlongGE s hY Z hZ J 1 hJ x
  rw [pow_one] at h1
  by_contra hxJ
  have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support J x).2 hxJ
  exact (IdealSheafData.stalk_eq_top_iff_notMem_support Z x).1 (top_le_iff.1 (htop ▸ h1)) hx

/-- If `(a, b)^* I_Δ ⊆ J` for the diagonal of a separated `s`, then `a` and `b` agree at every
point of `V(J)`. -/
private theorem apply_eq_of_comap_diagonal_le {S T Y : Scheme.{u}} (s : Y ⟶ S) [IsSeparated s]
    (a b : T ⟶ Y) (hk : a ≫ s = b ≫ s) (J : T.IdealSheafData)
    (hJ : (Limits.pullback.diagonal s).ker.comap (Limits.pullback.lift a b hk) ≤ J)
    {x : T} (hx : x ∈ (J.support : Set T)) : a x = b x := by
  have h1 := Scheme.IdealSheafData.support_antitone hJ hx
  rw [Scheme.IdealSheafData.support_comap] at h1
  change Limits.pullback.lift a b hk x ∈ ((Limits.pullback.diagonal s).ker.support : Set _) at h1
  rw [Scheme.Hom.support_ker,
    (Limits.pullback.diagonal s).isClosedEmbedding.isClosed_range.closure_eq] at h1
  obtain ⟨y, hy⟩ := h1
  have ha : a x = y := by
    rw [← Limits.pullback.lift_fst a b hk, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply,
      Limits.pullback.diagonal_fst]
    simp
  have hb : b x = y := by
    rw [← Limits.pullback.lift_snd a b hk, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply,
      Limits.pullback.diagonal_snd]
    simp
  rw [ha, hb]

/-- If `f^* Z = g^* Z'`, `f` and `g` agree on `V(f^* Z)`, and `V(Z)` lies in the image of `f`,
then `V(Z) ⊆ V(Z')`. -/
private theorem support_subset_of_comap_eq {T Y : Scheme.{u}} {f g : T ⟶ Y}
    {Z Z' : Y.IdealSheafData} (h : Z.comap f = Z'.comap g)
    (hfg : ∀ x ∈ ((Z.comap f).support : Set T), f x = g x)
    (hZ : (Z.support : Set Y) ⊆ Set.range f) : (Z.support : Set Y) ⊆ Z'.support := by
  intro _ hx
  obtain ⟨y, rfl⟩ := hZ hx
  have hy : y ∈ ((Z.comap f).support : Set T) := by
    rwa [Scheme.IdealSheafData.support_comap]
  rw [hfg y hy]
  rwa [h, Scheme.IdealSheafData.support_comap] at hy

/-- Smooth closed subschemes over a field are reduced, so they are determined by their
supports. -/
private theorem eq_of_support_eq {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    {Z Z' : Y.IdealSheafData} (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s))
    (hZ' : MMP.Mori.IsSmoothScheme (Z'.subschemeι ≫ s)) (h : Z.support = Z'.support) :
    Z = Z' := by
  have key : ∀ W : Y.IdealSheafData, MMP.Mori.IsSmoothScheme (W.subschemeι ≫ s) →
      W = Scheme.IdealSheafData.vanishingIdeal W.support := fun W hW => by
    have : Smooth (W.subschemeι ≫ s) := (MMP.Mori.isSmoothScheme_iff _).1 hW
    have : IsReduced W.subscheme := isReduced_of_smooth (W.subschemeι ≫ s)
    exact W.eq_vanishingIdeal_of_isReduced_subscheme _ rfl
  rw [key Z hZ, key Z' hZ', h]

private theorem locallyOfFiniteType_toBase {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (B : ClosedBlowupSequence X) :
    LocallyOfFiniteType (B.toBase ≫ s) := by
  induction B with
  | nil X =>
    change LocallyOfFiniteType (𝟙 X ≫ s)
    rw [Category.id_comp]
    infer_instance
  | cons Z B ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    have : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    have := ih (blowUpToBase Z ≫ s)
    change LocallyOfFiniteType ((B.toBase ≫ blowUpToBase Z) ≫ s)
    rwa [Category.assoc]

private theorem isSeparated_toBase {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsSeparated s]
    [LocallyOfFiniteType s] (B : ClosedBlowupSequence X) : IsSeparated (B.toBase ≫ s) := by
  induction B with
  | nil X =>
    change IsSeparated (𝟙 X ≫ s)
    rw [Category.id_comp]
    infer_instance
  | cons Z B ih =>
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    have : IsProper (blowUpToBase Z) := AlgebraicGeometry.isProper_blowUpToBase (I := Z)
    have := ih (blowUpToBase Z ≫ s)
    change IsSeparated ((B.toBase ≫ blowUpToBase Z) ≫ s)
    rwa [Category.assoc]

private theorem eqToHom_target_comp_toBase {X : Scheme.{u}} {D D' : ClosedBlowupSequence X}
    (h : D = D') : eqToHom (congrArg target h) ≫ D'.toBase = D.toBase := by
  subst h
  simp

private theorem eq_comap_of_snoc_eq {X : Scheme.{u}} {D D' : ClosedBlowupSequence X}
    (h : D = D') {W : D.target.IdealSheafData} {W' : D'.target.IdealSheafData}
    (e : snoc D W = snoc D' W') : W = W'.comap (eqToHom (congrArg target h)) := by
  subst h
  rw [eqToHom_refl, snoc_injective _ e]
  exact (Scheme.IdealSheafData.comap_id _).symm

private theorem range_eqToHom_comp {Y₁ Y₂ T : Scheme.{u}} (h : Y₁ = Y₂) (f : Y₂ ⟶ T) :
    Set.range (eqToHom h ≫ f) = Set.range f := by
  subst h
  simp

private theorem centersLieOver_truncate {X X₀ : Scheme.{u}} (B : ClosedBlowupSequence X)
    (f : X ⟶ X₀) (S : Set X₀) (hB : B.CentersLieOver f S) (j : ℕ) :
    (B.truncate j).CentersLieOver f S := by
  induction B generalizing X₀ j with
  | nil X => exact hB
  | cons Z B ih =>
    cases j with
    | zero => trivial
    | succ j => exact ⟨hB.1, ih _ _ hB.2 j⟩

private theorem image_subset_of_centersLieOver_snoc {X X₀ : Scheme.{u}}
    (C : ClosedBlowupSequence X) (Z : C.target.IdealSheafData) (f : X ⟶ X₀) (S : Set X₀)
    (h : (snoc C Z).CentersLieOver f S) :
    ((C.toBase ≫ f : C.target ⟶ X₀) : C.target → X₀) '' (Z.support : Set C.target) ⊆ S := by
  induction C generalizing X₀ with
  | nil X =>
    rintro _ ⟨x, hx, rfl⟩
    exact h.1 ⟨x, hx, rfl⟩
  | cons Z₀ C ih =>
    have := ih _ _ _ h.2
    change ((C.toBase ≫ blowUpToBase Z₀) ≫ f : C.target ⟶ X₀) '' _ ⊆ S
    rwa [Category.assoc]

private theorem range_pullbackHom {X Y : Scheme.{u}} (C : ClosedBlowupSequence X) (h : Y ⟶ X)
    [Flat h] : Set.range (C.pullbackHom h) = C.toBase ⁻¹' Set.range h := by
  have hP := (Kollar.isPullback_pullback_toBase_of_flat C h).flip
  rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso hP.isoPullback.hom.base).2.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-- An étale morphism is étale at every point. -/
private theorem etaleAt_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    EtaleAt f x := by
  obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens Y))
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens X))
    (show x ∈ f ⁻¹ᵁ V from hxV)
  exact ⟨U, hU, hxU, V, hV, hUV, HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV⟩

/-- An irreducible component of a scheme étale over a scheme `X` of finite type over `k` has the
dimension of an irreducible component of `X`: its generic point maps to a generic point of `X`
(étale morphisms are generizing), with finite residue field extension. -/
private theorem exists_topologicalKrullDim_eq_of_etale {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (ψ : U ⟶ X) [Etale ψ] {C : Set U}
    (hC : C ∈ irreducibleComponents U) :
    ∃ D ∈ irreducibleComponents X, topologicalKrullDim C = topologicalKrullDim D := by
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [hCcl.closure_eq] at hg
  set η := hC.1.genericPoint
  obtain ⟨D', hD', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := ψ η)).closure
  have hD'cl := isClosed_of_mem_irreducibleComponents D' hD'
  have hgD := hD'.1.isGenericPoint_genericPoint_closure
  rw [hD'cl.closure_eq] at hgD
  set ξ := hD'.1.genericPoint
  have hξ : ξ ⤳ ψ η := hgD.specializes (hsub (subset_closure rfl))
  obtain ⟨η', hη', hψη'⟩ := Flat.generalizingMap ψ hξ
  have hCη' : C ⊆ closure {η'} := by
    rw [← hg.def]
    exact specializes_iff_closure_subset.1 hη'
  have h' : closure {η'} ⊆ C := hC.2 isIrreducible_singleton.closure hCη'
  have hηη' : η ⤳ η' := specializes_iff_mem_closure.2 (hg.def ▸ h' (subset_closure rfl))
  have hD : closure {ψ η} = D' := by
    refine le_antisymm hsub ?_
    rw [← hgD.def]
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) isClosed_closure
    rw [← hψη']
    exact specializes_iff_mem_closure.1 (hηη'.map ψ.continuous)
  refine ⟨D', hD', ?_⟩
  rw [← hg.def, ← hD,
    MMP.topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg (ψ ≫ sX),
    MMP.topologicalKrullDim_closure_singleton_eq_toENat_residueTrdeg sX,
    Stacks.Chow.residueTrdeg_comp,
    Stacks.PurityRamification.residueTrdeg_eq_zero_of_etaleAt ψ (etaleAt_of_etale ψ η),
    add_zero]

/-- A scheme étale over an equidimensional scheme `X` of finite type over `k`, all of whose
irreducible components have positive dimension, is equidimensional with all irreducible
components of positive dimension. -/
private theorem equidimensional_of_etale {X U : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (ψ : U ⟶ X) [Etale ψ] :
    Equidimensional U ∧ ∀ Z ∈ irreducibleComponents U, 0 < topologicalKrullDim Z := by
  refine ⟨fun Z hZ W hW => ?_, fun Z hZ => ?_⟩
  · obtain ⟨D, hD, e⟩ := exists_topologicalKrullDim_eq_of_etale sX ψ hZ
    obtain ⟨D', hD', e'⟩ := exists_topologicalKrullDim_eq_of_etale sX ψ hW
    rw [e, e', hX D hD D' hD']
  · obtain ⟨D, hD, e⟩ := exists_topologicalKrullDim_eq_of_etale sX ψ hZ
    rw [e]
    exact hdim D hD

/-- **Kollár, Cor. 3.77 on an étale chart.** The pull-back `Z^U_i` of the `i`-th centre of an
order-`m` smooth blow-up sequence along an étale `ψ : U → X` lies in `V(M_i)`, for `M_i` the
transform of the maximal contact ideal `D^{m-1}(ψ^* I)` with marking `1`. -/
private theorem support_comap_subset_markedTransform [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {B : ClosedBlowupSequence X} (hB : B.IsOrderMPlainSeq sX I m)
    {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)} [LocallyOfFiniteType sU]
    [QuasiCompact sU] (ψ : U ⟶ X) [Etale ψ] (hsU : ψ ≫ sX = sU)
    {i : ℕ} {C : ClosedBlowupSequence X} {Z : C.target.IdealSheafData}
    (hZ : B.truncate (i + 1) = snoc C Z) :
    ((Z.comap (C.pullbackHom ψ)).support : Set (C.pullback ψ).target) ⊆
      ((C.pullback ψ).markedTransform
        ⟨higherDerivativeIdeal sU (I.comap ψ) (m - 1), 1⟩).I.support := by
  have hXs : MMP.Mori.IsSmoothScheme sX := (MMP.Mori.isSmoothScheme_iff sX).2 inferInstance
  obtain ⟨hUeq, hUdim⟩ := equidimensional_of_etale sX hX hdim ψ
  have hGe := (ClosedBlowupSequence.isOrderGePlainSeq_pullback_of_etale sX hXs hX I hI m hm1
    hm.le B hB ψ).1
  rw [hsU] at hGe
  have hInz : IsNonzeroAtGenericPoints (I.comap ψ) := by
    have h0 := isOrderGePlainSeq_truncate _ _ _ hGe 0
    rw [Kollar.truncate_zero] at h0
    exact h0.2
  have hGei := isOrderGePlainSeq_truncate _ _ _ hGe (i + 1)
  rw [Kollar.pullback_truncate, hZ, pullback_snoc] at hGei
  obtain ⟨hsm, hZsm, hord⟩ := isOrderGePlainSeq_snoc _ _ _ _
    (isOrderGePlainSeq_higherDerivativeIdeal sU hUeq hUdim ⟨I.comap ψ, m⟩ hInz _ hGei
      (m - 1) (Nat.sub_le m 1)).1
  simp only [show m - (m - 1) = 1 by omega] at hord
  exact support_subset_of_orderAlongGE_one _ hsm _ hZsm _ hord

end Proof_lem_kr3d_etale_equivalent_sequences_centers_agree

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_etale_equivalent_sequences_centers_agree in
/-- **Étale equivalent sequences: the centres agree** (Kollár, proof of Thm. 3.97). Let `X` be
separated, smooth, equidimensional and of finite type over a field `k` of characteristic `0`,
every irreducible component of positive dimension; `I` nonzero at the generic points with
`maxOrder I = m ≥ 1`; `B`, `B'` smooth blow-up sequences of order `m` starting with `(X, I)`;
and `ψ, ψ' : U ⟶ X` an étale chart pair for `I` with `B.pullback ψ = B'.pullback ψ'`. Let
`i < B.length` with `B.truncate i = C = B'.truncate i`. If the pair `(ψ_i, ψ'_i)` of
`ψ_i = C.pullbackHom ψ`, `ψ'_i = C.pullbackHom ψ'` pulls the ideal of the diagonal of
`C.target ×_k C.target` back into the marked transform of `(D^{m-1}(ψ^*I), 1)` along
`C.pullback ψ`, then `B.truncate (i + 1) = B'.truncate (i + 1)`: the `i`-th centres agree. -/
@[mmp "lem_kr3d_etale_equivalent_sequences_centers_agree"]
public theorem truncate_succ_eq_of_isEtaleChartPair {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX] [IsSeparated sX]
    (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {B B' : ClosedBlowupSequence X} (hB : B.IsOrderMPlainSeq sX I m)
    (hB' : B'.IsOrderMPlainSeq sX I m) {U : Scheme.{u}} {sU : U ⟶ Spec (.of k)}
    {ψ ψ' : U ⟶ X} (hψ : IsEtaleChartPair sX I sU ψ ψ') (hBB' : B.pullback ψ = B'.pullback ψ')
    {i : ℕ} (hi : i < B.length) {C : ClosedBlowupSequence X} (hC : B.truncate i = C)
    (hC' : B'.truncate i = C)
    (hdiag : ∀ (hU : C.pullback ψ = C.pullback ψ')
      (hk : C.pullbackHom ψ ≫ C.toBase ≫ sX =
        (eqToHom (congrArg ClosedBlowupSequence.target hU) ≫ C.pullbackHom ψ') ≫
          C.toBase ≫ sX),
      (Limits.pullback.diagonal (C.toBase ≫ sX)).ker.comap (Limits.pullback.lift _ _ hk) ≤
        ((C.pullback ψ).markedTransform
          ⟨higherDerivativeIdeal sU (I.comap ψ) (m - 1), 1⟩).I) :
    B.truncate (i + 1) = B'.truncate (i + 1) := by
  have := hψ.etale
  have := hψ.etale'
  have := hψ.locallyOfFiniteType
  have := hψ.quasiCompact
  have hXs : MMP.Mori.IsSmoothScheme sX := (MMP.Mori.isSmoothScheme_iff sX).2 inferInstance
  -- the `i`-th centres
  have hlen : B.length = B'.length := by
    rw [← length_pullback B ψ, hBB', length_pullback]
  have hsnoc : ∀ B₀ : ClosedBlowupSequence X, B₀.truncate i = C → i < B₀.length →
      ∃ W : C.target.IdealSheafData, B₀.truncate (i + 1) = snoc C W := by
    rintro B₀ rfl h
    exact exists_truncate_succ B₀ i h
  obtain ⟨Z, hZ⟩ := hsnoc B hC hi
  obtain ⟨Z', hZ'⟩ := hsnoc B' hC' (hlen ▸ hi)
  rw [hZ, hZ']
  suffices Z = Z' by rw [this]
  -- the pulled-back sequences
  have hU : C.pullback ψ = C.pullback ψ' := by
    have h := congrArg (fun D => D.truncate i) hBB'
    simp only [Kollar.pullback_truncate, hC, hC'] at h
    exact h
  have hP : snoc (C.pullback ψ) (Z.comap (C.pullbackHom ψ)) =
      snoc (C.pullback ψ') (Z'.comap (C.pullbackHom ψ')) := by
    rw [← pullback_snoc, ← pullback_snoc, ← hZ, ← hZ', ← Kollar.pullback_truncate,
      ← Kollar.pullback_truncate, hBB']
  set φ := eqToHom (congrArg ClosedBlowupSequence.target hU) ≫ C.pullbackHom ψ' with hφ
  have hZU : Z.comap (C.pullbackHom ψ) = Z'.comap φ := by
    rw [eq_comap_of_snoc_eq hU hP, hφ, Scheme.IdealSheafData.comap_comp]
  have hk : C.pullbackHom ψ ≫ C.toBase ≫ sX = φ ≫ C.toBase ≫ sX := by
    rw [reassoc_of% (Kollar.pullbackHom_toBase_comm C ψ), hφ, Category.assoc,
      reassoc_of% (Kollar.pullbackHom_toBase_comm C ψ'),
      reassoc_of% (eqToHom_target_comp_toBase hU),
      hψ.comp_eq, hψ.comp_eq']
  -- `Z^U_i ⊆ V(M_i)`, by Cor. 3.77 on `U`
  have hsub := support_comap_subset_markedTransform sX hX hdim hI hm1 hm hB ψ hψ.comp_eq hZ
  -- `ψ_i` and `ψ'_i` agree on `Z^U_i`
  have := isSeparated_toBase sX C
  have hagree : ∀ x ∈ ((Z.comap (C.pullbackHom ψ)).support : Set _),
      C.pullbackHom ψ x = φ x := fun x hx =>
    apply_eq_of_comap_diagonal_le _ _ _ hk _ (hdiag hU hk) (hsub hx)
  -- the centres lie in the images of `ψ_i` and `ψ'_i`
  have hm' : (maxOrder I).toNat = m := by rw [hm]; rfl
  have hcos := ClosedBlowupSequence.centersLieOver_cosupport_of_isOrderMPlainSeq sX hXs hX I hI m
    hm1 hm.le
  have hrange : ∀ (B₀ : ClosedBlowupSequence X) (W : C.target.IdealSheafData) (χ : U ⟶ X),
      [Etale χ] → B₀.IsOrderMPlainSeq sX I m → B₀.truncate (i + 1) = snoc C W →
      MarkedIdeal.cosupport ⟨I, m⟩ ⊆ Set.range χ →
      (W.support : Set C.target) ⊆ Set.range (C.pullbackHom χ) := by
    intro B₀ W χ _ hB₀ hW hχ x hx
    have hl := centersLieOver_truncate _ _ _ (hcos B₀ hB₀) (i + 1)
    rw [hW] at hl
    have := image_subset_of_centersLieOver_snoc _ _ _ _ hl ⟨x, hx, rfl⟩
    rw [range_pullbackHom]
    exact hχ this
  have hr := hrange B Z ψ hB hZ (hm' ▸ hψ.cosupport_subset)
  have hr' : (Z'.support : Set C.target) ⊆ Set.range φ := by
    rw [hφ, range_eqToHom_comp]
    exact hrange B' Z' ψ' hB' hZ' (hm' ▸ hψ.cosupport_subset')
  -- equal supports
  have hsupp : Z.support = Z'.support := Closeds.ext <|
    (support_subset_of_comap_eq hZU hagree hr).antisymm
    (support_subset_of_comap_eq hZU.symm (fun x hx => (hagree x (hZU ▸ hx)).symm) hr')
  -- smooth centres are reduced
  have := locallyOfFiniteType_toBase sX C
  have hZs := isSmoothScheme_of_isOrderMPlainSeq_snoc C Z sX I m
    (hZ ▸ isOrderMPlainSeq_truncate B sX I m hB (i + 1))
  have hZs' := isSmoothScheme_of_isOrderMPlainSeq_snoc C Z' sX I m
    (hZ' ▸ isOrderMPlainSeq_truncate B' sX I m hB' (i + 1))
  exact eq_of_support_eq (C.toBase ≫ sX) hZs hZs' hsupp

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## The centres of a blow-up sequence stay on a hypersurface inside `D^{m-1}(I)`

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
`0`, with every irreducible component of positive dimension, let `(I, m)` be a marked ideal
sheaf with `m ≥ 1` and `I` nonzero on every irreducible component, and let
`Π = (X_i, Z_i)_{i ≤ r}` be a smooth blow-up sequence of order `≥ m` starting with `(X, I, m)`.
If `H ⊆ X` is a smooth hypersurface with `𝒪_X(-H) ⊆ D^{m-1}(I)`, then every centre `Z_i` is
contained in the `i`-th term `H_i ⊆ X_i` of the restriction `Π|_H`.

The `i`-th centre is read by splitting `Π = Π'.append (cons Z C)` with `Π'` of length `i`, so
that `X_i` is the target of `Π'`, `Z_i = Z`, and `H_i ⊆ X_i` is the closed subscheme cut out by
the kernel of the closed immersion `Π'.restrictHom H : H_i → X_i`. The containment `Z_i ⊆ H_i`
is scheme-theoretic: the ideal sheaf of `H_i` is contained in that of `Z_i`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace Proof_lem_kr3d_hypersurface_in_derived_sequence

open MMP.Resolution.ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- An ideal sheaf contained in one of order `≥ 1` along a smooth centre `Z` of a smooth scheme
is contained in the ideal sheaf of `Z`. -/
private theorem le_of_le_of_orderAlongGE_one {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) {K I : X.IdealSheafData} (hKI : K ≤ I)
    (hI : OrderAlongGE I (Z.support : Set X) ((1 : ℕ) : ℕ∞)) : K ≤ Z := by
  refine hKI.trans (IdealSheafData.le_of_stalk_le _ _ fun x => ?_)
  simpa using stalk_le_pow_of_orderAlongGE sX hX Z hZ I 1 hI x

/-- An effective Cartier divisor can be cancelled from an inclusion: `A·D ≤ B·D` forces
`A ≤ B`. -/
private theorem le_of_mul_le_mul_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {A B D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : A * D ≤ B * D) : A ≤ B := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  obtain ⟨g, hg, hgs⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
  have hy := MMP.Resolution.stalk_le_stalk_of_le h y
  simp only [IdealSheafData.stalk_mul, hgs] at hy
  intro x hx
  have hxg : x * g ∈ IdealSheafData.stalk B y * Ideal.span {g} :=
    hy (Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self g))
  obtain ⟨b, hb, hbg⟩ := Ideal.mem_mul_span_singleton.mp hxg
  rw [hg.2 hbg] at hb
  exact hb

/-- The canonical lift of a closed immersion `j` has the same ideal sheaf as the canonical lift
of the closed immersion of the subscheme cut out by `ker j`. -/
private theorem ker_canonicalLift_eq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = (canonicalLift j.ker.subschemeι Z).ker := by
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι (by simp)
  have key : ∀ (t : S ⟶ j.image) [IsIso t] (g : j.image ⟶ X),
      (canonicalLift (t ≫ g) Z).ker = (canonicalLift g Z).ker := by
    intro t _ g
    have : IsIso (canonicalLift t (Z.comap g)) := MMP.Resolution.Kollar.isIso_canonicalLift t _
    rw [← Scheme.Hom.ker_comp_of_isIso (eqToHom (congrArg blowUp
        (Scheme.IdealSheafData.comap_comp Z t g).symm)),
      ← canonicalLift_comp_canonicalLift, Scheme.Hom.ker_comp_of_isIso]
  conv_lhs => rw [← j.toImage_imageι]
  exact key j.toImage j.imageι

/-- The induction along the sequence: for a closed immersion `j : S → X` cut out by a smooth
hypersurface inside `I`, with `(I, 1)` starting a sequence of order `≥ 1`, every centre `Z_i`
contains the `i`-th term of the pull-back of the sequence along `j`. -/
private theorem ker_pullbackHom_le {k : Type u} [Field k] [CharZero k] :
    ∀ {X : Scheme.{u}} (B' : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k))
      (b : MarkedIdeal X) (_hb : b.m = 1) (Z : B'.target.IdealSheafData)
      (C : ClosedBlowupSequence (blowUp Z)) (_hB : IsOrderGePlainSeq sX b (B'.append (cons Z C)))
      {S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
      (_hH : IsSmoothHypersurface sX j.ker) (_hle : j.ker ≤ b.I),
      (B'.pullbackHom j).ker ≤ Z := by
  intro X B'
  induction B' with
  | nil X =>
    intro sX b hb Z C hB S j _ hH hle
    obtain ⟨hX, -, hZ, -, hord, -⟩ := hB
    exact le_of_le_of_orderAlongGE_one sX hX Z hZ hle (hb ▸ hord)
  | cons Z₀ B'' ih =>
    intro sX b hb Z C hB S j _ hH hle
    obtain ⟨hX, -, hZ₀, hcodim, hord, hB''⟩ := hB
    have hK : j.ker ≤ Z₀ := le_of_le_of_orderAlongGE_one sX hX Z₀ hZ₀ hle (hb ▸ hord)
    have hlift := MMP.Resolution.ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hX j.ker Z₀ hH
      hZ₀ hK
    have : IsClosedImmersion (canonicalLift j Z₀) :=
      MMP.Resolution.Bridges.isClosedImmersion_canonicalLift j Z₀
    refine ih _ (b.birationalTransform Z₀) hb Z C hB'' (canonicalLift j Z₀) ?_ ?_
    · rw [ker_canonicalLift_eq]
      exact hlift.2.2
    · have hbt := MarkedIdeal.birationalTransform_mul_eq sX hX Z₀ hZ₀ hcodim b hord
      rw [hb, pow_one] at hbt
      refine le_of_mul_le_mul_of_isEffectiveCartierDivisor
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z₀) ?_
      rw [hbt, ker_canonicalLift_eq, hlift.2.1]
      exact Scheme.IdealSheafData.comap_mono _ hle

end Proof_lem_kr3d_hypersurface_in_derived_sequence

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_hypersurface_in_derived_sequence in
/-- **The centres stay on `H`** (Kollár Thm. 3.80, proof of (1)). Let `X` be smooth,
equidimensional and of finite type over a field `k` of characteristic `0`, with every
irreducible component of positive dimension, let `a = (I, m)` be a marked ideal with `m ≥ 1` and
`I` nonzero on every irreducible component, and let `B` be a smooth blow-up sequence of order
`≥ m` starting with `(X, I, m)`. If `H ⊆ X` is a smooth hypersurface with `H ≤ D^{m-1}(I)` as
ideal sheaves, then for every splitting `B = B'.append (cons Z C)` the centre `Z` on
`X_i = B'.target` contains `H_i`, the image of `B'.restrictHom H`: its ideal sheaf
`ker (B'.restrictHom H)` is contained in `Z`. -/
@[mmp "lem_kr3d_hypersurface_in_derived_sequence"]
public theorem IsOrderGePlainSeq.ker_restrictHom_le_of_le_higherDerivativeIdeal {k : Type u}
    [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {a : MarkedIdeal X} (ha : 1 ≤ a.m) (hI : IsNonzeroAtGenericPoints a.I)
    {B : ClosedBlowupSequence X} (hB : IsOrderGePlainSeq sX a B)
    {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H)
    (hHI : H ≤ higherDerivativeIdeal sX a.I (a.m - 1))
    {B' : ClosedBlowupSequence X} {Z : B'.target.IdealSheafData}
    {C : ClosedBlowupSequence (blowUp Z)} (hsplit : B = B'.append (cons Z C)) :
    (B'.restrictHom H).ker ≤ Z := by
  obtain ⟨hB₁, -⟩ := isOrderGePlainSeq_higherDerivativeIdeal sX hX hdim a hI B hB (a.m - 1)
    (Nat.sub_le _ _)
  subst hsplit
  exact ker_pullbackHom_le B' sX _ (by change a.m - (a.m - 1) = 1; omega) Z C hB₁
    H.subschemeι (by rwa [Scheme.IdealSheafData.ker_subschemeι])
    (by rwa [Scheme.IdealSheafData.ker_subschemeι])

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## A smooth hypersurface inside the maximal contact ideal has maximal contact

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
`0`, with every irreducible component of positive dimension, and let `I` be an ideal sheaf
nonzero on every irreducible component with `m = maxord I ≥ 1`. If `H ⊆ X` is a smooth
hypersurface with `𝒪_X(-H) ⊆ MC(I) = D^{m-1}(I)`, then `H` is a hypersurface of maximal
contact for `I`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace Proof_lem_kr3d_maximal_contact_from_ideal_inclusion

open MMP.Resolution.ClosedBlowupSequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- If every centre `Z` of `B`, read on a splitting `B = B'.append (cons Z C)`, contains the
image of the pulled-back morphism `B'.pullbackHom j`, then the centres of `B` are contained in
the restriction of `B` along `j`. -/
private theorem centersContainedIn_of_forall_ker_le {X S : Scheme.{u}}
    (B : ClosedBlowupSequence X) (j : S ⟶ X)
    (h : ∀ (B' : ClosedBlowupSequence X) (Z : B'.target.IdealSheafData)
      (C : ClosedBlowupSequence (blowUp Z)), B = B'.append (cons Z C) →
        (B'.pullbackHom j).ker ≤ Z) :
    B.CentersContainedIn j := by
  induction B generalizing S with
  | nil => trivial
  | cons Z B ih =>
    exact ⟨h (nil _) Z B rfl,
      ih _ fun B' Z' C hB => h (cons Z B') Z' C (by rw [hB]; rfl)⟩

/-- Along a smooth centre `Z` along which `ord_Z I = m`, the controlled transform of `I` is the
birational transform of the marked ideal `(I, m)`. -/
private theorem birationalTransform_eq_controlledTransform {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX)
    [LocallyOfFiniteType sX] [QuasiCompact sX] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (I : X.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) (m : ℕ) (hord : OrderAlongEq I (Z.support : Set X) m) :
    MarkedIdeal.birationalTransform Z ⟨I, m⟩ = ⟨controlledTransform Z I, m⟩ := by
  have hdiv : controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
    have hfun : (fun W : componentsOf (Z.support : Set X) => (orderAlong I W.2.1.1).toNat) =
        fun _ => m := funext fun W => by rw [hord W.1 W.2]; rfl
    rw [controlledTransformDivisorIdeal_eq_exceptionalDivisorIdeal, hfun]
    refine IdealSheafData.eq_of_stalk_eq _ _ fun y => ?_
    obtain ⟨n, hn, -, hW⟩ := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ (fun _ => m) y
    rw [hn, IdealSheafData.stalk_pow]
    by_cases hx : blowUpToBase Z y ∈ (Z.support : Set X)
    · obtain ⟨W, rfl⟩ := hW hx
      rfl
    · have htop : IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y = ⊤ := by
        rwa [IdealSheafData.stalk_eq_top_iff_notMem_support, Scheme.IdealSheafData.support_comap]
      rw [htop, Ideal.top_pow, Ideal.top_pow]
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase Z) ^ m) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) m
  have h1 := MarkedIdeal.birationalTransform_mul_eq sX hX Z hZ hcodim ⟨I, m⟩
    (fun W hW => (hord W hW).ge)
  have h2 := controlledTransform_mul_eq sX hX Z hZ hcodim I hI
  rw [hdiv] at h2
  have := le_antisymm
    (Proof_lem_kr3d_hypersurface_in_derived_sequence.le_of_mul_le_mul_of_isEffectiveCartierDivisor
      hDc (h1.trans h2.symm).le)
    (Proof_lem_kr3d_hypersurface_in_derived_sequence.le_of_mul_le_mul_of_isEffectiveCartierDivisor
      hDc (h1.trans h2.symm).ge)
  change MarkedIdeal.mk _ m = MarkedIdeal.mk _ m
  rw [← this]
  rfl

/-- A smooth blow-up sequence of order `m` starting with `(X, I)` is a smooth blow-up sequence
of order `≥ m` starting with `(X, I, m)`. -/
private theorem isOrderGePlainSeq_of_isOrderMPlainSeq {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) :
    ∀ (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]
      (I : X.IdealSheafData) (m : ℕ), B.IsOrderMPlainSeq s I m →
        B.IsOrderGePlainSeq s ⟨I, m⟩ := by
  induction B with
  | nil X => exact fun _ _ _ _ _ hB => hB
  | cons Z B ih =>
    intro s _ _ I m hB
    obtain ⟨hX, hI, hZ, hcodim, hord, hB'⟩ := hB
    haveI := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : IsProper (blowUpToBase Z) := isProper_blowUpToBase Z
    refine ⟨hX, hI, hZ, hcodim, fun W hW => (hord W hW).ge, ?_⟩
    change B.IsOrderGePlainSeq _ (MarkedIdeal.birationalTransform Z ⟨I, m⟩)
    rw [birationalTransform_eq_controlledTransform s hX Z hZ hcodim I hI m hord]
    exact ih _ _ m hB'

/-- The codimension of an irreducible closed subset of an open subscheme is that of its closure. -/
private theorem codimension_map_of_isOpenImmersion {X₀ X : Scheme.{u}} (j : X₀ ⟶ X)
    [IsOpenImmersion j] (W : IrreducibleCloseds X₀) :
    codimension (IrreducibleCloseds.map j j.continuous W) = codimension W := by
  have hf := j.isOpenEmbedding
  rw [codimension_eq_coheight, codimension_eq_coheight]
  refine (Order.coheight_eq_of_strictMono _
    (IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing) ?_ _).symm
  intro a b hab
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding j hf
  have hb : (j ⁻¹' (b : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨x, hab.le (subset_closure ⟨x, hx, rfl⟩)⟩
  refine ⟨e.symm ⟨b, hb⟩, ?_, ?_⟩
  · rw [← e.lt_iff_lt, OrderIso.apply_symm_apply]
    exact hab
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)

/-- The trace of a smooth hypersurface on an open subscheme is a smooth hypersurface. -/
private theorem isSmoothHypersurface_comap_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H)
    (X₀ : X.Opens) : IsSmoothHypersurface (X₀.ι ≫ sX) (H.comap X₀.ι) := by
  obtain ⟨hHs, hHc⟩ := hH
  refine ⟨?_, ?_⟩
  · haveI := MMP.Mori.IsSmoothScheme.smooth hHs
    have he : (H.comap X₀.ι).subschemeι ≫ X₀.ι ≫ sX =
        (H.comapIso X₀.ι).hom ≫ Limits.pullback.snd X₀.ι H.subschemeι ≫ H.subschemeι ≫ sX := by
      rw [← H.comapIso_hom_fst X₀.ι, Category.assoc, Limits.pullback.condition_assoc]
    rw [he]
    exact MMP.Mori.isSmoothScheme_of_smooth inferInstance
  · intro W₀ hW₀
    have hf := X₀.ι.isOpenEmbedding
    set W := IrreducibleCloseds.map X₀.ι X₀.ι.continuous W₀
    have hWH : (W : Set X) ⊆ H.support := by
      refine closure_minimal ?_ H.support.2
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_support_comap_iff X₀.ι H x).1 (hW₀.prop hx)
    have hWmax : Maximal (fun W' : IrreducibleCloseds X ↦ (W' : Set X) ⊆ H.support) W := by
      refine ⟨hWH, fun W' hW' hWW' => ?_⟩
      let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding X₀.ι hf
      obtain ⟨x, hx⟩ := W₀.isIrreducible.nonempty
      have hne : (X₀.ι ⁻¹' (W' : Set X)).Nonempty := ⟨x, hWW' (subset_closure ⟨x, hx, rfl⟩)⟩
      have h1 : W₀ ≤ e.symm ⟨W', hne⟩ := by
        rw [← e.le_iff_le, OrderIso.apply_symm_apply]
        exact hWW'
      have h2 : e.symm ⟨W', hne⟩ ≤ W₀ := hW₀.2
        (fun y hy => (mem_support_comap_iff X₀.ι H y).2 (hW' hy)) h1
      have h3 : (⟨W', hne⟩ : {V : IrreducibleCloseds X | (X₀.ι ⁻¹' V).Nonempty}) ≤ e W₀ := by
        rw [← OrderIso.apply_symm_apply e ⟨W', hne⟩]
        exact e.monotone h2
      exact h3
    rw [← codimension_map_of_isOpenImmersion X₀.ι W₀]
    exact hHc W hWmax

/-- A `k`-algebra isomorphism carries the first derivative of an ideal into the first derivative
of its image. -/
private theorem map_derivativeIdealOfRing_le {k R S : Type*} [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra k S] (φ : R →+* S) (hφ : Function.Bijective φ)
    (hk : ∀ c : k, φ (algebraMap k R c) = algebraMap k S c) (J : Ideal R) :
    (derivativeIdealOfRing k J).map φ ≤ derivativeIdealOfRing k (J.map φ) := by
  let e : R ≃ₐ[k] S := AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective φ hφ) hk
  have he : ∀ r, e r = φ r := fun _ => rfl
  let δ' : Derivation k R R → Derivation k S S := fun δ =>
    Derivation.mk' (e.toLinearMap ∘ₗ δ.toLinearMap ∘ₗ e.symm.toLinearMap) fun a b => by
      simp [Derivation.leibniz, smul_eq_mul]
  unfold derivativeIdealOfRing
  rw [Ideal.map_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨δ, f, hf, rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨δ' δ, φ f, Ideal.mem_map_of_mem _ hf, ?_⟩
  change e (δ (e.symm (e f))) = φ (δ f)
  rw [e.symm_apply_apply, he]

/-- The first derivative is monotone: `I ≤ J` gives `D(I) ≤ D(J)`. -/
private theorem derivativeIdeal_mono {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I J : X.IdealSheafData} (h : I ≤ J) :
    derivativeIdeal sX I ≤ derivativeIdeal sX J := by
  refine le_sInf fun K hK => sInf_le fun W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  exact Ideal.span_mono fun _ ⟨δ, f, hf, hδ⟩ => ⟨δ, f, h W hf, hδ⟩

/-- The first derivative is formed locally: restricting `D(I)` to an open subscheme lands in
the first derivative of the restriction. -/
private theorem comap_derivativeIdeal_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (X₀ : X.Opens) (I : X.IdealSheafData) :
    (derivativeIdeal sX I).comap X₀.ι ≤ derivativeIdeal (X₀.ι ≫ sX) (I.comap X₀.ι) := by
  intro W
  let W' : X.affineOpens := ⟨X₀.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion X₀.ι⟩
  have hWW : X₀.ι ⁻¹ᵁ W'.1 = W.1 := X₀.ι.preimage_image_eq W.1
  have hle : W.1 ≤ X₀.ι ⁻¹ᵁ W'.1 := hWW.ge
  rw [Stacks.IdealSheaf.ideal_comap_appLE _ X₀.ι W' W hle, derivativeIdeal_ideal,
    derivativeIdeal_ideal]
  unfold sectionDerivativeIdeal
  rw [Stacks.IdealSheaf.ideal_comap_appLE _ X₀.ι W' W hle]
  letI := MMP.Mori.sectionAlgebra sX W'.1
  letI := MMP.Mori.sectionAlgebra (X₀.ι ≫ sX) W.1
  have hiso : IsIso (X₀.ι.appLE W'.1 W.1 hle) := by
    have : IsIso (X₀.ι.app W'.1) := Scheme.Hom.isIso_app X₀.ι W'.1 (by
      change X₀.ι ''ᵁ W.1 ≤ X₀.ι.opensRange
      exact X₀.ι.image_le_opensRange W.1)
    have h2 : (homOfLE hle).op = (eqToHom hWW.symm).op := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, h2]
    infer_instance
  refine map_derivativeIdealOfRing_le _ (ConcreteCategory.bijective_of_isIso _) (fun c => ?_) _
  have h := Scheme.Hom.appLE_comp_appLE X₀.ι sX ⊤ W'.1 W.1 (by simp) hle
  exact congrArg (fun t => ((Scheme.ΓSpecIso (.of k)).inv ≫ t).hom c) h

/-- Higher derivative ideals are formed locally: restricting `D^r(I)` to an open subscheme lands
in `D^r` of the restriction. -/
private theorem comap_higherDerivativeIdeal_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (X₀ : X.Opens) (I : X.IdealSheafData)
    (r : ℕ) :
    (higherDerivativeIdeal sX I r).comap X₀.ι ≤
      higherDerivativeIdeal (X₀.ι ≫ sX) (I.comap X₀.ι) r := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ]
    exact (comap_derivativeIdeal_le sX X₀ _).trans (derivativeIdeal_mono _ ih)

/-- The ideal a smooth blow-up sequence of order `m` starts with is nonzero at generic points. -/
private theorem isNonzeroAtGenericPoints_of_isOrderMPlainSeq {k : Type u} [Field k] {X : Scheme.{u}}
    {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ}
    (hB : B.IsOrderMPlainSeq s I m) : IsNonzeroAtGenericPoints I := by
  cases B with
  | nil => exact hB.2
  | cons => exact hB.2.1

end Proof_lem_kr3d_maximal_contact_from_ideal_inclusion

namespace MMP.Resolution

open Proof_lem_kr3d_maximal_contact_from_ideal_inclusion in
/-- **Kollár, Thm. 3.80(1)**, ideal form. Let `X` be smooth, equidimensional and of finite type
over a field `k` of characteristic `0`, with every irreducible component of positive dimension,
and let `I` be an ideal sheaf nonzero at the generic point of every irreducible component with
maximal order `m ≥ 1`. A smooth hypersurface `H` whose ideal sheaf is contained in the maximal
contact ideal `maximalContactIdeal sX I` is a hypersurface of maximal contact for `I`. -/
@[mmp "lem_kr3d_maximal_contact_from_ideal_inclusion"]
public theorem isHypersurfaceOfMaximalContact_of_le_maximalContactIdeal {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {H : X.IdealSheafData} (hH : IsSmoothHypersurface sX H)
    (hHI : H ≤ maximalContactIdeal sX I) :
    IsHypersurfaceOfMaximalContact sX I H := by
  refine ⟨hH.1, hH.2, fun X₀ B hB => ?_⟩
  have hmn : (maxOrder I).toNat = m := by rw [hm]; rfl
  rw [hmn] at hB
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  have hHI₀ : H.comap X₀.ι ≤ higherDerivativeIdeal (X₀.ι ≫ sX) (I.comap X₀.ι) (m - 1) :=
    (Scheme.IdealSheafData.comap_mono X₀.ι (hmn ▸ hHI)).trans
      (comap_higherDerivativeIdeal_le sX X₀ I (m - 1))
  have hE := Proof_lem_kr3d_etale_equivalent_sequences_centers_agree.equidimensional_of_etale
    sX hX hdim X₀.ι
  refine centersContainedIn_of_forall_ker_le B _ fun B' Z C hsplit => ?_
  exact ClosedBlowupSequence.IsOrderGePlainSeq.ker_restrictHom_le_of_le_higherDerivativeIdeal
    (X₀.ι ≫ sX) hE.1 hE.2
    (a := ⟨I.comap X₀.ι, m⟩) hm1 (isNonzeroAtGenericPoints_of_isOrderMPlainSeq hB)
    (isOrderGePlainSeq_of_isOrderMPlainSeq B _ _ m hB)
    (isSmoothHypersurface_comap_opens sX hH X₀) hHI₀ hsplit

end MMP.Resolution

end

/-!
## Formal uniqueness of hypersurfaces of maximal contact

Let `X` be a smooth, equidimensional scheme of finite type over a field `k` of characteristic
zero, all of whose irreducible components have positive dimension, let `I` be a maximal contact
invariant ideal sheaf, nonzero at the generic point of every irreducible component, with
`m = maxord I ≥ 1`, and let `E = (E^1, …, E^s)` be an ordered snc divisor. Let `H, H' ⊆ X` be
smooth hypersurfaces with `𝒪_X(-H), 𝒪_X(-H') ⊆ MC(I)`, and let `p ∈ X` be a closed point with
`ord_p I = m`. Choose local equations `x₁, x₁'` of `H, H'` at `p` and `x₂, …, xₙ` such that
`(x₁, x₂, …, xₙ)` and `(x₁', x₂, …, xₙ)` are regular systems of parameters of `𝒪_{p,X}`, and
such that every `E^i` through `p` is `(x_l = 0)` near `p` for some `l ≥ 2`.

Then the substitution `x₁' ↦ x₁`, `x_l ↦ x_l` (`l ≥ 2`) of `𝒪̂_{p,X} = κ(p)[[x₁', x₂, …, xₙ]]`
is a `k`-algebra automorphism satisfying conditions (1)–(4) of formal equivalence; in
particular `H` and `H'` are formally equivalent at `p` with respect to `(X, I, E)`.

The substitution is described intrinsically: it is a `k`-algebra automorphism `φ` of
`𝒪̂_{p,X}` with `φ(x₁') = x₁` and `φ(x_l) = x_l` for `l ≥ 2` which induces the identity on the
residue field `κ(p)`, i.e. `s - φ(s) ∈ 𝔪_p 𝒪̂_{p,X}` for every `s ∈ 𝒪_{p,X}`. The last
condition is needed: a `k`-automorphism of `𝒪̂_{p,X}` may act on `κ(p)` by a nontrivial element
of `Aut_k(κ(p))`, and then it need not preserve `Î`. Such a `φ` exists, and it is unique,
since a `k`-algebra endomorphism of `𝒪̂_{p,X}` is local, hence continuous, and the coefficient
field `κ(p)` (finite and separable over `k`) is the unique one lifting the given action on the
residue field. So the statement says that such a `φ` exists and that every such `φ` satisfies
(1)–(4), which are the conditions of `AreFormallyEquivalent sX p I E H H'`. The coordinates
`x₂, …, xₙ` are indexed by `Fin n`, so the regular systems of parameters are `Fin.cons x₁ y`
and `Fin.cons x₁' y`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Resolution

namespace Proof_lem_kr3d_formal_uniqueness_of_maximal_contact

/-- A `k`-algebra isomorphism `R ≃ S` carries the derivative ideal of `J.comap e` into the
pull-back of the derivative ideal of `J`. -/
private lemma derivativeIdealOfRing_comap_le {A₀ R S : Type*} [CommRing A₀] [CommRing R]
    [CommRing S] [Algebra A₀ R] [Algebra A₀ S] (e : R ≃ₐ[A₀] S) (J : Ideal S) :
    derivativeIdealOfRing A₀ (J.comap e) ≤ (derivativeIdealOfRing A₀ J).comap e := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨δ, f, hf, rfl⟩
  let δ' : Derivation A₀ S S :=
    Derivation.mk' (e.toLinearMap ∘ₗ δ.toLinearMap ∘ₗ e.symm.toLinearMap) fun a b => by
      simp [Derivation.leibniz, smul_eq_mul]
  have : e (δ f) = δ' (e f) := by
    rw [show δ' (e f) = e (δ (e.symm (e f))) from rfl, AlgEquiv.symm_apply_apply]
  refine Ideal.mem_comap.2 ?_
  rw [this]
  exact Ideal.subset_span ⟨δ', e f, hf, rfl⟩

/-- A `K`-algebra map `K[[t₁, …, t_N]] → A` into a local ring sending every `tᵢ` into the
maximal ideal agrees, on residues, with the constant coefficient. -/
private lemma residue_apply_eq_residue_constantCoeff {A : Type*} [CommRing A] [IsLocalRing A]
    (K : Subring A) {N : ℕ} (G : MvPowerSeries (Fin N) K →ₐ[K] A)
    (hG : ∀ i, G (MvPowerSeries.X i) ∈ maximalIdeal A) (f : MvPowerSeries (Fin N) K) :
    residue A (G f) = residue A ((MvPowerSeries.constantCoeff f : K) : A) := by
  have h := mvPowerSeries_hom_ext (⊥ : Ideal (ResidueField A)) N
    ((residue A).comp G.toRingHom)
    ((residue A).comp (K.subtype.comp MvPowerSeries.constantCoeff)) (fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, MvPowerSeries.constantCoeff_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap, AlgHom.commutes]
      rfl)
    (fun i => by simpa using (residue_eq_zero_iff _).2 (hG i))
    (fun i => by simpa using (residue_eq_zero_iff _).2 (hG i))
  exact RingHom.congr_fun h f

/-- Two ring maps `K[[t₁, …, t_N]] → A` into a Noetherian local ring that agree on constants,
send every `tᵢ` into the maximal ideal, and agree on the `tᵢ` modulo an ideal `B ⊆ 𝔪`, agree
modulo `B` everywhere. -/
private lemma sub_mem_of_sub_X_mem {K A : Type*} [CommRing K] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {N : ℕ} (F G : MvPowerSeries (Fin N) K →+* A) {B : Ideal A}
    (hB : B ≤ maximalIdeal A) (hC : ∀ r, F (MvPowerSeries.C r) = G (MvPowerSeries.C r))
    (hX : ∀ i, F (MvPowerSeries.X i) - G (MvPowerSeries.X i) ∈ B)
    (hFX : ∀ i, F (MvPowerSeries.X i) ∈ maximalIdeal A) (f : MvPowerSeries (Fin N) K) :
    F f - G f ∈ B := by
  have : Nontrivial (A ⧸ B) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hB)
  have : IsLocalRing (A ⧸ B) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk B) Ideal.Quotient.mk_surjective
  have h := mvPowerSeries_hom_ext (maximalIdeal (A ⧸ B)) N ((Ideal.Quotient.mk B).comp F)
    ((Ideal.Quotient.mk B).comp G) (fun r => by simp [hC])
    (fun i => by simpa [Ideal.Quotient.eq] using hX i) (fun i => by
      rw [RingHom.comp_apply, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      have h1 : F (MvPowerSeries.X i) * b - 1 ∈ B := by
        rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
      apply (maximalIdeal.isMaximal A).ne_top
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (Ideal.mul_mem_right b _ (hFX i)) (hB h1)
      simpa using this)
  rw [← Ideal.Quotient.eq]
  exact RingHom.congr_fun h f

/-- The image in `R̂` of a member of a regular system of parameters of `R` lies in the maximal
ideal of `R̂`. -/
private lemma algebraMap_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {N : ℕ} {x : Fin N → R} (hx : MMP.Mori.IsRegularSystemOfParameters x)
    (i : Fin N) :
    algebraMap R (AdicCompletion (maximalIdeal R) R) (x i) ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  rw [← MMP.Flips.ResolutionInputs.span_range_algebraMap_eq_maximalIdeal hx]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- A ring automorphism of `R̂` that is the identity modulo `𝔪 R̂` on the image of `R` induces the
identity on the residue field of `R̂`. -/
private lemma residue_apply_eq_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (φ : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal R) R)
    (hφ : ∀ s, algebraMap R _ s - φ (algebraMap R _ s) ∈
      maximalIdeal (AdicCompletion (maximalIdeal R) R))
    (a : AdicCompletion (maximalIdeal R) R) : residue _ (φ a) = residue _ a := by
  obtain ⟨r, hr⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue _ a)
  obtain ⟨s, rfl⟩ := residue_surjective r
  rw [ResidueField.map_residue] at hr
  have hs := hφ s
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hs
  have hφa : φ (a - algebraMap R _ s) ∈ maximalIdeal _ := by
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
      ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hr]
  rw [← residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hφa
  rw [hφa, ← hs, ← hr]

/-- If `φ` corresponds, under a ring isomorphism `e : A ≃ B`, to a map `θ` of `A` that carries
`e⁻¹ J` onto itself, then `φ` carries `J` onto itself. -/
private lemma map_eq_of_image_comap_eq {A B E Φ : Type*} [CommRing A] [CommRing B]
    [EquivLike E A B] [RingEquivClass E A B] [FunLike Φ B B] [RingHomClass Φ B B]
    (e : E) (φ : Φ) {θ : A → A} (h : ∀ f, φ (e f) = e (θ f)) {J : Ideal B}
    (himg : θ '' J.comap e = J.comap e) : J.map φ = J := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) fun a ha => ?_
  · obtain ⟨f, rfl⟩ := EquivLike.surjective e a
    rw [Ideal.mem_comap, h]
    exact (himg.subset ⟨f, ha, rfl⟩ : θ f ∈ J.comap e)
  · obtain ⟨f, rfl⟩ := EquivLike.surjective e a
    obtain ⟨f₀, hf₀, rfl⟩ := himg.symm.subset (show f ∈ J.comap e from ha)
    rw [← h]
    exact Ideal.mem_map_of_mem _ hf₀

end Proof_lem_kr3d_formal_uniqueness_of_maximal_contact

namespace MMP.Resolution

open Proof_lem_kr3d_formal_uniqueness_of_maximal_contact in
/-- **Formal uniqueness of maximal contact** (Kollár 3.95, formal part). Let `X` be smooth,
equidimensional and of finite type over a field `k` of characteristic `0`, with every
irreducible component of positive dimension. Let `I` be a maximal contact invariant ideal sheaf,
nonzero at the generic points, with `m = maxord I ≥ 1`, and `E` an ordered snc divisor. Let
`H, H'` be smooth hypersurfaces whose ideal sheaves lie in `maximalContactIdeal sX I`, and `p` a
closed point with `ord_p I = m`. Let `x₁, x₁'` be local equations of `H, H'` at `p` and
`y = (x₂, …, xₙ)` such that `(x₁, y)` and `(x₁', y)` are regular systems of parameters, with each
`E^i` through `p` equal near `p` to some `(y_l = 0)`. Then there is a `k`-algebra automorphism
`φ` of `𝒪̂_{p,X}` with `φ(x₁') = x₁` and `φ(y_l) = y_l` inducing the identity on `κ(p)`. Every such
`φ` maps `Î_{H'}` onto `Î_H`, preserves `Î` and every `Î_{E^i}`, and satisfies
`h - φ(h) ∈ D^{m-1}_{𝒪̂/k}(Î)`. These are conditions (1)–(4) of `AreFormallyEquivalent`. -/
@[mmp "lem_kr3d_formal_uniqueness_of_maximal_contact"]
public theorem formalUniqueness_of_le_maximalContactIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : TopologicalSpace.Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsMCInvariant sX I) (hIgen : IsNonzeroAtGenericPoints I)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    {E : OrderedDivisor X} (hEo : E.IsOrderedDivisor) (hE : E.IsSNC sX)
    {H H' : X.IdealSheafData} (hH : IsSmoothHypersurface sX H) (hH' : IsSmoothHypersurface sX H')
    (hHI : H ≤ maximalContactIdeal sX I) (hH'I : H' ≤ maximalContactIdeal sX I)
    {p : X} (hp : IsClosed ({p} : Set X)) (hpm : multAt I p = m)
    {n : ℕ} {x₁ x₁' : X.presheaf.stalk p} {y : Fin n → X.presheaf.stalk p}
    (hx₁ : IdealSheafData.stalk H p = Ideal.span {x₁})
    (hx₁' : IdealSheafData.stalk H' p = Ideal.span {x₁'})
    (hreg : MMP.Mori.IsRegularSystemOfParameters (Fin.cons x₁ y : Fin (n + 1) → _))
    (hreg' : MMP.Mori.IsRegularSystemOfParameters (Fin.cons x₁' y : Fin (n + 1) → _))
    (hEy : ∀ i, p ∈ (E.E i).support → ∃ l, IdealSheafData.stalk (E.E i) p = Ideal.span {y l}) :
    letI := completedAlgebra sX p
    let ι := algebraMap (X.presheaf.stalk p)
      (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))
    (∃ φ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃ₐ[k]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      φ (ι x₁') = ι x₁ ∧ (∀ l, φ (ι (y l)) = ι (y l)) ∧
        ∀ s, ι s - φ (ι s) ∈ (maximalIdeal (X.presheaf.stalk p)).map ι) ∧
    ∀ φ : AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃ₐ[k]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      φ (ι x₁') = ι x₁ → (∀ l, φ (ι (y l)) = ι (y l)) →
        (∀ s, ι s - φ (ι s) ∈ (maximalIdeal (X.presheaf.stalk p)).map ι) →
        (completedIdeal H' p).map φ = completedIdeal H p ∧
          (completedIdeal I p).map φ = completedIdeal I p ∧
          (∀ i, (completedIdeal (E.E i) p).map φ = completedIdeal (E.E i) p) ∧
          ∀ h, h - φ h ∈
            higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1) := by
  letI := completedAlgebra sX p
  intro ι
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨K, hkK, hK⟩ :=
    (MMP.Flips.ResolutionInputs.existsUnique_isFieldOfRepresentatives_completion sX p hp).exists
  obtain ⟨F, ⟨hFX, hFb⟩, hFu⟩ :=
    MMP.Flips.ResolutionInputs.existsUnique_algHom_X_eq_bijective_stalk p hreg K hK
  obtain ⟨F', ⟨hF'X, hF'b⟩, -⟩ :=
    MMP.Flips.ResolutionInputs.existsUnique_algHom_X_eq_bijective_stalk p hreg' K hK
  have hFm : ∀ i, F (MvPowerSeries.X i) ∈ maximalIdeal _ := fun i => by
    rw [hFX]; exact algebraMap_mem_maximalIdeal hreg i
  have hF'm : ∀ i, F' (MvPowerSeries.X i) ∈ maximalIdeal _ := fun i => by
    rw [hF'X]; exact algebraMap_mem_maximalIdeal hreg' i
  have hmax : (maximalIdeal (X.presheaf.stalk p)).map ι =
      maximalIdeal (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have hFF' : ∀ f, residue _ (F f) = residue _ (F' f) := fun f => by
    rw [residue_apply_eq_residue_constantCoeff K F hFm,
      residue_apply_eq_residue_constantCoeff K F' hF'm]
  -- the `k`-algebra structure of the field of representatives
  letI : Algebra k K := ((algebraMap k _).codRestrict K fun c => hkK ⟨c, rfl⟩).toAlgebra
  have hkalg : ∀ G : MvPowerSeries (Fin (n + 1)) K →ₐ[K]
      AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
      Function.Bijective G → ∃ e : MvPowerSeries (Fin (n + 1)) K ≃ₐ[k]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p),
        ∀ f, e f = G f := fun G hG =>
    ⟨AlgEquiv.ofRingEquiv (f := (AlgEquiv.ofBijective G hG).toRingEquiv) fun c => by
      change G (algebraMap k _ c) = _
      rw [MvPowerSeries.algebraMap_apply,
        MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap, AlgHom.commutes]
      rfl, fun f => rfl⟩
  obtain ⟨e, he⟩ := hkalg F' hF'b
  obtain ⟨eF, heF⟩ := hkalg F hFb
  have hcons : ∀ i, F' (MvPowerSeries.X i) - F (MvPowerSeries.X i) ∈
      Ideal.span {ι x₁ - ι x₁'} := fun i => by
    rw [hFX, hF'X]
    refine Fin.cases ?_ (fun l => ?_) i
    · rw [Fin.cons_zero, Fin.cons_zero, Ideal.mem_span_singleton']
      exact ⟨-1, by ring⟩
    · simp
  refine ⟨⟨e.symm.trans eF, ?_, fun l => ?_, fun s => ?_⟩, fun φ hφ1 hφy hφs => ?_⟩
  · rw [AlgEquiv.trans_apply, show ι x₁' = e (MvPowerSeries.X 0) by rw [he, hF'X, Fin.cons_zero],
      e.symm_apply_apply, heF, hFX, Fin.cons_zero]
  · conv_lhs => rw [show ι (y l) = e (MvPowerSeries.X l.succ) by rw [he, hF'X, Fin.cons_succ]]
    rw [AlgEquiv.trans_apply, e.symm_apply_apply, heF, hFX, Fin.cons_succ]
  · rw [hmax, ← residue_eq_zero_iff, map_sub, sub_eq_zero, AlgEquiv.trans_apply, heF, hFF',
      ← he, AlgEquiv.apply_symm_apply]
  -- every admissible `φ` restricts to the identity on `K`
  have hfix : ∀ a ∈ K, φ a = a :=
    MMP.Flips.ResolutionInputs.eq_self_of_isFieldOfRepresentatives_completion sX p hp K hkK hK
      φ.toAlgHom (residue_apply_eq_of_sub_mem φ.toRingEquiv fun s => hmax ▸ hφs s)
  have hφF : ∀ f, φ (F' f) = F f := by
    let G : MvPowerSeries (Fin (n + 1)) K →ₐ[K]
        AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) :=
      { (φ.toRingEquiv.toRingHom).comp F'.toRingHom with
        commutes' := fun r => by
          simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
            MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, AlgHom.commutes]
          exact hfix _ r.2 }
    have hG : G = F := hFu G ⟨fun i => by
      change φ (F' _) = _
      rw [hF'X]
      refine Fin.cases ?_ (fun l => ?_) i
      · simpa using hφ1
      · simpa using hφy l, φ.bijective.comp hF'b⟩
    exact fun f => congrArg (fun G' => G' f) hG
  -- the ideal `B₀ = (x₁ - x₁') 𝒪̂ ⊆ D^{m-1}(Î)`
  have h1 : 1 ≤ maxOrder I := by rw [hm]; exact_mod_cast hm1
  have hB : completedIdeal (maximalContactIdeal sX I) p =
      higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1) :=
    (completedIdeal_higherDerivativeIdeal sX hX hdim hp I).2 h1
  have hmemB : ∀ {J : X.IdealSheafData} {z}, J ≤ maximalContactIdeal sX I →
      IdealSheafData.stalk J p = Ideal.span {z} →
      ι z ∈ higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1) :=
    fun hJ hz => hB ▸ Ideal.map_mono (stalk_le_stalk_of_le hJ p)
      (Ideal.mem_map_of_mem _ (hz ▸ Ideal.mem_span_singleton_self _))
  have hB₀B : Ideal.span {ι x₁ - ι x₁'} ≤
      higherDerivativeIdealOfRing k (completedIdeal I p) ((maxOrder I).toNat - 1) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact sub_mem (hmemB hHI hx₁) (hmemB hH'I hx₁')
  have hB₀m : Ideal.span {ι x₁ - ι x₁'} ≤ maximalIdeal _ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have h0 := sub_mem (algebraMap_mem_maximalIdeal hreg 0) (algebraMap_mem_maximalIdeal hreg' 0)
    rwa [Fin.cons_zero, Fin.cons_zero] at h0
  refine ⟨?_, ?_, fun i => ?_, fun h => ?_⟩
  · -- (1)
    rw [completedIdeal, completedIdeal, hx₁, hx₁', Ideal.map_span, Ideal.map_span,
      Set.image_singleton, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hφ1
  · -- (2)
    letI : Field K := hK.1.toField
    -- `K` is separable over `k`
    have : Module.Finite k (ResidueField
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p))) := by
      letI := MMP.Mori.stalkAlgebra sX p
      exact MMP.Flips.ResolutionInputs.finite_residueField_adicCompletion
        (MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX p hp)
    let ρ : K →ₐ[k] ResidueField
        (AdicCompletion (maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p)) :=
      { (residue _).comp K.subtype with commutes' := fun c => rfl }
    have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_injective ρ hK.2.1
    have : Algebra.IsSeparable k K := Algebra.IsAlgebraic.isSeparable_of_perfectField
    -- `F = F' ∘ θ` with `θ` the substitution `tᵢ ↦ F'⁻¹(F tᵢ)`
    let eK' := AlgEquiv.ofBijective F' hF'b
    let θ : MvPowerSeries (Fin (n + 1)) K →ₐ[K] MvPowerSeries (Fin (n + 1)) K :=
      eK'.symm.toAlgHom.comp F
    have hθ : ∀ f, F' (θ f) = F f := fun f => eK'.apply_symm_apply (F f)
    have hθb : Function.Bijective θ := eK'.symm.bijective.comp hFb
    have hg : ∀ i, θ (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries (Fin (n + 1)) K) :=
      fun i => by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map F'
        rw [hθ] at this
        exact hFm i this
    have hθs := MMP.Flips.ResolutionInputs.eq_substAlgHom_of_X hg θ fun i => rfl
    have hform : IsAutomorphismOfFormOnePlus ((Ideal.span {ι x₁ - ι x₁'}).comap e)
        (fun i => θ (MvPowerSeries.X i)) := by
      refine ⟨fun i => MMP.Flips.ResolutionInputs.constantCoeff_eq_zero_of_mem_maximalIdeal
        (hg i), ?_, fun i => ?_⟩
      · rw [← MvPowerSeries.coe_substAlgHom
          (MMP.Flips.ResolutionInputs.hasSubst_of_mem_maximalIdeal hg), ← hθs]
        exact hθb
      · rw [Ideal.mem_comap, map_sub, he, he, hθ]
        have := neg_mem (hcons i)
        rwa [neg_sub] at this
    have hB₀'m : (Ideal.span {ι x₁ - ι x₁'}).comap e ≤ maximalIdeal _ := fun z hz => by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hB₀m (Ideal.mem_comap.1 hz) (hu.map e)
    have hD : (Ideal.span {ι x₁ - ι x₁'}).comap e *
        derivativeIdealOfRing k ((completedIdeal I p).comap e) ≤ (completedIdeal I p).comap e :=
      calc _ ≤ (Ideal.span {ι x₁ - ι x₁'}).comap e *
            (derivativeIdealOfRing k (completedIdeal I p)).comap e :=
            Ideal.mul_mono_right (derivativeIdealOfRing_comap_le e _)
        _ ≤ (Ideal.span {ι x₁ - ι x₁'} * derivativeIdealOfRing k (completedIdeal I p)).comap e :=
            Ideal.le_comap_mul e
        _ ≤ _ := Ideal.comap_mono ((Ideal.mul_mono_left hB₀B).trans
            (IsMCInvariant.completedIdeal hX hdim hp hI h1))
    have htfae := Kollar.tfae_image_subst_eq_of_isAutomorphismOfFormOnePlus (k := k)
      (I := (completedIdeal I p).comap e) hB₀'m
    have h21 := htfae.out 2 1
    have himg := h21.1 hD _ hform
    rw [← MvPowerSeries.coe_substAlgHom
      (MMP.Flips.ResolutionInputs.hasSubst_of_mem_maximalIdeal hg), ← hθs] at himg
    exact map_eq_of_image_comap_eq e φ (fun f => by rw [he, he, hφF, hθ]) himg
  · -- (3)
    by_cases hpi : p ∈ (E.E i).support
    · obtain ⟨l, hl⟩ := hEy i hpi
      rw [completedIdeal, hl, Ideal.map_span, Ideal.map_span, Set.image_singleton,
        Set.image_singleton]
      exact congrArg (fun z => Ideal.span {z}) (hφy l)
    · rw [completedIdeal, (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 hpi,
        Ideal.map_top, Ideal.map_top]
  · -- (4)
    obtain ⟨f, rfl⟩ := hF'b.2 h
    rw [hφF]
    exact hB₀B (sub_mem_of_sub_X_mem F'.toRingHom F.toRingHom hB₀m
      (fun r => by simp [MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap]) hcons hF'm f)

end MMP.Resolution

end

/-!
## Logarithmic derivatives of derived transforms lie in derivatives of the transform

Let `X` be a smooth equidimensional scheme of finite type over a field `k` of characteristic
`0`, with every irreducible component of positive dimension, let `(I, m)` be a marked ideal sheaf
with `I` nonzero on every irreducible component, and let `Π = (X_i, Z_i)_{i ≤ r}` be a smooth
blow-up sequence of order `≥ m` starting with `(X, I, m)`, with marked ideals `(I_i, m)`. Let
`S ⊆ X` be a smooth hypersurface whose restriction `(S_i)` contains every centre, `Z_i ⊆ S_i`.
Then for `0 ≤ j ≤ s ≤ m` the transform `T_r(D^j I, m - j)` is an ideal sheaf on `X_r` and
`D^{s-j}(-log S_r)(T_r(D^j I, m - j)) ⊆ D^s(I_r)`. This is the inclusion "right side ⊆ left
side" of the decomposition of Kollár's Thm. 3.88.

The hypersurface `S_r ⊆ X_r` is the closed subscheme cut out by the kernel of the morphism
`Π.restrictHom S : S_r → X_r` of the restriction `Π|_S`, and the containment of the centres in
the `S_i` is `Π.CentersContainedIn S.subschemeι`. The transform `T_r(D^j I, m - j)` is
`derivedTransformJ`, whose value `some J` records that it is an ideal sheaf `J`; the
logarithmic derivative `D^{s-j}(-log S_r)` can only be applied to an ideal sheaf, so the
statement asserts this as well.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

namespace Proof_lem_kr3d_log_decomposition_right_in_left

open MMP.Resolution.ClosedBlowupSequence

section

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- `D(-log S)(J) ⊆ D(J')` for `J ⊆ J'`: a logarithmic derivation is a derivation. -/
private theorem logDerivativeIdeal_le_derivativeIdeal (S : X.IdealSheafData)
    {J J' : X.IdealSheafData} (h : J ≤ J') :
    logDerivativeIdeal sX S J ≤ derivativeIdeal sX J' := by
  refine sInf_le_sInf fun K hK W => le_trans ?_ (hK W)
  letI := MMP.Mori.sectionAlgebra sX W.1
  refine Ideal.span_mono ?_
  rintro _ ⟨δ, -, f, hf, rfl⟩
  exact ⟨δ, f, (Scheme.IdealSheafData.le_def.mp h W) hf, rfl⟩

/-- `D^r(-log S)(J) ⊆ D^r(J')` for `J ⊆ J'`. -/
private theorem higherLogDerivativeIdeal_le_higherDerivativeIdeal (S : X.IdealSheafData)
    {J J' : X.IdealSheafData} (h : J ≤ J') (r : ℕ) :
    higherLogDerivativeIdeal sX S J r ≤ higherDerivativeIdeal sX J' r := by
  induction r with
  | zero => exact h
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherLogDerivativeIdeal, Function.iterate_succ_apply']
    exact logDerivativeIdeal_le_derivativeIdeal sX S ih

end

end Proof_lem_kr3d_log_decomposition_right_in_left

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_log_decomposition_right_in_left in
/-- **Logarithmic derivatives of derived transforms** (Kollár Thm. 3.88, "right ⊆ left"). Let `X`
be smooth, equidimensional and of finite type over a field `k` of characteristic `0`, with every
irreducible component of positive dimension, let `a = (I, m)` be a marked ideal with `I` nonzero
on every irreducible component, `B` a smooth blow-up sequence of order `≥ m` starting with
`(X, I, m)`, and `S ⊆ X` a smooth hypersurface such that every centre of `B` lies in the
corresponding term of the restriction `B|_S`. Then for `j ≤ s ≤ m` the transform
`T_r(D^j I, m - j)` is an ideal sheaf `J` on `X_r` with `D^{s-j}(-log S_r)(J) ≤ D^s(I_r)`, where
`S_r` is cut out by the kernel of `B.restrictHom S` and `I_r` is the marked transform of
`(I, m)`. -/
@[mmp "lem_kr3d_log_decomposition_right_in_left"]
public theorem higherLogDerivativeIdeal_derivedTransformJ_le {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : Equidimensional X)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (a : MarkedIdeal X) (ha : IsNonzeroAtGenericPoints a.I)
    (B : ClosedBlowupSequence X) (hB : IsOrderGePlainSeq sX a B)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    (hZS : B.CentersContainedIn S.subschemeι)
    {j s : ℕ} (hjs : j ≤ s) (hs : s ≤ a.m) :
    ∃ J, derivedTransformJ sX B a j = some J ∧
      higherLogDerivativeIdeal (B.toBase ≫ sX) (B.restrictHom S).ker J (s - j) ≤
        higherDerivativeIdeal (B.toBase ≫ sX) (B.markedTransform a).I s := by
  obtain ⟨J, hJ, hJle⟩ := ClosedBlowupSequence.derivedTransformJ_le_higherDerivativeIdeal sX hX
    hdim a ha B hB j (hjs.trans hs)
  refine ⟨J, hJ, ?_⟩
  have h := higherLogDerivativeIdeal_le_higherDerivativeIdeal (B.toBase ≫ sX)
    (B.restrictHom S).ker hJle (s - j)
  rwa [Kollar.higherDerivativeIdeal_higherDerivativeIdeal, Nat.sub_add_cancel hjs] at h

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## Restriction to a smooth hypersurface commutes with transforms along a blow-up sequence

Let `X` be smooth, equidimensional of positive dimension and of finite type over a field `k` of
characteristic `0`, `S ⊆ X` a smooth hypersurface and `𝐁 = (X_i, Z_i)_{i ≤ r}` a smooth blow-up
sequence of order `≥ a` starting with `(X, J, a)`, `a ≥ 1`. If every centre `Z_i` lies in the
restriction `S_i ⊆ X_i` and `J|_S` is nonzero on every irreducible component of `S`, then the
restriction `𝐁|_S = (S_i, Z_i)` is a smooth blow-up sequence of order `≥ a` starting with
`(S, J|_S, a)`, and its marked ideals are the restrictions `(J_i|_{S_i}, a)` of those of `𝐁`
(iterating Kollár 3.62).

The `i`-th morphism `j_i : S_i → X_i` of `𝐁|_S` and the `i`-th marked ideal are read on the
truncation `𝐁.truncate i`, as in `MMP.Resolution.Kollar.isClosedImmersion_restrictHom_truncate`.
The `i`-th centre is read by splitting `𝐁 = 𝐁'.append (cons Z 𝐂)` with `𝐁'` of length `i`, so
that `X_i` is the target of `𝐁'` and `Z_i = Z`. The containment `Z_i ⊆ S_i` is asked
set-theoretically, `Z_i ⊆ j_i(S_i)`; as `Z_i` is smooth, hence reduced, this is the same as
the scheme-theoretic containment. Restriction `I ↦ I·𝒪_S` of ideal sheaves is the inverse image
ideal `Scheme.IdealSheafData.comap`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry MMP.Resolution MMP.Resolution.ClosedBlowupSequence

variable {k : Type u} [Field k]

namespace Proof_lem_kr3d_restriction_commutes_with_transform_sequence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Kollár 3.62 for one smooth blow-up: if `J` has order `≥ a` along the smooth centre `Z`,
the birational transform of `(J|_T, a)` along `Z|_T` is the restriction of that of `(J, a)`
along the canonical lift of `j`. -/
private theorem birationalTransform_comap_eq_of_orderAlongGE {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (j : T ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (J : X.IdealSheafData) (a : ℕ) (hord : OrderAlongGE J (Z.support : Set X) a) :
    (⟨J.comap j, a⟩ : MarkedIdeal T).birationalTransform (Z.comap j) =
      ⟨(MarkedIdeal.birationalTransform Z ⟨J, a⟩).I.comap (canonicalLift j Z), a⟩ :=
  Kollar.birationalTransform_comap_eq_comap_canonicalLift j Z ⟨J, a⟩
    (comap_le_comap_pow_of_stalk_le _ _ _ _ (stalk_le_pow_of_orderAlongGE sX hX Z hZ J a hord))

/-- Along a smooth blow-up sequence of order `≥ a`, restricting to `T` commutes with every
truncated marked transform (iterated Kollár 3.62). -/
private theorem markedTransform_truncate_pullback :
    ∀ {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (B : ClosedBlowupSequence X) (j : T ⟶ X)
      (J : X.IdealSheafData) (a : ℕ), B.IsOrderGePlainSeq sX ⟨J, a⟩ → ∀ i : ℕ,
      ((B.truncate i).pullback j).markedTransform ⟨J.comap j, a⟩ =
        ⟨((B.truncate i).markedTransform ⟨J, a⟩).I.comap ((B.truncate i).pullbackHom j), a⟩
  | _, _, _, .nil _, _, _, _, _, _ => rfl
  | _, _, _, .cons _ _, _, _, _, _, 0 => rfl
  | _, _, sX, .cons Z C, j, J, a, hB, i + 1 => by
    obtain ⟨hX, -, hZ, -, hord, hC⟩ := hB
    have ih := markedTransform_truncate_pullback (blowUpToBase Z ≫ sX) C (canonicalLift j Z)
      (MarkedIdeal.birationalTransform Z ⟨J, a⟩).I a hC i
    change ((C.truncate i).pullback (canonicalLift j Z)).markedTransform
        ((⟨J.comap j, a⟩ : MarkedIdeal _).birationalTransform (Z.comap j)) = _
    rw [birationalTransform_comap_eq_of_orderAlongGE sX hX j Z hZ J a hord]
    exact ih

/-- A smooth centre contained in the image of a closed immersion `j` contains its ideal. -/
private theorem ker_le_of_subset_range {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (j : T ⟶ X) [IsClosedImmersion j] (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hZT : (Z.support : Set X) ⊆ Set.range j) : j.ker ≤ Z := by
  have := Aux.isReduced_subscheme_of_isSmoothScheme sX Z hZ
  rw [← MMP.Mori.vanishingIdeal_support_eq_self Z]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 fun x hx => ?_
  show x ∈ (j.ker.support : Set X)
  rw [Scheme.Hom.support_ker]
  exact subset_closure (hZT hx)

/-- A closed immersion is smooth over a base exactly when the closed subscheme it cuts out is. -/
private theorem isSmoothScheme_comp_iff {T Y S : Scheme.{u}} (f : T ⟶ Y) [IsClosedImmersion f]
    (s : Y ⟶ S) :
    MMP.Mori.IsSmoothScheme (f ≫ s) ↔ MMP.Mori.IsSmoothScheme (f.ker.subschemeι ≫ s) := by
  change _ ↔ MMP.Mori.IsSmoothScheme (f.imageι ≫ s)
  constructor
  · intro h
    have := h.smooth
    rw [show f.imageι ≫ s = inv f.toImage ≫ f ≫ s by
      rw [IsIso.eq_inv_comp, ← Category.assoc, f.toImage_imageι]]
    exact MMP.Mori.isSmoothScheme_of_smooth inferInstance
  · intro h
    have := h.smooth
    rw [← f.toImage_imageι, Category.assoc]
    exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- The canonical lift of `e ≫ H ↪ X`, `e` an isomorphism, along a smooth centre containing the
smooth hypersurface `H` (Kollár 3.62 setting). -/
private theorem canonicalLift_iso_comp_smooth_hypersurface [CharZero k] {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (H : X.IdealSheafData)
    (hH : IsSmoothHypersurface sX H) (e : T ⟶ H.subscheme) [IsIso e]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZH : H ≤ Z) :
    MMP.Mori.IsSmoothScheme (canonicalLift (e ≫ H.subschemeι) Z ≫ blowUpToBase Z ≫ sX) ∧
      MMP.Mori.IsPureCodimOne (canonicalLift (e ≫ H.subschemeι) Z).ker.support := by
  obtain ⟨hL, -, hLs⟩ := ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hX H Z hH hZ hZH
  have := Kollar.isIso_canonicalLift e (Z.comap H.subschemeι)
  have hc := canonicalLift_comp_canonicalLift H.subschemeι e Z
  have hφ : canonicalLift (e ≫ H.subschemeι) Z =
      eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z e H.subschemeι)) ≫
        canonicalLift e (Z.comap H.subschemeι) ≫ canonicalLift H.subschemeι Z := by
    rw [hc]; simp
  rw [hφ, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso]
  refine ⟨?_, hLs.2⟩
  have h1 := ((isSmoothScheme_comp_iff _ _).2 hLs.1).smooth
  simp only [Category.assoc]
  exact MMP.Mori.isSmoothScheme_of_smooth inferInstance

/-- The canonical lift of a closed immersion onto a smooth hypersurface, along a smooth centre
inside it, is again a closed immersion onto a smooth hypersurface. -/
private theorem canonicalLift_smooth_hypersurface [CharZero k] {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (j : T ⟶ X) [IsClosedImmersion j]
    (hT : MMP.Mori.IsSmoothScheme (j ≫ sX)) (hTc : MMP.Mori.IsPureCodimOne j.ker.support)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hZT : (Z.support : Set X) ⊆ Set.range j) :
    MMP.Mori.IsSmoothScheme (canonicalLift j Z ≫ blowUpToBase Z ≫ sX) ∧
      MMP.Mori.IsPureCodimOne (canonicalLift j Z).ker.support := by
  have : Smooth sX := hX.smooth
  have h := canonicalLift_iso_comp_smooth_hypersurface sX hX j.ker
    ⟨(isSmoothScheme_comp_iff j sX).1 hT, hTc⟩ j.toImage Z hZ
    (ker_le_of_subset_range sX j Z hZ hZT)
  rwa [Scheme.Hom.toImage_imageι] at h

/-- The inverse image in `T` of a smooth centre inside the image of `j` is smooth. -/
private theorem isSmoothScheme_comap_subschemeι_comp {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (j : T ⟶ X) [IsClosedImmersion j]
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hZT : (Z.support : Set X) ⊆ Set.range j) :
    MMP.Mori.IsSmoothScheme ((Z.comap j).subschemeι ≫ j ≫ sX) := by
  have : Smooth sX := hX.smooth
  have hmap : ((Z.comap j).subschemeι ≫ j).ker = Z := by
    change (Z.comap j).map j = Z
    rw [Stacks.IdealSheaf.map_comap_of_isClosedImmersion,
      sup_eq_left.2 (ker_le_of_subset_range sX j Z hZ hZT)]
  rw [← Category.assoc, isSmoothScheme_comp_iff, hmap]
  exact hZ

/-- The order bound along a smooth centre passes to the restriction to `T` (Kollár 3.47). -/
private theorem orderAlongGE_comap {X T : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (j : T ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (J : X.IdealSheafData) (a : ℕ) (hord : OrderAlongGE J (Z.support : Set X) a) :
    OrderAlongGE (J.comap j) ((Z.comap j).support : Set T) a := by
  intro W hW
  have hηW : hW.1.1.genericPoint ∈ ((Z.comap j).support : Set T) :=
    closure_minimal hW.1.2 (Z.comap j).support.isClosed
      hW.1.1.isGenericPoint_genericPoint_closure.mem
  have hsupp : ∀ x : T, x ∈ ((Z.comap j).support : Set T) → j x ∈ (Z.support : Set X) := by
    intro x hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  have hjη := hsupp _ hηW
  have hm : IdealSheafData.stalk Z (j hW.1.1.genericPoint) ≤
      IsLocalRing.maximalIdeal _ :=
    IsLocalRing.le_maximalIdeal fun h =>
      ((IdealSheafData.stalk_eq_top_iff_notMem_support Z _).1 h) hjη
  have h1 : IdealSheafData.stalk (J.comap j) hW.1.1.genericPoint ≤
      IsLocalRing.maximalIdeal _ ^ a := by
    rw [IdealSheafData.stalk_comap]
    refine (Ideal.map_mono (stalk_le_pow_of_orderAlongGE sX hX Z hZ J a hord _)).trans ?_
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ((Ideal.map_mono hm).trans ?_) a
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact fun h => hx (isUnit_of_map_unit (j.stalkMap _).hom x h)
  exact le_iSup₂_of_le a h1 le_rfl

/-- On a smooth `T`, a centre along which an ideal nonzero at the generic points has order
`≥ 1` has no irreducible component which is a component of `T`. -/
private theorem hasComponentsOfPositiveCodim_of_orderAlongGE {T : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) (hT : MMP.Mori.IsSmoothScheme sT) (W I : T.IdealSheafData)
    (hI : IsNonzeroAtGenericPoints I) {a : ℕ} (ha : 1 ≤ a)
    (hord : OrderAlongGE I (W.support : Set T) a) :
    HasComponentsOfPositiveCodim (W.support : Set T) := by
  intro C hC
  have : Smooth sT := hT.smooth
  have hred : IsReduced T := by
    have h0 : MMP.Mori.IsSmoothScheme ((⊥ : T.IdealSheafData).subschemeι ≫ sT) :=
      MMP.Mori.isSmoothScheme_of_smooth inferInstance
    have := Aux.isReduced_subscheme_of_isSmoothScheme sT ⊥ h0
    exact isReduced_of_isOpenImmersion (inv (⊥ : T.IdealSheafData).subschemeι)
  by_contra hlt
  have h0 : codimension (irreducibleClosure hC.1.1) = 0 :=
    ENat.lt_one_iff_eq_zero.1 (not_le.1 hlt)
  rw [codimension_eq_coheight, Order.coheight_eq_zero] at h0
  have hη := hC.1.1.isGenericPoint_genericPoint_closure
  have hcomp : closure ({hC.1.1.genericPoint} : Set T) ∈ irreducibleComponents T := by
    rw [hη.def]
    refine ⟨hC.1.1.closure, fun S hS hle => ?_⟩
    have h1 := @h0 ⟨closure S, hS.closure, isClosed_closure⟩
      (show closure C ⊆ closure S from hle.trans subset_closure)
    exact subset_closure.trans (show closure S ⊆ closure C from h1)
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents (hx := hcomp)
  have hm := IsLocalRing.isField_iff_maximalIdeal_eq.1 hfield
  have hle : IdealSheafData.stalk I hC.1.1.genericPoint ≤ IsLocalRing.maximalIdeal _ ^ a :=
    (natCast_le_idealOrder_iff' _ a).1 (hord C hC)
  apply hI _ hcomp
  rw [eq_bot_iff, ← hm]
  exact hle.trans (Ideal.pow_le_self (by omega))

/-- The restriction claim along a closed immersion onto a smooth hypersurface. -/
private theorem isOrderGePlainSeq_pullback [CharZero k] :
    ∀ {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (B : ClosedBlowupSequence X) (j : T ⟶ X)
      [IsClosedImmersion j] (J : X.IdealSheafData) (a : ℕ), 1 ≤ a →
      B.IsOrderGePlainSeq sX ⟨J, a⟩ → MMP.Mori.IsSmoothScheme (j ≫ sX) →
      MMP.Mori.IsPureCodimOne j.ker.support → IsNonzeroAtGenericPoints (J.comap j) →
      (∀ (B' : ClosedBlowupSequence X) (Z : B'.target.IdealSheafData)
        (C : ClosedBlowupSequence (blowUp Z)), B = B'.append (cons Z C) →
          (Z.support : Set B'.target) ⊆ Set.range (B'.pullbackHom j)) →
      (B.pullback j).IsOrderGePlainSeq (j ≫ sX) ⟨J.comap j, a⟩
  | _, _, _, .nil _, _, _, _, _, _, hB, hT, _, hJT, _ => ⟨hT, hJT⟩
  | _, _, sX, .cons Z C, j, _, J, a, ha, hB, hT, hTc, hJT, hZS => by
    obtain ⟨hX, -, hZ, -, hord, hC⟩ := hB
    have hX' : Smooth sX := hX.smooth
    have hZT : (Z.support : Set _) ⊆ Set.range j := hZS (.nil _) Z C rfl
    have hordT := orderAlongGE_comap sX hX j Z hZ J a hord
    refine ⟨hT, hJT, isSmoothScheme_comap_subschemeι_comp sX hX j Z hZ hZT,
      hasComponentsOfPositiveCodim_of_orderAlongGE (j ≫ sX) hT _ _ hJT ha hordT, hordT, ?_⟩
    have h362 := birationalTransform_comap_eq_of_orderAlongGE sX hX j Z hZ J a hord
    have : IsClosedImmersion (canonicalLift j Z) :=
      MMP.Resolution.Bridges.isClosedImmersion_canonicalLift j Z
    obtain ⟨hT1, hT1c⟩ := canonicalLift_smooth_hypersurface sX hX j hT hTc Z hZ hZT
    have hJT1 : IsNonzeroAtGenericPoints
        ((MarkedIdeal.birationalTransform Z ⟨J, a⟩).I.comap (canonicalLift j Z)) := by
      have h := congrArg MarkedIdeal.I h362
      dsimp only at h
      rw [← h]
      intro η hη hbot
      refine isNonzeroAtGenericPoints_comap_blowUpToBase (Z.comap j) hJT η hη
        (eq_bot_iff.2 (hbot ▸ stalk_le_stalk_of_le (le_idealColon _ _) η))
    have ih := isOrderGePlainSeq_pullback (blowUpToBase Z ≫ sX) C (canonicalLift j Z)
      (MarkedIdeal.birationalTransform Z ⟨J, a⟩).I a ha hC hT1 hT1c hJT1
      (fun B' Z' C' h => hZS (cons Z B') Z' C' (by rw [h]; rfl))
    change (C.pullback (canonicalLift j Z)).IsOrderGePlainSeq
        (blowUpToBase (Z.comap j) ≫ j ≫ sX)
        ((⟨J.comap j, a⟩ : MarkedIdeal _).birationalTransform (Z.comap j))
    rw [h362, ← Category.assoc, ← canonicalLift_comp_blowUpToBase, Category.assoc]
    exact ih

end Proof_lem_kr3d_restriction_commutes_with_transform_sequence

namespace MMP.Resolution.ClosedBlowupSequence

open Proof_lem_kr3d_restriction_commutes_with_transform_sequence in
/-- **Restriction commutes with transforms along a sequence** (iterated Kollár 3.62). Let `X` be
smooth, equidimensional of positive dimension and of finite type over a field `k` of
characteristic `0`, `S ⊆ X` a smooth hypersurface, `(J, a)` a marked ideal with `a ≥ 1`, `J`
nonzero on every irreducible component of `X` and `J|_S` nonzero on every irreducible component
of `S`, and `B` a smooth blow-up sequence of order `≥ a` starting with `(X, J, a)` whose every
centre `Z_i` lies in the image of `j_i : S_i → X_i`. Then the restriction `B|_S` is a smooth
blow-up sequence of order `≥ a` starting with `(S, J|_S, a)`, and for every `i` its `i`-th marked
ideal is `(J_i|_{S_i}, a)`. -/
@[mmp "lem_kr3d_restriction_commutes_with_transform_sequence"]
public theorem IsOrderGePlainSeq.restrict {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hdim : ∃ n : ℕ, 0 < n ∧ ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n)
    {S : X.IdealSheafData} (hS : IsSmoothHypersurface sX S)
    {J : X.IdealSheafData} {a : ℕ} (ha : 1 ≤ a) (hJ : IsNonzeroAtGenericPoints J)
    (hJS : IsNonzeroAtGenericPoints (J.comap S.subschemeι))
    {B : ClosedBlowupSequence X} (hB : B.IsOrderGePlainSeq sX ⟨J, a⟩)
    (hZS : ∀ (B' : ClosedBlowupSequence X) (Z : B'.target.IdealSheafData)
      (C : ClosedBlowupSequence (blowUp Z)), B = B'.append (cons Z C) →
        (Z.support : Set B'.target) ⊆ Set.range (B'.restrictHom S)) :
    (B.restrict S).IsOrderGePlainSeq (S.subschemeι ≫ sX) ⟨J.comap S.subschemeι, a⟩ ∧
      ∀ i : ℕ, ((B.truncate i).restrict S).markedTransform ⟨J.comap S.subschemeι, a⟩ =
        ⟨((B.truncate i).markedTransform ⟨J, a⟩).I.comap ((B.truncate i).restrictHom S), a⟩ := by
  refine ⟨isOrderGePlainSeq_pullback sX B S.subschemeι J a ha hB hS.1 ?_ hJS hZS,
    markedTransform_truncate_pullback sX B S.subschemeι J a hB⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact hS.2

end MMP.Resolution.ClosedBlowupSequence

end

/-!
## The order of the maximal coefficient ideal

Let `X` be a smooth, equidimensional scheme of finite type over a field `k` of characteristic
zero, all of whose irreducible components have positive dimension, and let `I` be an ideal
sheaf, nonzero at the generic point of every irreducible component, whose maximal order
`m = maxord I` is a natural number `m ≥ 1`. For `s ≥ 1` the maximal coefficient ideal
`W_s(I)` has order `s` at every point where `I` has order `m`, and order `0` (it is the unit
ideal there) at every point where `I` has order less than `m`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution IsLocalRing

namespace Proof_lem_kr3e_order_of_maximal_coefficient_ideal

/-- `MC(I)^s ≤ W_s(I)`: the summand of `W_s(I)` at the vector `c` with `c_{m-1} = s` and all
other entries `0` is `MC(I)^s`. -/
private theorem maximalContactIdeal_pow_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    (s : ℕ) : maximalContactIdeal sX I ^ s ≤ maximalCoefficientIdeal sX I s := by
  unfold maximalCoefficientIdeal maximalContactIdeal
  rw [hm, ENat.toNat_coe]
  let j : Fin (m + 1) := ⟨m - 1, by omega⟩
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (c : Fin (m + 1) → ℕ)
    (_ : ((s : ℕ) : ℤ) ≤ (coefficientWeight m c : ℤ)) =>
      ∏ i : Fin (m + 1), higherDerivativeIdeal sX I (i : ℕ) ^ c i) (Pi.single j s) ?_)
  · rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp [j]
  · simp only [coefficientWeight]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
    simp [j, Nat.sub_sub_self hm1]

/-- The order of the unit ideal of a local ring is `0`. -/
private lemma idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases j with _ | j
  · rfl
  · exact absurd (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j)))
      (by simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)

/-- Upper bound: `ord_x W_s(I) ≤ s · ord_x MC(I)`, since `MC(I)^s ≤ W_s(I)`. -/
private theorem multAt_maximalCoefficientIdeal_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {m : ℕ} (hm1 : 1 ≤ m) (hm : maxOrder I = m)
    (s : ℕ) (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    multAt (maximalCoefficientIdeal sX I s) x ≤ s * multAt (maximalContactIdeal sX I) x :=
  multAt_pow x _ s ▸ Kollar.multAt_antitone (maximalContactIdeal_pow_le sX hm1 hm s) x

/-- Lower bound: at a point of maximal order `m`, `D^j I` has order `m - j`, so every summand
`∏_j (D^j I)^{c_j}` of `W_s(I)` has order at least `∑_j (m - j) c_j ≥ s`. -/
private theorem le_multAt_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) {I : X.IdealSheafData}
    {m : ℕ} (hm : maxOrder I = m) (s : ℕ) {x : X}
    (hx : multAt I x = m) : (s : ℕ∞) ≤ multAt (maximalCoefficientIdeal sX I s) x := by
  rw [multAt, natCast_le_idealOrder_iff']
  have hD (j : ℕ) : IdealSheafData.stalk (higherDerivativeIdeal sX I j) x ≤
      maximalIdeal (X.presheaf.stalk x) ^ (m - j) :=
    (natCast_le_idealOrder_iff' _ _).1 <| by
      change _ ≤ multAt _ x
      rw [multAt_higherDerivativeIdeal sX hdim I j x, hx, ENat.coe_sub]
  unfold maximalCoefficientIdeal
  rw [hm, ENat.toNat_coe, iSup_subtype', stalk_iSup]
  refine iSup_le fun ⟨c, hc⟩ => ?_
  rw [Aux.stalk_prod]
  calc ∏ j : Fin (m + 1), IdealSheafData.stalk (higherDerivativeIdeal sX I (j : ℕ) ^ c j) x
      ≤ ∏ j : Fin (m + 1), maximalIdeal (X.presheaf.stalk x) ^ ((m - j) * c j) :=
        Finset.prod_le_prod' fun j _ => by
          rw [Aux.stalk_pow, pow_mul]
          exact Ideal.pow_right_mono (hD j) _
    _ = maximalIdeal (X.presheaf.stalk x) ^ coefficientWeight m c := by
        rw [Finset.prod_pow_eq_pow_sum, coefficientWeight]
    _ ≤ maximalIdeal (X.presheaf.stalk x) ^ s := Ideal.pow_le_pow_right (by exact_mod_cast hc)

end Proof_lem_kr3e_order_of_maximal_coefficient_ideal

namespace MMP.Resolution

open Proof_lem_kr3e_order_of_maximal_coefficient_ideal in
/-- On a smooth, equidimensional scheme of finite type over a field of characteristic zero all of
whose irreducible components have positive dimension, let `I` be an ideal sheaf nonzero at the
generic point of every irreducible component with maximal order a natural number `m ≥ 1`, and
let `s ≥ 1`. Then at every point `x`, the maximal coefficient ideal
`maximalCoefficientIdeal sX I s` has order `s` if `multAt I x = m`, and order `0` if
`multAt I x < m`. -/
@[mmp "lem_kr3e_order_of_maximal_coefficient_ideal"]
public theorem multAt_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [QuasiCompact sX]
    (hX : Equidimensional X) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : maxOrder I = m) {s : ℕ} (hs : 1 ≤ s) (x : X) :
    (multAt I x = m → multAt (maximalCoefficientIdeal sX I s) x = s) ∧
      (multAt I x < m → multAt (maximalCoefficientIdeal sX I s) x = 0) := by
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
  have hle := multAt_maximalCoefficientIdeal_le sX hm1 hm s x
  refine ⟨fun hx => le_antisymm ?_ (le_multAt_maximalCoefficientIdeal sX hdim hm s hx),
    fun hx => nonpos_iff_eq_zero.1 ?_⟩
  · simpa [multAt_maximalContactIdeal_eq_one sX hX hI hm1 hm hx] using hle
  · have hu := stalk_maximalContactIdeal_eq_top_of_multAt_lt sX hX hdim hI (by simp [hm])
      (hm ▸ hx)
    simpa [multAt, hu, idealOrder_top] using hle

end MMP.Resolution

end

/-!
## The derivative of a maximal coefficient ideal (Kollár, Prop. 3.99(3))

On a smooth equidimensional scheme `X` of positive dimension over a field `k` of characteristic
zero, for an ideal sheaf `I` with `m = maxord I ≥ 1`, the first derivative of the maximal
coefficient ideal
of order `s + 1` is the maximal coefficient ideal of order `s`:
`D(W_{s+1}(I)) = W_s(I)` for every `s ≥ 0`.
-/

section

universe u

open AlgebraicGeometry CategoryTheory MMP.Resolution MMP.Resolution.Kollar

namespace Proof_lem_kr3e_derivative_of_maximal_coefficient_ideal

section Ring

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {m : ℕ} {D : ℕ → Ideal A}
  {Wt : ℤ → Ideal A}

variable (k) in
/-- In an algebra over a field of characteristic `0`, every nonzero natural number is a unit. -/
private theorem isUnit_natCast [CharZero k] {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  rw [← map_natCast (algebraMap k A)]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn)).map _

variable (Wt) in
/-- `J ⊆ W_a` and every derivative of `J` lies in `W_{a-1}`. -/
private def Good (δ : Derivation k A A) (J : Ideal A) (a : ℤ) : Prop :=
  J ≤ Wt a ∧ ∀ f ∈ J, δ f ∈ Wt (a - 1)

private theorem good_mul {δ : Derivation k A A}
    (hmul : ∀ s t, Wt s * Wt t ≤ Wt (s + t)) {J K : Ideal A} {a b : ℤ}
    (hJ : Good Wt δ J a) (hK : Good Wt δ K b) : Good Wt δ (J * K) (a + b) := by
  refine ⟨(Ideal.mul_mono hJ.1 hK.1).trans (hmul a b), fun f hf => ?_⟩
  refine Submodule.mul_induction_on hf (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    refine add_mem ?_ ?_
    · have := hmul a (b - 1) (Ideal.mul_mem_mul (hJ.1 hx) (hK.2 y hy))
      rwa [show a + (b - 1) = a + b - 1 by ring] at this
    · have := hmul b (a - 1) (Ideal.mul_mem_mul (hK.1 hy) (hJ.2 x hx))
      rwa [show b + (a - 1) = a + b - 1 by ring] at this
  · rw [map_add]
    exact add_mem hx hy

private theorem good_top {δ : Derivation k A A} (htop : ∀ s ≤ 0, Wt s = ⊤) :
    Good Wt δ ⊤ 0 :=
  ⟨(htop 0 le_rfl).ge, fun f _ => by rw [htop (0 - 1) (by norm_num)]; trivial⟩

private theorem good_pow {δ : Derivation k A A}
    (hmul : ∀ s t, Wt s * Wt t ≤ Wt (s + t)) (htop : ∀ s ≤ 0, Wt s = ⊤) {J : Ideal A} {a : ℤ}
    (hJ : Good Wt δ J a) (n : ℕ) : Good Wt δ (J ^ n) (n * a) := by
  induction n with
  | zero => simpa [Ideal.one_eq_top] using good_top htop
  | succ n ih =>
    rw [pow_succ, show ((n + 1 : ℕ) : ℤ) * a = n * a + a by push_cast; ring]
    exact good_mul hmul ih hJ

private theorem good_prod {δ : Derivation k A A} {ι : Type*}
    (hmul : ∀ s t, Wt s * Wt t ≤ Wt (s + t)) (htop : ∀ s ≤ 0, Wt s = ⊤) (F : ι → Ideal A)
    (a : ι → ℤ) (hF : ∀ i, Good Wt δ (F i) (a i)) (S : Finset ι) :
    Good Wt δ (∏ i ∈ S, F i) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top] using good_top htop
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact good_mul hmul (hF i) ih

/-- The hypotheses on the chain `D_j` and the ideals `W_s`. -/
private structure Chain (k : Type*) [Field k] [Algebra k A] (m : ℕ) (D : ℕ → Ideal A)
    (Wt : ℤ → Ideal A) : Prop where
  succ : ∀ j, D (j + 1) = derivativeIdealOfRing k (D j)
  top : D m = ⊤
  eq : ∀ s, Wt s = ⨆ (c : Fin (m + 1) → ℕ) (_ : s ≤ (coefficientWeight m c : ℤ)),
    ∏ j : Fin (m + 1), D j ^ c j
  mul : ∀ s t, Wt s * Wt t ≤ Wt (s + t)

variable (H : Chain k m D Wt)

include H

private theorem Chain.anti {s t : ℤ} (h : s ≤ t) : Wt t ≤ Wt s := by
  rw [H.eq, H.eq]
  exact iSup_mono fun c => iSup_mono' fun hc => ⟨h.trans hc, le_rfl⟩

private theorem Chain.eq_top {s : ℤ} (hs : s ≤ 0) : Wt s = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [H.eq]
  refine le_iSup_of_le 0 (le_iSup_of_le (by simpa [coefficientWeight] using hs) ?_)
  simp [Ideal.one_eq_top]

private theorem Chain.prod_le (c : Fin (m + 1) → ℕ) :
    ∏ j : Fin (m + 1), D j ^ c j ≤ Wt (coefficientWeight m c) := by
  rw [H.eq]
  exact le_iSup_of_le c (le_iSup_of_le le_rfl le_rfl)

private theorem Chain.le_of_le {j : ℕ} (hj : j ≤ m) : D j ≤ Wt ((m - j : ℕ) : ℤ) := by
  classical
  set e : Fin (m + 1) → ℕ := Pi.single ⟨j, by omega⟩ 1 with he
  have := H.prod_le e
  have hw : coefficientWeight m e = m - j := by
    simp [he, coefficientWeight, Pi.single_apply]
  have hp : ∏ i : Fin (m + 1), D i ^ e i = D j := by
    rw [Finset.prod_eq_single (⟨j, by omega⟩ : Fin (m + 1))]
    · simp [he]
    · intro b _ hb; simp [he, Pi.single_apply, hb, Ideal.one_eq_top]
    · simp
  rwa [hw, hp] at this

private theorem Chain.good (δ : Derivation k A A) {j : ℕ} (hj : j ≤ m) :
    Good Wt δ (D j) ((m - j : ℕ) : ℤ) := by
  refine ⟨H.le_of_le hj, fun f hf => ?_⟩
  have hδ : δ f ∈ D (j + 1) := by
    rw [H.succ]
    exact Ideal.subset_span ⟨δ, f, hf, rfl⟩
  rcases Nat.lt_or_ge j m with h | h
  · have := H.le_of_le (j := j + 1) h hδ
    rwa [show ((m - (j + 1) : ℕ) : ℤ) = ((m - j : ℕ) : ℤ) - 1 by omega] at this
  · rw [H.eq_top (by omega)]; trivial

/-- `D(W_{s+1}) ⊆ W_s`: the Leibniz rule. -/
private theorem Chain.derivative_le (s : ℤ) : derivativeIdealOfRing k (Wt (s + 1)) ≤ Wt s := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨δ, f, hf, rfl⟩
  rw [H.eq] at hf
  have key : ∀ c : Fin (m + 1) → ℕ, Good Wt δ (∏ j : Fin (m + 1), D j ^ c j)
      (coefficientWeight m c) := by
    intro c
    have := good_prod H.mul (fun s hs => H.eq_top hs) (fun j : Fin (m + 1) => D j ^ c j)
      (fun j => (c j : ℤ) * ((m - j : ℕ) : ℤ))
      (fun j => good_pow H.mul (fun s hs => H.eq_top hs) (H.good δ (by omega)) _) Finset.univ
    convert this using 1
    simp [coefficientWeight, mul_comm]
  induction hf using Submodule.iSup_induction' with
  | mem c f hf =>
    induction hf using Submodule.iSup_induction' with
    | mem hc f hf => exact H.anti (by omega) ((key c).2 f hf)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy

private theorem Chain.pow_mem {x : A} (hx : x ∈ Wt 1) (n : ℕ) : x ^ n ∈ Wt n := by
  induction n with
  | zero => rw [Nat.cast_zero, H.eq_top le_rfl]; trivial
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    exact H.mul n 1 (Ideal.mul_mem_mul ih hx)

/-- If `x ∈ W_1` and `δ` is a derivation, then `x^{s-t} (δx)^{t+1} W_t ⊆ D(W_{s+1})` for
`t ≤ s`. -/
private theorem Chain.mul_mem_derivative [CharZero k] {x : A} (hx : x ∈ Wt 1)
    (δ : Derivation k A A) (s : ℕ) : ∀ t ≤ s, ∀ g ∈ Wt t,
      x ^ (s - t) * δ x ^ (t + 1) * g ∈ derivativeIdealOfRing k (Wt ((s : ℤ) + 1)) := by
  set E := derivativeIdealOfRing k (Wt ((s : ℤ) + 1))
  have hE : ∀ y ∈ Wt ((s : ℤ) + 1), δ y ∈ E := fun y hy => Ideal.subset_span ⟨δ, y, hy, rfl⟩
  have hdiv : ∀ (n : ℕ) (y : A), n ≠ 0 → (n : A) * y ∈ E → y ∈ E := fun n _ hn =>
    (Ideal.unit_mul_mem_iff_mem _ (isUnit_natCast k hn)).mp
  intro t
  induction t with
  | zero =>
    intro _ g _
    refine hdiv (s + 1) _ (Nat.succ_ne_zero s) ?_
    have := E.mul_mem_left g (hE _ (by exact_mod_cast H.pow_mem hx (s + 1)))
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul] at this
    rw [Nat.sub_zero]
    convert this using 1
    ring
  | succ t ih =>
    intro ht g hg
    obtain ⟨N, hN⟩ : ∃ N, s - t = N + 1 := ⟨s - (t + 1), by omega⟩
    rw [show s - (t + 1) = N by omega]
    have hy : x ^ (N + 1) * g ∈ Wt ((s : ℤ) + 1) := by
      have := H.mul (N + 1 : ℕ) (t + 1 : ℕ) (Ideal.mul_mem_mul (H.pow_mem hx (N + 1)) hg)
      convert this using 2
      push_cast; omega
    have hδg : δ g ∈ Wt t := H.derivative_le t (Ideal.subset_span ⟨δ, g, by
      simpa using hg, rfl⟩)
    have h2 := ih (by omega) (δ g) hδg
    rw [hN] at h2
    have h3 := E.mul_mem_left (δ x ^ (t + 1)) (hE _ hy)
    refine hdiv (N + 1) _ (Nat.succ_ne_zero N) ?_
    have h4 := E.sub_mem h3 h2
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul] at h4
    convert h4 using 1
    push_cast
    ring

end Ring

/-! ### Ideal sheaves -/

section Sheaf

private theorem ideal_prod {X : Scheme.{u}} {ι : Type*} (S : Finset ι)
    (F : ι → X.IdealSheafData) (W : X.affineOpens) :
    (∏ i ∈ S, F i).ideal W = ∏ i ∈ S, (F i).ideal W := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top]; rfl
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, ih]

/-- If `u^n J(W) ⊆ K(W)` on an affine open `W`, then `J ⊆ K` on the basic open `D(u)`. -/
private theorem ideal_affineBasicOpen_le {X : Scheme.{u}} {J K : X.IdealSheafData}
    {W : X.affineOpens} {u : Γ(X, W)} {n : ℕ} (h : ∀ g ∈ J.ideal W, u ^ n * g ∈ K.ideal W) :
    J.ideal (X.affineBasicOpen u) ≤ K.ideal (X.affineBasicOpen u) := by
  rw [← J.map_ideal_basicOpen, ← K.map_ideal_basicOpen]
  refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
  have := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE (X.basicOpen_le u)).op).hom (h g hg)
  rw [map_mul, map_pow] at this
  exact (Ideal.unit_mul_mem_iff_mem _ ((X.toRingedSpace.isUnit_res_basicOpen u).pow n)).mp this

/-- The ideals of sections of `D^j(I)` and `W_s(I)` over an affine open form a `Chain`. -/
private theorem chain {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    (htop : higherDerivativeIdeal sX I (maxOrder I).toNat = ⊤) (W : X.affineOpens) :
    letI := MMP.Mori.sectionAlgebra sX W.1
    Chain k (maxOrder I).toNat (fun j => (higherDerivativeIdeal sX I j).ideal W)
      (fun s => (maximalCoefficientIdeal sX I s).ideal W) := by
  letI := MMP.Mori.sectionAlgebra sX W.1
  refine ⟨fun j => ?_, by simp only [htop]; rfl, fun s => ?_, fun s t => ?_⟩
  · rw [higherDerivativeIdeal_succ, derivativeIdeal_ideal]; rfl
  · simp only [maximalCoefficientIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    refine iSup_congr fun c => ?_
    by_cases h : s ≤ (coefficientWeight (maxOrder I).toNat c : ℤ)
    · simp only [h, iSup_pos, ideal_prod, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    · simp only [h, iSup_false, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  · simpa using Scheme.IdealSheafData.le_def.mp
      (Kollar.maximalCoefficientIdeal_mul_le sX I s t) W

/-- If `D^m(I) = 𝒪_X` with `m = maxord I ≥ 1`, then every point has an affine neighbourhood `W`
and a section `u` not vanishing at it with `u^{s+1} W_s(I)(W) ⊆ D(W_{s+1}(I))(W)`. -/
private theorem exists_basicOpen_pow_mul_mem {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat)
    (htop : higherDerivativeIdeal sX I (maxOrder I).toNat = ⊤) (s : ℕ) (p : X) :
    ∃ (W : X.affineOpens) (u : Γ(X, W)), p ∈ X.basicOpen u ∧
      ∀ g ∈ (maximalCoefficientIdeal sX I s).ideal W, u ^ (s + 1) * g ∈
        (derivativeIdeal sX (maximalCoefficientIdeal sX I ((s : ℤ) + 1))).ideal W := by
  have hMC : derivativeIdeal sX (maximalContactIdeal sX I) = ⊤ := by
    rw [maximalContactIdeal, ← higherDerivativeIdeal_succ, Nat.sub_add_cancel hm, htop]
  obtain ⟨W, hW, hpW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : X.Opens) from trivial)
  let W' : X.affineOpens := ⟨W, hW⟩
  letI := MMP.Mori.sectionAlgebra sX W
  have H := chain sX I htop W'
  have h1 : (1 : Γ(X, W)) ∈ sectionDerivativeIdeal sX (maximalContactIdeal sX I) W' := by
    rw [← derivativeIdeal_ideal, hMC]; trivial
  obtain ⟨_, ⟨δ, f, hf, rfl⟩, hu⟩ : ∃ g ∈ {g | ∃ δ : Derivation k Γ(X, W) Γ(X, W),
      ∃ f ∈ (maximalContactIdeal sX I).ideal W', δ f = g},
      g ∉ Ideal.comap (X.presheaf.germ W p hpW).hom (IsLocalRing.maximalIdeal _) := by
    by_contra! hall
    simpa [IsLocalRing.notMem_maximalIdeal] using (Ideal.span_le.mpr hall) h1
  have hf1 : f ∈ (maximalCoefficientIdeal sX I 1).ideal W' := by
    have := H.le_of_le (j := (maxOrder I).toNat - 1) (by omega) hf
    rwa [show (((maxOrder I).toNat - ((maxOrder I).toNat - 1) : ℕ) : ℤ) = 1 by omega] at this
  refine ⟨W', δ f, (X.mem_basicOpen _ p hpW).mpr
    (IsLocalRing.notMem_maximalIdeal.mp hu), fun g hg => ?_⟩
  rw [derivativeIdeal_ideal]
  have := H.mul_mem_derivative hf1 δ s s le_rfl g hg
  rwa [Nat.sub_self, pow_zero, one_mul] at this

end Sheaf

/-! ### The unit ideal `D^m(I) = 𝒪_X` -/

/-- On an equidimensional space of dimension at least one, every irreducible component has
positive dimension. -/
private theorem pos_of_equidimensional {X : Type*} [TopologicalSpace X]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X) :
    ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z := by
  intro Z hZ
  by_contra! h
  have h0 : topologicalKrullDim X ≤ 0 :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
      fun W hW => (hequi W hW Z hZ).trans_le h
  exact absurd (hdim.trans h0) (by decide)

private theorem multAt_le_toNat_maxOrder {X : Scheme.{u}} {I : X.IdealSheafData}
    (hne : maxOrder I ≠ ⊤) (x : X) : multAt I x ≤ (maxOrder I).toNat := by
  rw [ENat.coe_toNat hne]
  exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) x (Set.mem_univ x)

/-- On an equidimensional scheme of positive dimension, smooth over a field of characteristic
zero, `D^m(I) = 𝒪_X` for `m = maxord I` finite. -/
private theorem higherDerivativeIdeal_maxOrder_eq_top {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hne : maxOrder I ≠ ⊤) :
    higherDerivativeIdeal sX I (maxOrder I).toNat = ⊤ := by
  refine eq_top_of_maxOrder_lt_one ((iSup₂_le fun x _ => ?_).trans_lt zero_lt_one)
  rw [multAt_higherDerivativeIdeal sX (pos_of_equidimensional hequi hdim)]
  exact (tsub_eq_zero_of_le (multAt_le_toNat_maxOrder hne x)).le

end Proof_lem_kr3e_derivative_of_maximal_coefficient_ideal

namespace MMP.Resolution.Kollar

open Proof_lem_kr3e_derivative_of_maximal_coefficient_ideal in
/-- **Kollár, Prop. 3.99(3)**. Let `X` be a smooth equidimensional scheme of positive dimension
over a field `k` of characteristic zero and `I` an ideal sheaf with `m = maxord I ≥ 1`. Then
for every `s ≥ 0`, `D(W_{s+1}(I)) = W_s(I)`. -/
@[mmp "lem_kr3e_derivative_of_maximal_coefficient_ideal"]
public theorem derivativeIdeal_maximalCoefficientIdeal_succ {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) (s : ℕ) :
    derivativeIdeal sX (maximalCoefficientIdeal sX I ((s : ℤ) + 1)) =
      maximalCoefficientIdeal sX I s := by
  have htop := higherDerivativeIdeal_maxOrder_eq_top sX hequi hdim I
    fun h => by simp [h] at hm
  refine le_antisymm (Scheme.IdealSheafData.le_def.mpr fun W => ?_) ?_
  · letI := MMP.Mori.sectionAlgebra sX W.1
    rw [derivativeIdeal_ideal]
    exact (chain sX I htop W).derivative_le s
  choose W u hpu hu using exists_basicOpen_pow_mul_mem sX I hm htop s
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun p => X.affineBasicOpen (u p)) ?_
    (fun p => ideal_affineBasicOpen_le (hu p))
  exact eq_top_iff.mpr fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hpu p⟩

end MMP.Resolution.Kollar

end

/-!
## Maximal coefficient ideals of order a multiple of `lcm(2, …, m)` are D-balanced

Let `X` be a smooth, equidimensional scheme of positive dimension over a field `k` of
characteristic zero, and `I` an ideal sheaf on `X` with `m = maxord I ≥ 1`. Put
`L = lcm(2, …, m)` and `s = r L` with `r ≥ max(1, m - 1)`. Then the maximal coefficient ideal
`W_s(I)` is D-balanced: `(D^i W_s(I))^s ⊆ W_s(I)^{s-i}` for `0 ≤ i < s`.

Kollár states the result on a smooth variety. D-balancedness is a local condition, so the
statement is made for a smooth equidimensional scheme of positive dimension, which need not be
connected.
-/

section

universe u

open AlgebraicGeometry CategoryTheory MMP.Resolution.Kollar MMP.Resolution

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

namespace Proof_lem_kr3e_maximal_coefficient_ideal_d_balanced

private theorem maximalCoefficientIdeal_zero (I : X.IdealSheafData) :
    maximalCoefficientIdeal sX I 0 = ⊤ := by
  refine top_le_iff.mp (le_iSup_of_le 0 (le_iSup_of_le (by simp) ?_))
  simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
  exact le_of_eq rfl

private theorem maximalCoefficientIdeal_anti (I : X.IdealSheafData) {s t : ℤ} (h : s ≤ t) :
    maximalCoefficientIdeal sX I t ≤ maximalCoefficientIdeal sX I s := by
  unfold maximalCoefficientIdeal
  exact iSup_mono fun c => iSup_mono' fun h' => ⟨h.trans h', le_rfl⟩

private theorem maximalCoefficientIdeal_pow_le (I : X.IdealSheafData) (a : ℤ) (n : ℕ) :
    maximalCoefficientIdeal sX I a ^ n ≤ maximalCoefficientIdeal sX I (n * a) := by
  induction n with
  | zero => simp [maximalCoefficientIdeal_zero]
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ((maximalCoefficientIdeal_mul_le sX I _ _).trans ?_)
    exact le_of_eq (by congr 1; push_cast; ring)

/-- The weight inequality `(n - i) s ≤ n (s - i)` for `i ≤ n ≤ s`. -/
private theorem sub_mul_le_mul_sub {i n s : ℕ} (hi : i ≤ n) (hns : n ≤ s) :
    ((n - i : ℕ) : ℤ) * s ≤ n * ((s - i : ℕ) : ℤ) := by
  push_cast [hi, hi.trans hns]
  nlinarith

variable [CharZero k] [Smooth sX]

private theorem higherDerivativeIdeal_maximalCoefficientIdeal
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) (t : ℕ) :
    ∀ i ≤ t, higherDerivativeIdeal sX (maximalCoefficientIdeal sX I t) i =
      maximalCoefficientIdeal sX I ((t - i : ℕ) : ℤ) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    rw [higherDerivativeIdeal_succ, ih (by omega)]
    have : ((t - i : ℕ) : ℤ) = ((t - (i + 1) : ℕ) : ℤ) + 1 := by omega
    rw [this, derivativeIdeal_maximalCoefficientIdeal_succ sX hequi hdim I hm]

private theorem maxOrder_maximalCoefficientIdeal_le
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) (s : ℕ) :
    maxOrder (maximalCoefficientIdeal sX I s) ≤ s := by
  refine iSup₂_le fun x _ => ?_
  by_contra h
  rw [not_le, ← ENat.add_one_le_iff (ENat.coe_ne_top _)] at h
  have h' := (succ_le_multAt_iff_forall_mem_support sX _ s x).1 (by exact_mod_cast h) s le_rfl
  rw [higherDerivativeIdeal_maximalCoefficientIdeal sX hequi hdim I hm s s le_rfl,
    Nat.sub_self, Nat.cast_zero, maximalCoefficientIdeal_zero,
    Scheme.IdealSheafData.support_top] at h'
  exact h'

end Proof_lem_kr3e_maximal_coefficient_ideal_d_balanced

namespace MMP.Resolution.Kollar

open Proof_lem_kr3e_maximal_coefficient_ideal_d_balanced in
/-- **Kollár, Prop. 3.99(8)**. On a smooth equidimensional scheme of positive dimension over a
field of characteristic zero, for an ideal sheaf `I` with `m = maxord I ≥ 1`, `L = lcm(2, …, m)`
and `r ≥ max(1, m - 1)`, the maximal coefficient ideal `W_{rL}(I)` is D-balanced. -/
@[mmp "lem_kr3e_maximal_coefficient_ideal_d_balanced"]
public theorem isDBalanced_maximalCoefficientIdeal {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X)
    (I : X.IdealSheafData) (hm : 1 ≤ (maxOrder I).toNat) {r : ℕ}
    (hr : max 1 ((maxOrder I).toNat - 1) ≤ r) :
    IsDBalanced sX (maximalCoefficientIdeal sX I ((r * lcmUpTo (maxOrder I).toNat : ℕ) : ℤ)) := by
  set s : ℕ := r * lcmUpTo (maxOrder I).toNat
  intro i hi
  have hns := ENat.toNat_le_of_le_coe (maxOrder_maximalCoefficientIdeal_le sX hequi hdim I hm s)
  rw [higherDerivativeIdeal_maximalCoefficientIdeal sX hequi hdim I hm s i (by omega),
    maximalCoefficientIdeal_pow sX I hm r (by omega) (by omega)]
  refine (maximalCoefficientIdeal_pow_le sX I _ _).trans (maximalCoefficientIdeal_anti sX I ?_)
  exact sub_mul_le_mul_sub hi.le hns

end MMP.Resolution.Kollar

end
