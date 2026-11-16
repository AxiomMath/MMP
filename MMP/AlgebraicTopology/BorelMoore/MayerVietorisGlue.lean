module

public import MMP.AlgebraicTopology.BorelMoore.MayerVietorisCycles

/-!
# Exactness of the Borel–Moore Mayer–Vietoris sequence at `H_q A ⊕ H_q B`: gluing

Let `A`, `B` be open subsets of a Hausdorff space `Y`, `I = A ⊓ B`, and `S`, `T` disjoint closed
sets with `Y - B ⊆ interior S` and `Y - A ⊆ interior T` (as produced by `exists_mvSeparation`
when `A ∪ B = Y` and `Y` is normal). Put `K = (interior T)ᶜ ⊆ A` and `L = (interior S)ᶜ ⊆ B`:
closed sets covering `Y`, with `K ∩ L ⊆ I`. If `x` is a locally finite cycle of `A` and `y` one
of `B` whose restrictions to `I` are homologous, there is a cycle `z` of `Y` with `z|_A ~ x` and
`z|_B ~ y` (`exists_glue`).

**Construction.** Subdivide `x` for the cover `{A - S, A - T}`: `x = x_L + x_K + ∂ e` with `x_L`
supported in `L` and `x_K` in `K`; likewise `y = y_L + y_K + ∂ e'`. With `x|_I - y|_I = ∂ w`,
the chain `w' = w - e|_I + e'|_I` has `∂ w' = (x_L + x_K)|_I - (y_L + y_K)|_I`, and subdividing
`w'` for the cover `{I - S, I - T}` gives chains `W_L` in `L` and `W_K` in `K` with
`∂ w' = ∂ W_L + ∂ W_K`. Then
`g = x_K|_I - y_K|_I - ∂ W_K = y_L|_I - x_L|_I + ∂ W_L`
is supported in `K ∩ L`. Extending `x_K`, `y_L` and `g` by zero to chains `X_K`, `Y_L`, `G` of
`Y`, the chain `z = X_K + Y_L - G` is a cycle, and `z|_A = x_K + (Y_L - G)|_A`, where
`(Y_L - G)|_A` is supported in `L`, is `x_L` up to a boundary; similarly on `B`.

The comparison of `(Y_L - G)|_A` with `x_L` is made on `I`: the iterated restriction
`Y → A → I` and the direct one `Y → I` differ by the boundary of the restriction homotopy
(`directRestrictChainMap_sub_iterated_of_d`), which does not enlarge supports
(`IsSupportedIn.homotopyMap`); and a chain of `A` supported in `L` vanishes when its
restriction to `I` does (`eq_zero_of_subRestrict_eq_zero`).

## Main results

* `MMP.borelMooreHomology.IsSupportedIn.homotopyMap`.
* `MMP.borelMooreHomology.subRestrict_restrictChainMap_eq_sub_d`.
* `MMP.borelMooreHomology.exists_restrictChainMap_eq_add_d`.
* `MMP.borelMooreHomology.exists_glue`: exactness at `H_q A ⊕ H_q B`, in
  positive degree.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21, §3.3.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section glue

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {Y : TopCat.{u}} [T2Space Y]

/-- The homotopy between the direct and the iterated restriction does not enlarge supports. -/
lemma IsSupportedIn.homotopyMap (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {N : Set Y} {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M N c) :
    IsSupportedIn R M ((fun x : subOpens U U' ↦ x.1.1) ⁻¹' N : Set (TopCat.of (subOpens U U')))
      ((borelMooreHomology.homotopyMap R M U h n).hom c) := by
  intro τ hτ
  change kernelFun (homKernel U n) c.1 τ ≠ 0 at hτ
  obtain ⟨σ, hσ⟩ : ∃ σ, homKernel U n σ τ • c.1 σ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hτ (finsum_eq_zero_of_forall_eq_zero h')
  have := (isAdmissibleKernel_homKernel U h n).image_subset σ τ (smul_ne_zero_left hσ)
  intro x hx
  exact hc σ (smul_ne_zero_right hσ) (this ⟨x, hx, rfl⟩)

/-- For a chain `v` of `Y` whose boundary is supported in `U`, restricting `v` to `U` and then
to `U' ≤ U` is restricting `v` to `U'`, up to the boundary of the restriction homotopy. -/
lemma subRestrict_restrictChainMap_eq_sub_d (U : TopologicalSpace.Opens Y)
    {U' : TopologicalSpace.Opens Y} (h : U' ≤ U) {k : ℕ}
    {v : (borelMooreChainComplex R M Y).X (k + 1)}
    (hv : IsSupportedIn R M (U : Set Y) (((borelMooreChainComplex R M Y).d (k + 1) k).hom v)) :
    subRestrict R M U h (k + 1) (((restrictChainMap R M U).f (k + 1)).hom v) =
      ((restrictChainMap R M U').f (k + 1)).hom v -
        ((borelMooreChainComplex R M (TopCat.of U')).d (k + 1 + 1) (k + 1)).hom
          (((borelMooreHomology.chainMap R M (subOpensInv U h)
            (isProperMap_subOpensInv U h)).f (k + 1 + 1)).hom
            ((borelMooreHomology.homotopyMap R M U h (k + 1)).hom v)) := by
  set φ := borelMooreHomology.chainMap R M (subOpensMap U h) (isProperMap_subOpensMap U h)
  have hdir := directRestrictChainMap_sub_iterated_of_d (R := R) (M := M) h hv
  have hdir' : ((directRestrictChainMap R M U h).f (k + 1)).hom v =
      (φ.f (k + 1)).hom (((restrictChainMap R M U').f (k + 1)).hom v) := rfl
  have hit : ((iteratedRestrictChainMap R M U (U' := U')).f (k + 1)).hom v =
      ((restrictChainMap R M (subOpens U U')).f (k + 1)).hom
        (((restrictChainMap R M U).f (k + 1)).hom v) := rfl
  rw [hdir', hit] at hdir
  rw [subRestrict_apply, eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 hdir).symm, map_sub,
    chainMap_chainMap_of_comp_eq_id R M _ _ _ _ rfl, hom_f_d_apply]

/-- A chain of `U` supported in a set `L` with `L ∩ U ⊆ U'` vanishes if its restriction to `U'`
vanishes. -/
lemma eq_zero_of_subRestrict_eq_zero (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {L : Set Y} (hLU : L ∩ U ⊆ (U' : Set Y)) {n : ℕ}
    {c : (borelMooreChainComplex R M (TopCat.of U)).X n}
    (hc : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) c)
    (h0 : subRestrict R M U h n c = 0) : c = 0 := by
  have hc' : IsSupportedIn R M (subOpens U U' : Set (TopCat.of U)) c :=
    hc.mono fun z hz ↦ (mem_subOpens U).2 (hLU ⟨hz, z.2⟩)
  refine eq_zero_of_restrictChainMap hc' ?_
  rw [subRestrict_apply] at h0
  have := congrArg ((borelMooreHomology.chainMap R M (subOpensMap U h)
    (isProperMap_subOpensMap U h)).f n).hom h0
  rwa [chainMap_chainMap_of_comp_eq_id R M _ _ _ _ rfl, map_zero] at this

/-- A chain of `I ≤ U` supported in a closed set `K` of `Y` with `K ∩ U ⊆ I` is the restriction
of a chain of `U` supported in `K`. -/
theorem exists_subRestrict_eq_of_isSupportedIn {I U : TopologicalSpace.Opens Y} (h : I ≤ U)
    {K : Set Y} (hK : IsClosed K) (hKU : K ∩ U ⊆ (I : Set Y)) {n : ℕ}
    {w₁ : (borelMooreChainComplex R M (TopCat.of I)).X n}
    (hw₁ : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of I)) w₁) :
    ∃ a : (borelMooreChainComplex R M (TopCat.of U)).X n,
      IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of U)) a ∧
        subRestrict R M U h n a = w₁ := by
  set FU : Set (TopCat.of U) := Subtype.val ⁻¹' K
  have hFU : IsClosed FU := hK.preimage continuous_subtype_val
  have hFUs : FU ⊆ (subOpens U I : Set (TopCat.of U)) := fun z hz ↦
    (mem_subOpens U).2 (hKU ⟨hz, z.2⟩)
  have hw₁' : IsSupportedIn R M (Subtype.val ⁻¹' FU : Set (TopCat.of (subOpens U I)))
      (((borelMooreHomology.chainMap R M (subOpensMap U h)
        (isProperMap_subOpensMap U h)).f n).hom w₁) :=
    hw₁.chainMap _ _ (by rintro _ ⟨z, hz, rfl⟩; exact hz)
  obtain ⟨a, haF, ha⟩ := exists_restrictChainMap_eq hFU hFUs hw₁'
  refine ⟨a, haF, ?_⟩
  rw [subRestrict_apply, ha]
  exact chainMap_chainMap_of_comp_eq_id R M _ _ _ _ rfl n w₁

/-- **Comparison of a restriction through `I`.** Let `I ≤ U` be open and `L` closed with
`L ∩ U ⊆ I`. If a chain `v` of `Y` supported in `L`, with boundary supported in `U`, restricts on
`I` to `x₀|_I + ∂ W` for chains `x₀` of `U` and `W` of `I` supported in `L`, then
`v|_U = x₀ + ∂ a` for a chain `a` of `U`. -/
theorem exists_restrictChainMap_eq_add_d {I U : TopologicalSpace.Opens Y} (h : I ≤ U)
    {L : Set Y} (hL : IsClosed L) (hLU : L ∩ U ⊆ (I : Set Y)) {k : ℕ}
    {v : (borelMooreChainComplex R M Y).X (k + 1)} (hvL : IsSupportedIn R M L v)
    (hdv : IsSupportedIn R M (U : Set Y) (((borelMooreChainComplex R M Y).d (k + 1) k).hom v))
    {x₀ : (borelMooreChainComplex R M (TopCat.of U)).X (k + 1)}
    (hx₀ : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) x₀)
    {W : (borelMooreChainComplex R M (TopCat.of I)).X (k + 1 + 1)}
    (hW : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of I)) W)
    (hv : ((restrictChainMap R M I).f (k + 1)).hom v = subRestrict R M U h (k + 1) x₀ +
      ((borelMooreChainComplex R M (TopCat.of I)).d (k + 1 + 1) (k + 1)).hom W) :
    ∃ a : (borelMooreChainComplex R M (TopCat.of U)).X (k + 1 + 1),
      ((restrictChainMap R M U).f (k + 1)).hom v = x₀ +
        ((borelMooreChainComplex R M (TopCat.of U)).d (k + 1 + 1) (k + 1)).hom a := by
  set ψ := borelMooreHomology.chainMap R M (subOpensInv U h) (isProperMap_subOpensInv U h)
  set Hv := (borelMooreHomology.homotopyMap R M U h (k + 1)).hom v
  have hHv : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of I))
      ((ψ.f (k + 1 + 1)).hom Hv) :=
    (hvL.homotopyMap U h).chainMap _ _ (by rintro _ ⟨z, hz, rfl⟩; exact hz)
  obtain ⟨a, haL, ha⟩ := exists_subRestrict_eq_of_isSupportedIn h hL hLU (hW.sub hHv)
  refine ⟨a, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_subRestrict_eq_zero U h hLU ((hvL.restrictChainMap U).sub (hx₀.add haL.d_of)) ?_
  rw [map_sub, map_add, subRestrict_restrictChainMap_eq_sub_d U h hdv, hv, subRestrict_d, ha,
    map_sub]
  abel

variable {A B : TopologicalSpace.Opens Y} {S T : Set Y}

/-- **Gluing: exactness of the Borel–Moore Mayer–Vietoris sequence at `H_q A ⊕ H_q B`**, in
positive degree. If `x` is a cycle of `A`, `y` a cycle of `B` and `x|_{A ⊓ B} - y|_{A ⊓ B}` is a
boundary, there is a cycle `z` of `Y` with `z|_A - x` and `z|_B - y` boundaries. -/
theorem exists_glue (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T)
    (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T) {q : ℕ}
    {x : (borelMooreChainComplex R M (TopCat.of A)).X (q + 1)}
    (hx : ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom x = 0)
    {y : (borelMooreChainComplex R M (TopCat.of B)).X (q + 1)}
    (hy : ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom y = 0)
    {w : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1 + 1)}
    (hw : subRestrict R M A inf_le_left (q + 1) x - subRestrict R M B inf_le_right (q + 1) y =
      ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom w) :
    ∃ z : (borelMooreChainComplex R M Y).X (q + 1),
      ((borelMooreChainComplex R M Y).d (q + 1) q).hom z = 0 ∧
      (∃ a : (borelMooreChainComplex R M (TopCat.of A)).X (q + 1 + 1),
        ((restrictChainMap R M A).f (q + 1)).hom z = x +
          ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1 + 1) (q + 1)).hom a) ∧
      (∃ b : (borelMooreChainComplex R M (TopCat.of B)).X (q + 1 + 1),
        ((restrictChainMap R M B).f (q + 1)).hom z = y +
          ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1 + 1) (q + 1)).hom b) := by
  set K : Set Y := (interior T)ᶜ
  set L : Set Y := (interior S)ᶜ
  have hK : IsClosed K := isOpen_interior.isClosed_compl
  have hL : IsClosed L := isOpen_interior.isClosed_compl
  have hLB : L ⊆ (B : Set Y) := Set.compl_subset_comm.1 hBS
  have hKA : K ⊆ (A : Set Y) := Set.compl_subset_comm.1 hAT
  have hLKI : L ∩ K ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y) := fun p hp ↦
    ⟨hKA hp.2, hLB hp.1⟩
  have hLA : L ∩ A ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y) := fun p hp ↦
    ⟨hp.2, hLB hp.1⟩
  have hKB : K ∩ B ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y) := fun p hp ↦
    ⟨hKA hp.1, hp.2⟩
  set sA := subRestrict R M A (inf_le_left : A ⊓ B ≤ A)
  set sB := subRestrict R M B (inf_le_right : A ⊓ B ≤ B)
  -- splitting `x` and `y`
  obtain ⟨-, xL, xK, e, hxs, hxL, hxK, -, -⟩ := exists_isMVConn (R := R) (M := M) (I := A)
    hS hT hST (fun p hp ↦ hKA hp.2) x hx
  obtain ⟨-, yL, yK, e', hys, hyL, hyK, -, -⟩ := exists_isMVConn (R := R) (M := M) (I := B)
    hS hT hST (fun p hp ↦ hLB hp.1) y hy
  have hdxK : ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom xK =
      -((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom xL := by
    have := congrArg ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom hxs
    rw [hx, map_add, map_add, d_d_apply, add_zero] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hdyL : ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom yL =
      -((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom yK := by
    have := congrArg ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom hys
    rw [hy, map_add, map_add, d_d_apply, add_zero] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  -- the chain `w'` of `A ⊓ B`
  obtain ⟨w', hw'⟩ : ∃ w' : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1 + 1),
      w' = w - sA (q + 1 + 1) e + sB (q + 1 + 1) e' := ⟨_, rfl⟩
  have hdw' : ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom w' =
      sA (q + 1) xL + sA (q + 1) xK - (sB (q + 1) yL + sB (q + 1) yK) := by
    rw [hw', map_add, map_sub, ← hw, ← subRestrict_d, ← subRestrict_d, hxs, hys]
    simp only [map_add]
    abel
  -- subdividing `w'` for the cover `{I - S, I - T}`
  set 𝒰 := mvCover (A ⊓ B) S T
  set s : Set ((TopCat.toSSet.obj (TopCat.of ↥(A ⊓ B))).obj (op ⦋q + 1 + 1⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of ↥(A ⊓ B)))}
  obtain ⟨hwL, hwK⟩ := isSupportedIn_chainPart_mvCover (I := A ⊓ B) hS hT hST (M := M) w'
  have hsplit := chainPart_add_chainPart_compl R M s
    (((smallChainMapLF R M 𝒰).f (q + 1 + 1)).hom w')
  have hsAxL : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of ↥(A ⊓ B))) (sA (q + 1) xL) :=
    hxL.subRestrict A _
  have hsAxK : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of ↥(A ⊓ B))) (sA (q + 1) xK) :=
    hxK.subRestrict A _
  have hsByL : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of ↥(A ⊓ B))) (sB (q + 1) yL) :=
    hyL.subRestrict B _
  have hsByK : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of ↥(A ⊓ B))) (sB (q + 1) yK) :=
    hyK.subRestrict B _
  obtain ⟨WL, hWLdef⟩ : ∃ WL : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1 + 1),
      WL = (chainPart R M s).hom (((smallChainMapLF R M 𝒰).f (q + 1 + 1)).hom w') +
        (smallHomotopyMap R M 𝒰 (q + 1)).hom (sA (q + 1) xL - sB (q + 1) yL) := ⟨_, rfl⟩
  obtain ⟨WK, hWKdef⟩ : ∃ WK : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1 + 1),
      WK = (chainPart R M sᶜ).hom (((smallChainMapLF R M 𝒰).f (q + 1 + 1)).hom w') +
        (smallHomotopyMap R M 𝒰 (q + 1)).hom (sA (q + 1) xK - sB (q + 1) yK) := ⟨_, rfl⟩
  have hWL : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of ↥(A ⊓ B))) WL := by
    rw [hWLdef]
    exact hwL.add ((hsAxL.sub hsByL).smallHomotopyMap 𝒰)
  have hWK : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of ↥(A ⊓ B))) WK := by
    rw [hWKdef]
    exact hwK.add ((hsAxK.sub hsByK).smallHomotopyMap 𝒰)
  have hdW : ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom WL +
      ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom WK =
      sA (q + 1) xL + sA (q + 1) xK - (sB (q + 1) yL + sB (q + 1) yK) := by
    have hee := eq_smallChainMapLF_add_succ R M 𝒰 (q + 1) w'
    have := congrArg ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1)
      (q + 1)).hom hee
    rw [map_add, map_add, d_d_apply, add_zero, ← hsplit, hdw'] at this
    rw [hWLdef, hWKdef, map_add, map_add, map_sub, map_sub]
    rw [this]
    simp only [map_sub, map_add]
    abel
  -- the chain `g` of `A ⊓ B`, supported in `L ∩ K`
  obtain ⟨g, hgdef⟩ : ∃ g : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1),
      g = sA (q + 1) xK - sB (q + 1) yK -
        ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom WK :=
    ⟨_, rfl⟩
  have hg' : g = sB (q + 1) yL - sA (q + 1) xL +
      ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom WL := by
    rw [hgdef, ← sub_eq_zero]
    rw [← sub_eq_zero] at hdW
    rw [← neg_eq_zero, ← hdW]
    abel
  have hgK : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of ↥(A ⊓ B))) g := by
    rw [hgdef]
    exact (hsAxK.sub hsByK).sub hWK.d_of
  have hgL : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of ↥(A ⊓ B))) g := by
    rw [hg']
    exact (hsByL.sub hsAxL).add hWL.d_of
  -- extensions by zero
  obtain ⟨XK, hXK, hXKr⟩ := exists_restrictChainMap_eq hK hKA hxK
  obtain ⟨YL, hYL, hYLr⟩ := exists_restrictChainMap_eq hL hLB hyL
  obtain ⟨G, hG, hGr⟩ := exists_restrictChainMap_eq (hL.inter hK) hLKI
    (hgL.inter hgK : IsSupportedIn R M (Subtype.val ⁻¹' (L ∩ K) : Set (TopCat.of ↥(A ⊓ B))) g)
  have hXKI : ((restrictChainMap R M (A ⊓ B)).f (q + 1)).hom XK = sA (q + 1) xK := by
    rw [← hXKr, subRestrict_restrictChainMap_of_isSupportedIn A _ (hXK.mono hKA)]
  have hYLI : ((restrictChainMap R M (A ⊓ B)).f (q + 1)).hom YL = sB (q + 1) yL := by
    rw [← hYLr, subRestrict_restrictChainMap_of_isSupportedIn B _ (hYL.mono hLB)]
  -- supports of the boundaries
  have hdXK : IsSupportedIn R M (L ∩ K) (((borelMooreChainComplex R M Y).d (q + 1) q).hom XK) := by
    refine isSupportedIn_of_restrictChainMap A (hXK.mono hKA).d_of ?_
    rw [hom_f_d_apply, hXKr]
    refine IsSupportedIn.inter ?_ hxK.d_of
    rw [hdxK]
    exact hxL.d_of.neg
  have hdYL : IsSupportedIn R M (L ∩ K) (((borelMooreChainComplex R M Y).d (q + 1) q).hom YL) := by
    refine isSupportedIn_of_restrictChainMap B (hYL.mono hLB).d_of ?_
    rw [hom_f_d_apply, hYLr]
    refine IsSupportedIn.inter hyL.d_of ?_
    rw [hdyL]
    exact hyK.d_of.neg
  refine ⟨XK + YL - G, ?_, ?_, ?_⟩
  · -- `z` is a cycle
    refine eq_zero_of_restrictChainMap (V := A ⊓ B) (by
      rw [map_sub, map_add]
      exact ((hdXK.add hdYL).sub hG.d_of).mono hLKI) ?_
    rw [hom_f_d_apply, map_sub, map_add, hXKI, hYLI, hGr, hgdef, map_sub, map_sub, d_d_apply,
      sub_zero]
    have h0 : ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom (sB (q + 1) yL) +
        ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom (sB (q + 1) yK) =
          0 := by
      rw [← subRestrict_d, ← subRestrict_d, ← map_add, hdyL, neg_add_cancel, map_zero]
    rw [← h0]
    simp only [map_add, map_sub]
    abel
  · -- `z|_A ~ x`
    have hv : ((restrictChainMap R M (A ⊓ B)).f (q + 1)).hom (YL - G) =
        sA (q + 1) xL +
          ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom (-WL) := by
      rw [map_sub, hYLI, hGr, hg', map_neg]
      abel
    obtain ⟨a, ha⟩ := exists_restrictChainMap_eq_add_d (I := A ⊓ B) (U := A) inf_le_left hL hLA
      (hYL.sub (hG.mono inter_subset_left))
      (by rw [map_sub]; exact (hdYL.sub hG.d_of).mono fun p hp ↦ hKA hp.2) hxL hWL.neg hv
    refine ⟨a - e, ?_⟩
    rw [add_sub_assoc, map_add, ha, hXKr, hxs, map_sub]
    abel
  · -- `z|_B ~ y`
    have hv : ((restrictChainMap R M (A ⊓ B)).f (q + 1)).hom (XK - G) =
        sB (q + 1) yK +
          ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom WK := by
      rw [map_sub, hXKI, hGr, hgdef]
      abel
    obtain ⟨b, hb⟩ := exists_restrictChainMap_eq_add_d (I := A ⊓ B) (U := B) inf_le_right hK hKB
      (hXK.sub (hG.mono inter_subset_right))
      (by rw [map_sub]; exact (hdXK.sub hG.d_of).mono fun p hp ↦ hLB hp.1) hyK hWK hv
    refine ⟨b - e', ?_⟩
    have hz : XK + YL - G = YL + (XK - G) := by abel
    rw [hz, map_add, hb, hYLr, hys, map_sub]
    abel

end glue

end borelMooreHomology

end MMP
