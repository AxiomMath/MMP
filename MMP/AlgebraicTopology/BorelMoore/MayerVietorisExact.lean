module

public import MMP.AlgebraicTopology.BorelMoore.MayerVietoris

/-!
# Exactness of the Borel–Moore Mayer–Vietoris sequence at `H_{q+1}(A ∩ B)`

Let `A`, `B` be open subsets of a Hausdorff space `Y`, `I = A ⊓ B`, and `S`, `T` disjoint closed
sets with `Y - B ⊆ interior S`, `Y - A ⊆ interior T` (as produced by `exists_mvSeparation` when
`A ∪ B = Y` and `Y` is normal). If `w` is a cycle of `I` whose connecting chain `c`
(`IsMVConn`) is a boundary `∂ v` in `Y`, then `w` is homologous to `x|_I - y|_I` for cycles `x`
of `A` and `y` of `B` (`IsMVConn.exists_eq_sub_add_d`), the restrictions being read in `I`
through the homeomorphisms `subOpensHomeo` of `I` with its preimages in `A` and in `B`.

With `w = w₁ + w₂ + ∂ e`: `w₁` is supported off `interior S`, a closed subset of `A` inside the
preimage of `I`, so it extends to a chain `a` of `A`; likewise `w₂` to a chain `b` of `B`. Then
`x = a - v|_A` and `y = -b - v|_B` are cycles (their boundaries are supported in that preimage and
restrict to `0`, because the iterated and the direct restriction agree on chains supported in
`A`), and the chain homotopy between the iterated and the direct restriction
(`directRestrictChainMap_sub_succ`), which vanishes on chains supported in `A`
(`homotopyMap_eq_zero_of_isSupportedIn`), gives `x|_I - y|_I = w₁ + w₂ + ∂(⋯)`.

## Main definitions

* `MMP.borelMooreHomology.subRestrict`: restriction of chains from `U` to an open `U' ≤ U`, read
  in `U'`.

## Main results

* `MMP.borelMooreHomology.homotopyMap_eq_zero_of_isSupportedIn`: the homotopy between the direct
  and the iterated restriction vanishes on chains supported in `U`.
* `MMP.borelMooreHomology.iteratedRestrictChainMap_eq_of_isSupportedIn`: on chains
  supported in `U`, `(c|_U)|_{U'}` is `c|_{U'}` read in `U`.
* `MMP.borelMooreHomology.IsMVConn.exists_eq_sub_add_d`: exactness at
  `H_{q+1}(A ∩ B)`.

## References

* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
* [G. Bredon, *Sheaf Theory*][bredon1997], V.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

section push

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {X Z : TopCat.{u}}

/-- The push-forward of a chain supported in `N` is supported in any `N' ⊇ f '' N`. -/
lemma IsSupportedIn.chainMap (f : X ⟶ Z) (hf : IsProperMap f) {N : Set X} {N' : Set Z}
    (hNN' : f '' N ⊆ N') {n : ℕ} {c : (borelMooreChainComplex R M X).X n}
    (hc : IsSupportedIn R M N c) :
    IsSupportedIn R M N' (((borelMooreHomology.chainMap R M f hf).f n).hom c) := by
  intro σ hσ
  change pushforwardFun ((TopCat.toSSet.map f).app _) c.1 σ ≠ 0 at hσ
  obtain ⟨σ', hσ', rfl⟩ := support_pushforwardFun_subset _ c.1 hσ
  rw [singularSimplexImage_map]
  exact (image_mono (hc σ' hσ')).trans hNN'

variable (R M) in
/-- If `f ≫ g = 𝟙 X` for proper maps `f` and `g`, then pushing a chain forward along `f` and then
along `g` returns the chain. -/
lemma chainMap_chainMap_of_comp_eq_id (f : X ⟶ Z) (g : Z ⟶ X) (hf : IsProperMap f)
    (hg : IsProperMap g) (hfg : f ≫ g = 𝟙 X) (n : ℕ) (c : (borelMooreChainComplex R M X).X n) :
    ((borelMooreHomology.chainMap R M g hg).f n).hom
      (((borelMooreHomology.chainMap R M f hf).f n).hom c) = c := by
  have key : ∀ (k : X ⟶ X) (hk : IsProperMap k), k = 𝟙 X →
      borelMooreHomology.chainMap R M k hk = 𝟙 _ := by
    rintro k hk rfl
    exact chainMap_id R M
  have h := congrArg (fun φ ↦ (φ.f n).hom c)
    ((chainMap_comp R M f g hf hg).symm.trans (key _ _ hfg))
  simpa using h

end push

section iterated

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {Y : TopCat.{u}} [T2Space Y]
  {U : TopologicalSpace.Opens Y} {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)

/-- The homotopy between the direct and the iterated restriction vanishes on chains supported
in `U`. -/
lemma homotopyMap_eq_zero_of_isSupportedIn {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M (U : Set Y) c) : (homotopyMap R M U h n).hom c = 0 := by
  apply Subtype.ext
  funext ω
  change kernelFun (homKernel U n) c.1 ω = 0
  refine finsum_eq_zero_of_forall_eq_zero fun σ ↦ ?_
  by_cases h0 : c.1 σ = 0
  · rw [h0, smul_zero]
  have hσ : Finsupp.single (SingularCochain.simplexEquiv Y n σ) (1 : ℤ) ∈ inside ℤ n (U : Set Y) :=
    Finsupp.single_mem_supported ℤ _
      ((range_simplexEquiv σ).trans_subset (hc σ h0))
  have : homKernel U n σ ω = 0 := by
    rw [homKernel, homCoeff]
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    have hbad : ∀ N, badChain ℤ (U : Set Y) N n
        (Finsupp.single (SingularCochain.simplexEquiv Y n σ) 1) = 0 := by
      intro N
      induction N with
      | zero => rw [badChain_zero, badProj_eq_zero_of_mem_inside hσ]
      | succ N ih => rw [badChain_succ, ih, map_zero, map_zero]
    rw [hbad, map_zero]
    simp [restrFin]
  rw [this, zero_smul]

/-- On chains supported in `U`, the iterated restriction `(c|_U)|_{U'}` is the direct one. -/
lemma iteratedRestrictChainMap_eq_of_isSupportedIn {n : ℕ}
    {c : (borelMooreChainComplex R M Y).X n} (hc : IsSupportedIn R M (U : Set Y) c) :
    ((iteratedRestrictChainMap R M U (U' := U')).f n).hom c =
      ((directRestrictChainMap R M U h).f n).hom c := by
  symm
  rw [← sub_eq_zero]
  rcases n with _ | k
  · have := congrArg (fun φ ↦ φ.hom c) (directRestrictChainMap_sub_zero R M U h)
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply] at this
    rw [this, homotopyMap_eq_zero_of_isSupportedIn h hc, map_zero]
  · have := congrArg (fun φ ↦ φ.hom c) (directRestrictChainMap_sub_succ R M U h k)
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, ModuleCat.hom_add,
      LinearMap.add_apply, LinearMap.comp_apply] at this
    rw [this, homotopyMap_eq_zero_of_isSupportedIn h hc,
      homotopyMap_eq_zero_of_isSupportedIn h hc.d, map_zero, add_zero]

/-- For a chain `v` whose boundary is supported in `U`, the direct and the iterated restriction of
`v` differ by a boundary. -/
lemma directRestrictChainMap_sub_iterated_of_d {k : ℕ}
    {v : (borelMooreChainComplex R M Y).X (k + 1)}
    (hv : IsSupportedIn R M (U : Set Y) (((borelMooreChainComplex R M Y).d (k + 1) k).hom v)) :
    ((directRestrictChainMap R M U h).f (k + 1)).hom v -
        ((iteratedRestrictChainMap R M U (U' := U')).f (k + 1)).hom v =
      ((borelMooreChainComplex R M (TopCat.of (subOpens U U'))).d (k + 1 + 1) (k + 1)).hom
        ((homotopyMap R M U h (k + 1)).hom v) := by
  have := congrArg (fun φ ↦ φ.hom v) (directRestrictChainMap_sub_succ R M U h k)
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_comp, ModuleCat.hom_add,
    LinearMap.add_apply, LinearMap.comp_apply] at this
  rw [this, homotopyMap_eq_zero_of_isSupportedIn h hv, zero_add]

end iterated

section exact

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {Y : TopCat.{u}} [T2Space Y]

omit [T2Space Y] in
/-- The map `subOpensInv U h` from the preimage of `U'` in `U` to `U'` is proper. -/
lemma isProperMap_subOpensInv (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) : IsProperMap (subOpensInv U h) := by
  change IsProperMap (subOpensHomeo U h).symm
  exact (subOpensHomeo U h).symm.isProperMap

variable (R M) in
/-- The restriction of chains from `U` to `U' ≤ U`, read in `U'`: restrict to the preimage of
`U'` in `U`, then push forward along the homeomorphism with `U'`. -/
def subRestrict (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)
    (n : ℕ) :
    (borelMooreChainComplex R M (TopCat.of U)).X n →ₗ[R]
      (borelMooreChainComplex R M (TopCat.of U')).X n :=
  ((borelMooreHomology.chainMap R M (subOpensInv U h) (isProperMap_subOpensInv U h)).f n).hom ∘ₗ
    ((restrictChainMap R M (subOpens U U')).f n).hom

/-- `subRestrict R M U h n x` is the push-forward along `subOpensInv U h` of the restriction of
`x` to the preimage of `U'` in `U`. -/
lemma subRestrict_apply (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {n : ℕ} (x : (borelMooreChainComplex R M (TopCat.of U)).X n) :
    subRestrict R M U h n x =
      ((borelMooreHomology.chainMap R M (subOpensInv U h) (isProperMap_subOpensInv U h)).f n).hom
        (((restrictChainMap R M (subOpens U U')).f n).hom x) :=
  rfl

/-- **One half of exactness at `H_{q+1}(I)`.** Let `I ≤ U` be open, `K` closed with
`K ∩ U ⊆ I`, `w₁` a chain of `I` supported in `K`, and `c = ∂ v` a chain of `Y` supported in
`K ∩ I` with `c|_I = ∂ w₁`. Then there are a cycle `x` of `U` and a chain `α` of `I` with
`x|_I = w₁ - v|_I + ∂ α`, where `x|_I` is `subRestrict`. -/
theorem exists_cycle_subRestrict_eq {I U : TopologicalSpace.Opens Y} (h : I ≤ U) {K : Set Y}
    (hK : IsClosed K) (hKU : K ∩ U ⊆ (I : Set Y)) {q : ℕ}
    {w₁ : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    (hw₁ : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of I)) w₁)
    {c : (borelMooreChainComplex R M Y).X q} (hcK : IsSupportedIn R M K c)
    (hcI : IsSupportedIn R M (I : Set Y) c)
    (hcd : ((restrictChainMap R M I).f q).hom c =
      ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁)
    (v : (borelMooreChainComplex R M Y).X (q + 1))
    (hv : ((borelMooreChainComplex R M Y).d (q + 1) q).hom v = c) :
    ∃ (x : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1))
      (α : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1)),
      ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom x = 0 ∧
      subRestrict R M U h (q + 1) x = w₁ - ((restrictChainMap R M I).f (q + 1)).hom v +
        ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom α := by
  set FU : Set (TopCat.of U) := Subtype.val ⁻¹' K
  have hFU : IsClosed FU := hK.preimage continuous_subtype_val
  have hFUs : FU ⊆ (subOpens U I : Set (TopCat.of U)) := fun z hz ↦
    (mem_subOpens U).2 (hKU ⟨hz, z.2⟩)
  set φ := borelMooreHomology.chainMap R M (subOpensMap U h) (isProperMap_subOpensMap U h)
  set ψ := borelMooreHomology.chainMap R M (subOpensInv U h) (isProperMap_subOpensInv U h)
  have hψφ : ∀ n (z : (borelMooreChainComplex R M (TopCat.of I)).X n),
      (ψ.f n).hom ((φ.f n).hom z) = z := fun n z ↦
    chainMap_chainMap_of_comp_eq_id R M _ _ _ _ rfl n z
  set w₁' := (φ.f (q + 1)).hom w₁
  have hw₁' : IsSupportedIn R M (Subtype.val ⁻¹' FU : Set (TopCat.of (subOpens U I))) w₁' :=
    hw₁.chainMap _ _ (by rintro _ ⟨z, hz, rfl⟩; exact hz)
  obtain ⟨a, haF, ha⟩ := exists_restrictChainMap_eq hFU hFUs hw₁'
  set x := a - ((restrictChainMap R M U).f (q + 1)).hom v
  have hcA : IsSupportedIn R M FU (((restrictChainMap R M U).f q).hom c) :=
    hcK.restrictChainMap U
  have hdx : ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom x =
      ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom a -
        ((restrictChainMap R M U).f q).hom c := by
    rw [map_sub, ← hom_f_d_apply, hv]
  have hiter : ((restrictChainMap R M (subOpens U I)).f q).hom
      (((restrictChainMap R M U).f q).hom c) = (φ.f q).hom
        (((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁) := by
    have := iteratedRestrictChainMap_eq_of_isSupportedIn (R := R) (M := M) h (hcI.mono h)
    refine this.trans ?_
    change (φ.f q).hom (((restrictChainMap R M I).f q).hom c) = _
    rw [hcd]
  refine ⟨x, (ψ.f (q + 1 + 1)).hom ((homotopyMap R M U h (q + 1)).hom v), ?_, ?_⟩
  · rw [hdx]
    refine eq_zero_of_restrictChainMap (V := subOpens U I) ((haF.d_of.sub hcA).mono hFUs) ?_
    rw [map_sub, hom_f_d_apply, ha, hiter, hom_f_d_apply, sub_self]
  · have hdir := directRestrictChainMap_sub_iterated_of_d (R := R) (M := M) h (k := q) (v := v)
      (by rw [hv]; exact hcI.mono h)
    have hdir' : ((directRestrictChainMap R M U h).f (q + 1)).hom v =
        (φ.f (q + 1)).hom (((restrictChainMap R M I).f (q + 1)).hom v) := rfl
    have hit : ((iteratedRestrictChainMap R M U (U' := I)).f (q + 1)).hom v =
        ((restrictChainMap R M (subOpens U I)).f (q + 1)).hom
          (((restrictChainMap R M U).f (q + 1)).hom v) := rfl
    rw [hdir', hit] at hdir
    rw [subRestrict_apply, map_sub, ha, map_sub]
    change (ψ.f (q + 1)).hom w₁' - _ = _
    rw [hψφ, eq_sub_of_add_eq' (sub_eq_iff_eq_add.1 hdir).symm, map_sub, hψφ,
      ← hom_f_d_apply]
    abel

variable {A B : TopologicalSpace.Opens Y} {S T : Set Y}

/-- **Exactness of the Borel–Moore Mayer–Vietoris sequence at `H_{q+1}(A ∩ B)`.** If the
connecting chain `c` of a cycle `w` of `A ⊓ B` is a boundary `∂ v` in `Y`, then `w` is
homologous to `x|_{A ⊓ B} - y|_{A ⊓ B}` for cycles `x` of `A` and `y` of `B`. -/
theorem IsMVConn.exists_eq_sub_add_d (hBS : (B : Set Y)ᶜ ⊆ interior S)
    (hAT : (A : Set Y)ᶜ ⊆ interior T) {q : ℕ}
    {w : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1)}
    (hw : ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w = 0)
    {c : (borelMooreChainComplex R M Y).X q} (hc : IsMVConn R M (A ⊓ B) S T w c)
    (v : (borelMooreChainComplex R M Y).X (q + 1))
    (hv : ((borelMooreChainComplex R M Y).d (q + 1) q).hom v = c) :
    ∃ (x : (borelMooreChainComplex R M (TopCat.of A)).X (q + 1))
      (y : (borelMooreChainComplex R M (TopCat.of B)).X (q + 1))
      (u : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1 + 1)),
      ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom x = 0 ∧
      ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom y = 0 ∧
      w = subRestrict R M A inf_le_left (q + 1) x - subRestrict R M B inf_le_right (q + 1) y +
        ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1 + 1) (q + 1)).hom u := by
  obtain ⟨w₁, w₂, e₀, hw', h₁, h₂, hcI, hcd⟩ := hc
  have hd12 : ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w₁ =
      -((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w₂ := by
    have := congrArg ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom hw'
    rw [hw, map_add, map_add, d_d_apply, add_zero] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hcF : IsSupportedIn R M ((interior S)ᶜ ∩ (interior T)ᶜ) c := by
    refine isSupportedIn_of_restrictChainMap (A ⊓ B) hcI ?_
    rw [hcd]
    refine IsSupportedIn.inter h₁.d_of ?_
    rw [hd12]
    exact h₂.d_of.neg
  have hSB : (interior S)ᶜ ⊆ (B : Set Y) := compl_subset_comm.1 hBS
  have hTA : (interior T)ᶜ ⊆ (A : Set Y) := compl_subset_comm.1 hAT
  obtain ⟨x, α, hx, hxr⟩ := exists_cycle_subRestrict_eq (R := R) (M := M) (I := A ⊓ B)
    inf_le_left isOpen_interior.isClosed_compl (fun y hy ↦ ⟨hy.2, hSB hy.1⟩) h₁
    (hcF.mono inter_subset_left) hcI hcd v hv
  obtain ⟨y, β, hy, hyr⟩ := exists_cycle_subRestrict_eq (R := R) (M := M) (I := A ⊓ B)
    inf_le_right isOpen_interior.isClosed_compl (fun y hy ↦ ⟨hTA hy.1, hy.2⟩) h₂.neg
    (hcF.mono inter_subset_right) hcI (by rw [hcd, hd12, map_neg]) v hv
  refine ⟨x, y, e₀ - α + β, hx, hy, ?_⟩
  rw [hxr, hyr, hw', map_add, map_sub]
  abel

end exact

end borelMooreHomology

end MMP
