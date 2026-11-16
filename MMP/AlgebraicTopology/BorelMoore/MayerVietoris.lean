module

public import MMP.AlgebraicTopology.BorelMoore.LongExactQuasiIso

/-!
# The Mayer–Vietoris connecting chain of Borel–Moore homology

Let `A`, `B` be open subsets covering a normal Hausdorff space `Y`, with intersection `I`.
Restriction of locally finite chains goes from `Y` to `A`, `B` and `I`, so the connecting map of
the Mayer–Vietoris sequence of Borel–Moore homology goes `H_{q+1}(A ∩ B) → H_q(A ∪ B)`.

**Separation.** By normality there are closed sets `S`, `T`, disjoint, with `Y - B ⊆ interior S`
and `Y - A ⊆ interior T` (`exists_mvSeparation`). A locally finite chain of `I` supported off
`interior S` is locally finite near `Y - B`, so it is a chain of `A`; one supported off
`interior T` is a chain of `B`; one supported in `F = (interior S)ᶜ ∩ (interior T)ᶜ`, a closed
subset of `Y` inside `I`, is the restriction of a chain of `Y` supported in `F`
(`exists_restrictChainMap_eq`).

**The connecting chain.** Subdividing a cycle `w` of `I` for the cover `{I - S, I - T}`
(`smallChainMapLF`) writes `w = w₁ + w₂ + ∂ e` with `w₁` off `interior S` and `w₂` off
`interior T`. Then `∂ w₁ = -∂ w₂` lies in `F`, so it is the restriction of a unique chain `c` of
`Y` supported in `I`; `c` is a cycle, the connecting chain of `w` (`IsMVConn`,
`exists_isMVConn`, `IsMVConn.d_eq_zero`). Its homology class depends only on that of `w`
(`IsMVConn.exists_sub_eq_d`): if `w₁ + w₂ = ∂ e` with `w₁`, `w₂` as above, then subdividing `e`
for the same cover gives a chain `x` of `I` supported in `F` with `∂ x = ∂ w₁`, and `c` is the
boundary of the extension of `x` to `Y` (`exists_eq_d_of_add_eq_d`).

The relation `IsMVConn` is stated for any open `I` containing `F`, and for chains with
coefficients in any module `M`, so that it serves both the Mayer–Vietoris step of Bredon's
induction for `lem_ext_c19_borel_moore_independent` and the second clause of
`thm_ext_c19_poincare_alexander_duality`.
## Main definitions

* `MMP.borelMooreHomology.IsMVConn`: `c` is a connecting chain of `w`.

## Main results

* `MMP.borelMooreHomology.exists_mvSeparation`: the separating closed sets.
* `MMP.borelMooreHomology.exists_isMVConn`: every cycle of `I` has a connecting
  chain.
* `MMP.borelMooreHomology.IsMVConn.d_eq_zero`: a connecting chain is a cycle.
* `MMP.borelMooreHomology.IsMVConn.exists_sub_eq_d`: the class of the connecting
  chain depends only on the class of `w`.

## References

* [G. Bredon, *Sheaf Theory*][bredon1997], V.
* [A. Borel, J. C. Moore, *Homology theory for locally compact spaces*][borelmoore1960], §3.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology Opposite Topology Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open LocallyFiniteChain

section separation

variable {Y : Type*} [TopologicalSpace Y] [NormalSpace Y]

/-- **Separation for an open cover by two sets.** If the open sets `A`, `B` cover a normal space,
there are disjoint closed sets `S`, `T` with `Y - B ⊆ interior S` and `Y - A ⊆ interior T`. -/
theorem exists_mvSeparation {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = univ) :
    ∃ S T : Set Y, IsClosed S ∧ IsClosed T ∧ Disjoint S T ∧ Bᶜ ⊆ interior S ∧
      Aᶜ ⊆ interior T := by
  have hBA : Bᶜ ⊆ A := fun x hx ↦ by
    have : x ∈ A ∪ B := hAB ▸ mem_univ x
    exact this.resolve_right hx
  obtain ⟨P, hP, hBP, hPA⟩ := normal_exists_closure_subset hB.isClosed_compl hA hBA
  have hAP : Aᶜ ⊆ (closure P)ᶜ := compl_subset_compl.2 hPA
  obtain ⟨Q, hQ, hAQ, hQP⟩ := normal_exists_closure_subset hA.isClosed_compl
    isClosed_closure.isOpen_compl hAP
  exact ⟨closure P, closure Q, isClosed_closure, isClosed_closure,
    Set.disjoint_left.2 fun _ hxP hxQ ↦ hQP hxQ hxP,
    hBP.trans (hP.subset_interior_iff.2 subset_closure),
    hAQ.trans (hQ.subset_interior_iff.2 subset_closure)⟩

end separation

section support

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {P : TopCat.{u}}

/-- A chain supported in `N` and in `N'` is supported in `N ∩ N'`. -/
lemma IsSupportedIn.inter {n : ℕ} {N N' : Set P} {c : (borelMooreChainComplex R M P).X n}
    (hc : IsSupportedIn R M N c) (hc' : IsSupportedIn R M N' c) :
    IsSupportedIn R M (N ∩ N') c := fun σ hσ ↦ subset_inter (hc σ hσ) (hc' σ hσ)

/-- A scalar multiple of a chain supported in `N` is supported in `N`. -/
lemma IsSupportedIn.smul {n : ℕ} {N : Set P} {c : (borelMooreChainComplex R M P).X n}
    (hc : IsSupportedIn R M N c) (r : R) : IsSupportedIn R M N (r • c) := fun σ hσ ↦
  hc σ fun h ↦ hσ (by change r • c.1 σ = 0; rw [h, smul_zero])

end support

section connecting

variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {Y : TopCat.{u}} [T2Space Y]

/-- The cover `{I - S, I - T}` of an open set `I`. -/
abbrev mvCover (I : TopologicalSpace.Opens Y) (S T : Set Y) : Set (Set (TopCat.of I)) :=
  {Subtype.val ⁻¹' Sᶜ, Subtype.val ⁻¹' Tᶜ}

/-- `c` is a *Mayer–Vietoris connecting chain* of the chain `w` of the open set `I`, for the
separating closed sets `S`, `T`: `w = w₁ + w₂ + ∂ e` with `w₁` supported off `interior S` and `w₂`
off `interior T`, and `c` is the chain of `Y` supported in `I` whose restriction to `I` is
`∂ w₁`. -/
def IsMVConn (I : TopologicalSpace.Opens Y) (S T : Set Y) {q : ℕ}
    (w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1))
    (c : (borelMooreChainComplex R M Y).X q) : Prop :=
  ∃ (w₁ w₂ : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1))
    (e : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1)),
    w = w₁ + w₂ + ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom e ∧
    IsSupportedIn R M (Subtype.val ⁻¹' (interior S)ᶜ : Set (TopCat.of I)) w₁ ∧
    IsSupportedIn R M (Subtype.val ⁻¹' (interior T)ᶜ : Set (TopCat.of I)) w₂ ∧
    IsSupportedIn R M (I : Set Y) c ∧
    ((restrictChainMap R M I).f q).hom c =
      ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁

variable {R M} {I : TopologicalSpace.Opens Y} {S T : Set Y}
  (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T)

omit [T2Space Y] in
include hS hT hST in
/-- Every simplex in the support of the subdivided chain `ρ c` of `I` lies in `I - S` or in
`I - T`. -/
lemma mvCover_singularSimplexImage_subset_or {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of I)).X n)
    {τ : (TopCat.toSSet.obj (TopCat.of I)).obj (op ⦋n⦌)}
    (hτ : (((smallChainMapLF R M (mvCover I S T)).f n).hom c).1 τ ≠ 0) :
    singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' Sᶜ ∨
      singularSimplexImage _ τ ⊆ Subtype.val ⁻¹' Tᶜ := by
  refine smallChainMapLF_small_of_union R M (hS.isOpen_compl.preimage continuous_subtype_val)
    (hT.isOpen_compl.preimage continuous_subtype_val) ?_ n c hτ
  ext x
  simp only [mem_union, mem_preimage, mem_compl_iff, mem_univ, iff_true]
  by_contra h
  push Not at h
  exact Set.disjoint_left.1 hST h.1 h.2

omit [T2Space Y] in
include hS hT hST in
/-- The part of `ρ c` off `S` is supported off `interior S`, the rest off `interior T`. -/
lemma isSupportedIn_chainPart_mvCover {n : ℕ}
    (c : (borelMooreChainComplex R M (TopCat.of I)).X n) :
    IsSupportedIn R M (Subtype.val ⁻¹' (interior S)ᶜ : Set (TopCat.of I))
        ((chainPart R M
          {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of I))}).hom
          (((smallChainMapLF R M (mvCover I S T)).f n).hom c)) ∧
      IsSupportedIn R M (Subtype.val ⁻¹' (interior T)ᶜ : Set (TopCat.of I))
        ((chainPart R M {τ | singularSimplexImage _ τ ⊆
          (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of I))}ᶜ).hom
          (((smallChainMapLF R M (mvCover I S T)).f n).hom c)) := by
  refine ⟨fun τ hτ ↦ (isSupportedIn_chainPart _ τ hτ).trans
    (preimage_mono (compl_subset_compl.2 interior_subset)), fun τ hτ ↦ ?_⟩
  obtain ⟨hτ', hΨτ⟩ := mem_of_chainPart_ne_zero hτ
  rcases mvCover_singularSimplexImage_subset_or hS hT hST c hΨτ with h | h
  · exact absurd h hτ'
  · exact h.trans (preimage_mono (compl_subset_compl.2 interior_subset))

include hS hT hST in
/-- **Existence of the connecting chain.** If `(interior S)ᶜ ∩ (interior T)ᶜ ⊆ I`, every cycle `w`
of `I` has a connecting chain. -/
theorem exists_isMVConn (hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ (I : Set Y)) {q : ℕ}
    (w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1))
    (hw : ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w = 0) :
    ∃ c, IsMVConn R M I S T w c := by
  set 𝒰 := mvCover I S T
  set Ψ := smallChainMapLF R M 𝒰
  set s : Set ((TopCat.toSSet.obj (TopCat.of I)).obj (op ⦋q + 1⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of I))}
  set w₁ := (chainPart R M s).hom ((Ψ.f (q + 1)).hom w)
  set w₂ := (chainPart R M sᶜ).hom ((Ψ.f (q + 1)).hom w)
  set e := (smallHomotopyMap R M 𝒰 (q + 1)).hom w
  have hsplit : w₁ + w₂ = (Ψ.f (q + 1)).hom w := chainPart_add_chainPart_compl R M s _
  have hρ := sub_smallChainMapLF_eq_d_of_cycle R M 𝒰 w (fun m hm ↦ by
    obtain rfl : m = q := by omega
    exact hw)
  have hw' : w = w₁ + w₂ +
      ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom e := by
    rw [hsplit, ← hρ]
    abel
  obtain ⟨h₁, h₂⟩ := isSupportedIn_chainPart_mvCover (I := I) hS hT hST (M := M) w
  have hd : ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁ =
      -((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₂ := by
    have := congrArg ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom hw'
    rw [hw, map_add, map_add, d_d_apply, add_zero] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hdF : IsSupportedIn R M (Subtype.val ⁻¹' ((interior S)ᶜ ∩ (interior T)ᶜ) :
      Set (TopCat.of I)) (((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁) := by
    refine IsSupportedIn.inter h₁.d_of ?_
    rw [hd]
    exact h₂.d_of.neg
  obtain ⟨c, hcF, hc⟩ := exists_restrictChainMap_eq
    (isOpen_interior.isClosed_compl.inter isOpen_interior.isClosed_compl) hFI hdF
  exact ⟨c, w₁, w₂, e, hw', h₁, h₂, hcF.mono hFI, hc⟩

/-- A connecting chain is a cycle. -/
theorem IsMVConn.d_eq_zero {q : ℕ} {w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1)}
    {c : (borelMooreChainComplex R M Y).X (q + 1)} (h : IsMVConn R M I S T w c) :
    ((borelMooreChainComplex R M Y).d (q + 1) q).hom c = 0 := by
  obtain ⟨w₁, -, -, -, -, -, hcI, hc⟩ := h
  refine eq_zero_of_restrictChainMap hcI.d_of ?_
  rw [hom_f_d_apply, hc, d_d_apply]

/-- The connecting relation is additive. -/
lemma IsMVConn.add {q : ℕ} {w w' : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c c' : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c)
    (h' : IsMVConn R M I S T w' c') : IsMVConn R M I S T (w + w') (c + c') := by
  obtain ⟨w₁, w₂, e, rfl, h₁, h₂, hc, hcd⟩ := h
  obtain ⟨w₁', w₂', e', rfl, h₁', h₂', hc', hcd'⟩ := h'
  refine ⟨w₁ + w₁', w₂ + w₂', e + e', ?_, h₁.add h₁', h₂.add h₂', hc.add hc', ?_⟩
  · simp only [map_add]
    abel
  · rw [map_add, map_add, hcd, hcd']

/-- The connecting relation is compatible with scalars. -/
lemma IsMVConn.smul {q : ℕ} {w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c) (r : R) :
    IsMVConn R M I S T (r • w) (r • c) := by
  obtain ⟨w₁, w₂, e, rfl, h₁, h₂, hc, hcd⟩ := h
  refine ⟨r • w₁, r • w₂, r • e, ?_, h₁.smul r, h₂.smul r, hc.smul r, ?_⟩
  · simp only [map_smul, smul_add]
  · rw [map_smul, map_smul, hcd]

/-- The connecting relation is compatible with negation. -/
lemma IsMVConn.neg {q : ℕ} {w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c) :
    IsMVConn R M I S T (-w) (-c) := by
  have := h.smul (-1)
  rwa [neg_one_smul, neg_one_smul] at this

/-- The connecting relation is compatible with subtraction. -/
lemma IsMVConn.sub {q : ℕ} {w w' : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c c' : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c)
    (h' : IsMVConn R M I S T w' c') : IsMVConn R M I S T (w - w') (c - c') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg

/-- `0` is a connecting chain of the chain `0`. -/
lemma isMVConn_zero {q : ℕ} : IsMVConn R M I S T
    (0 : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1))
    (0 : (borelMooreChainComplex R M Y).X q) :=
  ⟨0, 0, 0, by simp, isSupportedIn_zero, isSupportedIn_zero, isSupportedIn_zero, by simp⟩

/-- Changing `w` by a boundary keeps its connecting chains. -/
lemma IsMVConn.add_d {q : ℕ} {w : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c)
    (u : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1)) :
    IsMVConn R M I S T
      (w + ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom u) c := by
  obtain ⟨w₁, w₂, e, rfl, h₁, h₂, hc, hcd⟩ := h
  refine ⟨w₁, w₂, e + u, ?_, h₁, h₂, hc, hcd⟩
  rw [map_add]
  abel

include hS hT hST in
/-- **The connecting chain of a boundary is a boundary.** If `w₁ + w₂ = ∂ e` with `w₁` supported
off `interior S` and `w₂` off `interior T`, the chain `c` of `Y` supported in `I` with
`c|_I = ∂ w₁` is a boundary. -/
theorem exists_eq_d_of_add_eq_d (hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ (I : Set Y)) {q : ℕ}
    {w₁ w₂ : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    (e : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1))
    (he : w₁ + w₂ = ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom e)
    (h₁ : IsSupportedIn R M (Subtype.val ⁻¹' (interior S)ᶜ : Set (TopCat.of I)) w₁)
    (h₂ : IsSupportedIn R M (Subtype.val ⁻¹' (interior T)ᶜ : Set (TopCat.of I)) w₂)
    {c : (borelMooreChainComplex R M Y).X q} (hcI : IsSupportedIn R M (I : Set Y) c)
    (hc : ((restrictChainMap R M I).f q).hom c =
      ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1) q).hom w₁) :
    ∃ v : (borelMooreChainComplex R M Y).X (q + 1),
      c = ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  set dI := fun k ↦ (borelMooreChainComplex R M (TopCat.of I)).d (k + 1) k
  set 𝒰 := mvCover I S T
  set Ψ := smallChainMapLF R M 𝒰
  set D := smallHomotopyMap R M 𝒰
  set s : Set ((TopCat.toSSet.obj (TopCat.of I)).obj (op ⦋q + 1 + 1⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' Sᶜ : Set (TopCat.of I))}
  set e₁ := (chainPart R M s).hom ((Ψ.f (q + 1 + 1)).hom e)
  set e₂ := (chainPart R M sᶜ).hom ((Ψ.f (q + 1 + 1)).hom e)
  have hsplit : e₁ + e₂ = (Ψ.f (q + 1 + 1)).hom e := chainPart_add_chainPart_compl R M s _
  obtain ⟨he₁, he₂⟩ := isSupportedIn_chainPart_mvCover (I := I) hS hT hST (M := M) e
  have hee := eq_smallChainMapLF_add_succ R M 𝒰 (q + 1) e
  -- `∂ e = ∂ e₁ + ∂ e₂ + ∂ D w₁ + ∂ D w₂`
  have hde : (dI (q + 1)).hom e = (dI (q + 1)).hom e₁ + (dI (q + 1)).hom e₂ +
      (dI (q + 1)).hom ((D (q + 1)).hom w₁) + (dI (q + 1)).hom ((D (q + 1)).hom w₂) := by
    conv_lhs => rw [hee]
    rw [← hsplit, ← he]
    simp only [dI, map_add, d_d_apply]
    abel
  set x := w₁ - (dI (q + 1)).hom e₁ - (dI (q + 1)).hom ((D (q + 1)).hom w₁)
  have hx' : x = -(w₂ - (dI (q + 1)).hom e₂ - (dI (q + 1)).hom ((D (q + 1)).hom w₂)) := by
    have := he.trans hde
    simp only [x]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  have hxS : IsSupportedIn R M (Subtype.val ⁻¹' (interior S)ᶜ : Set (TopCat.of I)) x :=
    (h₁.sub he₁.d_of).sub (h₁.smallHomotopyMap 𝒰).d_of
  have hxT : IsSupportedIn R M (Subtype.val ⁻¹' (interior T)ᶜ : Set (TopCat.of I)) x := by
    rw [hx']
    exact ((h₂.sub he₂.d_of).sub (h₂.smallHomotopyMap 𝒰).d_of).neg
  have hdx : (dI q).hom x = (dI q).hom w₁ := by
    simp only [x, map_sub, dI, d_d_apply, sub_zero]
  obtain ⟨x', hx'F, hx'⟩ := exists_restrictChainMap_eq
    (isOpen_interior.isClosed_compl.inter isOpen_interior.isClosed_compl) hFI
    (hxS.inter hxT : IsSupportedIn R M (Subtype.val ⁻¹' ((interior S)ᶜ ∩ (interior T)ᶜ) :
      Set (TopCat.of I)) x)
  refine ⟨x', (sub_eq_zero.1 (eq_zero_of_restrictChainMap (hcI.sub (hx'F.mono hFI).d_of) ?_))⟩
  rw [map_sub, hom_f_d_apply, hx', hc]
  exact sub_eq_zero.2 hdx.symm

include hS hT hST in
/-- **The class of the connecting chain depends only on the class of `w`.** -/
theorem IsMVConn.exists_sub_eq_d (hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ (I : Set Y)) {q : ℕ}
    {w w' : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1)}
    {c c' : (borelMooreChainComplex R M Y).X q} (h : IsMVConn R M I S T w c)
    (h' : IsMVConn R M I S T w' c')
    (u : (borelMooreChainComplex R M (TopCat.of I)).X (q + 1 + 1))
    (hu : w - w' = ((borelMooreChainComplex R M (TopCat.of I)).d (q + 1 + 1) (q + 1)).hom u) :
    ∃ v : (borelMooreChainComplex R M Y).X (q + 1),
      c - c' = ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  obtain ⟨w₁, w₂, e, he, h₁, h₂, hc, hcd⟩ := h.sub h'
  refine exists_eq_d_of_add_eq_d hS hT hST hFI (u - e) ?_ h₁ h₂ hc hcd
  rw [map_sub, ← hu, he]
  abel

end connecting

end borelMooreHomology

end MMP
