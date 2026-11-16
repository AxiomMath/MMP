module

public import MMP.AlgebraicTopology.BorelMoore.MayerVietorisExact

/-!
# Cycles of `A ∪ B` vanishing on `A` and on `B` are carried by `A ∩ B`

Let `A`, `B` be open subsets of a Hausdorff space `Y` and `S`, `T` disjoint closed sets with
`Y - B ⊆ interior S`, `Y - A ⊆ interior T`, so that `F = (interior S)ᶜ ∩ (interior T)ᶜ` is a closed
set inside `A ∩ B`. A cycle `z` of `Y` whose restrictions to `A` and to `B` are boundaries is
homologous to a cycle supported in `F` (`exists_isSupportedIn_eq_add_d`), and then to the
connecting chain (`IsMVConn`) of a cycle of `A ⊓ B` (`exists_isMVConn_of_restrictChainMap_eq_d`):
exactness of the Borel–Moore Mayer–Vietoris sequence at `H_q(A ∪ B)`. For the second step, one
more move on `A` and on `B` (`exists_eq_add_d_restrictChainMap_eq_d`) gives `g₁ ~ g` supported in
`F` with `g₀|_A = ∂ r`, `g₁|_B = ∂ r'`, `g₀ = g₁ + ∂ v₂`, `r` off `interior S`, `r'` off
`interior T`, `v₂` off `interior S`; then `w = (r|_I - v₂|_I) - r'|_I` is a cycle of `I` with
connecting chain `g₁`.

The step (`exists_isSupportedIn_inter_eq_add_d_of_restrictChainMap_add_eq_d`): let `K ⊆ U` and `L`
be closed, `O₁ ⊆ K`, `O₂ ⊆ L` open and covering `Y`, and `z = z₁ + z₂` with `z₁` in `L`, `z₂` in
`K` and `z|_U = ∂ a`. Subdividing `a` for the cover `{O₁, O₂}` of `U` splits `ρ a = p + r`, `p` in
`O₁` and `r` in `O₂`; then `z₂|_U - ∂ p - ∂ D (z₂|_U) = ∂ r + ∂ D (z₁|_U) - z₁|_U` lies in
`K ∩ L`, and since `p` and `D (z₂|_U)` are supported in the closed set `K ⊆ U` they extend to `Y`:
`z₂ = g + ∂(⋯)` with `g` supported in `K ∩ L`. Applied on `A` (moving `z₂` into `F`) and then on
`B` (moving all of the result into `F`), after subdividing `z` for the cover `{Y - S, Y - T}`.
## Main results

* `MMP.borelMooreHomology.exists_isSupportedIn_inter_eq_add_d_of_restrictChainMap_add_eq_d`: a
  chain in `K` bounding on `U` together with a chain in `L` is homologous to one in `K ∩ L`.
* `MMP.borelMooreHomology.exists_isSupportedIn_eq_add_d`: a cycle bounding on `A` and on `B` is
  homologous to one supported in `(interior S)ᶜ ∩ (interior T)ᶜ`.
* `MMP.borelMooreHomology.exists_isMVConn_of_restrictChainMap_eq_d`: exactness at
  `H_q(A ∪ B)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology Opposite Set Simplicial

universe u

namespace MMP

namespace borelMooreHomology

open SingularChain LocallyFiniteChain

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {Y : TopCat.{u}} [T2Space Y]

private theorem exists_isSupportedIn_d_eq_of_cover (U : TopologicalSpace.Opens Y)
    {K L O₁ O₂ : Set Y} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO₁K : O₁ ⊆ K) (hO₂L : O₂ ⊆ L)
    (hO : O₁ ∪ O₂ = univ) {q : ℕ} (a : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1)) :
    ∃ p r : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1),
      IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of U)) p ∧
      IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) r ∧
      ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom a =
        ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom p +
          ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom r +
          ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom
            ((smallHomotopyMap R M ({Subtype.val ⁻¹' O₁, Subtype.val ⁻¹' O₂} :
              Set (Set (TopCat.of U))) q).hom
              (((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom a)) := by
  set dU := fun k ↦ (borelMooreChainComplex R M (TopCat.of U)).d (k + 1) k
  set 𝒰 : Set (Set (TopCat.of U)) := {Subtype.val ⁻¹' O₁, Subtype.val ⁻¹' O₂}
  set Ψ := smallChainMapLF R M 𝒰
  set D := smallHomotopyMap R M 𝒰
  set s : Set ((TopCat.toSSet.obj (TopCat.of U)).obj (op ⦋q + 1⦌)) :=
    {τ | singularSimplexImage _ τ ⊆ (Subtype.val ⁻¹' O₁ : Set (TopCat.of U))}
  set p := (chainPart R M s).hom ((Ψ.f (q + 1)).hom a)
  set r := (chainPart R M sᶜ).hom ((Ψ.f (q + 1)).hom a)
  have hsplit : p + r = (Ψ.f (q + 1)).hom a := chainPart_add_chainPart_compl R M s _
  have hp : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of U)) p := fun τ hτ ↦
    (isSupportedIn_chainPart _ τ hτ).trans (preimage_mono hO₁K)
  have hr : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) r := by
    intro τ hτ
    obtain ⟨hτ', hΨτ⟩ := mem_of_chainPart_ne_zero hτ
    rcases smallChainMapLF_small_of_union R M (hO₁.preimage continuous_subtype_val)
        (hO₂.preimage continuous_subtype_val) (by
          ext x
          have : (x : Y) ∈ O₁ ∪ O₂ := hO ▸ mem_univ _
          simpa using this) (q + 1) a hΨτ with h | h
    · exact absurd h hτ'
    · exact h.trans (preimage_mono hO₂L)
  refine ⟨p, r, hp, hr, ?_⟩
  conv_lhs => rw [eq_smallChainMapLF_add_succ R M 𝒰 q a]
  rw [← hsplit]
  change (dU q).hom (p + r + (dU (q + 1)).hom ((D (q + 1)).hom a) + (D q).hom ((dU q).hom a)) = _
  simp only [dU, map_add, d_d_apply, add_zero]

/-- **Moving a chain into `K ∩ L`.** Let `K ⊆ U` and `L` be closed, `O₁ ⊆ K` and `O₂ ⊆ L` open
with `O₁ ∪ O₂ = Y`, and `z₁`, `z₂` chains supported in `L` and in `K` with `(z₁ + z₂)|_U = ∂ a`.
Then `z₂ = g + ∂ v` for a chain `g` supported in `K ∩ L`. -/
theorem exists_isSupportedIn_inter_eq_add_d_of_restrictChainMap_add_eq_d
    (U : TopologicalSpace.Opens Y) {K L O₁ O₂ : Set Y} (hK : IsClosed K) (hKU : K ⊆ U)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO₁K : O₁ ⊆ K) (hO₂L : O₂ ⊆ L) (hO : O₁ ∪ O₂ = univ)
    {q : ℕ} {z₁ z₂ : (borelMooreChainComplex R M Y).X q} (hz₁ : IsSupportedIn R M L z₁)
    (hz₂ : IsSupportedIn R M K z₂) (a : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1))
    (ha : ((restrictChainMap R M U).f q).hom (z₁ + z₂) =
      ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom a) :
    ∃ (g : (borelMooreChainComplex R M Y).X q) (v : (borelMooreChainComplex R M Y).X (q + 1)),
      IsSupportedIn R M (K ∩ L) g ∧
        z₂ = g + ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  obtain ⟨p, r, hp, hr, hda₀⟩ :=
    exists_isSupportedIn_d_eq_of_cover (R := R) (M := M) U hO₁ hO₂ hO₁K hO₂L hO a
  set dU := fun k ↦ (borelMooreChainComplex R M (TopCat.of U)).d (k + 1) k
  set 𝒰 : Set (Set (TopCat.of U)) := {Subtype.val ⁻¹' O₁, Subtype.val ⁻¹' O₂}
  set D := smallHomotopyMap R M 𝒰
  set ζ₁ := ((restrictChainMap R M U).f q).hom z₁
  set ζ₂ := ((restrictChainMap R M U).f q).hom z₂
  have hζ₁ : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) ζ₁ := hz₁.restrictChainMap U
  have hζ₂ : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of U)) ζ₂ := hz₂.restrictChainMap U
  have hda : (dU q).hom a = (dU q).hom p + (dU q).hom r + (dU q).hom ((D q).hom ζ₁) +
      (dU q).hom ((D q).hom ζ₂) := by
    rw [hda₀, ← ha, map_add ((restrictChainMap R M U).f q).hom]
    simp only [dU, map_add]
    rw [← add_assoc]
  set γ := ζ₂ - (dU q).hom p - (dU q).hom ((D q).hom ζ₂)
  have hγ' : γ = (dU q).hom r + (dU q).hom ((D q).hom ζ₁) - ζ₁ := by
    have h1 : ζ₁ + ζ₂ = (dU q).hom a := by rw [← map_add]; exact ha
    rw [hda] at h1
    simp only [γ]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h1
    rw [← h1]
    abel
  have hγL : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) γ := by
    rw [hγ']
    exact (hr.d_of.add (hζ₁.smallHomotopyMap 𝒰).d_of).sub hζ₁
  obtain ⟨p', hp'K, hp'⟩ := exists_restrictChainMap_eq hK hKU hp
  obtain ⟨δ', hδ'K, hδ'⟩ := exists_restrictChainMap_eq hK hKU (hζ₂.smallHomotopyMap 𝒰)
  set g := z₂ - ((borelMooreChainComplex R M Y).d (q + 1) q).hom p' -
    ((borelMooreChainComplex R M Y).d (q + 1) q).hom δ'
  have hgK : IsSupportedIn R M K g := (hz₂.sub hp'K.d_of).sub hδ'K.d_of
  have hgr : ((restrictChainMap R M U).f q).hom g = γ := by
    simp only [g, γ, map_sub, hom_f_d_apply, hp', hδ']
    rfl
  have hgL : IsSupportedIn R M L g :=
    isSupportedIn_of_restrictChainMap U (hgK.mono hKU) (hgr ▸ hγL)
  refine ⟨g, p' + δ', hgK.inter hgL, ?_⟩
  simp only [g, map_add]
  abel

/-- **Moving a chain into `K ∩ L`, keeping the bounding chain.** As
`exists_isSupportedIn_inter_eq_add_d_of_restrictChainMap_add_eq_d` with `z₁ = 0`: a chain `z`
supported in `K` with `z|_U = ∂ a` is `g + ∂ v` with `v` supported in `K`, `g` supported in
`K ∩ L`, and `g|_U = ∂ r` for a chain `r` of `U` supported in `L`. -/
theorem exists_eq_add_d_restrictChainMap_eq_d (U : TopologicalSpace.Opens Y)
    {K L O₁ O₂ : Set Y} (hK : IsClosed K) (hKU : K ⊆ U) (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hO₁K : O₁ ⊆ K) (hO₂L : O₂ ⊆ L) (hO : O₁ ∪ O₂ = univ) {q : ℕ}
    {z : (borelMooreChainComplex R M Y).X q} (hz : IsSupportedIn R M K z)
    (a : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1))
    (ha : ((restrictChainMap R M U).f q).hom z =
      ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom a) :
    ∃ (g : (borelMooreChainComplex R M Y).X q) (v : (borelMooreChainComplex R M Y).X (q + 1))
      (r : (borelMooreChainComplex R M (TopCat.of U)).X (q + 1)),
      IsSupportedIn R M (K ∩ L) g ∧ IsSupportedIn R M K v ∧
      IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) r ∧
      ((restrictChainMap R M U).f q).hom g =
        ((borelMooreChainComplex R M (TopCat.of U)).d (q + 1) q).hom r ∧
      z = g + ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  obtain ⟨p, r, hp, hr, hda₀⟩ :=
    exists_isSupportedIn_d_eq_of_cover (R := R) (M := M) U hO₁ hO₂ hO₁K hO₂L hO a
  set dU := fun k ↦ (borelMooreChainComplex R M (TopCat.of U)).d (k + 1) k
  set 𝒰 : Set (Set (TopCat.of U)) := {Subtype.val ⁻¹' O₁, Subtype.val ⁻¹' O₂}
  set D := smallHomotopyMap R M 𝒰
  set ζ := ((restrictChainMap R M U).f q).hom z
  have hζ : IsSupportedIn R M (Subtype.val ⁻¹' K : Set (TopCat.of U)) ζ := hz.restrictChainMap U
  have hda : (dU q).hom a = (dU q).hom p + (dU q).hom r + (dU q).hom ((D q).hom ζ) := by
    rw [hda₀, ← ha]
  obtain ⟨p', hp'K, hp'⟩ := exists_restrictChainMap_eq hK hKU hp
  obtain ⟨δ', hδ'K, hδ'⟩ := exists_restrictChainMap_eq hK hKU (hζ.smallHomotopyMap 𝒰)
  set g := z - ((borelMooreChainComplex R M Y).d (q + 1) q).hom p' -
    ((borelMooreChainComplex R M Y).d (q + 1) q).hom δ'
  have hgK : IsSupportedIn R M K g := (hz.sub hp'K.d_of).sub hδ'K.d_of
  have hgr : ((restrictChainMap R M U).f q).hom g = (dU q).hom r := by
    simp only [g, map_sub, hom_f_d_apply, hp', hδ']
    change ζ - (dU q).hom p - (dU q).hom ((D q).hom ζ) = (dU q).hom r
    have key : ζ = (dU q).hom p + (dU q).hom r + (dU q).hom ((D q).hom ζ) := ha.trans hda
    nth_rewrite 1 [key]
    abel
  have hgL : IsSupportedIn R M L g :=
    isSupportedIn_of_restrictChainMap U (hgK.mono hKU) (hgr ▸ hr.d_of)
  refine ⟨g, p' + δ', r, hgK.inter hgL, hp'K.add hδ'K, hr, hgr, ?_⟩
  simp only [g, map_add]
  abel

variable {A B : TopologicalSpace.Opens Y} {S T : Set Y}

/-- **A cycle of `Y` whose restrictions to `A` and to `B` are boundaries is homologous to a
cycle supported in `F = (interior S)ᶜ ∩ (interior T)ᶜ ⊆ A ∩ B`.** -/
theorem exists_isSupportedIn_eq_add_d (hS : IsClosed S) (hT : IsClosed T) (hST : Disjoint S T)
    (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T) {q : ℕ}
    (z : (borelMooreChainComplex R M Y).X q)
    (hz : ∀ m, m + 1 = q → ((borelMooreChainComplex R M Y).d q m).hom z = 0)
    (a : (borelMooreChainComplex R M (TopCat.of A)).X (q + 1))
    (ha : ((restrictChainMap R M A).f q).hom z =
      ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom a)
    (b : (borelMooreChainComplex R M (TopCat.of B)).X (q + 1))
    (hb : ((restrictChainMap R M B).f q).hom z =
      ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom b) :
    ∃ (g : (borelMooreChainComplex R M Y).X q) (v : (borelMooreChainComplex R M Y).X (q + 1)),
      IsSupportedIn R M ((interior S)ᶜ ∩ (interior T)ᶜ) g ∧
        z = g + ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  have hSB : (interior S)ᶜ ⊆ (B : Set Y) := compl_subset_comm.1 hBS
  have hTA : (interior T)ᶜ ⊆ (A : Set Y) := compl_subset_comm.1 hAT
  have hSi : Sᶜ ⊆ (interior S)ᶜ := compl_subset_compl.2 interior_subset
  have hTi : Tᶜ ⊆ (interior T)ᶜ := compl_subset_compl.2 interior_subset
  have hcov : Tᶜ ∪ Sᶜ = univ := by
    rw [← compl_inter, disjoint_iff_inter_eq_empty.1 hST.symm, compl_empty]
  -- subdivide `z` for the cover `{Y - S, Y - T}`
  set 𝒱 : Set (Set Y) := {Sᶜ, Tᶜ}
  set s : Set ((TopCat.toSSet.obj Y).obj (op ⦋q⦌)) := {τ | singularSimplexImage Y τ ⊆ Sᶜ}
  set z₁ := (chainPart R M s).hom (((smallChainMapLF R M 𝒱).f q).hom z)
  set z₂ := (chainPart R M sᶜ).hom (((smallChainMapLF R M 𝒱).f q).hom z)
  have hsplit : z₁ + z₂ = ((smallChainMapLF R M 𝒱).f q).hom z :=
    chainPart_add_chainPart_compl R M s _
  have hρ := sub_smallChainMapLF_eq_d_of_cycle R M 𝒱 z hz
  have hz₁ : IsSupportedIn R M (interior S)ᶜ z₁ := fun τ hτ ↦
    (isSupportedIn_chainPart _ τ hτ).trans hSi
  have hz₂ : IsSupportedIn R M (interior T)ᶜ z₂ := by
    intro τ hτ
    obtain ⟨hτ', hΨτ⟩ := mem_of_chainPart_ne_zero hτ
    rcases smallChainMapLF_small_of_union R M hS.isOpen_compl hT.isOpen_compl
        (by rw [union_comm]; exact hcov) q z hΨτ with h | h
    · exact absurd h hτ'
    · exact h.trans hTi
  set e := (smallHomotopyMap R M 𝒱 q).hom z
  have hze : z = z₁ + z₂ + ((borelMooreChainComplex R M Y).d (q + 1) q).hom e := by
    rw [hsplit, ← hρ]
    abel
  -- the first move, on `A`
  obtain ⟨g, v₁, hgF, hg⟩ :=
    exists_isSupportedIn_inter_eq_add_d_of_restrictChainMap_add_eq_d (R := R) (M := M) A
      isOpen_interior.isClosed_compl hTA hT.isOpen_compl hS.isOpen_compl hTi hSi hcov hz₁ hz₂
      (a - ((restrictChainMap R M A).f (q + 1)).hom e) (by
        rw [map_sub, ← hom_f_d_apply, ← ha, hze, map_add, map_add, map_add]
        abel)
  -- the second move, on `B`
  have hc₀ : IsSupportedIn R M (interior S)ᶜ (z₁ + g) := hz₁.add (hgF.mono inter_subset_right)
  have hz' : z = (z₁ + g) + ((borelMooreChainComplex R M Y).d (q + 1) q).hom (v₁ + e) := by
    rw [hze, hg, map_add]
    abel
  obtain ⟨g', v₂, -, hg'F, -, -, -, hg'⟩ :=
    exists_eq_add_d_restrictChainMap_eq_d (R := R) (M := M) B isOpen_interior.isClosed_compl hSB
      hS.isOpen_compl hT.isOpen_compl hSi hTi (by rw [union_comm]; exact hcov) hc₀
      (b - ((restrictChainMap R M B).f (q + 1)).hom (v₁ + e)) (by
        rw [map_sub, ← hom_f_d_apply, ← hb, hz']
        simp only [map_add]
        abel)
  refine ⟨g', v₂ + (v₁ + e), hg'F, ?_⟩
  rw [hz', hg']
  simp only [map_add]
  abel

/-- On chains supported in `U`, restricting to `U` and then to `U' ≤ U` (read in `U'`) is
restricting to `U'`. -/
lemma subRestrict_restrictChainMap_of_isSupportedIn (U : TopologicalSpace.Opens Y)
    {U' : TopologicalSpace.Opens Y} (h : U' ≤ U) {n : ℕ} {c : (borelMooreChainComplex R M Y).X n}
    (hc : IsSupportedIn R M (U : Set Y) c) :
    subRestrict R M U h n (((restrictChainMap R M U).f n).hom c) =
      ((restrictChainMap R M U').f n).hom c := by
  rw [subRestrict_apply]
  have := iteratedRestrictChainMap_eq_of_isSupportedIn (R := R) (M := M) h hc
  change ((borelMooreHomology.chainMap R M (subOpensInv U h) (isProperMap_subOpensInv U h)).f n).hom
    (((iteratedRestrictChainMap R M U (U' := U')).f n).hom c) = _
  rw [this]
  exact chainMap_chainMap_of_comp_eq_id R M (subOpensMap U h) (subOpensInv U h)
    (isProperMap_subOpensMap U h) (isProperMap_subOpensInv U h) rfl n _

/-- The restriction `subRestrict` from chains of `U` to chains of `U' ≤ U` commutes with the
boundary maps. -/
lemma subRestrict_d (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y} (h : U' ≤ U)
    {n : ℕ} (x : (borelMooreChainComplex R M (TopCat.of U)).X (n + 1)) :
    subRestrict R M U h n (((borelMooreChainComplex R M (TopCat.of U)).d (n + 1) n).hom x) =
      ((borelMooreChainComplex R M (TopCat.of U')).d (n + 1) n).hom
        (subRestrict R M U h (n + 1) x) := by
  rw [subRestrict_apply, subRestrict_apply, hom_f_d_apply, hom_f_d_apply]

/-- If a chain of `U` is supported in the preimage of `L`, then its restriction `subRestrict` to
`U' ≤ U` is supported in the preimage of `L` in `U'`. -/
lemma IsSupportedIn.subRestrict (U : TopologicalSpace.Opens Y) {U' : TopologicalSpace.Opens Y}
    (h : U' ≤ U) {L : Set Y} {n : ℕ} {x : (borelMooreChainComplex R M (TopCat.of U)).X n}
    (hx : IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U)) x) :
    IsSupportedIn R M (Subtype.val ⁻¹' L : Set (TopCat.of U')) (subRestrict R M U h n x) := by
  rw [subRestrict_apply]
  exact (hx.restrictChainMap (subOpens U U')).chainMap _ _ (by rintro _ ⟨z, hz, rfl⟩; exact hz)

/-- **Exactness of the Borel–Moore Mayer–Vietoris sequence at `H_q(A ∪ B)`.** A cycle `z` of `Y`
whose restrictions to `A` and to `B` are boundaries is homologous to the connecting chain of a
cycle of `A ⊓ B`. -/
theorem exists_isMVConn_of_restrictChainMap_eq_d (hS : IsClosed S) (hT : IsClosed T)
    (hST : Disjoint S T) (hBS : (B : Set Y)ᶜ ⊆ interior S) (hAT : (A : Set Y)ᶜ ⊆ interior T)
    {q : ℕ} (z : (borelMooreChainComplex R M Y).X q)
    (hz : ∀ m, m + 1 = q → ((borelMooreChainComplex R M Y).d q m).hom z = 0)
    (a : (borelMooreChainComplex R M (TopCat.of A)).X (q + 1))
    (ha : ((restrictChainMap R M A).f q).hom z =
      ((borelMooreChainComplex R M (TopCat.of A)).d (q + 1) q).hom a)
    (b : (borelMooreChainComplex R M (TopCat.of B)).X (q + 1))
    (hb : ((restrictChainMap R M B).f q).hom z =
      ((borelMooreChainComplex R M (TopCat.of B)).d (q + 1) q).hom b) :
    ∃ (w : (borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).X (q + 1))
      (c : (borelMooreChainComplex R M Y).X q) (v : (borelMooreChainComplex R M Y).X (q + 1)),
      ((borelMooreChainComplex R M (TopCat.of ↥(A ⊓ B))).d (q + 1) q).hom w = 0 ∧
      IsMVConn R M (A ⊓ B) S T w c ∧
        z = c + ((borelMooreChainComplex R M Y).d (q + 1) q).hom v := by
  have hSB : (interior S)ᶜ ⊆ (B : Set Y) := compl_subset_comm.1 hBS
  have hTA : (interior T)ᶜ ⊆ (A : Set Y) := compl_subset_comm.1 hAT
  have hFI : (interior S)ᶜ ∩ (interior T)ᶜ ⊆ ((A ⊓ B : TopologicalSpace.Opens Y) : Set Y) :=
    fun y hy ↦ ⟨hTA hy.2, hSB hy.1⟩
  have hSi : Sᶜ ⊆ (interior S)ᶜ := compl_subset_compl.2 interior_subset
  have hTi : Tᶜ ⊆ (interior T)ᶜ := compl_subset_compl.2 interior_subset
  have hcov : Tᶜ ∪ Sᶜ = univ := by
    rw [← compl_inter, disjoint_iff_inter_eq_empty.1 hST.symm, compl_empty]
  obtain ⟨g, v₀, hgF, hg⟩ := exists_isSupportedIn_eq_add_d hS hT hST hBS hAT z hz a ha b hb
  -- on `A`
  obtain ⟨g₀, v₁, r, hg₀F, -, hr, hg₀r, hg₀⟩ := exists_eq_add_d_restrictChainMap_eq_d (R := R)
    (M := M) A isOpen_interior.isClosed_compl hTA hT.isOpen_compl hS.isOpen_compl hTi hSi hcov
    (hgF.mono inter_subset_right) (a - ((restrictChainMap R M A).f (q + 1)).hom v₀) (by
      rw [map_sub, ← hom_f_d_apply, ← ha, hg, map_add]
      abel)
  -- on `B`
  obtain ⟨g₁, v₂, r', hg₁F, hv₂, hr', hg₁r, hg₁⟩ := exists_eq_add_d_restrictChainMap_eq_d (R := R)
    (M := M) B isOpen_interior.isClosed_compl hSB hS.isOpen_compl hT.isOpen_compl hSi hTi
    (by rw [union_comm]; exact hcov) (hg₀F.mono inter_subset_right)
    (b - ((restrictChainMap R M B).f (q + 1)).hom (v₀ + v₁)) (by
      rw [map_sub, ← hom_f_d_apply, ← hb, hg, hg₀]
      simp only [map_add]
      abel)
  have hg₀A : IsSupportedIn R M (A : Set Y) g₀ := hg₀F.mono (inter_subset_left.trans hTA)
  set I := A ⊓ B
  set dI := fun k ↦ (borelMooreChainComplex R M (TopCat.of I)).d (k + 1) k
  set w₁ := subRestrict R M A inf_le_left (q + 1) r - ((restrictChainMap R M I).f (q + 1)).hom v₂
  set w₂ := -subRestrict R M B inf_le_right (q + 1) r'
  have hdr : (dI q).hom (subRestrict R M A inf_le_left (q + 1) r) =
      ((restrictChainMap R M I).f q).hom g₀ := by
    rw [← subRestrict_d, ← hg₀r, subRestrict_restrictChainMap_of_isSupportedIn A inf_le_left hg₀A]
  have hdr' : (dI q).hom (subRestrict R M B inf_le_right (q + 1) r') =
      ((restrictChainMap R M I).f q).hom g₁ := by
    rw [← subRestrict_d, ← hg₁r, subRestrict_restrictChainMap_of_isSupportedIn B inf_le_right
      (hg₁F.mono (inter_subset_left.trans hSB))]
  have hdw₁ : (dI q).hom w₁ = ((restrictChainMap R M I).f q).hom g₁ := by
    simp only [w₁, map_sub, hdr]
    rw [← hom_f_d_apply]
    have : ((borelMooreChainComplex R M Y).d (q + 1) q).hom v₂ = g₀ - g₁ := by rw [hg₁]; abel
    rw [this, map_sub]
    abel
  refine ⟨w₁ + w₂, g₁, v₂ + v₁ + v₀, ?_, ⟨w₁, w₂, 0, by simp, ?_, ?_, hg₁F.mono hFI, hdw₁.symm⟩, ?_⟩
  · rw [map_add]
    change (dI q).hom w₁ + (dI q).hom w₂ = 0
    rw [hdw₁, map_neg, hdr', add_neg_cancel]
  · exact (hr.subRestrict A inf_le_left).sub (hv₂.restrictChainMap I)
  · exact (hr'.subRestrict B inf_le_right).neg
  · rw [hg, hg₀, hg₁]
    simp only [map_add]
    abel

end borelMooreHomology

end MMP
