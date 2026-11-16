module
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Threefold.SurfaceLocalRings

/-!
# Flips and abundance: Chow closures, crepant pull-back, the `ℝ`-Cartier locus and curves

Five lemmas from [KollarFlips].

*The Chow closure of an elliptic fibration.* Let `(Z₀, Z̄, Ū)` be a Chow closure of the log
elliptic fibration `f_U : U ⟶ Z` (`MMP.Flips.IsChowClosure`), with projections `g : Ū ⟶ Z̄` and
`u : Ū ⟶ X`. Then `u` is a projective birational surjective morphism mapping the open
`g⁻¹(Z₀)` isomorphically onto the dense open `f_U⁻¹(Z₀)` of `X`: the graph of `f_U` over `Z₀`
is a surjective section of `u|_{g⁻¹(Z₀)}`, hence its inverse. Moreover, if `E ⊆ Ū` is an
irreducible surface with `g(E)` a curve and `dim u(E) ≤ 1`, then every irreducible curve in
`u(E)` is `(K_X + Δ_X)`-trivial: a fibre `E ∩ g⁻¹(z̄)` over a closed point contains a curve,
whose image under `u` (finite on fibres of `g`) is all of `u(E)`.

*Crepant pull-back.* For a proper birational morphism `f : Y ⟶ X` of normal varieties and
`K_Y + D_Y = f^*(K_X + D)`, a divisor `E` over `Y` has the same discrepancy over `(X, D)` and
over `(Y, D_Y)`, because `g^* f^* = (f ∘ g)^*` on rational forms and on Cartier divisors.

*The `ℝ`-Cartier locus.* For `ℚ`-divisors `B₀, D₁, …, D_k` on a normal scheme, the set of
`b ∈ ℝ^k` with `B₀ + ∑ bᵢ Dᵢ` `ℝ`-Cartier, if nonempty, is a rational affine subspace
`b⁰ + ∑ⱼ ℝ wⱼ`, and `B₀ + ∑ bᵢ Dᵢ` is `ℚ`-Cartier on `b⁰ + ∑ⱼ ℚ wⱼ`. The proof decomposes a
real solution along a `ℚ`-basis of `ℝ`.

*Pluricanonical sections on a curve.* Let `C` be a smooth connected proper curve over an
algebraically closed field `k`, `Δ` a boundary on `C`, `m > 0` with `mΔ` integral and
`deg(K_C + Δ) > 0`, and `P` a closed point not in `⌊Δ⌋`. Then the global sections of
`L = 𝒪_C(12m(K_C + Δ))` surject onto `L(P) ⊕ ⨁_{Q ∈ ⌊Δ⌋} L(Q)`. With `S = {P} ∪ ⌊Δ⌋`, the
degree estimate `deg L(-S) > deg K_C` follows since `m · deg(K_C + Δ)` is a positive integer and
`#S ≤ 1 + deg Δ`; Riemann–Roch then gives, point by point, a section of `L(-T)` of exact order at
each new point, and the points of `S` are corrected one at a time.

## Main results

* `MMP.Flips.IsChowClosure.isProjectiveMorphism_snd`: `u` is projective, birational and
  surjective, and an isomorphism from `g⁻¹(Z₀)` onto the dense open `f_U⁻¹(Z₀)`.
* `MMP.Flips.IsChowClosure.intersectionNumber_eq_zero_of_dim_image_le_one`: curves in the image
  of a surface contracted by `u` are `(K_X + Δ_X)`-trivial.
* `MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff`: discrepancies are invariant under
  crepant pull-back.
* `MMP.Flips.exists_rat_affineSubspace_isCartierCombination`: the `ℝ`-Cartier locus is a
  rational affine subspace.
* `MMP.Flips.QWeilDivisor.IsBoundary.exists_mem_pluricanonicalSections_sub_vanishes`: global
  sections of `𝒪_C(12m(K_C + Δ))` surject onto the fibres at `P` and at the points of `⌊Δ⌋`.

## Implementation notes

`Ū` is the closed subscheme `Ubar.subscheme` of `Z̄ ×_k X`, and `g`, `u` are its inclusion
composed with the two projections. "`u` maps `g⁻¹(Z₀)` isomorphically onto `f_U⁻¹(Z₀)`" is
stated as: the restriction of `u` to the open `g⁻¹(j(Z₀))` is an open immersion with image
`f_U⁻¹(Z₀)`. In the second lemma the curve `g(E) ⊆ Z̄` is not named; the hypothesis is that
`g(E)` has dimension one (it is irreducible, and closed since `g` is proper).

The discrepancy is the relation `MMP.Flips.IsDiscrepancy`, so the equality of discrepancies is
an equivalence of the two relations for every real `a`; the valuation `ord_E` of `k(Y)` is a
valuation of `k(X)` through `f^* : k(X) → k(Y)`.

For the `ℝ`-Cartier locus the source takes `X` a normal variety and the `Dᵢ` prime; the argument
only uses that the `ℝ`-span of the Cartier divisors is the base change of their `ℚ`-span, so
`X` is any locally noetherian normal scheme and the `Dᵢ` are arbitrary `ℚ`-divisors indexed by
a finite type.

On the curve, `L = ω_C^{⊗12m}(12mΔ)` is the sheaf `MMP.Mori.pluricanonicalSections` of rational
`12m`-canonical forms `τ` with `ord_Γ(τ) + 12 coeff_Γ(G) ≥ 0`, where `G = mΔ`. A form lies in
`𝔪_Q L_Q` exactly when it is `0` or `ord_Q(τ) + 12 coeff_Q(G) ≥ 1`, so surjectivity onto the
fibres is stated as: for local sections `τ_Q` of `L` at the points `Q ∈ {P} ∪ ⌊Δ⌋` there is a
global section `s` with `s - τ_Q ∈ 𝔪_Q L_Q` at each of them. The points of `⌊Δ⌋` are the prime
divisors with coefficient `≥ 1`, and the degree of a divisor is the sum of its coefficients,
every closed point of `C` being `k`-rational.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], §2, 2.5, the
  proof of 12.2.11 (case 12.2.11.4) and the proof of 15.10
-/

universe u

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Flips

section ChowClosure

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open Limits

/-! ### The Chow closure is an isomorphism over the base -/

/-- A morphism from a reduced scheme whose image lies in the support of an ideal sheaf `I`
kills `I`. -/
private theorem le_ker_of_range_subset {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y)
    (I : Y.IdealSheafData) (h : Set.range f ⊆ I.support) : I ≤ f.ker := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp ?_
  intro x hx
  refine closure_minimal ?_ I.support.isClosed hx
  rintro _ ⟨y, -, rfl⟩
  exact h ⟨y, rfl⟩

/-- A morphism `f : U ⟶ Z` with every `f.app V : Γ(Z, V) ⟶ Γ(U, f⁻¹V)` an isomorphism has
nonempty preimages of nonempty opens. -/
private theorem nonempty_preimage_of_isIso_app {U Z : Scheme.{u}} (f : U ⟶ Z)
    (hf : ∀ V : Z.Opens, IsIso (f.app V)) (V : Z.Opens) (hV : (V : Set Z).Nonempty) :
    ((f ⁻¹ᵁ V : U.Opens) : Set U).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hbot : f ⁻¹ᵁ V = ⊥ := by ext x; simp [← SetLike.mem_coe, hne]
  haveI : Nonempty V := hV.to_subtype
  haveI := Scheme.component_nontrivial Z V
  haveI := hf V
  haveI : Subsingleton Γ(U, f ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := exists_pair_ne Γ(Z, V)
  exact hab ((ConcreteCategory.bijective_of_isIso (f.app V)).1 (Subsingleton.elim _ _))

/-- A separated morphism admitting a surjective section, with reduced source, is an
isomorphism: the section is a closed immersion that is surjective onto a reduced scheme. -/
private theorem isIso_of_surjective_section {V W : Scheme.{u}} [IsReduced W] (p : W ⟶ V)
    [IsSeparated p] (s : V ⟶ W) [Surjective s] (hs : s ≫ p = 𝟙 V) : IsIso p := by
  have : IsClosedImmersion (s ≫ p) := by rw [hs]; infer_instance
  have := IsClosedImmersion.of_comp s p
  have := isIso_of_isClosedImmersion_of_surjective s
  exact IsIso.inv_eq_of_hom_inv_id hs ▸ inferInstance

/-- A morphism of irreducible schemes that restricts to an open immersion of an open `W` onto a
nonempty open `O` is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_ι_comp {X Y : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (W : X.Opens) (O : Y.Opens)
    [IsOpenImmersion (W.ι ≫ f)] (hrange : Set.range (W.ι ≫ f).base = O)
    (hO : (O : Set Y).Nonempty) : IsBirationalMorphism f := by
  have hle : W ≤ f ⁻¹ᵁ O := fun w hw => (hrange ▸ ⟨⟨w, hw⟩, rfl⟩ : f.base w ∈ (O : Set Y))
  have hc := f.resLE_comp_ι hle
  have : IsOpenImmersion (f.resLE O W hle ≫ O.ι) := hc ▸ inferInstance
  have := IsOpenImmersion.of_comp (f.resLE O W hle) O.ι
  have : Surjective (f.resLE O W hle) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨w, hw⟩ : O.ι.base y ∈ Set.range (W.ι ≫ f).base := by
      rw [hrange, ← Scheme.Opens.range_ι O]; exact ⟨y, rfl⟩
    exact ⟨w, O.ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hc, hw])⟩
  obtain ⟨_, w, -, -⟩ := hrange ▸ hO
  exact isBirationalMorphism_of_isIso_resLE f W O ⟨_, w.2⟩ hO hle
    (isIso_of_mono_of_strongEpi _)

/-- Precomposing with an isomorphism does not change the range of the underlying map. -/
private theorem range_comp_base_of_isIso {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e]
    (g : B ⟶ C) : Set.range (e ≫ g).base = Set.range g.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso e.base).2.range_eq, Set.image_univ]

/-- A proper morphism whose image contains a dense set is surjective. -/
private theorem surjective_of_dense_subset_range {Y X : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    {S : Set X} (hS : Dense S) (hsub : S ⊆ Set.range f.base) : Surjective f :=
  ⟨fun x => (hS.closure_eq ▸ closure_minimal hsub f.isClosedMap.isClosed_range) (Set.mem_univ x)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {U : X.Opens}
  {Z Zbar : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} {sZbar : Zbar ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [LocallyOfFiniteType sX] [QuasiCompact sX]

private theorem IsChowClosure.nonempty_image_preimage {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    ((U.ι ''ᵁ (fU ⁻¹ᵁ Z₀) : X.Opens) : Set X).Nonempty := by
  obtain ⟨v, hv⟩ := nonempty_preimage_of_isIso_app fU
    h.isLogEllipticFiberSpace.isContraction.isIso_app Z₀ h.nonempty
  exact ⟨U.ι.base v, v, hv, rfl⟩

private theorem IsChowClosure.isProjectiveMorphism_subschemeι_snd {K : Divisor X}
    {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    IsProjectiveMorphism (Ubar.subschemeι ≫ pullback.snd sZbar sX) := by
  obtain ⟨n, i, hi, he⟩ := h.isProjectiveVariety.isProjective.baseChange sX
  exact ⟨n, Ubar.subschemeι ≫ i, inferInstance, by rw [Category.assoc, he]⟩

/-- **The Chow closure is an isomorphism over `Z₀`** (FA, proof of 15.10). For a Chow closure
`(Z₀, Z̄, Ū)` of `f_U` (`MMP.Flips.IsChowClosure`), the second projection `u : Ū ⟶ X` is a
projective, birational and surjective morphism; its restriction to the open `g⁻¹(j(Z₀))` of
`Ū` is an open immersion with image `f_U⁻¹(Z₀) ⊆ U ⊆ X`, so an isomorphism onto it; and
`f_U⁻¹(Z₀)` is dense in `X`. -/
@[mmp "lem_fa15_chow_family_iso_over_base"]
public theorem IsChowClosure.isProjectiveMorphism_snd {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    haveI := h.isOpenImmersion
    haveI := h.isIntegral
    IsProjectiveMorphism (Ubar.subschemeι ≫ pullback.snd sZbar sX) ∧
      IsBirationalMorphism (Ubar.subschemeι ≫ pullback.snd sZbar sX) ∧
      Surjective (Ubar.subschemeι ≫ pullback.snd sZbar sX) ∧
      IsOpenImmersion (((Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ j.opensRange).ι ≫
        Ubar.subschemeι ≫ pullback.snd sZbar sX) ∧
      Set.range (((Ubar.subschemeι ≫ pullback.fst sZbar sX) ⁻¹ᵁ j.opensRange).ι ≫
        Ubar.subschemeι ≫ pullback.snd sZbar sX).base = (U.ι ''ᵁ (fU ⁻¹ᵁ Z₀) : Set X) ∧
      Dense (U.ι ''ᵁ (fU ⁻¹ᵁ Z₀) : Set X) := by
  haveI := h.isOpenImmersion
  haveI := h.isIntegral
  haveI : IsSeparated sZbar := h.isProjectiveVariety.toIsSeparated
  set ι := Ubar.subschemeι
  set u := ι ≫ pullback.snd sZbar sX with hu
  set W := (ι ≫ pullback.fst sZbar sX) ⁻¹ᵁ j.opensRange with hW
  set V := fU ⁻¹ᵁ Z₀
  set Γ := chowGraph h.isLogEllipticFiberSpace.isContraction.comp_eq h.comp_eq
  have hWset (w : Ubar.subscheme) : w ∈ W ↔ ι.base w ∈ Set.range Γ.base := by
    rw [← h.image_preimage_eq]
    refine ⟨fun hw => ⟨w, ?_, rfl⟩, fun ⟨w', hw', he⟩ => ι.isEmbedding.injective he ▸ ?_⟩ <;>
      simpa [hW, Scheme.Hom.coe_opensRange]
  let Γ' : V.toScheme ⟶ Ubar.subscheme := IsClosedImmersion.lift ι Γ (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    refine le_ker_of_range_subset Γ Ubar ?_
    rw [← h.image_preimage_eq, ← Scheme.IdealSheafData.range_subschemeι]
    exact Set.image_subset_range _ _)
  have hΓ' : Γ' ≫ ι = Γ := IsClosedImmersion.lift_fac _ _ _
  let Γ'' : V.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι Γ' (by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hWset _).2 ⟨v, by rw [← hΓ']; rfl⟩)
  have hΓ'' : Γ'' ≫ W.ι = Γ' := IsOpenImmersion.lift_fac _ _ _
  have hΓsnd : Γ ≫ pullback.snd sZbar sX = V.ι ≫ U.ι := pullback.lift_snd _ _ _
  let u' : W.toScheme ⟶ V.toScheme := IsOpenImmersion.lift (V.ι ≫ U.ι) (W.ι ≫ u) (by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := (hWset (W.ι.base w)).1 w.2
    exact ⟨v, by rw [← hΓsnd, Scheme.Hom.comp_apply, hv]; rfl⟩)
  have hu' : u' ≫ V.ι ≫ U.ι = W.ι ≫ u := IsOpenImmersion.lift_fac _ _ _
  have hsec : Γ'' ≫ u' = 𝟙 _ := by
    rw [← cancel_mono (V.ι ≫ U.ι), Category.assoc, hu', Category.id_comp, ← Category.assoc,
      hΓ'', hu, ← Category.assoc, hΓ', hΓsnd]
  haveI : IsSeparated (u' ≫ V.ι ≫ U.ι) := hu' ▸ inferInstance
  haveI := IsSeparated.of_comp u' (V.ι ≫ U.ι)
  haveI : Surjective Γ'' := ⟨fun w => by
    obtain ⟨v, hv⟩ := (hWset (W.ι.base w)).1 w.2
    refine ⟨v, W.ι.isOpenEmbedding.injective (ι.isEmbedding.injective ?_)⟩
    rw [← hv, ← hΓ', ← hΓ'']
    rfl⟩
  haveI := isIso_of_surjective_section u' Γ'' hsec
  haveI hopen : IsOpenImmersion (W.ι ≫ u) := hu' ▸ inferInstance
  have hrange : Set.range (W.ι ≫ u).base = (U.ι ''ᵁ V : Set X) := by
    rw [← hu', range_comp_base_of_isIso, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    rfl
  have hdense := (U.ι ''ᵁ V).isOpen.dense h.nonempty_image_preimage
  haveI := isProper_of_isProjectiveMorphism u h.isProjectiveMorphism_subschemeι_snd
  exact ⟨h.isProjectiveMorphism_subschemeι_snd,
    isBirationalMorphism_of_isOpenImmersion_ι_comp u W _ hrange h.nonempty_image_preimage,
    surjective_of_dense_subset_range u hdense (hrange ▸ fun _ ⟨w, hw⟩ => ⟨W.ι.base w, hw⟩),
    hopen, hrange, hdense⟩

/-! ### Curves on a surface of the Chow closure contracted by `u` -/

section ContractedSurface

open TopologicalSpace Order Topology

/-- A closed subset `A` of dimension at least one of an irreducible closed set `B` of dimension
at most one is all of `B`. -/
private theorem eq_of_subset_of_one_le_topologicalKrullDim {T : Type*} [TopologicalSpace T]
    {A B : Set T} (hAB : A ⊆ B) (hA : IsClosed A) (hBi : IsIrreducible B)
    (hB : topologicalKrullDim B ≤ 1) (hA1 : 1 ≤ topologicalKrullDim A) : A = B := by
  by_contra hne
  have hι : IsInducing (Set.inclusion hAB) :=
    IsInducing.of_comp (continuous_inclusion hAB) continuous_subtype_val IsInducing.subtypeVal
  haveI : IrreducibleSpace B := Subtype.irreducibleSpace hBi
  let topB : IrreducibleCloseds B :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ B, isClosed_univ⟩
  have hcl : IsClosed (Set.range (Set.inclusion hAB)) := by
    rw [Set.range_inclusion]; exact hA.preimage continuous_subtype_val
  have hlt : ∀ Y : IrreducibleCloseds A,
      IrreducibleCloseds.map _ hι.continuous Y < topB := by
    intro Y
    refine lt_of_le_of_ne (fun _ _ => trivial) ?_
    intro heq
    have h1 : (Set.univ : Set B) ⊆ Set.range (Set.inclusion hAB) := by
      have : ((IrreducibleCloseds.map _ hι.continuous Y : IrreducibleCloseds B) : Set B) =
          Set.univ := congrArg SetLike.coe heq
      rw [← this, IrreducibleCloseds.coe_map]
      exact closure_minimal (Set.image_subset_range _ _) hcl
    apply hne
    refine subset_antisymm hAB fun x hx => ?_
    obtain ⟨y, hy⟩ := h1 (Set.mem_univ ⟨x, hx⟩)
    have := congrArg Subtype.val hy
    simp only [Set.coe_inclusion] at this
    exact this ▸ y.2
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (n := 1)).mp (by exact_mod_cast hA1)
  have hm := LTSeries.map_length l _ (IrreducibleCloseds.map_strictMono_of_isInducing hι)
  have hlen := RelSeries.snoc_length (l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hι))
    topB (hlt _)
  have h2' : (RelSeries.snoc (l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hι))
    topB (hlt _)).length = 2 := by omega
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim B :=
    (congrArg (fun n : ℕ => (n : WithBot ℕ∞)) h2').symm.le.trans (LTSeries.length_le_krullDim _)
  have := h2.trans hB
  norm_num at this

/-- A `T₀` space with two distinct points one specializing to the other has dimension at
least one. -/
private theorem one_le_topologicalKrullDim_of_specializes {W : Type*} [TopologicalSpace W]
    [T0Space W] {P Q : W} (hPQ : P ⤳ Q) (hne : P ≠ Q) : 1 ≤ topologicalKrullDim W := by
  let A : IrreducibleCloseds W := ⟨closure {Q}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds W := ⟨closure {P}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A < B := by
    refine lt_of_le_of_ne (show closure {Q} ⊆ closure {P} from
      specializes_iff_closure_subset.mp hPQ) fun heq => ?_
    have hQP : Q ⤳ P := specializes_iff_closure_subset.mpr
      (congrArg (fun Y : IrreducibleCloseds W => (Y : Set W)) heq).symm.le
    exact hne (hPQ.antisymm hQP).eq
  set L : LTSeries (IrreducibleCloseds W) := (RelSeries.singleton _ A).snoc B hAB
  have h1 : L.length = 1 := by
    simp only [L, RelSeries.snoc_length]; rfl
  have := LTSeries.length_le_krullDim L
  rw [h1] at this
  exact_mod_cast this

/-- A Noetherian, quasi-sober `T₁` space is discrete: each of its finitely many irreducible
components is the closure of a generic point, hence a single point. -/
private theorem discreteTopology_of_noetherianSpace_of_t1Space {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] [T1Space α] : DiscreteTopology α := by
  haveI : Finite α := by
    have hfin := NoetherianSpace.finite_irreducibleComponents (α := α)
    have hC : ∀ C ∈ irreducibleComponents α, C.Finite := fun C hC => by
      obtain ⟨c, hc⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
      rw [← isGenericPoint_def.mp hc, closure_singleton]
      exact Set.finite_singleton c
    have := hfin.sUnion hC
    rw [sUnion_irreducibleComponents] at this
    exact Set.finite_univ_iff.mp this
  infer_instance

/-- `u : Ū ⟶ X` is a closed map (it is projective, hence proper). -/
private theorem isClosedMap_u {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) :
    IsClosedMap (Ubar.subschemeι ≫ pullback.snd sZbar sX).base := by
  haveI := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_snd.1
  exact Scheme.Hom.isClosedMap _

/-- Fibre dimension: an irreducible surface `E ⊆ Ū` whose image under `g` is a curve contains
an irreducible closed curve inside a fibre of `g` over a closed point. -/
private theorem exists_curve_in_fiber {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {E : Set Ubar.subscheme}
    (hEc : IsClosed E) (hEi : IsIrreducible E) (hE : topologicalKrullDim E = 2)
    (hC : topologicalKrullDim ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base '' E) = 1) :
    ∃ z : Zbar, IsClosed {z} ∧ ∃ Φ : Set Ubar.subscheme,
      Φ ⊆ E ∧ Φ ⊆ (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z} ∧
      IsClosed Φ ∧ IsIrreducible Φ ∧ 1 ≤ topologicalKrullDim Φ := by
  set g := Ubar.subschemeι ≫ pullback.fst sZbar sX
  by_contra hcon
  push Not at hcon
  -- over a closed point, `E ∩ g⁻¹(z̄)` has no nontrivial specializations
  have hsp : ∀ z : Zbar, IsClosed {z} → ∀ a b : Ubar.subscheme, a ∈ E → b ∈ E →
      g.base a = z → g.base b = z → a ⤳ b → a = b := by
    intro z hz a b ha _ hga _ hab
    by_contra hne
    have hΦE : closure {a} ⊆ E := closure_minimal (Set.singleton_subset_iff.2 ha) hEc
    have hΦz : closure {a} ⊆ g.base ⁻¹' {z} :=
      closure_minimal (Set.singleton_subset_iff.2 hga) (hz.preimage g.continuous)
    have h1 := hcon z hz (closure {a}) hΦE hΦz isClosed_closure isIrreducible_singleton.closure
    refine h1.not_ge (one_le_topologicalKrullDim_of_specializes
      (P := (⟨a, subset_closure rfl⟩ : closure ({a} : Set Ubar.subscheme)))
      (Q := ⟨b, specializes_iff_mem_closure.mp hab⟩) ?_ fun he => hne (congrArg Subtype.val he))
    exact (Topology.IsInducing.subtypeVal.specializes_iff).mp hab
  -- `E` as a reduced closed subscheme
  let W : Ubar.subscheme.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨E, hEc⟩
  have hrange : Set.range W.subschemeι.base = E := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  set f := W.subschemeι ≫ g
  haveI : IsProper sX := isProper_of_isProjectiveMorphism _
    ((AlgebraicGeometry.isProjectiveVariety_iff k sX).mp
      h.satisfiesAbundanceAssumptions.isProjectiveVariety).2
  haveI : LocallyOfFiniteType sZbar := h.isNormalVariety.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZbar := h.isNormalVariety.1.toQuasiCompact
  haveI : IsProper f := by simp only [f, g]; infer_instance
  haveI : IsProper g := by simp only [g]; infer_instance
  -- `f` is quasi-finite at every point over a closed point
  have hqf : ∀ x, IsClosed {f.base x} → f.QuasiFiniteAt x := by
    intro x hx
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    haveI : T1Space (f.fiber (f.base x)) := by
      rw [t1Space_iff_specializes_imp_eq]
      intro p q hpq
      have hmem : ∀ r, f.base (f.fiberι (f.base x) r) = f.base x := fun r => by
        have : f.fiberι (f.base x) r ∈ f.base ⁻¹' {f.base x} := by
          rw [← Scheme.Hom.range_fiberι]; exact ⟨r, rfl⟩
        exact this
      have hpq' := hpq.map (f.fiberι (f.base x)).continuous
      have := hsp (f.base x) hx _ _ (hrange ▸ ⟨_, rfl⟩) (hrange ▸ ⟨_, rfl⟩) (hmem p) (hmem q)
        (hpq'.map W.subschemeι.continuous)
      exact (f.fiberι (f.base x)).isEmbedding.injective
        (W.subschemeι.isClosedEmbedding.injective this)
    haveI : IsLocallyNoetherian (f.fiber (f.base x)) :=
      inferInstanceAs (IsLocallyNoetherian (Limits.pullback _ _))
    haveI : IsNoetherian (f.fiber (f.base x)) := {}
    haveI := discreteTopology_of_noetherianSpace_of_t1Space (α := f.fiber (f.base x))
    exact isOpen_discrete _
  have hcm : IsClosedMap f.base := f.isClosedMap
  haveI : CompactSpace W.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace
      (W.subschemeι ≫ Ubar.subschemeι ≫ pullback.snd sZbar sX)
  have htop : f.quasiFiniteLocus = ⊤ := by
    by_contra hne
    have hK : IsClosed ((f.quasiFiniteLocus : Set W.subscheme)ᶜ) :=
      f.quasiFiniteLocus.isOpen.isClosed_compl
    have hKne : ((f.quasiFiniteLocus : Set W.subscheme)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      intro h'
      exact hne (SetLike.coe_injective (h'.trans TopologicalSpace.Opens.coe_top.symm))
    obtain ⟨x, hxK, hxc⟩ := hK.exists_closed_singleton hKne
    exact hxK (hqf x (by simpa using hcm _ hxc))
  haveI : LocallyQuasiFinite f := (f.quasiFiniteLocus_eq_top_iff).mp htop
  let eH : W.subscheme ≃ₜ E :=
    W.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  haveI : IrreducibleSpace E := Subtype.irreducibleSpace hEi
  haveI : IrreducibleSpace W.subscheme :=
    eH.symm.surjective.irreducibleSpace eH.symm.continuous
  have hdimE : topologicalKrullDim W.subscheme = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq eH eH.isHomeomorph, hE]; rfl
  have hrf : Set.range f.base = g.base '' E := by
    rw [← hrange, ← Set.range_comp]; rfl
  have hdimC : topologicalKrullDim (closure (Set.range f.base)) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hrf, (g.isClosedMap _ hEc).closure_eq, hC]; rfl
  have key := topologicalKrullDim_fiber_genericPoint_eq_sub f k (f ≫ sZbar) sZbar rfl hdimE hdimC
  have hd := f.isDiscrete_preimage_singleton (f.base (genericPoint W.subscheme))
  haveI : DiscreteTopology (f.base ⁻¹' {f.base (genericPoint W.subscheme)}) := hd.to_subtype
  haveI : DiscreteTopology (f.fiber (f.base (genericPoint W.subscheme))) :=
    (f.fiberHomeo _).isEmbedding.discreteTopology
  have h0 :=
    topologicalKrullDim_zero_of_discreteTopology (f.fiber (f.base (genericPoint W.subscheme)))
  rw [key] at h0
  norm_num at h0

/-- Over a closed point `z̄` of `Z̄`, the map `u` identifies no two distinct points of the fibre
`g⁻¹(z̄)` one of which specializes to the other: `u` restricted to the scheme-theoretic fibre is
the base change of the finite morphism `Spec κ(z̄) ⟶ Spec k` along `X ⟶ Spec k`. -/
private theorem eq_of_specializes_of_mem_fiber {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {z : Zbar} (hz : IsClosed {z})
    {a b : Ubar.subscheme} (hab : a ⤳ b)
    (ha : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base a = z)
    (hb : (Ubar.subschemeι ≫ pullback.fst sZbar sX).base b = z)
    (hu : (Ubar.subschemeι ≫ pullback.snd sZbar sX).base a =
      (Ubar.subschemeι ≫ pullback.snd sZbar sX).base b) : a = b := by
  haveI : LocallyOfFiniteType sZbar := h.isNormalVariety.1.toLocallyOfFiniteType
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hz
  haveI : IsFinite (Zbar.fromSpecResidueField z ≫ sZbar) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hpb : IsPullback ((pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX)
      ((pullback.fst sZbar sX).fiberToSpecResidueField z) sX
      (Zbar.fromSpecResidueField z ≫ sZbar) :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback sZbar sX).flip
  haveI : IsFinite ((pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb.flip inferInstance
  set F := (pullback.fst sZbar sX).fiberι z ≫ pullback.snd sZbar sX
  set e := (pullback.fst sZbar sX).fiberHomeo z
  have hma : Ubar.subschemeι.base a ∈ (pullback.fst sZbar sX).base ⁻¹' {z} := ha
  have hmb : Ubar.subschemeι.base b ∈ (pullback.fst sZbar sX).base ⁻¹' {z} := hb
  set a' := e.symm ⟨_, hma⟩
  set b' := e.symm ⟨_, hmb⟩
  have hsub : (⟨_, hma⟩ : (pullback.fst sZbar sX).base ⁻¹' {z}) ⤳ ⟨_, hmb⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp (hab.map Ubar.subschemeι.continuous)
  have hab' : a' ⤳ b' := hsub.map e.symm.continuous
  have hfa : (pullback.fst sZbar sX).fiberι z a' = Ubar.subschemeι.base a :=
    Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
  have hfb : (pullback.fst sZbar sX).fiberι z b' = Ubar.subschemeι.base b :=
    Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
  have hF : F a' = F b' := by
    simp only [F, Scheme.Hom.comp_base, TopCat.comp_app] at hu ⊢
    rw [hfa, hfb]; exact hu
  have hd := F.isDiscrete_preimage_singleton (F b')
  have : DiscreteTopology (F ⁻¹' {F b'}) := hd.to_subtype
  have hs : (⟨a', hF⟩ : F ⁻¹' {F b'}) ⤳ ⟨b', rfl⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hab'
  have hmem : (⟨a', hF⟩ : F ⁻¹' {F b'}) ∈ ({⟨b', rfl⟩} : Set (F ⁻¹' {F b'})) :=
    hs.mem_open (isOpen_discrete _) (Set.mem_singleton _)
  have hab'' : a' = b' := congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  have : Ubar.subschemeι.base a = Ubar.subschemeι.base b := by rw [← hfa, ← hfb, hab'']
  exact Ubar.subschemeι.isClosedEmbedding.injective this

/-- `u` is finite on the fibres of `g`: a closed curve in a fibre of `g` maps to a curve. -/
private theorem one_le_topologicalKrullDim_image_of_subset_fiber {K : Divisor X} {Δ : QDivisor X}
    {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens} {j : Z₀.toScheme ⟶ Zbar}
    {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {z : Zbar} (hz : IsClosed {z})
    {Φ : Set Ubar.subscheme}
    (hΦz : Φ ⊆ (Ubar.subschemeι ≫ pullback.fst sZbar sX).base ⁻¹' {z})
    (hΦc : IsClosed Φ) (hΦi : IsIrreducible Φ) (hΦ : 1 ≤ topologicalKrullDim Φ) :
    1 ≤ topologicalKrullDim ((Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' Φ) := by
  set u := (Ubar.subschemeι ≫ pullback.snd sZbar sX).base
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (n := 1)).mp (by exact_mod_cast hΦ)
  have hlt : l 0 < l (Fin.last _) := l.strictMono (by simp [Fin.lt_def, hl])
  haveI : QuasiSober Φ := hΦc.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨y0, hy0⟩ := QuasiSober.sober (l 0).isIrreducible (l 0).isClosed
  obtain ⟨y1, hy1⟩ := QuasiSober.sober (l (Fin.last _)).isIrreducible (l (Fin.last _)).isClosed
  have hsp : y1 ⤳ y0 := hy1.specializes (hlt.le hy0.mem)
  have hne : y1 ≠ y0 := by
    rintro rfl
    exact hlt.ne (SetLike.coe_injective
      ((isGenericPoint_def.mp hy0).symm.trans (isGenericPoint_def.mp hy1)))
  have hune : u y1.1 ≠ u y0.1 := fun heq =>
    hne (Subtype.ext (eq_of_specializes_of_mem_fiber h hz (hsp.map continuous_subtype_val)
      (hΦz y1.2) (hΦz y0.2) heq))
  exact one_le_topologicalKrullDim_of_specializes
    (P := (⟨u y1.1, Set.mem_image_of_mem _ y1.2⟩ : u '' Φ))
    (Q := ⟨u y0.1, Set.mem_image_of_mem _ y0.2⟩)
    ((Topology.IsInducing.subtypeVal.specializes_iff).mp
      ((hsp.map continuous_subtype_val).map (Scheme.Hom.continuous _)))
    fun he => hune (congrArg Subtype.val he)

/-- Let `(Z₀, Z̄, Ū)` be a Chow closure of `f_U` (`MMP.Flips.IsChowClosure`), with projections
`g : Ū ⟶ Z̄` and `u : Ū ⟶ X`. If `E ⊆ Ū` is an irreducible closed surface such that `g(E)` is a
curve and `u(E)` has dimension at most one, then every irreducible curve `Γ ⊆ u(E)` satisfies
`(K_X + Δ_X) · Γ = 0`. -/
@[mmp "lem_fa15_contracted_surface_curves_trivial"]
public theorem IsChowClosure.intersectionNumber_eq_zero_of_dim_image_le_one
    {K : Divisor X} {Δ : QDivisor X} {fU : U.toScheme ⟶ Z} {Z₀ : Z.Opens}
    {j : Z₀.toScheme ⟶ Zbar} {Ubar : (pullback sZbar sX).IdealSheafData}
    (h : IsChowClosure (sZ := sZ) k sX K Δ fU Z₀ j Ubar) {E : Set Ubar.subscheme}
    (hEc : IsClosed E) (hEi : IsIrreducible E) (hE : topologicalKrullDim E = 2)
    (hC : topologicalKrullDim ((Ubar.subschemeι ≫ pullback.fst sZbar sX).base '' E) = 1)
    (hu : topologicalKrullDim ((Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' E) ≤ 1)
    (Γ : ProperCurve sX)
    (hΓ : closure {Γ.point} ⊆ (Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' E) :
    (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le
      h.satisfiesAbundanceAssumptions.isQCartier = 0 := by
  obtain ⟨z, hz, Φ, hΦE, hΦz, hΦc, hΦi, hΦ⟩ := exists_curve_in_fiber h hEc hEi hE hC
  have heq : (Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' Φ =
      (Ubar.subschemeι ≫ pullback.snd sZbar sX).base '' E :=
    eq_of_subset_of_one_le_topologicalKrullDim (Set.image_mono hΦE) (isClosedMap_u h _ hΦc)
      (hEi.image _ (Scheme.Hom.continuous _).continuousOn) hu
      (one_le_topologicalKrullDim_image_of_subset_fiber h hz hΦz hΦc hΦi hΦ)
  refine h.intersectionNumber_eq_zero z hz Γ ?_
  rw [← heq] at hΓ
  exact hΓ.trans (Set.image_mono hΦz)

end ContractedSurface

end ChowClosure

/-! ### Discrepancies are invariant under crepant pull-back -/

section CrepantPullback

section Comp

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
  (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The divisor `(Y', f ∘ g, E)` over `X` of a divisor `(Y', g, E)` over `Y`. -/
private def compDivisorOver (E : ProperDivisorOver k (f ≫ sX)) :
    ProperDivisorOver k sX where
  Y := E.Y
  f := E.f ≫ f
  isNormalVariety := by
    have h := E.isNormalVariety
    rwa [← Category.assoc] at h
  isBirationalMorphism := by
    haveI := E.isIntegral
    haveI := E.isProper
    exact isBirationalMorphism_comp_of_isBirational f E.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism E.isBirationalMorphism)
  E := E.E
  isProper := by
    haveI := E.isProper
    infer_instance

/-- The valuation of the composite divisor over `X` is `ord_E ∘ f^*`. -/
private theorem compDivisorOver_valuation (E : ProperDivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext a
  change E.E.divisorialValuation _ = E.E.divisorialValuation _
  congr 1
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply E.f f a).symm

end Comp

section PullbackComp

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]

/-- The only irreducible component of an irreducible space is the whole space. -/
private theorem mem_irreducibleComponent_of_irreducibleSpace {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
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
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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
      (mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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

end PullbackComp

section FormsComp

variable {k : Type u} [Field k] [PerfectField k] {X Y Z : Scheme.{u}} [IsIntegral X]
  [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX]

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
public theorem pullbackRationalPluriForms_comp (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower k X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg k Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap k X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

end FormsComp

section Discrepancy

variable {k : Type u} [Field k] [PerfectField k]

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (E : ProperDivisorOver k sX) : HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, ?_⟩, E, rfl⟩
  rfl

/-- **The common value.** For a presentation `div_X(ω) + D = ∑ r_j L_j` by Cartier divisors and
`div_Y(f^*ω) + D_Y = ∑ r_j f^*L_j`, the discrepancy of `(Y', f ∘ g, E)` over `X` computed with
`ω` and `(r_j, L_j)` equals that of `(Y', g, E)` over `Y` computed with `f^*ω` and
`(r_j, f^*L_j)`. -/
private theorem exists_isDiscrepancyWith_comp {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n) {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0) {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType (f ≫ sX)]
    (hnY : topologicalKrullDim Y = n) {D_Y : RDivisor Y} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {L' : Fin m → Divisor Y} (hLc : ∀ j, (L j).IsCartier)
    (hsumX : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (hpb : ∀ j, ∃ hB, (L j).IsPullback f hB (L' j))
    (hsumY : haveI : IsDominant f := hf.isDominant
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + D_Y =
        ∑ j, r j • Divisor.toRDivisor (L' j))
    (E : ProperDivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    ∃ b : ℝ, IsDiscrepancyWith sX n D ω r L (compDivisorOver f hf E) b ∧
      IsDiscrepancyWith (f ≫ sX) n D_Y (pullbackRationalPluriForms sX f ω) r L' E b := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hbf := hf.functionFieldMap_bijective
  have hbg := E.isBirationalMorphism.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hL'c : ∀ j, (L' j).IsCartier := fun j => (hpb j).2.isCartier (hLc j)
  choose L'' hL'' using fun j =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hL'c j)
  refine ⟨(E.toDivisorOver.ordPullback (pullbackRationalPluriForms sX f ω) : ℝ) -
    ∑ j, r j * (L'' j).coeff E.E, ⟨hX, hn, hω, hLc, hsumX, L'', fun j => ⟨_,
      isPullback_comp (hpb j).2 (hL'' j)
        (map_componentGenericPoint_notMem_supp_of_isDominant (E.f ≫ f) (L j))⟩, ?_⟩,
    ⟨hY, hnY, pullbackRationalPluriForms_ne_zero f hbf hd hω, hL'c, hsumY, L'',
      fun j => ⟨_, hL'' j⟩, rfl⟩⟩
  congr 2
  change E.E.ordForm (pullbackRationalPluriForms (f ≫ sX) E.f
    (pullbackRationalPluriForms sX f ω)) = E.E.ordForm (pullbackRationalPluriForms sX (E.f ≫ f) ω)
  rw [pullbackRationalPluriForms_comp f E.f hbf hbg hd ω]
  rfl

end Discrepancy

/-- **Discrepancies are invariant under crepant pull-back.** Let `f : Y ⟶ X` be a proper
birational morphism of normal varieties of dimension `n` over a perfect field `k`, `ω ≠ 0` a
rational `n`-form on `X` with `K_X = div_X(ω)` a canonical divisor, `D` an `ℝ`-divisor on `X`
with `K_X + D` `ℝ`-Cartier, and `D_Y` the `ℝ`-divisor on `Y` with
`div_Y(f^*ω) + D_Y = f^*(K_X + D)`, where `div_Y(f^*ω)` is a canonical divisor of `Y`. Then for
every divisor `E` over `Y`, `a` is the discrepancy
`a(ord_E, D)` over `X` (with `ord_E` a valuation of `k(X)` through `f^*`) if and only if it is the
discrepancy `a(ord_E, D_Y)` over `Y`. -/
@[mmp "lem_fa2_discrepancy_crepant_pullback"]
public theorem isDiscrepancy_comap_functionFieldMap_iff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {D : RDivisor X} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D))
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType (f ≫ sX)] {D_Y : RDivisor Y}
    (hDY : haveI : IsDominant f := hf.isDominant
      IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + D_Y))
    (hKY : haveI : IsDominant f := hf.isDominant
      (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n)
    (E : ProperDivisorOver k (f ≫ sX)) (a : ℝ) :
    haveI : IsDominant f := hf.isDominant
    IsDiscrepancy sX n (divisorOfForm ω) D (E.valuation.comap (functionFieldMap f)) a ↔
      IsDiscrepancy (f ≫ sX) n (divisorOfForm (pullbackRationalPluriForms sX f ω)) D_Y
        E.valuation a := by
  haveI : IsDominant f := hf.isDominant
  obtain ⟨m, r, L, L', hLc, hsumX, hpb, hsumY⟩ := hDY
  obtain ⟨b, hbX, hbY⟩ := exists_isDiscrepancyWith_comp hX hK.topologicalKrullDim_eq hω f hY hf
    hKY.topologicalKrullDim_eq hLc hsumX hpb hsumY E
  have hval := compDivisorOver_valuation f hf E
  constructor
  · rintro ⟨-, -, -, E₀, ω₀, m₀, r₀, L₀, hE₀, -, hw₀⟩
    obtain rfl : a = b := hw₀.eq hbX (hE₀.trans hval.symm)
    refine ⟨hKY, ⟨m, r, L', fun j => (hpb j).2.isCartier (hLc j), ?_⟩,
      hasNonemptyCenter_valuation E, E, _, m, r, L', rfl, rfl, hbY⟩
    rw [hsumY]
    simp only [toRDivisor_eq_mapCoeffs]
  · rintro ⟨-, -, -, E₁, τ₁, m₁, r₁, L₁, hE₁, -, hw₁⟩
    obtain rfl : a = b := hw₁.eq hbY hE₁
    exact ⟨hK, hKD, hval ▸ hasNonemptyCenter_valuation (compDivisorOver f hf E),
      compDivisorOver f hf E, ω, m, r, L, hval, rfl, hbX⟩

end CrepantPullback

/-! ### The `ℝ`-Cartier locus of a rational family of divisors -/

section CartierLocus

variable {X : Scheme.{u}}

/-- The `K`-span of the Cartier divisors. -/
private noncomputable def cartSpan (K : Type*) [Ring K] (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsNormal X] : Submodule K (DivisorWithCoeffs K X) :=
  Submodule.span K (Set.range fun L : {L : Divisor X // L.IsCartier} =>
    L.1.mapCoeffs (Int.cast : ℤ → K) Int.cast_zero)

/-- A `K`-divisor is a `K`-combination of Cartier divisors iff it lies in `cartSpan K X`. -/
private theorem isCartierCombination_iff_mem {K : Type*} [Ring K] [IsLocallyNoetherian X]
    [IsNormal X] (D : DivisorWithCoeffs K X) :
    IsCartierCombination D ↔ D ∈ cartSpan K X := by
  constructor
  · rintro ⟨m, r, L, hL, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨L j, hL j⟩, rfl⟩)
  · intro h
    obtain ⟨n, f, g, hg⟩ := (Submodule.mem_span_set' (R := K)).mp h
    choose L hL using fun i => (g i).2
    exact ⟨n, f, fun i => (L i).1, fun i => (L i).2, by rw [← hg]; simp [hL]⟩

private theorem toRDivisor_smul (q : ℚ) (D : QDivisor X) :
    QDivisor.toRDivisor (q • D) = (q : ℝ) • QDivisor.toRDivisor D := by
  ext E
  change ((q * D E : ℚ) : ℝ) = (q : ℝ) * (D E : ℝ)
  push_cast; rfl

private theorem toRDivisor_apply (D : QDivisor X) (E : MMP.Mori.PrimeDivisor X) :
    QDivisor.toRDivisor D E = (D E : ℝ) := rfl

private theorem toRDivisor_mapCoeffs_intCast (L : Divisor X) :
    QDivisor.toRDivisor (L.mapCoeffs (Int.cast : ℤ → ℚ) Int.cast_zero) =
      L.mapCoeffs (Int.cast : ℤ → ℝ) Int.cast_zero := by
  ext E
  change (((L E : ℤ) : ℚ) : ℝ) = ((L E : ℤ) : ℝ)
  push_cast; rfl

private theorem toRDivisor_mem_cartSpan [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X}
    (h : D ∈ cartSpan ℚ X) : QDivisor.toRDivisor D ∈ cartSpan ℝ X := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, rfl⟩ := hx
    exact Submodule.subset_span ⟨L, (toRDivisor_mapCoeffs_intCast L.1).symm⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [toRDivisor_smul]; exact Submodule.smul_mem _ _ hx

/-- The `ℚ`-linear map `ℝ`-divisors → `ℚ`-divisors applying a `ℚ`-linear functional
`φ : ℝ → ℚ` to every coefficient. -/
private noncomputable def coordDiv (φ : ℝ →ₗ[ℚ] ℚ) : RDivisor X →ₗ[ℚ] QDivisor X :=
  Finsupp.mapRange.linearMap φ

private theorem coordDiv_smul_toRDivisor (φ : ℝ →ₗ[ℚ] ℚ) (x : ℝ) (D : QDivisor X) :
    coordDiv φ (x • QDivisor.toRDivisor D) = φ x • D := by
  ext E
  change φ (x * (D E : ℝ)) = φ x * D E
  rw [mul_comm, ← smul_eq_mul, Rat.cast_smul_eq_qsmul, map_smul, smul_eq_mul, mul_comm]

/-- Taking a `ℚ`-linear coordinate `φ` of the coefficients of a real solution gives a rational
solution, with `1` replaced by `φ 1`. -/
private theorem coord_mem_cartSpan [IsLocallyNoetherian X] [IsNormal X] {ι : Type*} [Fintype ι]
    (B₀ : QDivisor X) (D : ι → QDivisor X) {b : ι → ℝ}
    (hb : QDivisor.toRDivisor B₀ + ∑ i, b i • QDivisor.toRDivisor (D i) ∈ cartSpan ℝ X)
    (φ : ℝ →ₗ[ℚ] ℚ) : φ 1 • B₀ + ∑ i, φ (b i) • D i ∈ cartSpan ℚ X := by
  obtain ⟨m, r, L, hL, hE⟩ := (isCartierCombination_iff_mem _).mpr hb
  have hE' := congrArg (coordDiv φ) hE
  simp only [map_add, map_sum, ← toRDivisor_mapCoeffs_intCast, coordDiv_smul_toRDivisor] at hE'
  rw [← one_smul ℝ (QDivisor.toRDivisor B₀), coordDiv_smul_toRDivisor] at hE'
  rw [hE']
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨L j, hL j⟩, rfl⟩)

/-- A real solution yields a rational one: take the coordinate along a `ℚ`-basis vector of `ℝ`
on which `1` has a nonzero coordinate, and rescale. -/
private theorem exists_rat_mem_cartSpan [IsLocallyNoetherian X] [IsNormal X] {ι : Type*}
    [Fintype ι] (B₀ : QDivisor X) (D : ι → QDivisor X) {b : ι → ℝ}
    (hb : QDivisor.toRDivisor B₀ + ∑ i, b i • QDivisor.toRDivisor (D i) ∈ cartSpan ℝ X) :
    ∃ b₀ : ι → ℚ, B₀ + ∑ i, b₀ i • D i ∈ cartSpan ℚ X := by
  let bas := Module.Basis.ofVectorSpace ℚ ℝ
  obtain ⟨β, hβ⟩ := Finsupp.ne_iff.mp (bas.repr.map_ne_zero_iff.mpr one_ne_zero)
  have ht : bas.coord β 1 ≠ 0 := hβ
  refine ⟨fun i => (bas.coord β 1)⁻¹ * bas.coord β (b i), ?_⟩
  convert Submodule.smul_mem _ (bas.coord β 1)⁻¹ (coord_mem_cartSpan B₀ D hb (bas.coord β))
    using 1
  simp only [smul_add, Finset.smul_sum, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- A real number is the sum of its `ℚ`-coordinates times the basis vectors, over any finite
set containing the support. -/
private theorem sum_basis_mul_repr {I : Type*} (bas : Module.Basis I ℚ ℝ) (x : ℝ)
    (T : Finset I) (hT : (bas.repr x).support ⊆ T) :
    ∑ γ ∈ T, bas γ * (bas.repr x γ : ℝ) = x := by
  conv_rhs => rw [← bas.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Rat.cast_smul_eq_qsmul ℝ, smul_eq_mul, mul_comm]

/-- If every `ℚ`-linear coordinate `ψ` of a real vector `b` satisfies
`ψ ∘ b - ψ 1 • b₀ ∈ K`, then `b - b₀` lies in the real span of `K`: it is a real combination of
any `ℚ`-basis of `K`. -/
private theorem exists_eq_add_sum_finBasis {ι : Type*} [Fintype ι] (K : Submodule ℚ (ι → ℚ))
    (b₀ : ι → ℚ) (b : ι → ℝ) (h : ∀ ψ : ℝ →ₗ[ℚ] ℚ, (fun i => ψ (b i)) - ψ 1 • b₀ ∈ K) :
    ∃ c : Fin (Module.finrank ℚ K) → ℝ,
      b = (fun i => (b₀ i : ℝ)) + ∑ j, c j • fun i => ((Module.finBasis ℚ K j : ι → ℚ) i : ℝ) := by
  classical
  let bas := Module.Basis.ofVectorSpace ℚ ℝ
  let w : Fin (Module.finrank ℚ K) → ι → ℚ := fun j => (Module.finBasis ℚ K j : ι → ℚ)
  let T : Finset _ := (bas.repr 1).support ∪ Finset.univ.biUnion fun i => (bas.repr (b i)).support
  let k : _ → ι → ℚ := fun γ => (fun i => bas.coord γ (b i)) - bas.coord γ 1 • b₀
  let q : _ → Fin (Module.finrank ℚ K) → ℚ :=
    fun γ j => (Module.finBasis ℚ K).repr ⟨k γ, h _⟩ j
  have hq : ∀ γ i, ∑ j, q γ j * w j i = k γ i := fun γ i => by
    have := congrArg (fun v : K => (v : ι → ℚ) i) ((Module.finBasis ℚ K).sum_repr ⟨k γ, h _⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using this
  refine ⟨fun j => ∑ γ ∈ T, bas γ * (q γ j : ℝ), funext fun i => ?_⟩
  have e1 := sum_basis_mul_repr bas 1 T Finset.subset_union_left
  have e2 := sum_basis_mul_repr bas (b i) T (Finset.subset_union_right.trans'
    (Finset.subset_biUnion_of_mem (fun i => (bas.repr (b i)).support) (Finset.mem_univ i)))
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ γ ∈ T, ∑ j, bas γ * (q γ j : ℝ) * (w j i : ℝ) =
      bas γ * (bas.repr (b i) γ : ℝ) - bas γ * (bas.repr 1 γ : ℝ) * (b₀ i : ℝ) := by
    intro γ _
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have := congrArg (fun x : ℚ => (x : ℝ)) (hq γ i)
    push_cast at this
    rw [this]
    simp only [k, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
    push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, e1, e2]
  ring

/-- Let `X` be a normal scheme, `B₀` and `D i` (`i ∈ ι`, `ι` finite) `ℚ`-divisors on `X`, such
that `B₀ + ∑ bᵢ Dᵢ` is `ℝ`-Cartier for some `b ∈ ℝ^ι`. Then there are `b⁰ ∈ ℚ^ι` and
`w₁, …, w_p ∈ ℚ^ι` such that `B₀ + ∑ bᵢ Dᵢ` is `ℝ`-Cartier exactly for `b ∈ b⁰ + ∑ⱼ ℝ wⱼ`, and
`B₀ + ∑ bᵢ Dᵢ` is `ℚ`-Cartier for every `b ∈ b⁰ + ∑ⱼ ℚ wⱼ`. -/
@[mmp "lem_fa2_r_cartier_rational_subspace"]
public theorem exists_rat_affineSubspace_isCartierCombination {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {ι : Type*} [Fintype ι] (B₀ : QDivisor X)
    (D : ι → QDivisor X)
    (hS : ∃ b : ι → ℝ, IsCartierCombination
      (QDivisor.toRDivisor B₀ + ∑ i, b i • QDivisor.toRDivisor (D i))) :
    ∃ (b₀ : ι → ℚ) (p : ℕ) (w : Fin p → ι → ℚ),
      (∀ b : ι → ℝ, IsCartierCombination
          (QDivisor.toRDivisor B₀ + ∑ i, b i • QDivisor.toRDivisor (D i)) ↔
        ∃ c : Fin p → ℝ, b = (fun i => (b₀ i : ℝ)) + ∑ j, c j • fun i => (w j i : ℝ)) ∧
      ∀ c : Fin p → ℚ, IsCartierCombination (B₀ + ∑ i, (b₀ + ∑ j, c j • w j) i • D i) := by
  classical
  let φ := Fintype.linearCombination ℚ D
  have hφ : ∀ c : ι → ℚ, φ c = ∑ i, c i • D i := Fintype.linearCombination_apply ℚ D
  let Kr : Submodule ℚ (ι → ℚ) := (cartSpan ℚ X).comap φ
  obtain ⟨b', hb'⟩ := hS
  obtain ⟨b₀, hb₀⟩ := exists_rat_mem_cartSpan B₀ D ((isCartierCombination_iff_mem _).mp hb')
  rw [← hφ] at hb₀
  let w : Fin (Module.finrank ℚ Kr) → ι → ℚ := fun j => (Module.finBasis ℚ Kr j : ι → ℚ)
  have hw : ∀ j, w j ∈ Kr := fun j => (Module.finBasis ℚ Kr j).2
  refine ⟨b₀, _, w, fun b => ?_, fun c => ?_⟩
  · rw [isCartierCombination_iff_mem]
    refine ⟨fun hb => exists_eq_add_sum_finBasis Kr b₀ b fun ψ => by
        change φ _ ∈ cartSpan ℚ X
        convert Submodule.sub_mem _ (coord_mem_cartSpan B₀ D hb ψ)
          (Submodule.smul_mem _ (ψ 1) hb₀) using 1
        rw [map_sub, map_smul, hφ, smul_add]
        abel, ?_⟩
    rintro ⟨c, rfl⟩
    have heq : QDivisor.toRDivisor B₀ + ∑ i, ((fun i => (b₀ i : ℝ)) +
        ∑ j, c j • fun i => (w j i : ℝ)) i • QDivisor.toRDivisor (D i) =
        QDivisor.toRDivisor (B₀ + φ b₀) + ∑ j, c j • QDivisor.toRDivisor (φ (w j)) := by
      refine Finsupp.ext fun E => ?_
      simp only [hφ, map_add, map_sum, toRDivisor_smul, Finsupp.add_apply,
        Finsupp.finset_sum_apply, Finsupp.smul_apply, toRDivisor_apply, Pi.add_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ (α := ι))]
      simp only [mul_assoc, add_assoc]
    rw [heq]
    exact add_mem (toRDivisor_mem_cartSpan hb₀) (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (toRDivisor_mem_cartSpan (hw j)))
  · rw [isCartierCombination_iff_mem]
    rw [show ∑ i, (b₀ + ∑ j, c j • w j) i • D i = φ b₀ + φ (∑ j, c j • w j) by
      rw [← map_add, hφ], ← add_assoc]
    exact add_mem hb₀ (Submodule.sum_mem Kr fun j _ => Kr.smul_mem _ (hw j))

end CartierLocus

/-! ### Pluricanonical sections of positive degree on a curve -/

section NormalizedSections

/-- A rational form `τ` *vanishes to order `≥ a` along `Q`*: it is `0` or `ord_Q τ ≥ a`. -/
private def VanishesTo {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] {n : ℕ} (Q : MMP.Mori.PrimeDivisor C) (a : ℤ)
    (τ : RationalPluriForms sC 1 (n : ℕ)) : Prop :=
  τ = 0 ∨ a ≤ Q.ordForm τ

section VanishesTo

variable {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C]
  [IsLocallyNoetherian C] {n : ℕ} {Q : MMP.Mori.PrimeDivisor C} {a : ℤ}

private theorem VanishesTo.add [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ + τ') := by
  rcases h with h | h
  · rw [h, zero_add]; exact h'
  rcases h' with h' | h'
  · rw [h', add_zero]; exact Or.inr h
  by_cases h0 : τ + τ' = 0
  · exact Or.inl h0
  exact Or.inr ((le_min h h').trans (Q.min_ordForm_le_ordForm_add h0))

private theorem VanishesTo.neg {τ : RationalPluriForms sC 1 (n : ℕ)} (h : VanishesTo Q a τ) :
    VanishesTo Q a (-τ) := by
  rcases h with h | h
  · rw [h, neg_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [PrimeDivisor.ordForm_neg])

private theorem VanishesTo.sub [IsNormal C] {τ τ' : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (h' : VanishesTo Q a τ') : VanishesTo Q a (τ - τ') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

private theorem VanishesTo.const_smul {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (c : k) : VanishesTo Q a (c • τ) := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]; exact Or.inl rfl
  rcases h with h | h
  · rw [h, smul_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [MMP.Fourfold.ordForm_const_smul Q hc])

private theorem VanishesTo.mono {b : ℤ} {τ : RationalPluriForms sC 1 (n : ℕ)}
    (h : VanishesTo Q a τ) (hb : b ≤ a) : VanishesTo Q b τ :=
  h.imp id hb.trans

end VanishesTo

/-- Membership in the global sections `H⁰(C, 𝒪(nK + E))` is the order condition at every prime
divisor. -/
private theorem mem_pluricanonicalSections_top_iff {k : Type u} [Field k] {C : Scheme.{u}}
    {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C] {n : ℕ}
    {E : Divisor C} {τ : RationalPluriForms sC 1 (n : ℕ)} :
    τ ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤ ↔
      ∀ Q : MMP.Mori.PrimeDivisor C, VanishesTo Q (-E.coeff Q) τ := by
  have htop : (⊤ : C.Opens) ≠ ⊥ := by
    intro h
    have hx : (Nonempty.some (inferInstance : Nonempty C)) ∈ (⊤ : C.Opens) := trivial
    rw [h] at hx
    exact hx
  rw [mem_pluricanonicalSections_of_ne_bot htop]
  refine ⟨fun h Q => ?_, fun h Q _ hτ => ?_⟩
  · by_cases hτ : τ = 0
    · exact Or.inl hτ
    · refine Or.inr ?_
      have := h Q ⟨Q.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
        trivial⟩ hτ
      omega
  · rcases h Q with h | h
    · exact (hτ h).elim
    · omega

/-- The order of a power of a nonzero rational function. -/
private theorem ord_pow_of_ne_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {g : X.functionField} (hg : g ≠ 0) (x : X) (n : ℕ) : X.ord (g ^ n) x = n * X.ord g x := by
  induction n with
  | zero => simp [Scheme.ord_of_isUnit]
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hg) hg, ih]; push_cast; ring

/-- **The `n`-th power of a canonical form.** On a curve with canonical divisor `K` there is a
nonzero rational `n`-canonical form `θ` with `ord_Γ θ = n · coeff_Γ K` along every prime
divisor `Γ`. -/
private theorem exists_ordForm_eq_mul_coeff {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    (Q : MMP.Mori.PrimeDivisor C) (n : ℕ) :
    ∃ θ : RationalPluriForms sC 1 (n : ℕ), θ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor C, Γ.ordForm θ = n * K.coeff Γ := by
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim C = 1 := hK.1
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hC hK
  obtain ⟨σ, hσ, h0⟩ := Q.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by rw [hdim]; rfl)
  have htr : (Algebra.trdeg k C.functionField).toNat = 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sC) (by rw [hdim]; rfl)
  set b := topFormsBasis Q.localRing hσ h0
  set g : C.functionField := (ZTensorPower.basis b 1).repr ω ()
  have hg : g ≠ 0 := by
    intro h
    have := basis_unit_repr_smul (ZTensorPower.basis b 1) ω
    rw [show (ZTensorPower.basis b 1).repr ω () = g from rfl, h, zero_smul] at this
    exact hω0 this.symm
  refine ⟨g ^ n • ZTensorPower.basis b n (), ?_, fun Γ => ?_⟩
  · exact smul_ne_zero (pow_ne_zero _ hg) ((ZTensorPower.basis b n).ne_zero ())
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul htr b
  have h1 := hN 1 ω hω0
  have h2 := hN n (g ^ n • ZTensorPower.basis b n ())
    (smul_ne_zero (pow_ne_zero _ hg) ((ZTensorPower.basis b n).ne_zero ()))
  rw [hω] at h1
  rw [h2]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_apply,
    if_true]
  rw [ord_pow_of_ne_zero hg]
  change K.coeff Γ = C.ord g Γ.genericPoint + 1 * N at h1
  rw [h1]; ring

/-- On a curve, the rational `m`-canonical forms are a line over `k(C)`: every form is a multiple
of a given nonzero one. -/
private theorem exists_eq_smul_of_ne_zero {k : Type u} [Field k] [PerfectField k]
    {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)} [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    [LocallyOfFiniteType sC] (hdim : topologicalKrullDim C = 1) {m : ℤ}
    (Q : MMP.Mori.PrimeDivisor C) {u : RationalPluriForms sC 1 m} (hu : u ≠ 0)
    (w : RationalPluriForms sC 1 m) : ∃ h : C.functionField, w = h • u := by
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Q.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sC) (d := 1)
    (by rw [hdim]; rfl)
  let B := ZTensorPower.basis (topFormsBasis Q.localRing hσ h0) m
  have hu' := basis_unit_repr_smul B u
  have hw' := basis_unit_repr_smul B w
  have hru : B.repr u () ≠ 0 := by
    intro h; rw [h, zero_smul] at hu'; exact hu hu'.symm
  refine ⟨B.repr w () / B.repr u (), ?_⟩
  have key : (B.repr w () / B.repr u ()) • (B.repr u () • B ()) = B.repr w () • B () := by
    rw [smul_smul, div_mul_cancel₀ _ hru]
  rw [hu'] at key
  exact hw'.symm.trans key.symm

/-- An element of the maximal ideal of `𝒪_{X,Γ}` vanishes along `Γ`. -/
private theorem one_le_ord_algebraMap_of_mem_maximalIdeal {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X) {a : Γ.localRing}
    (ha : a ∈ IsLocalRing.maximalIdeal Γ.localRing) (ha0 : a ≠ 0) :
    1 ≤ X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint := by
  have := Γ.isDiscreteValuationRing_localRing
  have hz := Γ.coheight_genericPoint
  have hne : algebraMap Γ.localRing X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha0
  rw [Scheme.le_ord_iff hz hne]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Γ.genericPoint) := krullDimLE_of_coheight_le hz.le
  change Multiplicative.ofAdd (1 : ℤ) ≤ Ring.ordFrac Γ.localRing _
  rw [Ring.ordFrac_eq_ord _ ha0,
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha0)]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := Γ.localRing) (mem_nonZeroDivisors_of_ne_zero ha0))
  have hpos : 0 < Ring.ord Γ.localRing a := by
    have : Nontrivial (Γ.localRing ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.2 (by
        rw [Ne, Ideal.span_singleton_eq_top]; exact ha)
    exact Module.length_pos
  rw [← hn] at hpos ⊢
  simp only [ENat.recTopCoe_coe]
  rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  have : 0 < n := by exact_mod_cast hpos
  omega

/-- **The fibre of `𝒪(nK + E)` at a point is spanned by a section of exact order.** If `u` has
exact order `-e` along `Q` and `w` has order `≥ -e`, then `w - c • u` has order `≥ 1 - e` for some
constant `c`. -/
private theorem exists_vanishesTo_sub_const_smul
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hdim : topologicalKrullDim C = 1) {n : ℕ}
    (Q : MMP.Mori.PrimeDivisor C) (e : ℤ) {u w : RationalPluriForms sC 1 (n : ℕ)} (hu : u ≠ 0)
    (hue : Q.ordForm u + e = 0) (hw : VanishesTo Q (-e) w) :
    ∃ c : k, VanishesTo Q (1 - e) (w - c • u) := by
  classical
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  let := stalkAlgebra sC Q.genericPoint
  let := functionFieldAlgebra sC
  have := isScalarTower_stalk_functionField sC Q.genericPoint
  rcases hw with hw0 | hw
  · exact ⟨0, Or.inl (by rw [hw0, zero_smul, sub_zero])⟩
  obtain ⟨h, rfl⟩ := exists_eq_smul_of_ne_zero hdim Q hu w
  by_cases hh : h = 0
  · exact ⟨0, Or.inl (by rw [hh, zero_smul, zero_smul, sub_zero])⟩
  have hd : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  rw [Q.ordForm_smul_of_topologicalKrullDim_eq hd hh hu] at hw
  -- `h` is regular at `Q`
  obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    Q.genericPoint hh fun Γ hΓ => by
      have hΓQ : Γ = Q := MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hΓ
        exact specializes_iff_mem_closure.2 hΓ)
      subst hΓQ; omega
  have hcl : IsClosed ({Q.genericPoint} : Set C) := by
    refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint C
      hdim fun h => ?_
    have h1 := Q.coheight_genericPoint
    rw [h, show genericPoint C = (⊤ : C) from rfl, Order.coheight_top] at h1
    exact zero_ne_one h1
  obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sC Q.genericPoint hcl
    (Ideal.Quotient.mk _ r)
  have hmem : r - algebraMap k Q.localRing c ∈ IsLocalRing.maximalIdeal Q.localRing := by
    rw [← Ideal.Quotient.eq, ← hc]; rfl
  refine ⟨c, ?_⟩
  have hsmul : h • u - c • u = algebraMap Q.localRing C.functionField
      (r - algebraMap k Q.localRing c) • u := by
    rw [MMP.Fourfold.RationalPluriForms.smul_def, ← sub_smul, map_sub, hr,
      ← IsScalarTower.algebraMap_apply]
  rw [hsmul]
  by_cases h0 : r - algebraMap k Q.localRing c = 0
  · exact Or.inl (by rw [h0, map_zero, zero_smul])
  have h0' : algebraMap Q.localRing C.functionField (r - algebraMap k Q.localRing c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0
  refine Or.inr ?_
  rw [Q.ordForm_smul_of_topologicalKrullDim_eq hd h0' hu]
  have := one_le_ord_algebraMap_of_mem_maximalIdeal Q hmem h0
  omega

private theorem image_top_eq_top {X : Scheme.{u}} {U : X.Opens} (hU : U = ⊤) : U.ι ''ᵁ ⊤ = ⊤ := by
  subst hU
  ext x
  simp

/-- Global sections of `M` and of its restriction to the open `U = ⊤` have the same dimension. -/
private theorem finrank_globalSectionsOver_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : X.Modules) {U : X.Opens} (hU : U = ⊤) :
    Module.finrank k ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) =
      Module.finrank k ((globalSectionsOver f).obj M) := by
  let g : ((globalSectionsOver f).obj M) →ₗ[k]
      ((globalSectionsOver (U.ι ≫ f)).obj (M.restrict U.ι)) :=
    { toFun := fun s => (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s
      map_add' := fun s t => map_add _ s t
      map_smul' := fun a (s : Γ(M, ⊤)) => by
        change (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom
            ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) • s) =
          ((U.ι.appIso ⊤).inv (((Scheme.ΓSpecIso (.of k)).inv ≫ (U.ι ≫ f).appTop).hom a)) •
            ((M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom s)
        refine (M.val.map_smul (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op _ s).trans ?_
        congr 1
        exact (congrArg (fun φ => φ.hom ((((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a)))
          (Scheme.Hom.app_appIso_inv U.ι ⊤)).symm }
  have hbij : Function.Bijective g := by
    have : IsIso (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op) := by
      have : (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤) = eqToHom (image_top_eq_top hU) :=
        Subsingleton.elim _ _
      rw [this, eqToHom_op, eqToHom_map]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op)
  exact (LinearEquiv.ofBijective g hbij).finrank_eq.symm

/-- **Riemann–Roch in large degree for `𝒪_C(D)`.** On a smooth proper curve over `k = k̄` with
canonical divisor `K`, `h⁰(D) = deg D + 1 - g` once `deg D > deg K = 2g - 2`, where
`g = h⁰(K)`. -/
private theorem h0_eq_sum_coeff_add_one_sub_h0_canonical
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (D : Divisor C)
    (hdeg : (K.sum fun _ a => a) < D.sum fun _ a => a) :
    (D.h0 k sC : ℤ) = (D.sum fun _ a => a) + 1 - K.h0 k sC := by
  obtain ⟨hcurve, hsmooth, hprop, hiso⟩ := curve_instances hC hsm hp hK.1 hsm
  set pY := (smoothLocus sC).ι ≫ sC
  have hdim : topologicalKrullDim (smoothLocus sC).toScheme ≤ 1 := by
    have : IsIso (smoothLocus sC).ι := by rw [hsm, ← Scheme.topIso_hom]; infer_instance
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (smoothLocus sC).ι)).isHomeomorph, hK.1]
    exact le_of_eq rfl
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have := (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D).isInvertibleModule_divisorialSheaf
  have h1 := degreeOn_smoothLocus_eq_sum hC hsm hp hK.1 hdim D
  have hg := h0_canonical_eq_genus hC hsm hp hK
  have hKz : ((K.sum fun _ a => a : ℤ) : ℚ) = K.sum fun _ a => (a : ℚ) := by simp [Finsupp.sum]
  have hKint : (K.sum fun _ a => a : ℤ) = 2 * (K.h0 k sC : ℤ) - 2 := by
    have : ((K.sum fun _ a => a : ℤ) : ℚ) = 2 * (K.h0 k sC : ℚ) - 2 :=
      hKz.trans (sum_coeff_canonical_eq hC hsm hp hK)
    exact_mod_cast this
  change invertibleCurveDegree k pY hdim
    ((Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf) = _ at h1
  let e := (Scheme.Modules.restrictFunctorIsoPullback (smoothLocus sC).ι).app D.divisorialSheaf
  set M := (Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf
  have hM : SheafOfModules.IsInvertible (smoothLocus sC).toScheme.sheaf.obj
      (smoothLocus sC).toScheme.ringCatSheaf.property M :=
    (inferInstance : SheafOfModules.IsInvertible (smoothLocus sC).toScheme.presheaf
      (smoothLocus sC).toScheme.ringCatSheaf.2 M)
  have hrr := finrank_cohomologyOverField_zero_sub_one_eq k pY hdim M hM
  rw [finrank_cohomologyOverField_unit_zero_eq_one pY] at hrr
  have hvan := isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree
    k pY M hM (by
      change _ ≤ invertibleCurveDegree k pY hdim M
      rw [h1, ← hg]; omega)
  have hone : Module.finrank k (cohomologyOverField k pY M 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hvan
    Module.finrank_zero_of_subsingleton
  change _ = invertibleCurveDegree k pY hdim M + _ - _ at hrr
  rw [hone, h1, ← hg] at hrr
  push_cast at hrr
  rw [sub_zero] at hrr
  rw [← hrr]
  congr 1
  calc D.h0 k sC = Module.finrank k ((globalSectionsOver sC).obj D.divisorialSheaf) := rfl
    _ = Module.finrank k ((globalSectionsOver pY).obj
          (D.divisorialSheaf.restrict (smoothLocus sC).ι)) :=
        (finrank_globalSectionsOver_restrict sC _ hsm).symm
    _ = Module.finrank k ((globalSectionsOver pY).obj
          ((Scheme.Modules.pullback (smoothLocus sC).ι).obj D.divisorialSheaf)) :=
        ((globalSectionsOver pY).mapIso e).toLinearEquiv.finrank_eq
    _ = _ := (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver pY _).finrank_eq.symm

/-- On an integral scheme, the valuation along `Γ` of an element of the factor of `K(X)` is the
order of vanishing of its image in the function field. -/
private theorem valuation_eq_ordHom {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (Γ : MMP.Mori.PrimeDivisor X)
    (y : X.presheaf.stalk (componentGenericPoint X Γ.component)) :
    Γ.valuation y = X.ordHom Γ.genericPoint Γ.coheight_genericPoint
      ((MMP.Positivity.componentToFunctionField Γ.component).hom y) := by
  let := Γ.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions Γ.genericPoint_mem_component
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  let ψ := IsLocalization.algEquiv (nonZeroDivisors Γ.localRing)
    (X.presheaf.stalk (componentGenericPoint X Γ.component)) (FractionRing Γ.localRing)
  change Ring.ordFrac Γ.localRing (ψ y) = Ring.ordFrac (X.presheaf.stalk Γ.genericPoint) _
  have key := MMP.Positivity.ordFrac_map_of_comp (R := Γ.localRing)
    (K₁ := FractionRing Γ.localRing) (K₂ := X.functionField)
    ((MMP.Positivity.componentToFunctionField Γ.component).hom.comp (ψ.symm : _ →+* _)) ?_ (ψ y)
  · simpa using key.symm
  · intro r
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    change (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom r =
      (X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- The generization from the factor of `K(X)` on a component to the function field is
injective. -/
private theorem eq_zero_of_componentToFunctionField_eq_zero {X : Scheme.{u}} [IsIntegral X]
    (Z : irreducibleComponents X) (y : X.presheaf.stalk (componentGenericPoint X Z))
    (hy : (MMP.Positivity.componentToFunctionField Z).hom y = 0) : y = 0 := by
  by_contra hy0
  exact ((MMP.Mori.isUnit_of_ne_zero_stalk Z hy0).map
    (MMP.Positivity.componentToFunctionField Z).hom).ne_zero hy

/-- **A rational function of exact order at a point in large degree.** If `deg D > deg K + 1`,
some nonzero `f ∈ H⁰(C, 𝒪_C(D))` has exact order `-coeff_Q D` along `Q`. -/
private theorem exists_ord_ge_neg_coeff_and_ord_eq
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (D : Divisor C)
    (hdeg : (K.sum fun _ a => a) + 1 < D.sum fun _ a => a) (Q : MMP.Mori.PrimeDivisor C) :
    ∃ f : C.functionField, f ≠ 0 ∧ (∀ Γ : MMP.Mori.PrimeDivisor C,
      -D.coeff Γ ≤ C.ord f Γ.genericPoint) ∧ C.ord f Q.genericPoint + D.coeff Q = 0 := by
  classical
  set D' : Divisor C := D - Finsupp.single Q 1 with hD'
  have hdegD' : (D'.sum fun _ a => a) = (D.sum fun _ a => a) - 1 := by
    rw [hD', Finsupp.sum_sub_index (fun _ _ _ => rfl)]; simp
  have h1 := h0_eq_sum_coeff_add_one_sub_h0_canonical hC hsm hp hK D (by omega)
  have h2 := h0_eq_sum_coeff_add_one_sub_h0_canonical hC hsm hp hK D' (by omega)
  have hne : D'.divisorialSubmodule ⊤ ≠ D.divisorialSubmodule ⊤ := by
    intro heq
    have : D'.h0 k sC = D.h0 k sC := by unfold Divisor.h0; rw [heq]
    omega
  have hle : D'.divisorialSubmodule ⊤ ≤ D.divisorialSubmodule ⊤ :=
    Divisor.divisorialSubmodule_mono (sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)) ⊤
  obtain ⟨φ, hφD, hφD'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  -- every prime divisor lies on the unique component of `C`
  have huniv : ∀ Z : irreducibleComponents C, Z.1 = Set.univ := fun Z =>
    Z.2.eq_of_le (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _)
  have hmemE : ∀ E : MMP.Mori.PrimeDivisor C, (E.support ∩ (⊤ : C.Opens)).Nonempty := fun E =>
    ⟨E.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl, trivial⟩
  have hp' : ∀ (Z : irreducibleComponents C) (hZ : componentGenericPoint C Z ∈ (⊤ : C.Opens)),
      (MMP.Positivity.componentToFunctionField Z).hom (φ ⟨Z, hZ⟩) =
        (MMP.Positivity.componentToFunctionField Q.component).hom
          (φ ⟨Q.component, Q.componentGenericPoint_mem_of_nonempty (hmemE Q)⟩) := by
    intro Z hZ
    have : Z = Q.component := Subtype.ext ((huniv _).trans (huniv _).symm)
    subst this; rfl
  set f := (MMP.Positivity.componentToFunctionField Q.component).hom
    (φ ⟨Q.component, Q.componentGenericPoint_mem_of_nonempty (hmemE Q)⟩) with hf
  -- the order condition along `E`, read in the function field
  have hord : ∀ (E : MMP.Mori.PrimeDivisor C) (a : ℤ),
      E.OrdGE a (φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty (hmemE E)⟩) ↔
        f = 0 ∨ a ≤ C.ord f E.genericPoint := by
    intro E a
    have hfE := hp' E.component (E.componentGenericPoint_mem_of_nonempty (hmemE E))
    unfold MMP.Mori.PrimeDivisor.OrdGE
    rw [valuation_eq_ordHom, hfE]
    by_cases hf0 : f = 0
    · simp only [hf0, true_or, iff_true]
      left
      exact eq_zero_of_componentToFunctionField_eq_zero _ _ (hfE.trans hf0)
    · rw [Scheme.le_ord_iff E.coheight_genericPoint hf0]
      have : φ ⟨E.component, E.componentGenericPoint_mem_of_nonempty (hmemE E)⟩ ≠ 0 := by
        intro h; apply hf0; rw [← hfE, h, map_zero]
      simp only [this, hf0, false_or]
      rfl
  have hf0 : f ≠ 0 := by
    intro h0
    exact hφD' fun E hE => (hord E _).2 (Or.inl h0)
  have hD : ∀ Γ : MMP.Mori.PrimeDivisor C, -D.coeff Γ ≤ C.ord f Γ.genericPoint := fun Γ =>
    ((hord Γ _).1 (hφD Γ (hmemE Γ))).resolve_left hf0
  have hD'coeff : ∀ Γ, D'.coeff Γ = D.coeff Γ - if Γ = Q then 1 else 0 := fun Γ => by
    simp [hD', DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, eq_comm]
  refine ⟨f, hf0, hD, ?_⟩
  by_contra hQ
  apply hφD'
  intro E hE
  refine (hord E _).2 (Or.inr ?_)
  have := hD E
  rw [hD'coeff]
  split_ifs with hEQ
  · subst hEQ; omega
  · omega

/-- **A section of exact order at a point in large degree.** If `deg(nK + E) > deg K + 1`, then
`𝒪_C(nK + E)` has a global section with exact order `-coeff_Q E` along `Q`. -/
private theorem exists_mem_pluricanonicalSections_ordForm_add_coeff_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (n : ℕ) (E : Divisor C)
    (hdeg : (K.sum fun _ a => a) + 1 < n * (K.sum fun _ a => a) + E.sum fun _ a => a)
    (Q : MMP.Mori.PrimeDivisor C) :
    ∃ u ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤, u ≠ 0 ∧ Q.ordForm u + E.coeff Q = 0 := by
  have : LocallyOfFiniteType sC := hC.1.toLocallyOfFiniteType
  have hd : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞) := by rw [hK.1]
  obtain ⟨θ, hθ0, hθ⟩ := exists_ordForm_eq_mul_coeff hC hK Q n
  set D : Divisor C := (n : ℤ) • K + E with hD
  have hcoeff : ∀ Γ, D.coeff Γ = n * K.coeff Γ + E.coeff Γ := fun Γ => by
    simp [hD, DivisorWithCoeffs.coeff_apply]
  have hdegD : (D.sum fun _ a => a) = n * (K.sum fun _ a => a) + E.sum fun _ a => a := by
    rw [hD, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_smul_index' (fun _ => rfl)]
    simp [Finsupp.sum, Finset.mul_sum]
  obtain ⟨f, hf0, hf, hfQ⟩ := exists_ord_ge_neg_coeff_and_ord_eq hC hsm hp hK D
    (by rw [hdegD]; exact hdeg) Q
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor C,
      Γ.ordForm (f • θ) = C.ord f Γ.genericPoint + n * K.coeff Γ := fun Γ => by
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd hf0 hθ0, hθ]
  refine ⟨f • θ, mem_pluricanonicalSections_top_iff.2 fun Γ => Or.inr ?_,
    smul_ne_zero hf0 hθ0, ?_⟩
  · have := hf Γ; rw [hcoeff] at this; rw [hord]; omega
  · rw [hord]; rw [hcoeff] at hfQ; omega

/-- **Fibre surjectivity of pluricanonical sections of large degree on a curve.** If
`deg(nK + E) - #S > deg K`, global sections of `𝒪_C(nK + E)` surject onto the fibres at the
points of `S`. The points are added one at a time: a section already right at the points of
`T` is corrected at a new point `Q₀` by a section of `𝒪(nK + E - T)` of exact order at `Q₀`. -/
private theorem exists_mem_pluricanonicalSections_sub_vanishes_of_degree
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1) (n : ℕ) (E : Divisor C)
    (S : Finset (MMP.Mori.PrimeDivisor C))
    (hdeg : (K.sum fun _ a => a) + (S.card : ℤ) < n * (K.sum fun _ a => a) + E.sum fun _ a => a)
    (τ : MMP.Mori.PrimeDivisor C → RationalPluriForms sC 1 (n : ℕ))
    (hτ : ∀ Q ∈ S, τ Q = 0 ∨ 0 ≤ Q.ordForm (τ Q) + E.coeff Q) :
    ∃ s ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤,
      ∀ Q ∈ S, s - τ Q = 0 ∨ 1 ≤ Q.ordForm (s - τ Q) + E.coeff Q := by
  classical
  suffices H : ∀ T ⊆ S, ∃ s ∈ pluricanonicalSections sC 1 (n : ℕ) E ⊤,
      ∀ Q ∈ T, VanishesTo Q (1 - E.coeff Q) (s - τ Q) by
    obtain ⟨s, hs, hsT⟩ := H S subset_rfl
    exact ⟨s, hs, fun Q hQ => (hsT Q hQ).imp id fun h => by omega⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun _ => ⟨0, zero_mem _, fun Q hQ => absurd hQ (Finset.notMem_empty Q)⟩
  | @insert Q₀ T hQ₀ ih =>
    intro hTS
    obtain ⟨s, hs, hsT⟩ := ih ((Finset.subset_insert _ _).trans hTS)
    set E' : Divisor C := E - ∑ Q ∈ T, Finsupp.single Q 1 with hE'
    have hcoeff' : ∀ Q, E'.coeff Q = E.coeff Q - if Q ∈ T then 1 else 0 := fun Q => by
      simp only [hE', DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply, Finsupp.finset_sum_apply,
        Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hdegE' : (E'.sum fun _ a => a) = (E.sum fun _ a => a) - T.card := by
      rw [hE', Finsupp.sum_sub_index (fun _ _ _ => rfl),
        ← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    have hcard : T.card + 1 ≤ S.card := by
      simpa [Finset.card_insert_of_notMem hQ₀] using Finset.card_le_card hTS
    obtain ⟨u, hu, hu0, hue⟩ := exists_mem_pluricanonicalSections_ordForm_add_coeff_eq_zero
      hC hsm hp hK n E' (by rw [hdegE']; push_cast at hdeg ⊢; omega) Q₀
    have hE'Q₀ : E'.coeff Q₀ = E.coeff Q₀ := by rw [hcoeff', if_neg hQ₀, sub_zero]
    rw [hE'Q₀] at hue
    have hw : VanishesTo Q₀ (-E.coeff Q₀) (τ Q₀ - s) := by
      refine VanishesTo.sub ?_ (mem_pluricanonicalSections_top_iff.1 hs Q₀)
      exact (hτ Q₀ (hTS (Finset.mem_insert_self _ _))).imp id fun h => by omega
    obtain ⟨c, hc⟩ := exists_vanishesTo_sub_const_smul hC hK.1 Q₀ (E.coeff Q₀) hu0 hue hw
    have hu' := mem_pluricanonicalSections_top_iff.1 hu
    refine ⟨s + c • u, ?_, fun Q hQ => ?_⟩
    · refine mem_pluricanonicalSections_top_iff.2 fun Q =>
        ((mem_pluricanonicalSections_top_iff.1 hs Q).add ?_)
      refine ((hu' Q).const_smul c).mono ?_
      rw [hcoeff']; split_ifs <;> omega
    · rcases Finset.mem_insert.1 hQ with rfl | hQT
      · rw [show s + c • u - τ Q = -(τ Q - s - c • u) by abel]
        exact hc.neg
      · rw [show s + c • u - τ Q = (s - τ Q) + c • u by abel]
        refine (hsT Q hQT).add (((hu' Q).const_smul c).mono ?_)
        rw [hcoeff', if_pos hQT]; omega

/-- **The degree estimate.** If `deg G = m · deg Δ` with `m ≥ 1`, `deg K + deg Δ > 0`, `G`
integral and `c ≤ 1 + deg Δ`, then `deg K + c < 12m · deg K + 12 · deg G`. The key point is that
`m(deg K + deg Δ) = m · deg K + deg G` is a positive integer, hence at least `1`. -/
private theorem add_lt_twelve_mul_add_twelve_mul {a b : ℤ} {D : ℚ} {m c : ℕ} (hm : 0 < m)
    (hb : (b : ℚ) = m * D) (hd : 0 < (a : ℚ) + D) (hc : (c : ℚ) ≤ 1 + D) :
    a + (c : ℤ) < ((12 * m : ℕ) : ℤ) * a + 12 * b := by
  have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℤ) < m * a + b := by
    have : (0 : ℚ) < m * a + b := by rw [hb]; nlinarith
    exact_mod_cast this
  have h1 : (1 : ℚ) ≤ m * a + b := by exact_mod_cast hpos
  have : (a : ℚ) + c < (12 * m : ℚ) * a + 12 * b := by
    rw [hb] at h1 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hmq) hd.le]
  push_cast
  exact_mod_cast this

/-- For a `ℚ`-divisor with nonnegative coefficients, the number of components of coefficient
`≥ 1` is at most the degree. -/
private theorem card_filter_one_le_le_sum {α : Type*} (Δ : α →₀ ℚ) (hΔ : ∀ a, 0 ≤ Δ a) :
    ((Δ.support.filter (fun a => 1 ≤ Δ a)).card : ℚ) ≤ Δ.sum fun _ a => a := by
  classical
  calc ((Δ.support.filter (fun a => 1 ≤ Δ a)).card : ℚ)
      = ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), (1 : ℚ) := by simp
    _ ≤ ∑ a ∈ Δ.support.filter (fun a => 1 ≤ Δ a), Δ a :=
      Finset.sum_le_sum fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑ a ∈ Δ.support, Δ a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a _ _ => hΔ a

/-- If `G = mΔ` coefficientwise, then `deg G = m · deg Δ`. -/
private theorem cast_sum_coeff_eq_mul_sum {C : Scheme.{u}} [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] {Δ : QWeilDivisor C} {m : ℕ} {G : Divisor C}
    (hG : ∀ Γ : WeilDivisorPrime C, (G.coeff Γ.1 : ℚ) = m * Δ Γ) :
    ((G.sum fun _ a => a : ℤ) : ℚ) = m * Δ.sum (fun _ a => a) := by
  classical
  let v : WeilDivisorPrime C → MMP.Mori.PrimeDivisor C := fun Γ => Γ.1
  have hvinj : Function.Injective v := fun _ _ h => Subtype.ext h
  have hmap : (Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero G) =
      m • Finsupp.mapDomain v Δ := by
    refine Finsupp.ext fun Q => ?_
    obtain ⟨Γ, rfl⟩ : ∃ Γ : WeilDivisorPrime C, v Γ = Q :=
      ⟨⟨Q, inferInstance, Q.isDiscreteValuationRing_localRing⟩, rfl⟩
    rw [Finsupp.mapRange_apply, Finsupp.smul_apply, Finsupp.mapDomain_apply_of_injective hvinj,
      nsmul_eq_mul]
    exact hG Γ
  have h1 : ((G.sum fun _ a => a : ℤ) : ℚ) =
      (Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero G).sum fun _ a => a := by
    rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
    simp [Finsupp.sum]
  rw [h1, hmap, Finsupp.sum_smul_index' (fun _ => rfl),
    Finsupp.sum_mapDomain_index (fun _ => smul_zero _) (fun _ _ _ => smul_add _ _ _)]
  simp [Finsupp.sum, Finset.mul_sum, nsmul_eq_mul]

/-- **Global sections of `𝒪(12m(K_C + Δ))` surject onto the fibres at `P` and `⌊Δ⌋`** (proof of
FA 12.2.11, case (12.2.11.4)). Let `C` be a smooth connected proper curve over an algebraically
closed field `k` with canonical divisor `K`, `Δ` a boundary on `C`, `m > 0` and `G = mΔ` integral,
with `deg(K_C + Δ) > 0`, and let `P` be a closed point of `C` not in `⌊Δ⌋`. Then for every
choice of local sections `τ_Q` of `L = 𝒪_C(12m(K_C + Δ))` at the points `Q ∈ {P} ∪ ⌊Δ⌋` there is
`s ∈ H⁰(C, L)` such that `s - τ_Q` vanishes at each such `Q`: the restriction
`H⁰(C, L) → L(P) ⊕ ⨁_{Q ∈ ⌊Δ⌋} L(Q)` is surjective.

`L` is `MMP.Mori.pluricanonicalSections sC 1 (12m) (12 G)`; `τ` is a local section of `L` at `Q`
when `τ = 0` or `ord_Q(τ) + 12 coeff_Q(G) ≥ 0`, and vanishes at `Q` when `τ = 0` or
`ord_Q(τ) + 12 coeff_Q(G) ≥ 1`. The points of `⌊Δ⌋` are the prime divisors `Q` with
`Δ_Q ≥ 1`; the degree of a divisor is the sum of its coefficients. -/
@[mmp "lem_fa12a_normalized_sections_positive_degree"]
public theorem QWeilDivisor.IsBoundary.exists_mem_pluricanonicalSections_sub_vanishes
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    [IsIntegral C] [IsLocallyNoetherian C] [IsNormal C]
    (hC : IsNormalVariety k sC) (hsm : IsSmoothScheme sC) (hp : IsProper sC)
    {K : Divisor C} (hK : K.IsCanonicalDivisor sC 1)
    {Δ : QWeilDivisor C} (hΔ : Δ.IsBoundary sC) {m : ℕ} (hm : 0 < m) {G : Divisor C}
    (hG : ∀ Γ : WeilDivisorPrime C, (G.coeff Γ.1 : ℚ) = m * Δ Γ)
    (hdeg : 0 < (K.sum fun _ a => (a : ℚ)) + Δ.sum (fun _ a => a))
    (P : Mori.PrimeDivisor C) (hP : ¬ ∃ Γ : WeilDivisorPrime C, Γ.1 = P ∧ 1 ≤ Δ Γ)
    (τ : Mori.PrimeDivisor C → RationalPluriForms sC 1 (12 * m : ℕ))
    (hτ : ∀ Q : Mori.PrimeDivisor C, (Q = P ∨ ∃ Γ : WeilDivisorPrime C, Γ.1 = Q ∧ 1 ≤ Δ Γ) →
      τ Q = 0 ∨ 0 ≤ Q.ordForm (τ Q) + 12 * G.coeff Q) :
    ∃ s ∈ pluricanonicalSections sC 1 (12 * m : ℕ) ((12 : ℤ) • G) ⊤,
      ∀ Q : Mori.PrimeDivisor C, (Q = P ∨ ∃ Γ : WeilDivisorPrime C, Γ.1 = Q ∧ 1 ≤ Δ Γ) →
        s - τ Q = 0 ∨ 1 ≤ Q.ordForm (s - τ Q) + 12 * G.coeff Q := by
  classical
  set F := Δ.support.filter (fun Γ => 1 ≤ Δ Γ)
  set S : Finset (MMP.Mori.PrimeDivisor C) := insert P (F.image fun Γ => Γ.1) with hSdef
  have hmemS : ∀ Q, Q ∈ S ↔ (Q = P ∨ ∃ Γ : WeilDivisorPrime C, Γ.1 = Q ∧ 1 ≤ Δ Γ) := by
    intro Q
    simp only [hSdef, F, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finsupp.mem_support_iff]
    refine or_congr_right ⟨?_, ?_⟩
    · rintro ⟨Γ, ⟨-, h1⟩, h⟩; exact ⟨Γ, h, h1⟩
    · rintro ⟨Γ, h, h1⟩; exact ⟨Γ, ⟨by linarith, h1⟩, h⟩
  have hcoeff : ∀ Q, ((12 : ℤ) • G).coeff Q = 12 * G.coeff Q := fun Q => by
    simp [DivisorWithCoeffs.coeff_apply]
  have hcard : (S.card : ℚ) ≤ 1 + Δ.sum (fun _ a => a) := by
    have h1 : S.card ≤ 1 + F.card := (Finset.card_insert_le _ _).trans <| by
      have := Finset.card_image_le (f := fun Γ : WeilDivisorPrime C => Γ.1) (s := F); omega
    have h1' : (S.card : ℚ) ≤ 1 + (F.card : ℚ) := by exact_mod_cast h1
    linarith [card_filter_one_le_le_sum Δ fun Γ => (hΔ.2.2.2 Γ).1]
  have hkey := add_lt_twelve_mul_add_twelve_mul (a := K.sum fun _ a => a) hm
    (cast_sum_coeff_eq_mul_sum hG) (by simpa [Finsupp.sum] using hdeg) hcard
  obtain ⟨s, hs, hsS⟩ := exists_mem_pluricanonicalSections_sub_vanishes_of_degree hC hsm hp hK
    (12 * m) ((12 : ℤ) • G) S
    (by rw [Finsupp.sum_smul_index' (fun _ => rfl)]; simpa [Finsupp.sum, Finset.mul_sum] using hkey)
    τ fun Q hQ => by rw [hcoeff]; exact hτ Q ((hmemS Q).1 hQ)
  refine ⟨s, hs, fun Q hQ => ?_⟩
  simpa [hcoeff] using hsS Q ((hmemS Q).2 hQ)

end NormalizedSections

end MMP.Flips
