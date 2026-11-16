module

public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.Curves.Maps.ScalarAutomorphisms
public import StacksFrontier.AlgebraicGeometry.PicardUFD.AffineScheme
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.LocalGenerator
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseChangeTensor

/-!
# Pinned data of the family of curve maps, constancy at marked points, injectivity on points

Let `M = curveMapSpace` be the coefficient space of tuples of sections of an invertible sheaf `L`
on a proper `k`-scheme `C` (`finalSpace` for a family of closed conditions `q`), with its family
`Φ : C ×ₖ M → ℙⁿ_k` (`finalFamily`). Every `T`-point `h` of `M` gives the tuple of sections
`σᵢ = Σⱼ (h^* xᵢⱼ) eⱼ` of `L` on `C ×ₖ T`, and `Φ|_T` has the pinned isomorphism
`Φ|_T^* 𝒪(1) ≅ pr_C^* L` carrying `Φ|_T^* Tᵢ` to `σᵢ`.

## Main results

* `MMP.Fourfold.exists_pinned_finalFamily_comp`: that pinned isomorphism, in coordinates, base
  changed along an arbitrary morphism.
* `MMP.Fourfold.eq_of_pinned_of_proportional`: two morphisms to `ℙⁿ_S` whose pinned tuples are
  proportional (`aᵢ b_{i'} = a_{i'} bᵢ`, one `b_{i₀}` a unit) are equal.
* `MMP.Fourfold.exists_marked_point_data`, `MMP.Fourfold.exists_marked_points_data`: for a
  `k`-point `P_β` of `C` and a generating tuple `τᵢ = Σⱼ aᵢⱼ eⱼ` of `L`, the values `ℓ_β` of the
  sections `e` in a frame of the fibre `P_β^* L`, the value `c_β = f(P_β)` in that frame, a
  normalizing functional `μ`, and the proportionality relations of the tuple `a` (the hypotheses
  `hprop`, `hnorm` of `MMP.Fourfold.exists_kPoint_curveMapSpace`).
* `MMP.Fourfold.finalSpace_markedMap_comp_finalFamily`,
  `MMP.Fourfold.curveMapSpace_markedMap_comp_family`: the family restricted to `P_β × M` is the
  constant map `f(P_β)`, when the closed conditions contain the proportionality conditions at
  `P_β`.
* `MMP.Fourfold.finalSpace_point_injective`, `MMP.Fourfold.curveMapSpace_point_injective`,
  `MMP.Fourfold.finalSpace_point_injective_of_mono`: for `C` proper integral over an
  algebraically closed field, two `K`-points of `M` with the same map `C_K → ℙⁿ` (or `→ U` through
  a monomorphism `U ⟶ ℙⁿ`) coincide.

## Implementation notes

The proof of constancy compares the two pinned isomorphisms through the section `V` of
`(o ≫ P)^* L` induced by a frame of the fibre; the tuples are `aᵢ V` and `bᵢ V`, and
`a_{i₀}` is a unit because the pinned tuple has no common zero
(`MMP.Fourfold.exists_iso_of_proportional`). For injectivity the isomorphism of `L_K` between two
tuples is a scalar (`H⁰(C_K, 𝒪) = K`), and the normalization forces it to be `1`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Stacks.ProjectiveFromSections Stacks.NonvanishingOpen
open Stacks.Ample (IsInvertibleModule nonvanishingLocus)

universe u

namespace MMP.Fourfold

section Pinned

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

/-- **Pinned data pulled back along a morphism**: a pinned isomorphism `Φ₁^* 𝒪(1) ≅ N` carrying
`Φ₁^* Tᵢ` to `sᵢ` pulls back along `r` to a pinned isomorphism `(r ≫ Φ₁)^* 𝒪(1) ≅ r^* N` carrying
`(r ≫ Φ₁)^* Tᵢ` to `r^* sᵢ`. -/
theorem exists_iso_pinned_pullback {X Y : Scheme.{u}} {n : ℕ} (r : X ⟶ Y)
    (Φ₁ : Y ⟶ projectiveSpaceAtUniverse.{u} n) (Φ₂ : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (hΦ : r ≫ Φ₁ = Φ₂) {N : Y.Modules} (s : Fin (n + 1) → Γ(N, ⊤))
    (α : (Scheme.Modules.pullback Φ₁).obj (twistingSheafAtUniverse.{u} n) ⟶ N) [IsIso α]
    (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u} Φ₁ i) = s i) :
    ∃ α' : (Scheme.Modules.pullback Φ₂).obj (twistingSheafAtUniverse.{u} n) ⟶
        (Scheme.Modules.pullback r).obj N,
      IsIso α' ∧ ∀ i, α'.app ⊤ (pullbackCoordSection.{u} Φ₂ i) =
        AlgebraicGeometry.pullbackGlobalSections r N (s i) := by
  subst hΦ
  refine ⟨(Scheme.Modules.pullbackComp r Φ₁).inv.app (twistingSheafAtUniverse.{u} n) ≫
    (Scheme.Modules.pullback r).map α, inferInstance, fun i => ?_⟩
  have := pullbackComp_inv_map_pullbackGlobalSections r Φ₁ α (coordGlobalSection.{u} n i)
  rw [← hα i]
  exact this

end Pinned

section Family

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.LinearSystemScheme (coordSection coordSection_pullback)

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **The pulled-back module of the family, in coordinates.** For a `T`-point `g` of the
coefficient space and `r : X ⟶ C ×ₖ T`, the pullback along `r` of `pr_C^* L` (twisted through
`familyModule g`) is isomorphic to the pullback of `L` along `r ≫ pr_C`, and the pulled-back
`i`-th section of the family goes to the coordinate section with coordinates `g^* x_{ij}`. -/
theorem exists_iso_familyModule_pullback {T X : Scheme.{u}} (g : T ⟶ coefficientSpace n N k)
    (r : X ⟶ pullback sC (g ≫ coefficientSpaceOver n N k)) (ρ₁ : X ⟶ C) (ρ₂ : X ⟶ T)
    (hρ₁ : r ≫ pullback.fst sC (g ≫ coefficientSpaceOver n N k) = ρ₁)
    (hρ₂ : r ≫ pullback.snd sC (g ≫ coefficientSpaceOver n N k) = ρ₂) :
    ∃ γ : (Scheme.Modules.pullback r).obj
        (familyModule (n := n) (N := N) (L := L) (sC := sC) g) ≅
        (Scheme.Modules.pullback ρ₁).obj L,
      ∀ i, γ.hom.app ⊤ (AlgebraicGeometry.pullbackGlobalSections r _
          (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g i)) =
        coordSection ρ₁ ρ₂ L e (fun j => g.appTop (coefficientCoord n N k i j)) := by
  subst hρ₂
  have hρ : (r ≫ familyPullbackMap (n := n) (N := N) (sC := sC) g) ≫
      pullback.fst sC (coefficientSpaceOver n N k) = ρ₁ := by
    rw [Category.assoc, familyPullbackMap_fst, hρ₁]
  subst hρ
  obtain ⟨γ1, hγ1⟩ := exists_iso_pullbackGlobalSections_comp r
    (familyPullbackMap (n := n) (N := N) (sC := sC) g)
    (r ≫ familyPullbackMap (n := n) (N := N) (sC := sC) g) rfl
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
  refine ⟨γ1 ≪≫ (Scheme.Modules.pullbackComp (r ≫ familyPullbackMap (n := n) (N := N) (sC := sC) g)
    (pullback.fst sC (coefficientSpaceOver n N k))).app L, fun i => ?_⟩
  change ((Scheme.Modules.pullbackComp (r ≫ familyPullbackMap (n := n) (N := N) (sC := sC) g)
    (pullback.fst sC (coefficientSpaceOver n N k))).hom.app L).app ⊤ (γ1.hom.app ⊤ _) = _
  unfold familySection
  rw [hγ1]
  unfold universalSection
  rw [coordSection_pullback]
  simp only [Stacks.LinearSystemScheme.coordSection, Category.assoc, familyPullbackMap_snd,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- **The pinned isomorphism of the family, base changed along any morphism.** Let `h : T' ⟶ M₁`
be a point of the scheme of tuples without common zero over `sT'`, and `u : X ⟶ C ×ₖ T'`. The
composite `Q = u ≫ Φ|_{T'}` has `Q^* 𝒪(1) ≅ ρ₁^* L` (`ρ₁ = u ≫ pr_C`) carrying `Q^* Tᵢ` to the
coordinate section of coordinates `(h ≫ ι)^* x_{ij}`. -/
theorem exists_pinned_family_comp [IsProper sC] {T' : Scheme.{u}} {sT' : T' ⟶ Spec (.of k)}
    (h : T' ⟶ noCommonZeroScheme (n := n) sC L e)
    (hh : h ≫ noCommonZeroScheme.over (n := n) sC L e = sT')
    {X : Scheme.{u}} (u : X ⟶ pullback sC sT') (ρ₁ : X ⟶ C) (ρ₂ : X ⟶ T')
    (hρ₁ : u ≫ pullback.fst sC sT' = ρ₁) (hρ₂ : u ≫ pullback.snd sC sT' = ρ₂)
    (Q : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hQ : u ≫ familyMapOfHom sC h hh ≫ noCommonZeroFamily (n := n) sC L e = Q) :
    ∃ α : (Scheme.Modules.pullback
        (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} n) ⟶ (Scheme.Modules.pullback ρ₁).obj L,
      IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection.{u}
        (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
        coordSection ρ₁ ρ₂ L e
          (fun j => (h ≫ noCommonZeroScheme.ι (n := n) sC L e).appTop
            (coefficientCoord n N k i j)) := by
  obtain ⟨αM, hiso, hαM⟩ := exists_iso_noCommonZeroFamily (n := n) sC L e
  obtain ⟨α', hα'iso, hα'⟩ := exists_iso_pinned_pullback (u ≫ familyMapOfHom sC h hh)
    (noCommonZeroFamily (n := n) sC L e ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (by rw [← hQ]; simp) _ αM hαM
  obtain ⟨γ, hγ⟩ := exists_iso_familyModule_pullback (n := n) (N := N) sC L e
    (noCommonZeroScheme.ι (n := n) sC L e) (u ≫ familyMapOfHom sC h hh) ρ₁ (ρ₂ ≫ h)
    (by rw [Category.assoc, familyMapOfHom_fst, hρ₁])
    (by rw [Category.assoc, familyMapOfHom_snd, ← Category.assoc, hρ₂])
  refine ⟨α' ≫ γ.hom, inferInstance, fun i => ?_⟩
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hα', hγ]
  simp only [Stacks.LinearSystemScheme.coordSection, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

end Family

section Final

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.LinearSystemScheme (coordSection coordSection_pullback)

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))
  [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- The inclusion of `M` into the coefficient space `𝔸(H⁰(C, L)^{n+1})`. -/
abbrev finalSpace.toCoefficientSpace : finalSpace (n := n) sC L e q Zc hZc ⟶
    coefficientSpace n N k :=
  finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q ≫
    closedLocus.ι (n := n) (N := N) (k := k) q

/-- The inclusion of `M` into the scheme of tuples without common zero. -/
def finalSpace.toNoCommonZero : finalSpace (n := n) sC L e q Zc hZc ⟶
    noCommonZeroScheme (n := n) sC L e :=
  finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.toNoCommonZero (n := n) sC L e q

/-- The inclusion of `M` into the scheme of tuples without common zero lies over `k`. -/
@[reassoc]
theorem finalSpace.toNoCommonZero_over :
    finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc ≫
        noCommonZeroScheme.over (n := n) sC L e =
      finalSpace.over (n := n) sC L e q Zc hZc := by
  unfold finalSpace.toNoCommonZero
  rw [Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_over]

/-- The inclusion of `M` into the scheme of tuples without common zero, followed by the inclusion
of that scheme into the coefficient space, is the inclusion of `M` into the coefficient space. -/
@[reassoc]
theorem finalSpace.toNoCommonZero_ι :
    finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc ≫ noCommonZeroScheme.ι (n := n) sC L e =
      finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc := by
  unfold finalSpace.toNoCommonZero
  rw [Category.assoc, closedNoCommonZeroScheme.toNoCommonZero_ι]

/-- The family `Φ : C ×ₖ M → ℙⁿ_k` of `M` is the base change along the inclusion of `M` into the
scheme of tuples without common zero, followed by the family of that scheme. -/
theorem finalFamily_eq :
    finalFamily (n := n) sC L e q Zc hZc =
      familyMapOfHom sC (finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc)
        (finalSpace.toNoCommonZero_over (n := n) sC L e q Zc hZc) ≫
      noCommonZeroFamily (n := n) sC L e := by
  unfold finalFamily closedNoCommonZeroFamily finalSpace.toNoCommonZero
  rw [← Category.assoc, ← familyMapOfHom_comp]

/-- **The pinned isomorphism of the family `Φ : C ×ₖ M → ℙⁿ_k` of `M`, base changed along any
morphism**: for `h : T' ⟶ M` over `sT'` and `u : X ⟶ C ×ₖ T'`, the composite
`Q = u ≫ Φ|_{T'}` has a pinned isomorphism `Q^* 𝒪(1) ≅ ρ₁^* L`, `ρ₁ = u ≫ pr_C`, carrying
`Q^* Tᵢ` to the coordinate section with coordinates `(h ≫ ι)^* x_{ij}`. -/
theorem exists_pinned_finalFamily_comp {T' : Scheme.{u}} {sT' : T' ⟶ Spec (.of k)}
    (h : T' ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hh : h ≫ finalSpace.over (n := n) sC L e q Zc hZc = sT')
    {X : Scheme.{u}} (u : X ⟶ pullback sC sT') (ρ₁ : X ⟶ C) (ρ₂ : X ⟶ T')
    (hρ₁ : u ≫ pullback.fst sC sT' = ρ₁) (hρ₂ : u ≫ pullback.snd sC sT' = ρ₂)
    (Q : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hQ : u ≫ familyMapOfHom sC h hh ≫ finalFamily (n := n) sC L e q Zc hZc = Q) :
    ∃ α : (Scheme.Modules.pullback
        (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
        (twistingSheafAtUniverse.{u} n) ⟶ (Scheme.Modules.pullback ρ₁).obj L,
      IsIso α ∧ ∀ i, α.app ⊤ (pullbackCoordSection.{u}
        (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
        coordSection ρ₁ ρ₂ L e
          (fun j => (h ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
            (coefficientCoord n N k i j)) := by
  have hh' : (h ≫ finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc) ≫
      noCommonZeroScheme.over (n := n) sC L e = sT' := by
    rw [Category.assoc, finalSpace.toNoCommonZero_over, hh]
  have key := exists_pinned_family_comp (n := n) (N := N) sC L e
    (h ≫ finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc) hh' u ρ₁ ρ₂ hρ₁ hρ₂ Q (by
      rw [← hQ, finalFamily_eq, familyMapOfHom_comp (sC := sC)
        (finalSpace.toNoCommonZero (n := n) sC L e q Zc hZc)
        (finalSpace.toNoCommonZero_over (n := n) sC L e q Zc hZc) h hh]
      simp only [Category.assoc])
  rw [Category.assoc, finalSpace.toNoCommonZero_ι] at key
  exact key

end Final

section Normalization

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))
  [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- The inclusion of `M` into the coefficient space lies over `k`. -/
@[reassoc]
theorem finalSpace.toCoefficientSpace_over :
    finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc ≫ coefficientSpaceOver n N k =
      finalSpace.over (n := n) sC L e q Zc hZc := by
  simp only [finalSpace.toCoefficientSpace, finalSpace.over, closedNoCommonZeroScheme.over,
    closedLocus.over, Category.assoc]

/-- **The functions of the closed conditions vanish on points of `M`.** -/
theorem appTop_toCoefficientSpace_eq_zero {T' : Scheme.{u}}
    (g : T' ⟶ finalSpace (n := n) sC L e q Zc hZc) (i : κ) :
    (g ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop (q i) = 0 :=
  (exists_lift_zeroLocusScheme_ι_iff (coefficientSpace n N k) q _).1
    ⟨g ≫ finalSpace.ι (n := n) sC L e q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L e q,
      by simp [finalSpace.toCoefficientSpace]⟩ i

/-- **The normalization at a point of `M`.** If the closed conditions include the normalization
`μ(σ) = 1`, then at every point `g : T' ⟶ M` over `sT'`, `Σᵢⱼ μᵢⱼ g^* xᵢⱼ = 1`. -/
theorem sum_appTop_toCoefficientSpace_normalization {T' : Scheme.{u}} {sT' : T' ⟶ Spec (.of k)}
    (μ : Fin (n + 1) → Fin N → k) (hμ : ∃ κ₀, q κ₀ = normalizationFunction n N k μ)
    (g : T' ⟶ finalSpace (n := n) sC L e q Zc hZc)
    (hg : g ≫ finalSpace.over (n := n) sC L e q Zc hZc = sT') :
    ∑ i, ∑ j, sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) *
      (g ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
        (coefficientCoord n N k i j) = 1 := by
  obtain ⟨κ₀, hκ₀⟩ := hμ
  have h0 := appTop_toCoefficientSpace_eq_zero (n := n) sC L e q Zc hZc g κ₀
  rw [hκ₀] at h0
  have hc : ∀ c : k, (g ≫ finalSpace.toCoefficientSpace (n := n) sC L e q Zc hZc).appTop
      (constFunction n N k c) = sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv c) := by
    intro c
    unfold constFunction
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      finalSpace.toCoefficientSpace_over, hg]
  unfold normalizationFunction linearFunction at h0
  simp only [map_sub, map_sum, map_mul, hc, map_one] at h0
  exact sub_eq_zero.1 h0

end Normalization

section Scalar

/-- **A scalar endomorphism acts on global sections by the image of the scalar.** -/
theorem app_top_eq_smul_of_eq_smul_id {K : Type u} [Field K] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of K)) (M : Y.Modules) (φ : M ⟶ M) (c : K)
    (h : letI := modulesLinearOverField K q; φ = c • 𝟙 M) (s : Γ(M, ⊤)) :
    φ.app ⊤ s = q.appTop ((Scheme.ΓSpecIso (.of K)).inv c) • s := by
  have h2 := IntegralTransformQcoh.sectionScalar_base K (Over.mk q) c M
  have h3 : φ =
      IntegralTransformQcoh.sectionScalar Y (q.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) M :=
    h.trans h2.symm
  rw [h3]
  exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionScalar_app_top _ M s

end Scalar

section Injectivity

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.LinearSystemScheme (coordSection coordSection_smul coordSection_bijective)

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ}
  (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))
  [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- **Injectivity of `M` on geometric points.** Let `C` be a proper integral `k`-scheme over an
algebraically closed field `k`, `w` a `k`-basis of `H⁰(C, L)`, and `M` the scheme of tuples without
common zero satisfying closed conditions `q` that contain the normalization `μ(σ) = 1`. Two
`K`-points `x, y` of `M` (`K ⊇ k` a field) with the same map `C_K → ℙⁿ_k` are equal. -/
theorem finalSpace_point_injective [IsAlgClosed k] [IsIntegral C] (μ : Fin (n + 1) → Fin N → k)
    (hμ : ∃ κ₀, q κ₀ = normalizationFunction n N k μ)
    {K : Type u} [Field K] [Algebra k K]
    (x y : Spec (.of K) ⟶ finalSpace (n := n) sC L w q Zc hZc)
    (hx : x ≫ finalSpace.over (n := n) sC L w q Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hy : y ≫ finalSpace.over (n := n) sC L w q Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hxy : familyMapOfHom sC x hx ≫ finalFamily (n := n) sC L w q Zc hZc =
      familyMapOfHom sC y hy ≫ finalFamily (n := n) sC L w q Zc hZc) : x = y := by
  set sK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hsK
  have hP : IsPullback (pullback.fst sC sK) (pullback.snd sC sK) sC sK :=
    IsPullback.of_hasPullback _ _
  set Px := familyMapOfHom sC x hx ≫ finalFamily (n := n) sC L w q Zc hZc with hPx
  obtain ⟨αx, hαx_iso, hαx⟩ := exists_pinned_finalFamily_comp (n := n) sC L w q Zc hZc x hx
    (𝟙 _) (pullback.fst sC sK) (pullback.snd sC sK) (Category.id_comp _) (Category.id_comp _) Px
    (Category.id_comp _)
  obtain ⟨αy, hαy_iso, hαy⟩ := exists_pinned_finalFamily_comp (n := n) sC L w q Zc hZc y hy
    (𝟙 _) (pullback.fst sC sK) (pullback.snd sC sK) (Category.id_comp _) (Category.id_comp _) Px
    ((Category.id_comp _).trans hxy.symm)
  haveI := hαx_iso
  haveI := hαy_iso
  obtain ⟨γ, hγ⟩ := exists_iso_of_pinned_same_hom
    (Px ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (fun i => coordSection (pullback.fst sC sK) (pullback.snd sC sK) L w
      (fun j => (x ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
        (coefficientCoord n N k i j)))
    (fun i => coordSection (pullback.fst sC sK) (pullback.snd sC sK) L w
      (fun j => (y ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
        (coefficientCoord n N k i j)))
    αx hαx αy hαy
  haveI : IsInvertibleModule (pullback sC sK)
      ((Scheme.Modules.pullback (pullback.fst sC sK)).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ L
  obtain ⟨c, hc⟩ := exists_units_smul_id_of_isInvertible_baseChange sC (pullback.fst sC sK)
    (pullback.snd sC sK) hP ((Scheme.Modules.pullback (pullback.fst sC sK)).obj L) γ
  set ax : Fin (n + 1) → Fin N → Γ(Spec (.of K), ⊤) := fun i j =>
    (x ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
      (coefficientCoord n N k i j) with hax
  set ay : Fin (n + 1) → Fin N → Γ(Spec (.of K), ⊤) := fun i j =>
    (y ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
      (coefficientCoord n N k i j) with hay
  set c'' : Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv (c : K) with hc''
  have hlin : ∀ i, ay i = c'' • ax i := by
    intro i
    have h1 := hγ i
    rw [app_top_eq_smul_of_eq_smul_id _ _ γ.hom (c : K) hc] at h1
    have h2 : (pullback.snd sC sK).appTop c'' • coordSection (pullback.fst sC sK)
        (pullback.snd sC sK) L w (ax i) =
        coordSection (pullback.fst sC sK) (pullback.snd sC sK) L w (ay i) := h1
    rw [← coordSection_smul] at h2
    have : Function.Injective (coordSection (pullback.fst sC sK) (pullback.snd sC sK) L w) := by
      haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
        Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
      haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
      haveI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated sC
      exact (coordSection_bijective hP L w).1
    exact (this h2).symm
  have nx : ∑ i, ∑ j, sK.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) * ax i j = 1 :=
    sum_appTop_toCoefficientSpace_normalization (n := n) sC L w q Zc hZc μ hμ x hx
  have ny : ∑ i, ∑ j, sK.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) * ay i j = 1 :=
    sum_appTop_toCoefficientSpace_normalization (n := n) sC L w q Zc hZc μ hμ y hy
  have hone : c'' = 1 := by
    have e1 : ∑ i, ∑ j, sK.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) * ay i j = c'' := by
      calc _ = ∑ i, ∑ j, c'' * (sK.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) * ax i j) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hlin i, Pi.smul_apply, smul_eq_mul]
            ring
        _ = c'' * ∑ i, ∑ j, sK.appTop ((Scheme.ΓSpecIso (.of k)).inv (μ i j)) * ax i j := by
            simp only [Finset.mul_sum]
        _ = c'' := by rw [nx, mul_one]
    exact e1.symm.trans ny
  have hay1 : ∀ i j, ay i j = ax i j := by
    intro i j
    rw [hlin i, hone, Pi.smul_apply, one_smul]
  have hcoef : x ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc =
      y ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc := by
    refine AffineSpace.hom_ext ?_ ?_
    · have e1 : ∀ z : Spec (.of K) ⟶ finalSpace (n := n) sC L w q Zc hZc,
          z ≫ finalSpace.over (n := n) sC L w q Zc hZc = sK →
          (z ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc) ≫
            coefficientSpaceOver n N k = sK := fun z hz => by
        rw [Category.assoc, finalSpace.toCoefficientSpace_over, hz]
      exact (e1 x hx).trans (e1 y hy).symm
    · rintro ⟨⟨i, j⟩⟩
      exact (hay1 i j).symm
  have h1 :
      x ≫ finalSpace.ι (n := n) sC L w q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L w q =
      y ≫ finalSpace.ι (n := n) sC L w q Zc hZc ≫ closedNoCommonZeroScheme.ι (n := n) sC L w q :=
    zeroLocusScheme.ι_cancel (coefficientSpace n N k) q _ _ (by
      simpa only [finalSpace.toCoefficientSpace, Category.assoc] using hcoef)
  rw [← Category.assoc, ← Category.assoc] at h1
  exact (cancel_mono _).1 ((cancel_mono _).1 h1)

end Injectivity

section NonvanishingHelpers

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.Ample (nonvanishingLocus)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

/-- **`W_{a • σ} = D(a) ∩ W_σ`** for a global function `a` and a global section `σ`. -/
theorem mem_nonvanishingLocus_smul_iff {X : Scheme.{u}} (N : X.Modules) (a : Γ(X, ⊤))
    (σ : Γ(N, ⊤)) (y : X) :
    y ∈ nonvanishingLocus N (a • σ) ↔ y ∈ X.basicOpen a ∧ y ∈ nonvanishingLocus N σ := by
  have h := Stacks.AmpleThickeningAscent.nonvanishingLocusOn_smul N (W := ⊤) a σ
  rw [Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top,
    Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_top] at h
  exact Set.ext_iff.1 h y

/-- **A pinned family generates.** If `Φ^* 𝒪(1) ≅ N` carries `Φ^* Tᵢ` to `sᵢ` then the `sᵢ` have
nonvanishing loci covering `X`. -/
theorem exists_mem_nonvanishingLocus_of_pinned {X : Scheme.{u}} {n : ℕ}
    (Φ : X ⟶ projectiveSpaceAtUniverse.{u} n) {N : X.Modules} (s : Fin (n + 1) → Γ(N, ⊤))
    (α : (Scheme.Modules.pullback Φ).obj (twistingSheafAtUniverse.{u} n) ⟶ N) [IsIso α]
    (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u} Φ i) = s i) (y : X) :
    ∃ i, y ∈ nonvanishingLocus N (s i) := by
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_coord n (Φ.base y)
  refine ⟨i, ?_⟩
  have h2 := nonvanishingLocus_app_top_eq_of_iso (asIso α) (pullbackCoordSection.{u} Φ i)
  have h3 : y ∈ nonvanishingLocus ((Scheme.Modules.pullback Φ).obj
      (twistingSheafAtUniverse.{u} n)) (pullbackCoordSection.{u} Φ i) :=
    (mem_nonvanishingLocus_pullbackCoordSection_iff Φ i y).2 hi
  rw [← h2] at h3
  rw [← hα i]
  exact h3

/-- A pinned family generates the stalks of an invertible module. -/
theorem generatesStalks_of_pinned {X : Scheme.{u}} {n : ℕ}
    (Φ : X ⟶ projectiveSpaceAtUniverse.{u} n) {N : X.Modules} [IsInvertibleModule X N]
    (s : Fin (n + 1) → Γ(N, ⊤))
    (α : (Scheme.Modules.pullback Φ).obj (twistingSheafAtUniverse.{u} n) ⟶ N) [IsIso α]
    (hα : ∀ i, α.app ⊤ (pullbackCoordSection.{u} Φ i) = s i) : GeneratesStalks s :=
  (Stacks.AmpleImmersionReduction.generatesStalks_iff_forall_exists_mem s).2 fun y =>
    exists_mem_nonvanishingLocus_of_pinned Φ s α hα y

end NonvanishingHelpers

section Proportional

open Stacks.Ample (nonvanishingLocus)

/-- **Proportional tuples differ by an automorphism of the module.** Let `s₁ = a • V` and
`s₂ = b • V` be two tuples of multiples of a section `V`, with `aᵢ b_{i'} = a_{i'} bᵢ` and `b_{i₀}`
a unit. If `s₁` has no common zero, then `a_{i₀}` is a unit, and multiplication by
`b_{i₀} a_{i₀}⁻¹` is an automorphism of `N` carrying `s₁` to `s₂`. -/
theorem exists_iso_of_proportional {X : Scheme.{u}} {N : X.Modules} (V : Γ(N, ⊤))
    {ι : Type*} (a b : ι → Γ(X, ⊤)) (s₁ s₂ : ι → Γ(N, ⊤))
    (hs₁ : ∀ i, s₁ i = a i • V) (hs₂ : ∀ i, s₂ i = b i • V)
    (hab : ∀ i i', a i * b i' = a i' * b i) (i₀ : ι) (hb : IsUnit (b i₀))
    (hgen : ∀ y : X, ∃ i, y ∈ nonvanishingLocus N (s₁ i)) :
    ∃ γ : N ≅ N, ∀ i, γ.hom.app ⊤ (s₁ i) = s₂ i := by
  have ha : IsUnit (a i₀) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ (a i₀) fun y hy => ?_
    rw [← X.mem_basicOpen (a i₀) y hy]
    obtain ⟨i, hi⟩ := hgen y
    rw [hs₁, mem_nonvanishingLocus_smul_iff] at hi
    have h1 : y ∈ X.basicOpen (a i * b i₀) := by
      rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hb]
      exact ⟨hi.1, trivial⟩
    rw [hab, Scheme.basicOpen_mul] at h1
    exact h1.1
  obtain ⟨ua, hua⟩ := ha
  obtain ⟨ut, hut⟩ : IsUnit (b i₀ * ↑ua⁻¹) := hb.mul ua⁻¹.isUnit
  have hcomp : ∀ a b : Γ(X, ⊤), IntegralTransformQcoh.sectionScalar X a N ≫
      IntegralTransformQcoh.sectionScalar X b N = IntegralTransformQcoh.sectionScalar X (b * a) N :=
    fun a b =>
      congrArg End.asHom ((IntegralTransformQcoh.sectionScalarRingHom X N).map_mul b a).symm
  have h1 : IntegralTransformQcoh.sectionScalar X 1 N = 𝟙 N :=
    congrArg End.asHom (IntegralTransformQcoh.sectionScalarRingHom X N).map_one
  refine ⟨⟨IntegralTransformQcoh.sectionScalar X (b i₀ * ↑ua⁻¹) N,
    IntegralTransformQcoh.sectionScalar X (↑ut⁻¹) N, ?_, ?_⟩, fun i => ?_⟩
  · rw [hcomp, ← hut, Units.inv_mul, h1]
  · rw [hcomp, ← hut, Units.mul_inv, h1]
  · change (IntegralTransformQcoh.sectionScalar X (b i₀ * ↑ua⁻¹) N).app ⊤ (s₁ i) = s₂ i
    rw [Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionScalar_app_top, hs₁, hs₂, smul_smul]
    congr 1
    calc b i₀ * ↑ua⁻¹ * a i = ↑ua⁻¹ * (a i * b i₀) := by ring
      _ = ↑ua⁻¹ * (↑ua * b i) := by rw [hab i i₀, ← hua]
      _ = b i := by rw [← mul_assoc, Units.inv_mul, one_mul]

end Proportional

section Proportionality

variable {k : Type u} [Field k] {n N : ℕ}

/-- The proportionality form evaluated along a ring hom `φ : k →+* A`. -/
theorem sum_proportionalityVector {A : Type*} [CommRing A] (φ : k →+* A) (ℓ : Fin N → k)
    (c : Fin (n + 1) → k) (i i' : Fin (n + 1)) (x : Fin (n + 1) → Fin N → A) :
    ∑ r, ∑ j, φ (proportionalityVector ℓ c i i' r j) * x r j =
      φ (c i') * ∑ j, φ (ℓ j) * x i j - φ (c i) * ∑ j, φ (ℓ j) * x i' j := by
  have h1 : ∀ (b : Fin (n + 1)) (y : k),
      ∑ r, ∑ j, φ (ℓ j * (if r = b then y else 0)) * x r j = φ y * ∑ j, φ (ℓ j) * x b j := by
    intro b y
    rw [Finset.sum_eq_single b]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [if_true, map_mul]
      ring
    · intro r _ hr
      simp [hr]
    · simp
  simp only [proportionalityVector, mul_sub, map_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h1 i (c i'), h1 i' (c i)]

/-- Pulled back along `g`, the proportionality function is
`c_{i'} Σⱼ ℓⱼ g^*x_{ij} - cᵢ Σⱼ ℓⱼ g^*x_{i'j}`. -/
theorem appTop_proportionalityFunction {T' : Scheme.{u}} {sT' : T' ⟶ Spec (.of k)}
    (g : T' ⟶ coefficientSpace n N k) (hg : g ≫ coefficientSpaceOver n N k = sT')
    (ℓ : Fin N → k) (c : Fin (n + 1) → k) (i i' : Fin (n + 1)) :
    g.appTop (proportionalityFunction n N k ℓ c i i') =
      sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i')) *
          ∑ j, sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) *
            g.appTop (coefficientCoord n N k i j) -
        sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i)) *
          ∑ j, sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) *
            g.appTop (coefficientCoord n N k i' j) := by
  have hc : ∀ y : k, g.appTop (constFunction n N k y) =
      sT'.appTop ((Scheme.ΓSpecIso (.of k)).inv y) := by
    intro y
    unfold constFunction
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
  have h := sum_proportionalityVector
    ((sT'.appTop.hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom) ℓ c i i'
    (fun r j => g.appTop (coefficientCoord n N k r j))
  unfold proportionalityFunction linearFunction
  simp only [map_sum, map_mul, hc]
  exact h

end Proportionality

section Marked

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))
  [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- The base change `C ×ₖ T ⟶ C ×ₖ T` along the identity of `T` is the identity. -/
theorem familyMapOfHom_id {T : Scheme.{u}} (sT : T ⟶ Spec (.of k)) (h : 𝟙 T ≫ sT = sT) :
    familyMapOfHom sC (𝟙 T) h = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

/-- The family `Φ : C ×ₖ M → ℙⁿ_k` lies over `k`. -/
theorem finalFamily_over :
    finalFamily (n := n) sC L e q Zc hZc ≫ pullback.fst (terminal.from (Spec (.of k)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      pullback.fst sC (finalSpace.over (n := n) sC L e q Zc hZc) ≫ sC := by
  rw [finalFamily_eq, Category.assoc, noCommonZeroFamily_over, ← Category.assoc,
    familyMapOfHom_fst]

/-- **The section `P × id : M ⟶ C ×ₖ M`** of a `k`-point `P` of `C`. -/
def finalSpace.markedMap (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) :
    finalSpace (n := n) sC L e q Zc hZc ⟶
      pullback sC (finalSpace.over (n := n) sC L e q Zc hZc) :=
  pullback.lift (finalSpace.over (n := n) sC L e q Zc hZc ≫ P) (𝟙 _)
    (by rw [Category.assoc, hP, Category.comp_id, Category.id_comp])

/-- The section `P × id : M ⟶ C ×ₖ M` followed by the projection to `C` is the constant map `P`. -/
@[reassoc]
theorem finalSpace.markedMap_fst (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) :
    finalSpace.markedMap (n := n) sC L e q Zc hZc P hP ≫
        pullback.fst sC (finalSpace.over (n := n) sC L e q Zc hZc) =
      finalSpace.over (n := n) sC L e q Zc hZc ≫ P :=
  pullback.lift_fst _ _ _

/-- The section `P × id : M ⟶ C ×ₖ M` followed by the projection to `M` is the identity. -/
@[reassoc]
theorem finalSpace.markedMap_snd (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) :
    finalSpace.markedMap (n := n) sC L e q Zc hZc P hP ≫
        pullback.snd sC (finalSpace.over (n := n) sC L e q Zc hZc) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end Marked

section Frame

variable {k : Type u} [Field k] {C : Scheme.{u}} (L : C.Modules) [IsInvertibleModule C L]
  {N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **A frame of the fibre of `L` at a `k`-point.** The pullback of an invertible module to the
spectrum of a field is trivial, so the images of the sections `e_j` are multiples `ℓ_j · v` of one
section `v` (a generator of the fibre). -/
theorem exists_fibre_frame (P : Spec (.of k) ⟶ C) :
    ∃ (ℓ : Fin N → k) (v : Γ((Scheme.Modules.pullback P).obj L, ⊤)),
      ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (e j) =
        (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v := by
  haveI : IsInvertibleModule (Spec (.of k)) ((Scheme.Modules.pullback P).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ L
  obtain ⟨E⟩ := Stacks.PicardUFD.nonempty_linearEquiv_appTop_of_isInvertible_of_isAffine
    (Spec (.of k)) ((Scheme.Modules.pullback P).obj L)
  refine ⟨fun j =>
    (Scheme.ΓSpecIso (.of k)).hom (E (AlgebraicGeometry.pullbackGlobalSections P L (e j))),
    E.symm 1, fun j => ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom
      (E (AlgebraicGeometry.pullbackGlobalSections P L (e j)))) =
      E (AlgebraicGeometry.pullbackGlobalSections P L (e j)) :=
    congrArg (fun φ => φ (E (AlgebraicGeometry.pullbackGlobalSections P L (e j))))
      (congrArg (fun φ => φ.hom) (Scheme.ΓSpecIso (.of k)).hom_inv_id.symm |>.symm)
  rw [h1, ← E.symm.map_smul, smul_eq_mul, mul_one, E.symm_apply_apply]

end Frame

section FrameTuple

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul)

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **The pullback of a tuple `Σⱼ aⱼ eⱼ` with scalar coefficients.** -/
theorem pullbackGlobalSections_tuple {Y : Scheme.{u}} (r : Y ⟶ C) (ρ : Y ⟶ Spec (.of k))
    (hr : r ≫ sC = ρ) (a : Fin N → k) :
    AlgebraicGeometry.pullbackGlobalSections r L
        (∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) • e j) =
      ∑ j, ρ.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) •
        AlgebraicGeometry.pullbackGlobalSections r L (e j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackGlobalSections_smul, ← hr, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- **The pullback of a tuple, in a frame**: if `r^* eⱼ = ℓⱼ V` then
`r^* (Σⱼ aⱼ eⱼ) = (Σⱼ ℓⱼ aⱼ) V`. -/
theorem pullbackGlobalSections_tuple_frame {Y : Scheme.{u}} (r : Y ⟶ C) (ρ : Y ⟶ Spec (.of k))
    (hr : r ≫ sC = ρ) (a ℓ : Fin N → k) (V : Γ((Scheme.Modules.pullback r).obj L, ⊤))
    (hV : ∀ j, AlgebraicGeometry.pullbackGlobalSections r L (e j) =
      ρ.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) • V) :
    AlgebraicGeometry.pullbackGlobalSections r L
        (∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) • e j) =
      ρ.appTop ((Scheme.ΓSpecIso (.of k)).inv (∑ j, ℓ j * a j)) • V := by
  rw [pullbackGlobalSections_tuple sC L e r ρ hr a]
  simp only [hV, smul_smul, map_sum, map_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end FrameTuple

section NeZero

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.Ample (nonvanishingLocus)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **The fibre vector of a generating tuple is nonzero.** If `f : C ⟶ ℙⁿ_k` has `f^* 𝒪(1) ≅ L`
carrying `f^* Tᵢ` to `τᵢ = Σⱼ aᵢⱼ eⱼ`, and `P` is a `k`-point of `C` with `P^* eⱼ = ℓⱼ v`, then
some `Σⱼ ℓⱼ aᵢⱼ` is nonzero: the value `f(P)` in the frame `v`. -/
theorem exists_ne_zero_fibre_tuple (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (ℓ : Fin N → k)
    (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (e j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v) :
    ∃ i, ∑ j, ℓ j * a i j ≠ 0 := by
  obtain ⟨α, hαiso, hα⟩ := exists_iso_pinned_pullback P
    (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    ((P ≫ f) ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) (by simp)
    (fun i => l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i)) l (fun i => rfl)
  obtain ⟨i, hi⟩ := exists_mem_nonvanishingLocus_of_pinned _ _ α hα
    (Classical.arbitrary (Spec (.of k)))
  refine ⟨i, fun h0 => ?_⟩
  rw [hτ, pullbackGlobalSections_tuple_frame sC L e P (𝟙 _) hP (a i) ℓ v (by simpa using hv),
    mem_nonvanishingLocus_smul_iff, h0] at hi
  simp at hi

end NeZero

section ProportionalMaps

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

/-- **Maps to `ℙⁿ_S` from proportional pinned tuples agree.** Two morphisms `Q, R : X ⟶ ℙⁿ_S`
over `S` with pinned isomorphisms `Q^* 𝒪(1) ≅ N`, `R^* 𝒪(1) ≅ N` carrying the coordinates to
`aᵢ • V` and `bᵢ • V`, where `aᵢ b_{i'} = a_{i'} bᵢ` and some `b_{i₀}` is a unit, are equal. -/
theorem eq_of_pinned_of_proportional {X S : Scheme.{u}} {n : ℕ} {N' : X.Modules}
    [IsInvertibleModule X N'] (V : Γ(N', ⊤)) (Q R : X ⟶ projectiveSpaceOver n S)
    (hover : Q ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
      R ≫ pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n)))
    (α₁ : (Scheme.Modules.pullback (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).obj
      (twistingSheafAtUniverse.{u} n) ⟶ N') [IsIso α₁]
    (α₂ : (Scheme.Modules.pullback (R ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).obj
      (twistingSheafAtUniverse.{u} n) ⟶ N') [IsIso α₂]
    (a b : Fin (n + 1) → Γ(X, ⊤))
    (hα₁ : ∀ i, α₁.app ⊤ (pullbackCoordSection.{u}
      (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n S) i) = a i • V)
    (hα₂ : ∀ i, α₂.app ⊤ (pullbackCoordSection.{u}
      (R ≫ projectiveSpaceOver.toIntegralAtUniverse n S) i) = b i • V)
    (hab : ∀ i i', a i * b i' = a i' * b i) (i₀ : Fin (n + 1)) (hb : IsUnit (b i₀)) : Q = R := by
  obtain ⟨γ, hγ⟩ := exists_iso_of_proportional V a b (fun i => a i • V) (fun i => b i • V)
    (fun _ => rfl) (fun _ => rfl) hab i₀ hb
    (fun y => exists_mem_nonvanishingLocus_of_pinned _ _ α₁ hα₁ y)
  exact eq_of_pinned_of_iso_over (fun i => a i • V) (fun i => b i • V)
    (generatesStalks_of_pinned _ _ α₁ hα₁) γ hγ Q R hover _ _ rfl rfl α₁ hα₁ α₂ hα₂

end ProportionalMaps

section FrameBaseChange

open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul)
open Stacks.LinearSystemScheme (coordSection)

variable {k : Type u} [Field k] {C : Scheme.{u}} (L : C.Modules) {N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **A frame of the fibre pulls back to a frame**: if `P^* eⱼ = ℓⱼ v` then
`(o ≫ P)^* eⱼ = o^*(ℓⱼ) V` for the section `V` corresponding to `o^* v`. -/
theorem exists_frame_pullback {X : Scheme.{u}} (o : X ⟶ Spec (.of k)) (P : Spec (.of k) ⟶ C)
    (ℓ : Fin N → k) (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (e j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v) :
    ∃ V : Γ((Scheme.Modules.pullback (o ≫ P)).obj L, ⊤), ∀ j,
      AlgebraicGeometry.pullbackGlobalSections (o ≫ P) L (e j) =
        o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) • V := by
  obtain ⟨θ, hθ⟩ := exists_iso_pullbackGlobalSections_comp o P (o ≫ P) rfl L
  refine ⟨θ.hom.app ⊤ (AlgebraicGeometry.pullbackGlobalSections o _ v), fun j => ?_⟩
  rw [← hθ, hv j, pullbackGlobalSections_smul, Scheme.Modules.Hom.app_smul]

/-- In a frame `π^* eⱼ = o^*(ℓⱼ) • V`, the coordinate section of `y` is `(Σⱼ o^*(ℓⱼ) yⱼ) • V`. -/
theorem coordSection_id_frame {X : Scheme.{u}} (π : X ⟶ C) (o : X ⟶ Spec (.of k))
    (ℓ : Fin N → k) (V : Γ((Scheme.Modules.pullback π).obj L, ⊤))
    (hV : ∀ j, AlgebraicGeometry.pullbackGlobalSections π L (e j) =
      o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) • V) (y : Fin N → Γ(X, ⊤)) :
    coordSection π (𝟙 X) L e y =
      (∑ j, o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) * y j) • V := by
  simp only [coordSection, hV, Scheme.Hom.id_appTop, CommRingCat.id_apply, smul_smul,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end FrameBaseChange

section ConstancyAbstract

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.LinearSystemScheme (coordSection)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **Constancy, for an abstract parameter scheme.** Let `f : C ⟶ ℙⁿ_k` with `f^* 𝒪(1) ≅ L`
carrying `f^* Tᵢ` to `τᵢ = Σⱼ aᵢⱼ eⱼ`, `P` a `k`-point of `C` with `P^* eⱼ = ℓⱼ v` and
`cᵢ = Σⱼ ℓⱼ aᵢⱼ`. If a morphism `Q : X ⟶ ℙⁿ_k` over `k` has `Q^* 𝒪(1) ≅ (o ≫ P)^* L` carrying
`Q^* Tᵢ` to the coordinate section `Σⱼ yᵢⱼ (o ≫ P)^* eⱼ` whose coefficient vectors `yᵢ` are
proportional to `c` (in `Γ(X, 𝒪)`), then `Q = (o ≫ P) ≫ f` is constant. -/
theorem eq_comp_of_pinned_tuple_frame [IsProper sC] {X : Scheme.{u}} (o : X ⟶ Spec (.of k))
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (ℓ : Fin N → k)
    (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (e j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v)
    (c : Fin (n + 1) → k) (hc : ∀ i, c i = ∑ j, ℓ j * a i j)
    (Q : X ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hQ : Q ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = o)
    (α₁ : (Scheme.Modules.pullback
        (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ (Scheme.Modules.pullback (o ≫ P)).obj L) [IsIso α₁]
    (y : Fin (n + 1) → Fin N → Γ(X, ⊤))
    (hα₁ : ∀ i, α₁.app ⊤ (pullbackCoordSection.{u}
      (Q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
        coordSection (o ≫ P) (𝟙 X) L e (y i))
    (hprop : ∀ i i', (∑ j, o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) * y i j) *
        o.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i')) =
      (∑ j, o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) * y i' j) *
        o.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i))) :
    Q = (o ≫ P) ≫ f := by
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_fibre_tuple sC L e f l a hτ P hP ℓ v hv
  haveI : IsInvertibleModule X ((Scheme.Modules.pullback (o ≫ P)).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (o ≫ P) L
  obtain ⟨V, hV⟩ := exists_frame_pullback L e o P ℓ v hv
  obtain ⟨α₂, hα₂iso, hα₂⟩ := exists_iso_pinned_pullback (o ≫ P)
    (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))
    (((o ≫ P) ≫ f) ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) (by simp)
    (fun i => l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i)) l (fun i => rfl)
  have hs₂ : ∀ i, α₂.app ⊤ (pullbackCoordSection.{u}
      (((o ≫ P) ≫ f) ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      o.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i)) • V := by
    intro i
    rw [hα₂, hτ, pullbackGlobalSections_tuple_frame sC L e (o ≫ P) o (by rw [Category.assoc, hP,
      Category.comp_id]) (a i) ℓ V hV, hc]
  refine eq_of_pinned_of_proportional V Q ((o ≫ P) ≫ f) ?_ α₁ α₂
    (fun i => ∑ j, o.appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) * y i j)
    (fun i => o.appTop ((Scheme.ΓSpecIso (.of k)).inv (c i))) ?_ hs₂ hprop i₀ ?_
  · rw [hQ, Category.assoc, hf, Category.assoc, hP, Category.comp_id]
  · intro i
    rw [hα₁, coordSection_id_frame L e (o ≫ P) o ℓ V hV]
  · exact (IsUnit.mk0 _ ((hc i₀) ▸ hi₀)).map ((Scheme.ΓSpecIso (.of k)).inv ≫ o.appTop).hom

end ConstancyAbstract

section Constancy

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.LinearSystemScheme (coordSection)
open AlgebraicGeometry.SectionsEqualizer (pullbackGlobalSections_smul)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ}
  (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))
  [IsProper sC] {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤))
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- On `M`, the proportionality conditions hold: `(Σⱼ ℓⱼ x_{ij}) c_{i'} = (Σⱼ ℓⱼ x_{i'j}) cᵢ`. -/
theorem finalSpace_proportionality (ℓ : Fin N → k) (c : Fin (n + 1) → k)
    (hq : ∀ i i', ∃ κ₀, q κ₀ = proportionalityFunction n N k ℓ c i i') (i i' : Fin (n + 1)) :
    (∑ j, (finalSpace.over (n := n) sC L w q Zc hZc).appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) *
        (𝟙 _ ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
          (coefficientCoord n N k i j)) *
      (finalSpace.over (n := n) sC L w q Zc hZc).appTop ((Scheme.ΓSpecIso (.of k)).inv (c i')) =
    (∑ j, (finalSpace.over (n := n) sC L w q Zc hZc).appTop ((Scheme.ΓSpecIso (.of k)).inv (ℓ j)) *
        (𝟙 _ ≫ finalSpace.toCoefficientSpace (n := n) sC L w q Zc hZc).appTop
          (coefficientCoord n N k i' j)) *
      (finalSpace.over (n := n) sC L w q Zc hZc).appTop ((Scheme.ΓSpecIso (.of k)).inv (c i)) := by
  obtain ⟨κ₀, hκ₀⟩ := hq i i'
  have h0 := appTop_toCoefficientSpace_eq_zero (n := n) sC L w q Zc hZc (𝟙 _) κ₀
  rw [hκ₀, appTop_proportionalityFunction _ (by
    rw [Category.id_comp, finalSpace.toCoefficientSpace_over]), sub_eq_zero] at h0
  exact (mul_comm _ _).trans (h0.trans (mul_comm _ _))

/-- **The family is constant on `P × M`.** Let `f : C ⟶ ℙⁿ_k` with `f^* 𝒪(1) ≅ L` carrying
`f^* Tᵢ` to `τᵢ = Σⱼ aᵢⱼ wⱼ`, and let `P` be a `k`-point of `C` with `P^* wⱼ = ℓⱼ v` in a frame
`v` of the fibre and `cᵢ = Σⱼ ℓⱼ aᵢⱼ` the value `f(P)` in that frame. If the closed conditions `q`
of `M` contain the proportionality conditions of the tuple at `P` to `c`, then the family
`Φ : C ×ₖ M → ℙⁿ_k` restricted to `P × M` is the constant map `f(P)`. -/
theorem finalSpace_markedMap_comp_finalFamily
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • w j)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (ℓ : Fin N → k)
    (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (w j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v)
    (c : Fin (n + 1) → k) (hc : ∀ i, c i = ∑ j, ℓ j * a i j)
    (hq : ∀ i i', ∃ κ₀, q κ₀ = proportionalityFunction n N k ℓ c i i') :
    finalSpace.markedMap (n := n) sC L w q Zc hZc P hP ≫
        finalFamily (n := n) sC L w q Zc hZc =
      finalSpace.over (n := n) sC L w q Zc hZc ≫ P ≫ f := by
  have hid : 𝟙 (finalSpace (n := n) sC L w q Zc hZc) ≫
      finalSpace.over (n := n) sC L w q Zc hZc = finalSpace.over (n := n) sC L w q Zc hZc :=
    Category.id_comp _
  obtain ⟨α₁, hα₁iso, hα₁⟩ := exists_pinned_finalFamily_comp (n := n) sC L w q Zc hZc
    (𝟙 _) hid (finalSpace.markedMap (n := n) sC L w q Zc hZc P hP)
    (finalSpace.over (n := n) sC L w q Zc hZc ≫ P) (𝟙 _)
    (finalSpace.markedMap_fst sC L w q Zc hZc P hP)
    (finalSpace.markedMap_snd sC L w q Zc hZc P hP)
    (finalSpace.markedMap (n := n) sC L w q Zc hZc P hP ≫ finalFamily (n := n) sC L w q Zc hZc)
    (by rw [familyMapOfHom_id, Category.id_comp])
  have h := eq_comp_of_pinned_tuple_frame sC L w (finalSpace.over (n := n) sC L w q Zc hZc)
    f hf l a hτ P hP ℓ v hv c hc
    (finalSpace.markedMap (n := n) sC L w q Zc hZc P hP ≫ finalFamily (n := n) sC L w q Zc hZc)
    (by rw [Category.assoc, finalFamily_over, ← Category.assoc,
      finalSpace.markedMap_fst, Category.assoc, hP, Category.comp_id])
    α₁ _ hα₁ (finalSpace_proportionality sC L w q Zc hZc ℓ c hq)
  rw [h, Category.assoc]

end Constancy

section Data

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **The data `ℓ_β, c_β` of a marked `k`-point.** For a `k`-point `P` of `C` and a generating
tuple `τᵢ = Σⱼ aᵢⱼ eⱼ` of `L` (the pull-backs of the coordinates by `f`), there are the values `ℓ`
of the sections `e` in a frame `v` of the fibre `P^* L` and the value `c = f(P)` of the tuple in
that frame, a nonzero vector satisfying the proportionality relations of the tuple of `f`. -/
theorem exists_marked_point_data (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) :
    ∃ (ℓ : Fin N → k) (v : Γ((Scheme.Modules.pullback P).obj L, ⊤)) (c : Fin (n + 1) → k),
      (∀ j, AlgebraicGeometry.pullbackGlobalSections P L (e j) =
        (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v) ∧
      (∀ i, c i = ∑ j, ℓ j * a i j) ∧
      (∀ i i', (∑ j, ℓ j * a i j) * c i' = (∑ j, ℓ j * a i' j) * c i) ∧ ∃ i, c i ≠ 0 := by
  obtain ⟨ℓ, v, hv⟩ := exists_fibre_frame L e P
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_fibre_tuple sC L e f l a hτ P hP ℓ v hv
  refine ⟨ℓ, v, fun i => ∑ j, ℓ j * a i j, hv, fun _ => rfl, fun i i' => mul_comm _ _,
    i₀, hi₀⟩

/-- **A normalizing functional.** If the tuple `a` is not zero, some coefficient functional `μ`
takes the value `1` on it. -/
theorem exists_normalizing_functional (a : Fin (n + 1) → Fin N → k) (h : ∃ i j, a i j ≠ 0) :
    ∃ μ : Fin (n + 1) → Fin N → k, ∑ i, ∑ j, μ i j * a i j = 1 := by
  obtain ⟨i₀, j₀, h₀⟩ := h
  refine ⟨fun i j => if i = i₀ ∧ j = j₀ then (a i₀ j₀)⁻¹ else 0, ?_⟩
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · simp [h₀]
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- A nonzero fibre vector forces a nonzero tuple of coefficients. -/
theorem exists_ne_zero_of_sum_ne_zero (a : Fin (n + 1) → Fin N → k) (ℓ : Fin N → k)
    (h : ∃ i, ∑ j, ℓ j * a i j ≠ 0) : ∃ i j, a i j ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  by_contra h'
  push Not at h'
  exact hi (Finset.sum_eq_zero fun j _ => by rw [h' i j, mul_zero])

end Data

section MarkedPointsConvenience

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- The data `ℓ_β, c_β` for a family of marked `k`-points, and a common normalizing
functional `μ`. -/
theorem exists_marked_points_data {ιB : Type} (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • e j)
    (P : ιB → (Spec (.of k) ⟶ C)) (hP : ∀ β, P β ≫ sC = 𝟙 _) [Nonempty ιB] :
    ∃ (ℓ : ιB → Fin N → k) (v : ∀ β, Γ((Scheme.Modules.pullback (P β)).obj L, ⊤))
      (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k),
      (∀ β j, AlgebraicGeometry.pullbackGlobalSections (P β) L (e j) =
        (Scheme.ΓSpecIso (.of k)).inv (ℓ β j) • v β) ∧
      (∀ β i, c β i = ∑ j, ℓ β j * a i j) ∧
      (∀ β i i', (∑ j, ℓ β j * a i j) * c β i' = (∑ j, ℓ β j * a i' j) * c β i) ∧
      (∀ β, ∃ i, c β i ≠ 0) ∧ ∑ i, ∑ j, μ i j * a i j = 1 := by
  have h := fun β => exists_marked_point_data sC L e f l a hτ (P β) (hP β)
  choose ℓ v c h1 h2 h3 h4 using h
  obtain ⟨β₀⟩ := ‹Nonempty ιB›
  obtain ⟨μ, hμ⟩ := exists_normalizing_functional a
    (exists_ne_zero_of_sum_ne_zero a (ℓ β₀) (by
      obtain ⟨i, hi⟩ := h4 β₀
      exact ⟨i, by rwa [h2] at hi⟩))
  exact ⟨ℓ, v, c, μ, h1, h2, h3, h4, hμ⟩

end MarkedPointsConvenience

section CurveMapSpace

open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Ample (nonvanishingLocus)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ}
  (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))
  [IsProper sC] {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ)
  {N' : ιE → ℕ}
  (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
    Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
      Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
  {ιB : Type} (ℓ : ιB → Fin N → k) (c : ιB → Fin (n + 1) → k) (μ : Fin (n + 1) → Fin N → k)
  (Zc : Set (projectiveSpaceOver n (Spec (.of k)))) (hZc : IsClosed Zc)

/-- **`Φ` fixes `f` on the marked points.** For the coefficient space `M` of the fixed-line
curve-map lemma and a marked `k`-point `P_β`, the family `Φ : C ×ₖ M → ℙⁿ_k` restricted to
`P_β × M` is the constant map `f(P_β)`. -/
theorem curveMapSpace_markedMap_comp_family
    (f : C ⟶ projectiveSpaceOver n (Spec (.of k)))
    (hf : f ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = sC)
    (l : (Scheme.Modules.pullback
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k)))).obj
      (twistingSheafAtUniverse.{u} n) ⟶ L) [IsIso l] (a : Fin (n + 1) → Fin N → k)
    (hτ : ∀ i, l.app ⊤ (pullbackCoordSection.{u}
        (f ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))) i) =
      ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a i j)) • w j)
    (β : ιB) (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _)
    (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (w j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ β j) • v)
    (hc : ∀ i, c β i = ∑ j, ℓ β j * a i j) :
    finalSpace.markedMap (n := n) sC L w
        (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc P hP ≫
      finalFamily (n := n) sC L w (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc =
    finalSpace.over (n := n) sC L w (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc ≫
      P ≫ f :=
  finalSpace_markedMap_comp_finalFamily (n := n) sC L w
    (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc f hf l a hτ P hP (ℓ β) v hv
    (c β) hc (fun i i' => ⟨Sum.inr (Sum.inl ⟨β, i, i'⟩), rfl⟩)

/-- **Injectivity of the coefficient space `M` on geometric points.** For `C` proper integral over
an algebraically closed field `k`, `K ⊇ k` a field and `K`-points `x, y` of `M` with the same map
`C_K → ℙⁿ_k`, `x = y`. -/
theorem curveMapSpace_point_injective [IsAlgClosed k] [IsIntegral C]
    {K : Type u} [Field K] [Algebra k K]
    (x y : Spec (.of K) ⟶ curveMapSpace (n := n) sC L w F d w' ℓ c μ Zc hZc)
    (hx : x ≫ finalSpace.over (n := n) sC L w
        (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hy : y ≫ finalSpace.over (n := n) sC L w
        (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hxy : familyMapOfHom sC x hx ≫ finalFamily (n := n) sC L w
        (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc =
      familyMapOfHom sC y hy ≫ finalFamily (n := n) sC L w
        (curveMapConditions (n := n) sC L w F d w' ℓ c μ) Zc hZc) : x = y :=
  finalSpace_point_injective (n := n) sC L w (curveMapConditions (n := n) sC L w F d w' ℓ c μ)
    Zc hZc μ ⟨Sum.inr (Sum.inr ()), rfl⟩ x y hx hy hxy

/-- **Injectivity for maps into a target through which `Φ` factors.** If `Φ = Ψ ≫ m` for a
monomorphism `m : U ⟶ ℙⁿ_k` (e.g. an immersion of a locally closed subscheme), two `K`-points of
`M` with equal maps `C_K → U` are equal. -/
theorem finalSpace_point_injective_of_mono [IsAlgClosed k] [IsIntegral C]
    {κ : Type*} (q : κ → Γ(coefficientSpace n N k, ⊤)) (μ' : Fin (n + 1) → Fin N → k)
    (hμ : ∃ κ₀, q κ₀ = normalizationFunction n N k μ')
    {K : Type u} [Field K] [Algebra k K] {U : Scheme.{u}}
    (m : U ⟶ projectiveSpaceOver n (Spec (.of k))) [Mono m]
    (Ψ : pullback sC (finalSpace.over (n := n) sC L w q Zc hZc) ⟶ U)
    (hΨ : Ψ ≫ m = finalFamily (n := n) sC L w q Zc hZc)
    (x y : Spec (.of K) ⟶ finalSpace (n := n) sC L w q Zc hZc)
    (hx : x ≫ finalSpace.over (n := n) sC L w q Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hy : y ≫ finalSpace.over (n := n) sC L w q Zc hZc =
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hxy : familyMapOfHom sC x hx ≫ Ψ = familyMapOfHom sC y hy ≫ Ψ) : x = y :=
  finalSpace_point_injective (n := n) sC L w q Zc hZc μ' hμ x y hx hy (by
    rw [← hΨ, ← Category.assoc, ← Category.assoc, hxy])

end CurveMapSpace

end MMP.Fourfold

end
