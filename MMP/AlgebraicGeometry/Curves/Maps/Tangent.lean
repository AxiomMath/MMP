module

public import MMP.AlgebraicGeometry.Curves.Maps.Charts
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.ProjectiveSpace.ZeroLocusFactorization

/-!
# Evaluation at rational points and Čech comparisons in the charts of a curve map

For a `k`-scheme `X` and a `k`-point `P : Spec k ⟶ X`, the functions on an open `V ∋ P` have a
value at `P`, a ring map `Γ(X, V) → k` (`k`-linear when `P` is a `k`-point of a `k`-scheme), which
kills the functions vanishing at `P` and commutes with restriction. For an invertible sheaf `L`
and a global section `σ` not vanishing on `V`, the pullback of a global section `s` to the point
is the value of `s / σ` times the pullback of `σ`. In the charts of a curve map these give the
values at the marked points of the local expressions of sections of `L`, and of families
`O ⊗_k B` over a `k`-algebra `B`.

A presheaf on the nerve of a cover is only seen by its Čech cochains over the nonempty
intersections, so presheaves isomorphic there have the same first Čech cohomology.

For an invertible sheaf `L` and a degree-one section `a`, the section ring `⨁ₑ Γ(X, L^{⊗e})`
dehomogenizes at `a` on its nonvanishing open; the substituted section `F(σ)` of a homogeneous
form `F` in a tuple `σ` of sections is read on the chart `X_{σ_i}` as the chart evaluation
`T_j ↦ σ_j / σ_i` of `F`, and these chart evaluations are compatible with pullback. On the
coefficient space of curve maps this compares the substituted equations with the chart
evaluations of the family tuples.

## Main definitions

* `MMP.Fourfold.CurveMapTangent.pointEval`: the value at a `k`-point of the functions on an open
  containing it; `MMP.Fourfold.CurveMapTangent.chartPointEval` on a source chart, as a map of
  `k`-algebras.
* `MMP.Fourfold.CurveMapTangent.tensorEval`: the induced map `O ⊗_k B → B`.
* `MMP.Fourfold.CurveMapTangent.NonemptyIso`: an isomorphism of presheaves on the nerve over the
  nonempty intersections, and `MMP.Fourfold.CurveMapTangent.NonemptyIso.h1Equiv`.
* `MMP.Fourfold.CurveMapTangent.dehomogenize`: dehomogenization of the section ring at a
  degree-one section.

## Main results

* `MMP.Fourfold.CurveMapTangent.substitutedSection_eq_zero_iff`: a substituted section vanishes
  iff all its chart evaluations do.
* `MMP.Fourfold.CurveMapTangent.pullSection_eq_zero_of_chartEval_pullback`: the pullback of a
  substituted section vanishes when the chart evaluations of the pulled-back tuple do.
* `MMP.Fourfold.CurveMapTangent.exists_lift_familyMap_of_equations`: a family tuple whose
  substituted equations vanish maps into the closed subscheme.
* `MMP.Fourfold.CurveMapTangent.pointEval_eq_zero_of_mem_maximalIdeal`: a function whose germ
  lies in the maximal ideal has value zero.
* `MMP.Fourfold.CurveMapTangent.pullbackGlobalSections_eq_smul`: the pullback of `s` to the point
  is `(s / σ)(P)` times the pullback of `σ`.
* `MMP.Fourfold.CurveMapTangent.appLE_div_pullbackCoordSection`: ratios of pulled-back
  coordinates pull back.
* `MMP.Fourfold.CurveMapTangent.exists_eq_mul_pointEval_localSection`: the values of a basis of
  `H⁰(L)` at a point are proportional to the values of their local expressions.
* `MMP.Fourfold.CurveMapTangent.tensorEval_eq_of_map_mk`: a family reducing to `f0` modulo an
  ideal evaluates at a point of its zero locus to the value of `f0`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned

universe u

namespace MMP.Fourfold.CurveMapTangent

open MMP.Fourfold MMP.Fourfold.CurveMapCharts

section PointEval

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (P : Spec (.of k) ⟶ X)

/-- **The value at a `k`-point** `P` of the functions on an open `V` containing it. -/
def pointEval {V : X.Opens} (hV : ⊤ ≤ P ⁻¹ᵁ V) : Γ(X, V) →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp (P.appLE V ⊤ hV).hom

/-- The value at `P` is the composite of `P.appLE V ⊤ hV` with `Γ(Spec k, ⊤) ≅ k`. -/
theorem pointEval_apply {V : X.Opens} (hV : ⊤ ≤ P ⁻¹ᵁ V) (x : Γ(X, V)) :
    pointEval P hV x = (Scheme.ΓSpecIso (.of k)).hom (P.appLE V ⊤ hV x) := rfl

/-- The value at a point does not see restriction. -/
theorem pointEval_res {V V' : X.Opens} (h : V' ≤ V) (hV : ⊤ ≤ P ⁻¹ᵁ V) (hV' : ⊤ ≤ P ⁻¹ᵁ V')
    (x : Γ(X, V)) : pointEval P hV' (X.presheaf.map (homOfLE h).op x) = pointEval P hV x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE P hV' (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [pointEval_apply, pointEval_apply, this]

/-- The value at a `k`-point of a `k`-scheme sends the image of a scalar `c` to `c`. -/
theorem pointEval_baseRingHom (sX : X ⟶ Spec (.of k)) (hP : P ≫ sX = 𝟙 _) {V : X.Opens}
    (hV : ⊤ ≤ P ⁻¹ᵁ V) (c : k) :
    pointEval P hV ((Stacks.Cech.baseRingHom sX V).hom c) = c := by
  have h1 : ∀ (g : Spec (.of k) ⟶ Spec (.of k)) (_ : g = 𝟙 _)
      (e : (⊤ : (Spec (.of k)).Opens) ≤ g ⁻¹ᵁ ⊤), g.appLE ⊤ ⊤ e = 𝟙 _ := by
    rintro g rfl e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact (Spec _).presheaf.map_id _
  have e : V ≤ sX ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hb : Stacks.Cech.baseRingHom sX V = (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V e :=
    Stacks.Cech.baseRingHom_eq_appLE sX V e
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V e ≫ P.appLE V ⊤ hV ≫
      (Scheme.ΓSpecIso (.of k)).hom = 𝟙 _ := by
    rw [← Category.assoc (sX.appLE ⊤ V e) (P.appLE V ⊤ hV), Scheme.Hom.appLE_comp_appLE, h1 _ hP,
      Category.id_comp]
    exact (Scheme.ΓSpecIso (.of k)).inv_hom_id
  rw [hb]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) c) key

end PointEval

section PointEvalField

variable {k : Type u} [Field k] {X : Scheme.{u}} (P : Spec (.of k) ⟶ X)

/-- Every nonzero global function on `Spec k` is a unit. -/
theorem isUnit_of_ne_zero_specField {y : Γ(Spec (.of k), ⊤)} (hy : y ≠ 0) : IsUnit y := by
  have h1 : (Scheme.ΓSpecIso (.of k)).hom y ≠ 0 := by
    intro h
    apply hy
    have := congrArg (Scheme.ΓSpecIso (.of k)).inv h
    rwa [Iso.hom_inv_id_apply, map_zero] at this
  have h2 := (h1.isUnit).map (Scheme.ΓSpecIso (.of k)).inv.hom
  rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply] at h2

/-- **A function vanishing at a `k`-point has value zero there**: if its germ at `P` lies in the
maximal ideal of the stalk, its value at `P` is zero. -/
theorem pointEval_eq_zero_of_mem_maximalIdeal {V : X.Opens} (hV : ⊤ ≤ P ⁻¹ᵁ V)
    (pt : Spec (.of k)) (hP : P.base pt ∈ V) (x : Γ(X, V))
    (hx : X.presheaf.germ V _ hP x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk _)) :
    pointEval P hV x = 0 := by
  by_contra hne
  have hy : P.appLE V ⊤ hV x ≠ 0 := by
    intro h
    apply hne
    rw [pointEval_apply, h, map_zero]
  have hu := isUnit_of_ne_zero_specField hy
  have hg := hu.map ((Spec (.of k)).presheaf.germ ⊤ pt trivial).hom
  have h1 := congrArg (fun φ => φ.hom x) (Scheme.Hom.germ_stalkMap P V pt hP)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  have e1 : ((Spec (.of k)).presheaf.germ ⊤ pt trivial) (P.appLE V ⊤ hV x) =
      P.stalkMap pt (X.presheaf.germ V _ hP x) := by
    rw [h1]
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE hV) pt trivial (P.app V x)
  rw [e1] at hg
  have := (isUnit_map_iff (P.stalkMap pt).hom _).1 hg
  exact (IsLocalRing.mem_maximalIdeal _).1 hx this

end PointEvalField

section PullbackToPoint

variable {X Y : Scheme.{u}} (P : Y ⟶ X) (L : X.Modules)

/-- **Pulling back a multiple of a section**: on an open `V` with `P⁻¹ V = ⊤`, if `σ` does not
vanish on `V`, the pullback of `s` is the pullback of `s / σ` times the pullback of `σ`. -/
theorem pullbackGlobalSections_eq_smul [Stacks.Ample.IsInvertibleModule X L] (s σ : Γ(L, ⊤))
    {V : X.Opens} (hV : ⊤ ≤ P ⁻¹ᵁ V) (hσ : V ≤ nvOpen L σ) :
    AlgebraicGeometry.pullbackGlobalSections P L s =
      P.appLE V ⊤ hV (div σ hσ (resT V s)) • AlgebraicGeometry.pullbackGlobalSections P L σ := by
  have key : ∀ t : Γ(L, ⊤), AlgebraicGeometry.pullbackGlobalSections P L t =
      AlgebraicGeometry.pullbackSectionHom P L V ⊤ hV (resT V t) := by
    intro t
    rw [Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection,
      ← Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top]
    exact (AlgebraicGeometry.pullbackSectionHom_map P L ⊤ V le_top ⊤ hV _ t).symm
  rw [key s, key σ]
  conv_lhs => rw [← div_smul σ hσ (resT V s)]
  exact AlgebraicGeometry.pullbackSectionHom_smul P L V ⊤ hV _ _

/-- A pulled-back section is nonzero at a point where the section does not vanish. -/
theorem pullbackGlobalSections_ne_zero (σ : Γ(L, ⊤)) (y : Y)
    (hy : P.base y ∈ Stacks.Ample.nonvanishingLocus L σ) :
    AlgebraicGeometry.pullbackGlobalSections P L σ ≠ 0 := by
  intro h
  have := (mem_nonvanishingLocus_pullbackGlobalSections_iff P L σ y).2 hy
  rwa [h, Stacks.Ample.nonvanishingLocus_zero] at this

/-- **Scalars on the sections of a module over `Spec k` cancel against a nonzero section.** -/
theorem smul_left_cancel_specField {k : Type u} [Field k] {M : (Spec (.of k)).Modules}
    {m : Γ(M, ⊤)} (hm : m ≠ 0) {r r' : Γ(Spec (.of k), ⊤)} (h : r • m = r' • m) : r = r' := by
  by_contra hne
  have hu := isUnit_of_ne_zero_specField (sub_ne_zero.2 hne)
  have h0 : (r - r') • m = 0 := by rw [sub_smul, h, sub_self]
  exact hm ((hu.smul_eq_zero).1 h0)

end PullbackToPoint

section CoordinateRatios

/-- **The ratios of pulled-back coordinates pull back.** For `g_C = f ≫ g_U` with
`g_U : U ⟶ ℙᵈ_ℤ`, the map `f` sends the ratio `g_U^* T_m / g_U^* T_l` on `W` to the ratio
`g_C^* T_m / g_C^* T_l` on `V ⊆ f⁻¹ W`. -/
theorem appLE_div_pullbackCoordSection {C U : Scheme.{u}} (f : C ⟶ U) {d : ℕ}
    (gU : U ⟶ projectiveSpaceAtUniverse.{u} d) (gC : C ⟶ projectiveSpaceAtUniverse.{u} d)
    (hg : gC = f ≫ gU) {W : U.Opens} {V : C.Opens} (e : V ≤ f ⁻¹ᵁ W) (l m : Fin (d + 1))
    (hW : W ≤ nvOpen ((Scheme.Modules.pullback gU).obj (twistingSheafAtUniverse.{u} d))
      (pullbackCoordSection.{u} gU l))
    (hV : V ≤ nvOpen ((Scheme.Modules.pullback gC).obj (twistingSheafAtUniverse.{u} d))
      (pullbackCoordSection.{u} gC l)) :
    f.appLE W V e
        (div (pullbackCoordSection.{u} gU l) hW (resT W (pullbackCoordSection.{u} gU m))) =
      div (pullbackCoordSection.{u} gC l) hV (resT V (pullbackCoordSection.{u} gC m)) := by
  subst hg
  have hW' := hW.trans (Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection gU l).le
  have hV' := hV.trans (Stacks.ProjectiveSpaceModuli.nvOpen_pullbackCoordSection (f ≫ gU) l).le
  rw [← eq_div _ hW (Stacks.ProjectiveSpaceModuli.resT_pullbackCoordSection_of_le gU l m hW').symm,
    ← eq_div _ hV
      (Stacks.ProjectiveSpaceModuli.resT_pullbackCoordSection_of_le (f ≫ gU) l m hV').symm]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) _)
    (Scheme.Hom.appLE_comp_appLE f gU _ W V hW' e)

end CoordinateRatios

section TensorEval

open TensorProduct

variable {k : Type u} [CommRing k] {O B : Type*} [CommRing O] [Algebra k O] [CommRing B]
  [Algebra k B]

/-- **Evaluation of a family over `B`**: a `k`-algebra map `ev : O → k` gives
`O ⊗_k B → B`. -/
def tensorEval (ev : O →ₐ[k] k) : O ⊗[k] B →ₐ[k] B :=
  (Algebra.TensorProduct.lid k B).toAlgHom.comp (Algebra.TensorProduct.map ev (AlgHom.id k B))

/-- Evaluation sends `a ⊗ c` to `ev a · c`. -/
theorem tensorEval_tmul (ev : O →ₐ[k] k) (a : O) (c : B) :
    tensorEval ev (a ⊗ₜ[k] c) = algebraMap k B (ev a) * c := by
  simp [tensorEval, Algebra.smul_def]

/-- Evaluation sends `∑ₘ aₘ ⊗ cₘ` to `∑ₘ ev aₘ · cₘ`. -/
theorem tensorEval_sum {N : ℕ} (ev : O →ₐ[k] k) (a : Fin N → O) (c : Fin N → B) :
    tensorEval ev (∑ m, a m ⊗ₜ[k] c m) = ∑ m, algebraMap k B (ev (a m)) * c m := by
  rw [map_sum]
  simp only [tensorEval_tmul]

/-- **A family reducing to `f0` modulo `I` evaluates, at a point of `V(I)`, to the value of
`f0`.** If `ev` kills the ideal `I` and `y z ≡ f0 z ⊗ 1` modulo `I ⊗ B`, then
`(ev ⊗ id)(y z) = ev (f0 z)`. -/
theorem tensorEval_eq_of_map_mk {S : Type*} [CommRing S] [Algebra k S] (ev : O →ₐ[k] k)
    (I : Ideal O) (hI : ∀ x ∈ I, ev x = 0) (f0 : S →ₐ[k] O) (y : O ⊗[k] B) (z : S)
    (hy : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (AlgHom.id k B) y =
      Ideal.Quotient.mk I (f0 z) ⊗ₜ[k] 1) :
    tensorEval ev y = algebraMap k B (ev (f0 z)) := by
  let ev' : (O ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I ev hI
  have hev : ev = ev'.comp (Ideal.Quotient.mkₐ k I) := by
    ext x
    rfl
  have h : tensorEval (B := B) ev = (tensorEval (B := B) ev').comp
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (AlgHom.id k B)) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [tensorEval, hev]
  rw [h, AlgHom.comp_apply, hy, tensorEval_tmul, mul_one]
  rfl

end TensorEval

section ChartEval

open TensorProduct Stacks.AlgebraicGeometry.SectionsBaseChange

variable {k : Type u} [Field k] {C U : Scheme.{u}} (sC : C ⟶ Spec (.of k)) (sU : U ⟶ Spec (.of k))
  {f : C ⟶ U} (hf : f ≫ sU = sC) {ι : Type u} [DecidableEq ι] [Fintype ι] (K : ChartCover f ι)
  [IsSeparated sU] [Smooth sU] {b : ℕ} (pts : Fin b → C)
  {L : C.Modules} [Stacks.Ample.IsInvertibleModule C L] {κ : Type*} (σ : κ → Γ(L, ⊤)) (l : ι → κ)
  (hσ : ∀ i, K.UC i ≤ nvCover σ (l i)) {N : ℕ}
  (w : letI := baseModule sC L ⊤; Module.Basis (Fin N) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- **The value at a `k`-point of the source charts**, as a map of `k`-algebras. -/
def chartPointEval (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (t : ι)
    (hV : ⊤ ≤ P ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) :
    (curveCharts sC sU K hf pts).O {t} →ₐ[k] k where
  toRingHom := pointEval P hV
  commutes' c := pointEval_baseRingHom P sC hP hV c

/-- The value at a point of a source chart is `pointEval`. -/
theorem chartPointEval_apply (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (t : ι)
    (hV : ⊤ ≤ P ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (x : (curveCharts sC sU K hf pts).O {t}) :
    chartPointEval sC sU hf K pts P hP t hV x = pointEval P hV x := rfl

/-- The value at a marked point lying in a chart kills the ideal of the marked points. -/
theorem chartPointEval_eq_zero_of_mem (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (t : ι)
    (hV : ⊤ ≤ P ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (β : Fin b) (pt : Spec (.of k))
    (hβ : pts β = P.base pt) (x : (curveCharts sC sU K hf pts).O {t})
    (hx : x ∈ (curveCharts sC sU K hf pts).𝔟 {t}) :
    chartPointEval sC sU hf K pts P hP t hV x = 0 := by
  have hmem : P.base pt ∈ ({t} : Finset ι).inf K.UC := hV trivial
  have hβ' : pts β ∈ ({t} : Finset ι).inf K.UC := hβ ▸ hmem
  have h1 := (mem_vanishingIdeal pts _ x).1 hx β hβ'
  have key : ∀ (p : C) (hp : p ∈ ({t} : Finset ι).inf K.UC), p = P.base pt →
      C.presheaf.germ _ p hp x ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk p) →
      C.presheaf.germ _ (P.base pt) hmem x ∈
        IsLocalRing.maximalIdeal (C.presheaf.stalk (P.base pt)) := by
    rintro p hp rfl h
    exact h
  exact pointEval_eq_zero_of_mem_maximalIdeal P hV pt hmem x (key _ hβ' hβ h1)

/-- **The pullback of a section to a point of a chart** is the value there of its local
expression times the pullback of the frame `σ_{l t}`. -/
theorem pullbackGlobalSections_eq_smul_localSection (P : Spec (.of k) ⟶ C) (t : ι)
    (hV : ⊤ ≤ P ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (s : Γ(L, ⊤)) :
    AlgebraicGeometry.pullbackGlobalSections P L s =
      (Scheme.ΓSpecIso (.of k)).inv (pointEval P hV (localSection sC sU hf K pts σ l hσ s t)) •
        AlgebraicGeometry.pullbackGlobalSections P L (σ (l t)) := by
  rw [pullbackGlobalSections_eq_smul P L s (σ (l t)) hV
    (inf_le_nvCover σ K.UC l hσ (Finset.mem_singleton_self t))]
  congr 1
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of k)) _).symm

/-- The local expression of the frame `σ_{l t}` in its own chart is `1`. -/
theorem localSection_self (t : ι) :
    localSection sC sU hf K pts σ l hσ (σ (l t)) t = 1 := by
  have h := div_smul_self (σ (l t)) (inf_le_nvCover σ K.UC l hσ (Finset.mem_singleton_self t)) 1
  rwa [one_smul] at h

/-- **The values of the basis at a point are proportional to the values of the local
expressions.** If the pullbacks of the `w_j` to a `k`-point of the chart `U_t` are
`ℓ_j · v` and `σ_{l t} = Σ_j a_j w_j`, then `ℓ_j = κ · (w_j / σ_{l t})(P)` for one `κ ∈ k`. -/
theorem exists_eq_mul_pointEval_localSection (P : Spec (.of k) ⟶ C) (hP : P ≫ sC = 𝟙 _) (t : ι)
    (hV : ⊤ ≤ P ⁻¹ᵁ (({t} : Finset ι).inf K.UC)) (ℓ : Fin N → k)
    (v : Γ((Scheme.Modules.pullback P).obj L, ⊤))
    (hv : ∀ j, AlgebraicGeometry.pullbackGlobalSections P L (w j) =
      (Scheme.ΓSpecIso (.of k)).inv (ℓ j) • v) (a : Fin N → k)
    (ha : σ (l t) = ∑ j, sC.appTop ((Scheme.ΓSpecIso (.of k)).inv (a j)) • w j) :
    ∃ c : k, ∀ j, ℓ j = c * pointEval P hV (localSection sC sU hf K pts σ l hσ (w j) t) := by
  set e : Fin N → k := fun j => pointEval P hV (localSection sC sU hf K pts σ l hσ (w j) t)
  have hsum : ∑ j, a j * e j = 1 := by
    have h1 := chartLocal_sum_coefficients sC sU hf K pts σ l hσ w a t
    rw [← ha] at h1
    have h1' : (1 : (curveCharts sC sU K hf pts).O {t}) =
        ∑ m, a m • localSection sC sU hf K pts σ l hσ (w m) t :=
      (localSection_self sC sU hf K pts σ l hσ t).symm.trans h1
    have h2 := congrArg (chartPointEval sC sU hf K pts P hP t hV) h1'
    rw [map_one, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, e j₀ ≠ 0 := by
    by_contra hne
    push Not at hne
    simp [hne] at hsum
  have hP0 : AlgebraicGeometry.pullbackGlobalSections P L (σ (l t)) ≠ 0 := by
    refine pullbackGlobalSections_ne_zero P L _ (IsLocalRing.closedPoint k) ?_
    have hmem : P.base (IsLocalRing.closedPoint k) ∈ ({t} : Finset ι).inf K.UC := hV trivial
    have := inf_le_nvCover σ K.UC l hσ (Finset.mem_singleton_self t) hmem
    rwa [← SetLike.mem_coe, Stacks.NonvanishingOpen.coe_nonvanishingOpen] at this
  have hcross : ∀ j, ℓ j₀ * e j = ℓ j * e j₀ := by
    intro j
    have hj := (pullbackGlobalSections_eq_smul_localSection sC sU hf K pts σ l hσ P t hV (w j)).symm.trans
      (hv j)
    have hj0 := (pullbackGlobalSections_eq_smul_localSection sC sU hf K pts σ l hσ P t hV
      (w j₀)).symm.trans (hv j₀)
    have key : (Scheme.ΓSpecIso (.of k)).inv (ℓ j₀ * e j) •
        AlgebraicGeometry.pullbackGlobalSections P L (σ (l t)) =
        (Scheme.ΓSpecIso (.of k)).inv (ℓ j * e j₀) •
        AlgebraicGeometry.pullbackGlobalSections P L (σ (l t)) := by
      rw [map_mul, map_mul, mul_smul, mul_smul]
      change _ • ((Scheme.ΓSpecIso (.of k)).inv (e j) • _) = _ • ((Scheme.ΓSpecIso (.of k)).inv (e j₀) • _)
      rw [hj, hj0, smul_smul, smul_smul, mul_comm]
    have := smul_left_cancel_specField hP0 key
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).1 this
  refine ⟨ℓ j₀ / e j₀, fun j => ?_⟩
  change ℓ j = ℓ j₀ / e j₀ * e j
  rw [div_mul_eq_mul_div, hcross j, mul_div_assoc, div_self hj₀, mul_one]

end ChartEval

section NonemptyIso

open MMP.Fourfold.CurveChartDeformations

variable {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι]

/-- **An isomorphism of presheaves on the nerve over the nonempty intersections.** The Čech
cochains only see the nonempty `s`, so such an isomorphism identifies the first Čech cohomology. -/
structure NonemptyIso (F G : CechPresheaf.{u} k ι) where
  /-- The component at a nonempty `s`. -/
  equiv : ∀ s : Finset ι, s.Nonempty → F.obj s ≃ₗ[k] G.obj s
  /-- The components commute with restriction. -/
  map_res : ∀ {s t : Finset ι} (h : s ⊆ t) (hs : s.Nonempty) (x : F.obj s),
    equiv t (hs.mono h) (F.res h x) = G.res h (equiv s hs x)

namespace NonemptyIso

variable {F G : CechPresheaf.{u} k ι} (e : NonemptyIso F G)

/-- The inverse isomorphism. -/
def symm : NonemptyIso G F where
  equiv s hs := (e.equiv s hs).symm
  map_res {s t} h hs x := by
    apply (e.equiv t (hs.mono h)).injective
    rw [e.map_res h hs, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The map on Čech `1`-cochains. -/
def c1 : F.C1 →ₗ[k] G.C1 where
  toFun b i j := e.equiv {i, j} (Finset.insert_nonempty _ _) (b i j)
  map_add' b b' := by ext i j; simp
  map_smul' r b := by ext i j; simp

/-- The map on Čech `1`-cochains is the component at `{i, j}` in each entry. -/
theorem c1_apply (b : F.C1) (i j : ι) :
    e.c1 b i j = e.equiv {i, j} (Finset.insert_nonempty _ _) (b i j) := rfl

/-- The map on Čech `1`-cochains sends cocycles to cocycles. -/
theorem isCocycle_c1 {b : F.C1} (hb : F.IsCocycle b) : G.IsCocycle (e.c1 b) := by
  intro i j l
  have h := congrArg (e.equiv {i, j, l} (Finset.insert_nonempty _ _)) (hb i j l)
  rw [map_add, map_sub, e.map_res _ (Finset.insert_nonempty _ _),
    e.map_res _ (Finset.insert_nonempty _ _), e.map_res _ (Finset.insert_nonempty _ _),
    map_zero] at h
  exact h

/-- The map on Čech `1`-cochains sends the coboundary of a `0`-cochain `c` to the coboundary of its
image under the components at the singletons. -/
theorem c1_d0 (c : F.C0) :
    e.c1 (F.d0 c) = G.d0 (fun i => e.equiv {i} (Finset.singleton_nonempty i) (c i)) := by
  ext i j
  simp only [c1_apply, CechPresheaf.d0, LinearMap.coe_mk, AddHom.coe_mk, map_sub]
  rw [e.map_res _ (Finset.singleton_nonempty _), e.map_res _ (Finset.singleton_nonempty _)]

/-- The induced map on first Čech cohomology. -/
def h1 : F.H1 →ₗ[k] G.H1 :=
  Submodule.mapQ F.B1 G.B1
    ((e.c1.restrict (fun b hb => e.isCocycle_c1 hb) : F.Z1 →ₗ[k] G.Z1))
    (by
      rintro ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨fun i => e.equiv {i} (Finset.singleton_nonempty i) (c i), ?_⟩
      change G.d0 _ = e.c1 b
      rw [← e.c1_d0, hc]
      rfl)

/-- The induced map on first Čech cohomology sends the class of a cocycle `b` to the class of its
image. -/
theorem h1_cls {b : F.C1} (hb : F.IsCocycle b) :
    e.h1 (F.cls b hb) = G.cls (e.c1 b) (e.isCocycle_c1 hb) := rfl

/-- **The first Čech cohomologies of presheaves isomorphic over the nonempty intersections
agree.** -/
def h1Equiv : F.H1 ≃ₗ[k] G.H1 :=
  LinearEquiv.ofLinear e.h1 e.symm.h1
    (LinearMap.ext fun z => by
      obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
      have hb' : G.IsCocycle b := hb
      change e.h1 (e.symm.h1 (G.cls b hb')) = G.cls b hb'
      rw [h1_cls, h1_cls]
      refine congrArg (Submodule.Quotient.mk (p := G.B1)) (Subtype.ext ?_)
      funext i j
      exact (e.equiv _ _).apply_symm_apply _)
    (LinearMap.ext fun z => by
      obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
      have hb' : F.IsCocycle b := hb
      change e.symm.h1 (e.h1 (F.cls b hb')) = F.cls b hb'
      rw [h1_cls, h1_cls]
      refine congrArg (Submodule.Quotient.mk (p := F.B1)) (Subtype.ext ?_)
      funext i j
      exact (e.equiv _ _).symm_apply_apply _)

end NonemptyIso

end NonemptyIso

/-! ### Substitution into sections of an invertible module, charts, and pullbacks

Dehomogenization of the section ring at a degree-one section, the chart evaluations
`T_j ↦ σ_j / σ_i` of a tuple of sections, and the comparison of substituted sections with chart
evaluations under pullback. -/

section Substitution

open Stacks.NonvanishingOpen
open Stacks.Ample (IsInvertibleModule nonvanishingLocus)
open Stacks.GradedSections (powSections sectionRing)
open Stacks.Algebraization (degreeOneSection)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

section Dehomogenization

open Stacks.SectionRingChartMap (ratio ratioR ratio_add ratioR_mul ratioR_congr
  ratioR_of of_mul_eq of_powSec_eq_pow le_nvOpen_powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen)
open Stacks.SectionRingProjMorphism.ToSpecZero (unitSec le_nvOpen_unitSec of_unitSec)
open Stacks.SectionExtension (powSec)
open Stacks.SectionRingGeometric (unitScalarAddEquiv)

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] {V : X.Opens}

/-- For `V` inside the nonvanishing open of a degree-one section `a`, each degree `m` has a section
`g` with `g = a ^ m` in the section ring and `V` inside the nonvanishing open of `g`. -/
theorem exists_generator (a : powSections L 1) (hV : V ≤ nvOpen L a) (m : ℕ) :
    ∃ g : powSections L m, DirectSum.of (powSections L) m g =
      (DirectSum.of (powSections L) 1 a) ^ m ∧ V ≤ nvOpen L g := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨unitSec L, by rw [pow_zero]; exact of_unitSec L, le_nvOpen_unitSec L⟩
  · have key : ∀ (j : ℕ) (h : j = m) (t : powSections L j),
        ∃ g : powSections L m, DirectSum.of (powSections L) m g = DirectSum.of (powSections L) j t ∧
          nvOpen L g = nvOpen L t := by
      rintro j rfl t
      exact ⟨t, rfl, rfl⟩
    obtain ⟨g, hg1, hg2⟩ := key (1 * m) (Nat.one_mul m) (powSec L a m)
    refine ⟨g, hg1.trans (of_powSec_eq_pow L a m), ?_⟩
    rw [hg2]
    exact le_nvOpen_powSec L a hV m hm

/-- The degreewise ratio as an additive map. -/
def ratioHom {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) : powSections L j →+ Γ(X, V) :=
  AddMonoidHom.mk' (fun s => ratio L g hg s) (fun s t => ratio_add L g hg s t)

variable (a : powSections L 1) (hV : V ≤ nvOpen L a)

/-- The chosen generator `a ^ m` in degree `m`. -/
def powGenerator (m : ℕ) : powSections L m := (exists_generator L a hV m).choose

/-- The generator `powGenerator L a hV m` is `a ^ m` in the section ring. -/
theorem of_powGenerator (m : ℕ) :
    DirectSum.of (powSections L) m (powGenerator L a hV m) =
      (DirectSum.of (powSections L) 1 a) ^ m :=
  (exists_generator L a hV m).choose_spec.1

/-- The open `V` lies in the nonvanishing open of `powGenerator L a hV m`. -/
theorem le_nvOpen_powGenerator (m : ℕ) : V ≤ nvOpen L (powGenerator L a hV m) :=
  (exists_generator L a hV m).choose_spec.2

/-- The degreewise ratio of `x` by `g` is the ratio of the element `x` of the section ring. -/
theorem ratioHom_apply {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) (x : powSections L j) :
    ratioHom L g hg x = ratioR L g hg (DirectSum.of (powSections L) j x) :=
  (ratioR_of L g hg x).symm

/-- The degreewise ratio in degree `0` sends the unit to `1`. -/
theorem ratioHom_powGenerator_one :
    ratioHom L (powGenerator L a hV 0) (le_nvOpen_powGenerator L a hV 0)
      (GradedMonoid.GOne.one : powSections L 0) = 1 := by
  have h1 : DirectSum.of (powSections L) 0 (GradedMonoid.GOne.one : powSections L 0) = 1 := rfl
  rw [ratioHom_apply, h1]
  rw [ratioR_congr L rfl (powGenerator L a hV 0) (unitSec L) (le_nvOpen_powGenerator L a hV 0)
    (le_nvOpen_unitSec L) (by rw [of_powGenerator, pow_zero, of_unitSec]) 1]
  rw [← of_unitSec L]
  exact Stacks.SectionRingChartMap.ratioR_of_self L (unitSec L) (le_nvOpen_unitSec L)

/-- The degreewise ratios by the generators `a ^ m` are multiplicative. -/
theorem ratioHom_powGenerator_mul {i j : ℕ} (x : powSections L i) (y : powSections L j) :
    ratioHom L (powGenerator L a hV (i + j)) (le_nvOpen_powGenerator L a hV (i + j))
      (GradedMonoid.GMul.mul x y) =
    ratioHom L (powGenerator L a hV i) (le_nvOpen_powGenerator L a hV i) x *
      ratioHom L (powGenerator L a hV j) (le_nvOpen_powGenerator L a hV j) y := by
  have hgg : V ≤ nvOpen L (Stacks.GradedSections.mul (powGenerator L a hV i)
      (powGenerator L a hV j)) :=
    Stacks.SectionRingChartMap.le_nvOpen_mul L (le_nvOpen_powGenerator L a hV i)
      (le_nvOpen_powGenerator L a hV j)
  rw [ratioHom_apply, ratioHom_apply, ratioHom_apply, ← DirectSum.of_mul_of]
  rw [ratioR_congr L rfl (powGenerator L a hV (i + j))
    (Stacks.GradedSections.mul (powGenerator L a hV i) (powGenerator L a hV j))
    (le_nvOpen_powGenerator L a hV (i + j)) hgg (by
      rw [of_powGenerator, pow_add, ← of_powGenerator L a hV i, ← of_powGenerator L a hV j,
        of_mul_eq]) _]
  exact ratioR_mul L _ _ (le_nvOpen_powGenerator L a hV i) (le_nvOpen_powGenerator L a hV j) hgg
    (Stacks.ExternalGrading.of_mem_summand i x) (Stacks.ExternalGrading.of_mem_summand j y)

/-- **Dehomogenization at a degree-one section**: the ring homomorphism `Γ_*(X, L) → Γ(V, 𝒪)`
dividing the degree-`j` component by `a ^ j`, for `V` inside the nonvanishing open of `a`. -/
def dehomogenize : sectionRing L →+* Γ(X, V) :=
  DirectSum.toSemiring (fun j => ratioHom L (powGenerator L a hV j) (le_nvOpen_powGenerator L a hV j))
    (ratioHom_powGenerator_one L a hV)
    (fun x y => ratioHom_powGenerator_mul L a hV x y)

/-- Dehomogenization sends a section `x` of degree `j` to `x / a ^ j`. -/
theorem dehomogenize_of {j : ℕ} (x : powSections L j) :
    dehomogenize L a hV (DirectSum.of (powSections L) j x) =
      ratio L (powGenerator L a hV j) (le_nvOpen_powGenerator L a hV j) x :=
  DirectSum.toSemiring_of _ _ _ j x

/-- The ratio by a section depends only on the section, not on the proof of nonvanishing. -/
theorem ratio_congr_generator {j : ℕ} {g g' : powSections L j} (h : g = g') (hg : V ≤ nvOpen L g)
    (hg' : V ≤ nvOpen L g') (x : powSections L j) : ratio L g hg x = ratio L g' hg' x := by
  subst h; rfl

/-- The generator in degree `1` is `a`. -/
theorem powGenerator_one : powGenerator L a hV 1 = a := by
  have h := of_powGenerator L a hV 1
  rw [pow_one] at h
  exact DirectSum.of_injective (β := fun i => powSections L i) 1 h

/-- The generator in degree `0` is the unit section. -/
theorem powGenerator_zero : powGenerator L a hV 0 = unitSec L := by
  have h := of_powGenerator L a hV 0
  rw [pow_zero, ← of_unitSec L] at h
  exact DirectSum.of_injective (β := fun i => powSections L i) 0 h

/-- Dehomogenization sends a section `x` of degree `1` to `x / a`. -/
theorem dehomogenize_of_one (x : powSections L 1) :
    dehomogenize L a hV (DirectSum.of (powSections L) 1 x) = ratio L a hV x := by
  rw [dehomogenize_of]
  exact ratio_congr_generator L (powGenerator_one L a hV) _ _ x

/-- Dehomogenization sends a degree-zero element `f ∈ Γ(X, 𝒪_X)` to its restriction to `V`. -/
theorem dehomogenize_sectionRingZeroHom (f : Γ(X, ⊤)) :
    dehomogenize L a hV (Stacks.SectionRingZero.sectionRingZeroHom X L f) =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op f := by
  rw [Stacks.SectionRingZero.sectionRingZeroHom_apply, dehomogenize_of,
    ratio_congr_generator L (powGenerator_zero L a hV) _ (le_nvOpen_unitSec L)]
  refine Stacks.SectionRingChartMap.ratio_unique L _ _ _ _ ?_
  have h1 : Stacks.SectionProduct.globalSection X (Stacks.TensorPowers.natTensorPow L 0)
      ((unitScalarAddEquiv X).symm f) =
      f • Stacks.SectionProduct.globalSection X (Stacks.TensorPowers.natTensorPow L 0)
        (unitSec L) := by
    have := Stacks.SectionRingGeometric.globalSection_unitComp X
      ((unitScalarAddEquiv X).symm f) (unitSec L)
    rw [Stacks.SectionRingZero.unitScalar_unitScalarAddEquiv_symm] at this
    have e : (unitScalarAddEquiv X).symm f = (unitScalarAddEquiv X).symm f ≫ unitSec L :=
      (Category.comp_id _).symm
    rw [e]
    exact this
  rw [h1]
  exact Scheme.Modules.map_smul _ _ _ _

end Dehomogenization

section Bridge

open Stacks.Algebraization (globalSection_degreeOneSection)
open MonoidalCategory

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- The nonvanishing open of `s` as a degree-one section is the nonvanishing open of `s`. -/
theorem nvOpen_degreeOneSection (s : Γ(L, ⊤)) :
    Stacks.AmpleFiniteAvoidance.nvOpen L (degreeOneSection L s) = nonvanishingOpen X L s := by
  refine TopologicalSpace.Opens.ext ?_
  rw [Stacks.AmpleFiniteAvoidance.coe_nvOpen]
  change Stacks.AmpleFiniteAvoidance.nvLocus L (degreeOneSection L s) = _
  unfold Stacks.AmpleFiniteAvoidance.nvLocus
  rw [globalSection_degreeOneSection]
  exact nonvanishingLocus_app_top_eq_of_iso (X := X) (M := L) (M' := Stacks.TensorPowers.natTensorPow L 1)
    (λ_ L).symm s

/-- An open inside the nonvanishing open of `s` lies inside the nonvanishing open of `s` as a
degree-one section. -/
theorem le_nvOpen_degreeOneSection {s : Γ(L, ⊤)} {V : X.Opens} (hV : V ≤ nonvanishingOpen X L s) :
    V ≤ Stacks.AmpleFiniteAvoidance.nvOpen L (degreeOneSection L s) :=
  hV.trans (nvOpen_degreeOneSection L s).ge

/-- The ratio of `s j` by `s i` as degree-one sections, on the chart of `s i`, is `ratio s i j`. -/
theorem ratio_degreeOneSection {ι : Type*} (s : ι → Γ(L, ⊤)) (i j : ι) :
    Stacks.SectionRingChartMap.ratio L (degreeOneSection L (s i))
      (le_nvOpen_degreeOneSection L (le_refl (nvCover s i))) (degreeOneSection L (s j)) =
    Stacks.ProjectiveFromSections.ratio s i j := by
  refine Stacks.SectionRingChartMap.ratio_unique L _ _ _ _ ?_
  have h1 : ∀ t : Γ(L, ⊤), Stacks.TensorPowerTrivialize.resTop
      (Stacks.TensorPowers.natTensorPow L 1) (((λ_ L).inv : L ⟶ Stacks.TensorPowers.natTensorPow L 1).app ⊤ t)
        (nvCover s i) =
      ((λ_ L).inv : L ⟶ Stacks.TensorPowers.natTensorPow L 1).app (nvCover s i)
        (Stacks.TensorPowerTrivialize.resTop L t (nvCover s i)) :=
    fun t => Stacks.TensorPowerTrivialize.resTop_app
      (((λ_ L).inv : L ⟶ Stacks.TensorPowers.natTensorPow L 1)) t (nvCover s i)
  rw [globalSection_degreeOneSection, globalSection_degreeOneSection, h1, h1]
  exact (congrArg (((λ_ L).inv : L ⟶ Stacks.TensorPowers.natTensorPow L 1).app (nvCover s i))
    (Stacks.ProjectiveFromSections.ratio_smul s i j).symm).trans
    (Scheme.Modules.Hom.app_smul _ _ _)

end Bridge

section Cover

open Stacks.TensorPowerTrivialize (resTop)

variable {X : Scheme.{u}}

/-- A global section of a module vanishing on an open cover vanishes. -/
theorem eq_zero_of_resTop_eq_zero_of_cover {N : X.Modules} {ι : Type*} (V : ι → X.Opens)
    (hV : (⊤ : X.Opens) ≤ ⨆ i, V i) (t : Γ(N, ⊤)) (h : ∀ i, resTop N t (V i) = 0) : t = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨Scheme.Modules.presheaf N, N.isSheaf⟩ : TopCat.Sheaf _ _)
    V ⊤ (fun i => homOfLE le_top) hV t 0 (fun i => by rw [map_zero]; exact h i)

end Cover

/-- Restriction along `V ≤ V` is the identity. -/
theorem resO_refl {X : Scheme.{u}} {V : X.Opens} (a : Γ(X, V)) (h : V ≤ V) :
    Stacks.ProjectiveFromSections.resO h a = a := by
  unfold Stacks.ProjectiveFromSections.resO
  rw [show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _]
  exact CategoryTheory.Functor.map_id_apply _ _ _

/-- The base ring map of `W.ι ≫ g` is the restriction to `W` of the base ring map of `g`. -/
theorem baseRingHom_ι_comp_apply {k : Type u} [CommRing k] {Y : Scheme.{u}} (W : Y.Opens)
    (g : Y ⟶ Spec (.of k)) (c : k) :
    Stacks.ProjectiveSpaceChartRatio.baseRingHom (W.ι ≫ g) c =
      W.topIso.inv (resO (le_top : W ≤ ⊤) (Stacks.ProjectiveSpaceChartRatio.baseRingHom g c)) := by
  rw [← Stacks.ProjectiveSpaceChartRatio.baseRingHom_comp W.ι g, RingHom.comp_apply]
  have h : (homOfLE (x := W.ι ''ᵁ ⊤) le_top).op =
      (homOfLE (le_top : W ≤ ⊤)).op ≫ (eqToHom W.ι_image_top).op :=
    Subsingleton.elim _ _
  have h2 := congrArg
    (fun g' => Y.presheaf.map g' (Stacks.ProjectiveSpaceChartRatio.baseRingHom g c)) h
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.ConcreteCategory.comp_apply] at h2
  exact h2

section PullbackRatio

open Stacks.AlgebraicGeometry.ProjChartRatioPullback (top_le_preimage_top)

variable {Y' W : Scheme.{u}} (f : Y' ⟶ W) (M : W.Modules) [IsInvertibleModule W M]

/-- The restriction to `V'` of a pulled-back global section is the pullback of its restriction to
`V`, for `V' ≤ f⁻¹ V`. -/
theorem resTop_pullbackGlobalSections (x : Γ(M, ⊤)) {V : W.Opens} {V' : Y'.Opens}
    (h : V' ≤ f ⁻¹ᵁ V) :
    Stacks.TensorPowerTrivialize.resTop ((Scheme.Modules.pullback f).obj M)
      (AlgebraicGeometry.pullbackGlobalSections f M x) V' =
    AlgebraicGeometry.pullbackSectionHom f M V V' h
      (Stacks.TensorPowerTrivialize.resTop M x V) := by
  rw [Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection,
    ← Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top]
  exact (Stacks.AlgebraicGeometry.ProjChartRatioPullback.map_pullbackSectionHom f M ⊤ ⊤ V'
    (homOfLE (le_top : V' ≤ ⊤)) (top_le_preimage_top f) (le_top.trans (top_le_preimage_top f))
    x).trans (AlgebraicGeometry.pullbackSectionHom_map f M ⊤ V le_top V' h
    (le_top.trans (top_le_preimage_top f)) x).symm

/-- The nonvanishing open of a pulled-back global section is the preimage of the nonvanishing open
of the section. -/
theorem nonvanishingOpen_pullbackGlobalSections (s : Γ(M, ⊤)) :
    nonvanishingOpen Y' ((Scheme.Modules.pullback f).obj M)
      (AlgebraicGeometry.pullbackGlobalSections f M s) = f ⁻¹ᵁ nonvanishingOpen W M s := by
  refine TopologicalSpace.Opens.ext ?_
  ext x
  exact mem_nonvanishingLocus_pullbackGlobalSections_iff f M s x

/-- The chart ratio `σ_j / σ_i` of the pulled-back tuple is the pullback along `f` of the ratio
`σ_j / σ_i`. -/
theorem chartRatio_pullback {n : ℕ} (σ : Fin (n + 1) → Γ(M, ⊤)) (i j : Fin (n + 1))
    (h : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      f ⁻¹ᵁ nvCover σ i) :
    chartRatio (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i j =
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i).topIso.inv
        (f.appLE (nvCover σ i)
          (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) h
          (ratio σ i j)) := by
  have hres : Stacks.TensorPowerTrivialize.resTop ((Scheme.Modules.pullback f).obj M)
      (AlgebraicGeometry.pullbackGlobalSections f M (σ j))
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) =
      f.appLE (nvCover σ i) (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i)
          h (ratio σ i j) •
        Stacks.TensorPowerTrivialize.resTop ((Scheme.Modules.pullback f).obj M)
      (AlgebraicGeometry.pullbackGlobalSections f M (σ i))
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) := by
    rw [resTop_pullbackGlobalSections f M _ h, resTop_pullbackGlobalSections f M _ h,
      ← AlgebraicGeometry.pullbackSectionHom_smul]
    exact congrArg _ (ratio_smul σ i j).symm
  have := Stacks.ChartDegreeEqualisation.chartRatio_eq_of_resTop_eq
    (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i j rfl _ hres
  rwa [resO_refl] at this

/-- Pulling back the restriction of a global function `a` to `V` gives the restriction to `V'` of
the pullback of `a`. -/
theorem appLE_presheaf_map_top {V : W.Opens} {V' : Y'.Opens} (h : V' ≤ f ⁻¹ᵁ V)
    (a : Γ(W, ⊤)) :
    f.appLE V V' h (W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a) =
      Y'.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (f.appTop a) := by
  have := CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE f h (homOfLE (le_top : V ≤ ⊤)).op) a
  refine this.trans ?_
  rfl

open Stacks.ProjectiveSpaceChartRatio in
/-- The chart evaluation of a polynomial `F` in the pulled-back tuple is the pullback along `f` of
the chart evaluation of `F` in `σ`. -/
theorem chartEval_pullback {k : Type u} [Field k] (π : W ⟶ Spec (.of k)) {n : ℕ}
    (σ : Fin (n + 1) → Γ(M, ⊤)) (i : Fin (n + 1))
    (h : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      f ⁻¹ᵁ nvCover σ i) (F : MvPolynomial (Fin (n + 1)) k) :
    chartEval (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) (f ≫ π) i F =
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i).topIso.inv
        (f.appLE (nvCover σ i)
          (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) h
          ((nvCover σ i).topIso.hom (chartEval σ π i F))) := by
  have key : chartEval (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) (f ≫ π) i =
      ((nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i).topIso.inv.hom.comp
        ((f.appLE (nvCover σ i) (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) h).hom.comp
          (((nvCover σ i).topIso.hom).hom.comp (chartEval σ π i)))) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, chartEval, MvPolynomial.eval₂Hom_C]
      rw [baseRingHom_ι_comp_apply, baseRingHom_ι_comp_apply]
      refine congrArg _ ?_
      have e1 := Iso.inv_hom_id_apply (nvCover σ i).topIso (resO (le_top : nvCover σ i ≤ ⊤) ((baseRingHom π) c))
      refine Eq.trans ?_ (congrArg (f.appLE (nvCover σ i) _ h) e1.symm)
      refine Eq.trans ?_ (appLE_presheaf_map_top f h _).symm
      rw [← baseRingHom_comp f π]
      rfl
    · simp only [RingHom.comp_apply, chartEval, MvPolynomial.eval₂Hom_X']
      rw [chartRatio_pullback f M σ i j h]
      refine congrArg _ (congrArg _ ?_)
      have e2 : (nvCover σ i).topIso.hom (chartRatio σ i j) = ratio σ i j := by
        rw [chartRatio]; exact Iso.inv_hom_id_apply _ _
      exact e2.symm
  exact congrArg (fun φ => φ F) key

end PullbackRatio

section SubstitutionRatio

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
  (L : X.Modules) [IsInvertibleModule X L] (σ : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1))

/-- The chart evaluation of the substituted element is the dehomogenization of the substituted
element. -/
theorem topIso_inv_dehomogenize_substitutedElement (F : MvPolynomial (Fin (n + 1)) k) :
    (nvCover σ i).topIso.inv
      (dehomogenize L (degreeOneSection L (σ i))
        (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i)))
        (substitutedElement π L σ F)) = chartEval σ π i F := by
  have key : ((nvCover σ i).topIso.inv.hom.comp
      ((dehomogenize L (degreeOneSection L (σ i))
        (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i)))).comp
        (MvPolynomial.eval₂Hom
          ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp
            (RingHom.comp π.appTop.hom (Scheme.ΓSpecIso (.of k)).inv.hom))
          (fun j => DirectSum.of (powSections L) 1 (degreeOneSection L (σ j)))))) =
      chartEval σ π i := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [dehomogenize_sectionRingZeroHom]
      simp only [chartEval, MvPolynomial.eval₂Hom_C]
      rw [baseRingHom_ι_comp_apply]
      rfl
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [dehomogenize_of_one, ratio_degreeOneSection, chartEval, MvPolynomial.eval₂Hom_X']
      rfl
  exact congrArg (fun φ => φ F) key

/-- For a form `F` of degree `d`, the substituted element `F(σ)` lies in degree `d` of the section
ring. -/
theorem substitutedElement_mem_grading {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) :
    substitutedElement π L σ F ∈ Stacks.AmpleFiniteAvoidance.grading L d := by
  classical
  have hsum : substitutedElement π L σ F = ∑ α ∈ F.support,
      ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp
            (RingHom.comp π.appTop.hom (Scheme.ΓSpecIso (.of k)).inv.hom)) (F.coeff α) *
        α.prod (fun j e => (DirectSum.of (powSections L) 1 (degreeOneSection L (σ j))) ^ e) := by
    conv_lhs => rw [F.as_sum]
    unfold substitutedElement
    rw [MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.eval₂_monomial]
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun α hα => ?_
  have h0 : ((Stacks.SectionRingZero.sectionRingZeroHom X L).comp
            (RingHom.comp π.appTop.hom (Scheme.ΓSpecIso (.of k)).inv.hom)) (F.coeff α) ∈
      Stacks.AmpleFiniteAvoidance.grading L 0 := by
    rw [RingHom.comp_apply, Stacks.SectionRingZero.sectionRingZeroHom_apply]
    exact Stacks.ExternalGrading.of_mem_summand 0 _
  have h1 : α.prod (fun j e => (DirectSum.of (powSections L) 1 (degreeOneSection L (σ j))) ^ e) ∈
      Stacks.AmpleFiniteAvoidance.grading L d := by
    have hα : ∑ j ∈ α.support, α j = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hF (MvPolynomial.mem_support_iff.1 hα)
    rw [← hα]
    unfold Finsupp.prod
    simpa using SetLike.prod_pow_mem_graded (Stacks.AmpleFiniteAvoidance.grading L)
      (F := α.support) (fun _ => 1)
      (fun j => DirectSum.of (powSections L) 1 (degreeOneSection L (σ j))) α
      (fun j _ => Stacks.ExternalGrading.of_mem_summand 1 _)
  simpa using SetLike.mul_mem_graded h0 h1

/-- For a form `F` of degree `d`, the chart evaluation of `F` on the chart of `σ i` is the ratio of
the substituted section `F(σ)` by `σ_i ^ d`. -/
theorem topIso_hom_chartEval_eq_ratio {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) :
    (nvCover σ i).topIso.hom (chartEval σ π i F) =
      Stacks.SectionRingChartMap.ratio L
        (powGenerator L (degreeOneSection L (σ i))
          (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i))) d)
        (le_nvOpen_powGenerator L _ (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i))) d)
        (substitutedSection π L σ F d) := by
  have hz := substitutedElement_mem_grading π L σ hF
  obtain ⟨t, ht⟩ := Stacks.ExternalGrading.mem_summand_iff.1 hz
  have hd : substitutedSection π L σ F d = t := by
    unfold substitutedSection
    rw [← ht, DirectSum.of_eq_same]
  rw [hd, ← topIso_inv_dehomogenize_substitutedElement π L σ i F, ← ht, dehomogenize_of]
  exact Iso.inv_hom_id_apply _ _

/-- For a form `F` of degree `d`, the substituted section `F(σ) ∈ Γ(X, L^{⊗ d})` vanishes if and
only if every chart evaluation `T_j ↦ σ_j / σ_i` kills `F`, for a generating tuple `σ`. -/
theorem substitutedSection_eq_zero_iff (hs : GeneratesStalks σ) {d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d) :
    substitutedSection π L σ F d = 0 ↔ ∀ i, chartEval σ π i F = 0 := by
  have hz := substitutedElement_mem_grading π L σ hF
  obtain ⟨t, ht⟩ := Stacks.ExternalGrading.mem_summand_iff.1 hz
  have hd : substitutedSection π L σ F d = t := by
    unfold substitutedSection
    rw [← ht, DirectSum.of_eq_same]
  have hdeh : ∀ i, (nvCover σ i).topIso.inv
      (Stacks.SectionRingChartMap.ratio L
        (powGenerator L (degreeOneSection L (σ i))
          (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i))) d)
        (le_nvOpen_powGenerator L _ _ d) t) = chartEval σ π i F := by
    intro i
    rw [← topIso_inv_dehomogenize_substitutedElement π L σ i F, ← ht, dehomogenize_of]
  rw [hd]
  constructor
  · rintro rfl i
    rw [← hdeh i, Stacks.SectionRingChartMap.ratio_zero, map_zero]
  · intro h
    have hr : ∀ i, Stacks.SectionRingChartMap.ratio L
        (powGenerator L (degreeOneSection L (σ i))
          (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i))) d)
        (le_nvOpen_powGenerator L _ _ d) t = 0 := by
      intro i
      have h2 := congrArg (nvCover σ i).topIso.hom ((hdeh i).trans (h i))
      rwa [Iso.inv_hom_id_apply, map_zero] at h2
    have hcover := isOpenCover_nvCover_of_generatesStalks σ hs
    have : Stacks.SectionProduct.globalSection X (Stacks.TensorPowers.natTensorPow L d) t = 0 := by
      refine eq_zero_of_resTop_eq_zero_of_cover (nvCover σ) (le_of_eq hcover.iSup_eq_top.symm) _ fun i => ?_
      rw [← Stacks.SectionRingChartMap.ratio_smul_resTop L _
        (le_nvOpen_powGenerator L _ (le_nvOpen_degreeOneSection L (le_refl (nvCover σ i))) d) t, hr i,
        zero_smul]
    exact (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
      (Stacks.TensorPowers.natTensorPow L d)).map_eq_zero_iff.1 this

end SubstitutionRatio

section PullbackEquations

open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection ratioOf_pullback
  nonvanishingOpen_pullSection)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf ratioOf_eq_of_resTop_eq)

variable {k : Type u} [Field k] {n : ℕ} {Y' W : Scheme.{u}} (f : Y' ⟶ W) (π : W ⟶ Spec (.of k))
  (M : W.Modules) [IsInvertibleModule W M] (σ : Fin (n + 1) → Γ(M, ⊤))

/-- If the pullback along `f` of the substituted section `F(σ) ∈ Γ(W, M^{⊗ d})` vanishes, every
chart evaluation of the pulled-back tuple kills `F`. -/
theorem chartEval_pullback_eq_zero {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d)
    (h0 : pullSection f M d (Stacks.SectionProduct.globalSection W _
      (substitutedSection π M σ F d)) = 0) (i : Fin (n + 1)) :
    chartEval (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) (f ≫ π) i F = 0 := by
  have hh : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      f ⁻¹ᵁ nvCover σ i :=
    (nonvanishingOpen_pullbackGlobalSections f M (σ i)).le
  rw [chartEval_pullback f M π σ i hh F, topIso_hom_chartEval_eq_ratio π M σ i hF]
  have hgen := le_nvOpen_powGenerator M (degreeOneSection M (σ i))
    (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d
  have hV' : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      nonvanishingOpen Y' (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback f).obj M) d)
        (pullSection f M d (Stacks.SectionProduct.globalSection W _
          (powGenerator M (degreeOneSection M (σ i))
            (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d))) := by
    rw [nonvanishingOpen_pullSection]
    exact hh.trans (fun x hx => hgen hx)
  have key := ratioOf_pullback f M (Stacks.SectionProduct.globalSection W _
      (powGenerator M (degreeOneSection M (σ i))
        (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d)) hgen
    (Stacks.SectionProduct.globalSection W _ (substitutedSection π M σ F d)) hh hV'
  rw [h0] at key
  have h00 : ratioOf ((Scheme.Modules.pullback f).obj M)
      (pullSection f M d (Stacks.SectionProduct.globalSection W _
          (powGenerator M (degreeOneSection M (σ i))
            (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d))) hV' 0 = 0 := by
    refine ratioOf_eq_of_resTop_eq _ _ hV' ?_
    rw [zero_smul]
    exact map_zero _
  rw [h00] at key
  change _ = 0
  have : f.appLE (nvCover σ i) (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) hh
      (Stacks.SectionRingChartMap.ratio M
        (powGenerator M (degreeOneSection M (σ i))
          (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d) hgen
        (substitutedSection π M σ F d)) = 0 := key.symm
  rw [this, map_zero]

/-- If the pulled-back tuple generates and all its chart evaluations kill `F`, the pullback of the
substituted section `F(σ) ∈ Γ(W, M^{⊗ d})` vanishes. -/
theorem pullSection_eq_zero_of_chartEval_pullback {d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d)
    (hs : GeneratesStalks (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)))
    {π' : Y' ⟶ Spec (.of k)} (hπ : f ≫ π = π')
    (h0 : ∀ i, chartEval (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j))
      π' i F = 0) :
    pullSection f M d (Stacks.SectionProduct.globalSection W _
      (substitutedSection π M σ F d)) = 0 := by
  subst hπ
  refine eq_zero_of_resTop_eq_zero_of_cover
    (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)))
    (le_of_eq (isOpenCover_nvCover_of_generatesStalks _ hs).iSup_eq_top.symm) _ fun i => ?_
  have hh : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      f ⁻¹ᵁ nvCover σ i :=
    (nonvanishingOpen_pullbackGlobalSections f M (σ i)).le
  have hgen := le_nvOpen_powGenerator M (degreeOneSection M (σ i))
    (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d
  have hV' : nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i ≤
      nonvanishingOpen Y' (Stacks.TensorPowers.natTensorPow ((Scheme.Modules.pullback f).obj M) d)
        (pullSection f M d (Stacks.SectionProduct.globalSection W _
          (powGenerator M (degreeOneSection M (σ i))
            (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d))) := by
    rw [nonvanishingOpen_pullSection]
    exact hh.trans (fun x hx => hgen hx)
  have key := ratioOf_pullback f M (Stacks.SectionProduct.globalSection W _
      (powGenerator M (degreeOneSection M (σ i))
        (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d)) hgen
    (Stacks.SectionProduct.globalSection W _ (substitutedSection π M σ F d)) hh hV'
  have hz : f.appLE (nvCover σ i)
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i) hh
      (Stacks.SectionRingChartMap.ratio M
        (powGenerator M (degreeOneSection M (σ i))
          (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d) hgen
        (substitutedSection π M σ F d)) = 0 := by
    have h1 := h0 i
    rw [chartEval_pullback f M π σ i hh F, topIso_hom_chartEval_eq_ratio π M σ i hF] at h1
    have h2 := congrArg
      (nvCover (fun j => AlgebraicGeometry.pullbackGlobalSections f M (σ j)) i).topIso.hom h1
    rwa [Iso.inv_hom_id_apply, map_zero] at h2
  have hr : ratioOf ((Scheme.Modules.pullback f).obj M)
      (pullSection f M d (Stacks.SectionProduct.globalSection W _
          (powGenerator M (degreeOneSection M (σ i))
            (le_nvOpen_degreeOneSection M (le_refl (nvCover σ i))) d))) hV'
      (pullSection f M d (Stacks.SectionProduct.globalSection W _
        (substitutedSection π M σ F d))) = 0 := key.trans hz
  rw [Stacks.AlgebraicGeometry.ProjChartCocycle.resTop_eq_ratioOf_smul _ _ hV', hr, zero_smul]

end PullbackEquations

section FamilyEquations

open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection top_le_preimage_top
  pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.SectionsBaseChange

/-- A global section whose image under an isomorphism of modules vanishes is zero. -/
theorem eq_zero_of_iso_app_eq_zero {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) {z : Γ(A, ⊤)}
    (h : e.hom.app ⊤ z = 0) : z = 0 := by
  have := congrArg (e.inv.app ⊤) h
  rw [map_zero] at this
  rw [← this, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
  rfl

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))

/-- **The pullback of the substituted universal section vanishes when the equation functions
vanish at a `T`-point.** -/
theorem pullSection_substitutedSection_eq_zero [IsProper sC] {T : Scheme.{u}} [IsAffine T]
    (g : T ⟶ coefficientSpace n N k) (d : ℕ) {N' : ℕ}
    (w' : letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
      Module.Basis (Fin N') Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤))
    (F : MvPolynomial (Fin (n + 1)) k)
    (hg : ∀ j, g.appTop (equationFunctions (n := n) sC L e d w' F j) = 0) :
    pullSection (familyPullbackMap (n := n) (N := N) (sC := sC) g)
      ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L) d
      (Stacks.SectionProduct.globalSection (universalCurve (n := n) (N := N) sC) _
        (substitutedSection (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
          ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
          (universalSection (n := n) sC L e) F d)) = 0 := by
  set x := Stacks.SectionProduct.globalSection (universalCurve (n := n) (N := N) sC) _
    (substitutedSection (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
      ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
      (universalSection (n := n) sC L e) F d)
  have h1 := (pullback_eq_zero_iff_coefficientFunctions (n := n) (N := N) sC w' g
    (substitutedUniversalSection (n := n) sC L e d F)).2 hg
  have h2 := eq_zero_of_iso_app_eq_zero
    ((Scheme.Modules.pullbackComp (familyPullbackMap (n := n) (N := N) (sC := sC) g)
        (pullback.fst sC (coefficientSpaceOver n N k))).app (Stacks.TensorPowers.natTensorPow L d))
    h1
  have h3 : AlgebraicGeometry.pullbackGlobalSections
      (familyPullbackMap (n := n) (N := N) (sC := sC) g) _
      (substitutedUniversalSection (n := n) sC L e d F) =
      ((Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)).map
        (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d).hom).app ⊤
        (AlgebraicGeometry.pullbackSectionHom (familyPullbackMap (n := n) (N := N) (sC := sC) g)
          _ ⊤ ⊤ (top_le_preimage_top _) x) := by
    rw [Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection,
      ← Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top]
    exact Stacks.PullbackUnitSection.pullbackSectionHom_app _
      (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d).hom ⊤ ⊤
      (top_le_preimage_top _) x
  rw [h3] at h2
  have h4 := eq_zero_of_iso_app_eq_zero
    ((Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)).mapIso
      (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d)) h2
  unfold pullSection
  rw [h4, map_zero]

/-- **Conversely, the equation functions vanish at a `T`-point when the pullback of the
substituted universal section vanishes.** -/
theorem equationFunctions_eq_zero_of_pullSection [IsProper sC] {T : Scheme.{u}}
    [IsAffine T] (g : T ⟶ coefficientSpace n N k) (d : ℕ) {N' : ℕ}
    (w' : letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
      Module.Basis (Fin N') Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤))
    (F : MvPolynomial (Fin (n + 1)) k)
    (h0 : pullSection (familyPullbackMap (n := n) (N := N) (sC := sC) g)
      ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L) d
      (Stacks.SectionProduct.globalSection (universalCurve (n := n) (N := N) sC) _
        (substitutedSection (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
          ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
          (universalSection (n := n) sC L e) F d)) = 0) :
    ∀ j, g.appTop (equationFunctions (n := n) sC L e d w' F j) = 0 := by
  set x := Stacks.SectionProduct.globalSection (universalCurve (n := n) (N := N) sC) _
    (substitutedSection (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
      ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
      (universalSection (n := n) sC L e) F d)
  refine (pullback_eq_zero_iff_coefficientFunctions (n := n) (N := N) sC w' g
    (substitutedUniversalSection (n := n) sC L e d F)).1 ?_
  have h3 : AlgebraicGeometry.pullbackGlobalSections
      (familyPullbackMap (n := n) (N := N) (sC := sC) g) _
      (substitutedUniversalSection (n := n) sC L e d F) =
      ((Scheme.Modules.pullback (familyPullbackMap (n := n) (N := N) (sC := sC) g)).map
        (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d).hom).app ⊤
        (AlgebraicGeometry.pullbackSectionHom (familyPullbackMap (n := n) (N := N) (sC := sC) g)
          _ ⊤ ⊤ (top_le_preimage_top _) x) := by
    rw [Stacks.AmpleFormalSystemLifting.pullbackGlobalSections_eq_pullbackGlobalSection,
      ← Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top]
    exact Stacks.PullbackUnitSection.pullbackSectionHom_app _
      (pullbackNatTensorPowIso (pullback.fst sC (coefficientSpaceOver n N k)) L d).hom ⊤ ⊤
      (top_le_preimage_top _) x
  have h4 : AlgebraicGeometry.pullbackSectionHom
      (familyPullbackMap (n := n) (N := N) (sC := sC) g) _ ⊤ ⊤ (top_le_preimage_top _) x = 0 := by
    have h5 := congrArg ((pullbackNatTensorPowIso (familyPullbackMap (n := n) (N := N) (sC := sC) g)
      ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L) d).hom.app ⊤)
      h0
    rw [map_zero] at h5
    rw [← h5]
    unfold pullSection
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
    rfl
  rw [h3, h4, map_zero, map_zero]

end FamilyEquations

section AffineLift

open Stacks.ClosedSubschemeProjQuotient Stacks.ClosedSubschemeProjectiveSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange

variable {k : Type u} [Field k] {C : Scheme.{u}} (sC : C ⟶ Spec (.of k))
  (L : C.Modules) [IsInvertibleModule C L] {n N : ℕ} (e : Fin N → Γ(L, ⊤))
  {ιE : Type} (F : ιE → MvPolynomial (Fin (n + 1)) k) (d : ιE → ℕ) {N' : ιE → ℕ}
  (w' : ∀ α, letI := baseModule sC (Stacks.TensorPowers.natTensorPow L (d α)) ⊤;
    Module.Basis (Fin (N' α)) Γ(Spec (.of k), ⊤)
      Γ(Stacks.TensorPowers.natTensorPow L (d α), ⊤))
  {Z : Scheme.{u}} (i : Z ⟶ AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of k))
  [IsClosedImmersion i]

/-- The chart evaluations of the family tuple kill a homogeneous `G` whose equation functions
vanish at `g`. -/
theorem chartEval_familySection_eq_zero [IsProper sC] {T : Scheme.{u}} [IsAffine T]
    (g : T ⟶ coefficientSpace n N k) {d : ℕ} {N'' : ℕ}
    (w'' : letI := baseModule sC (Stacks.TensorPowers.natTensorPow L d) ⊤;
      Module.Basis (Fin N'') Γ(Spec (.of k), ⊤) Γ(Stacks.TensorPowers.natTensorPow L d, ⊤))
    {G : MvPolynomial (Fin (n + 1)) k} (hG : G.IsHomogeneous d)
    (hg : ∀ j, g.appTop (equationFunctions (n := n) sC L e d w'' G j) = 0) (j : Fin (n + 1)) :
    chartEval (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g)
      (pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC) j G = 0 := by
  have := chartEval_pullback_eq_zero
    (familyPullbackMap (n := n) (N := N) (sC := sC) g)
    (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC)
    ((Scheme.Modules.pullback (pullback.fst sC (coefficientSpaceOver n N k))).obj L)
    (universalSection (n := n) sC L e) hG
    (pullSection_substitutedSection_eq_zero sC L e g d w'' G hg) j
  have e1 : familyPullbackMap (n := n) (N := N) (sC := sC) g ≫
      (pullback.fst sC (coefficientSpaceOver n N k) ≫ sC) =
      pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC := by
    rw [← Category.assoc, familyPullbackMap_fst]
  rwa [e1] at this

/-- **A `T`-point of the coefficient space whose substituted equations vanish has its family of
maps factoring through the closed subscheme `Z`** (for `T` affine, the equations `F_α` being
homogeneous generators of the ideal of `Z`). -/
theorem exists_lift_familyMap_of_equations [IsProper sC]
    (hF : ∀ α, (F α).IsHomogeneous (d α))
    (hJ : (closedSubschemeIdeal i).toIdeal = Ideal.span (Set.range F))
    {T : Scheme.{u}} [IsAffine T] (g : T ⟶ coefficientSpace n N k)
    (hg0 : ∀ t : T, g.base t ∈ noCommonZeroOpen (n := n) sC L e)
    (hg : ∀ α j, g.appTop (equationFunctions (n := n) sC L e (d α) (w' α) (F α) j) = 0) :
    ∃ ψ : pullback sC (g ≫ coefficientSpaceOver n N k) ⟶ Z,
      ψ ≫ i = toProjectiveSpaceOver (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g)
        (generatesStalks_familySection g hg0)
        (pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC) := by
  rw [exists_lift_closedImmersion_iff]
  intro j F' hF'
  rw [hJ] at hF'
  refine (Ideal.span_le (I := RingHom.ker (chartEval
    (familySection (n := n) (N := N) (L := L) (e := e) (sC := sC) g)
    (pullback.fst sC (g ≫ coefficientSpaceOver n N k) ≫ sC) j))).2 ?_ hF'
  rintro _ ⟨α, rfl⟩
  exact chartEval_familySection_eq_zero sC L e g (w' α) (hF α) (hg α) j

end AffineLift

end Substitution

end MMP.Fourfold.CurveMapTangent
