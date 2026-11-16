module

public import MMP.AlgebraicGeometry.DeRham.LogFormsCriterion
public import MMP.AlgebraicGeometry.DeRham.LogCartierRelation
public import MMP.AlgebraicGeometry.Cohomology.Cech.CupProduct
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz

/-!
# The wedge product of logarithmic forms

Let `k` be a perfect field of characteristic `p`, `V` a smooth proper `k`-scheme with a simple
normal crossing divisor `S = ⋃ⱼ V(Jⱼ)` with complement `U`, and `K^•` the sheaves of logarithmic
forms `Ω^•_{V/k}(log S)`, presented by injections `e : Γ(K^q, A) → Γ(Ω^q_{V/k}, A ∩ U)`
(`MMP.DeRham.FrobeniusSplittingData`). **Logarithmic forms are closed under the wedge product**:
for logarithmic forms `s`, `t` on `A`, the form `e s ∧ e t` on `A ∩ U` is `e` of a logarithmic
form `s ∧ t`. On a chart of the divisor with local equations `tⱼ`, Deligne's criterion identifies
the image of `e` with the span of the wedges of the forms `db` and `dlog tⱼ`, which is closed under
products; the charts inside `A` cover `A`, and the logarithmic forms they give glue since `K^q`
is a sheaf and `e` is injective.

The wedge product satisfies the Leibniz rule `d (s ∧ t) = ds ∧ t + (-1)^i s ∧ dt` for the
differential of `F_*K^•`, since `e` carries it to the de Rham differential, for which the rule
holds on every affine open. On the extension `𝒦` of `F_*K^•` to a `ℤ`-indexed complex this is a
product on sections in the sense of `MMP.DeRham.SectionProduct`, the input of the cup product on
Čech cochains of `𝒦`.

## Main definitions

* `MMP.DeRham.formsWedge`: the wedge product `Ω^i × Ω^j → Ω^m`, `i + j = m`, on any open.
* `MMP.DeRham.FrobeniusSplittingData.wedge`: the wedge product of logarithmic forms.
* `MMP.DeRham.FrobeniusSplittingData.extendWedge`: the wedge product on the terms of `𝒦` in
  nonnegative degrees.
* `MMP.DeRham.FrobeniusSplittingData.sectionProduct`: **the wedge product on `𝒦`**, as a
  `MMP.DeRham.SectionProduct`.

## Main results

* `MMP.DeRham.deRhamComplex_d_formsWedge`: the Leibniz rule for relative forms on any open.
* `MMP.DeRham.FrobeniusSplittingData.formsWedge_e_mem_range`: logarithmic forms are closed under
  the wedge product.
* `MMP.DeRham.FrobeniusSplittingData.e_wedge`, `wedge_map`, `complex_d_wedge`: the wedge product
  of logarithmic forms restricts to the wedge product on `U`, commutes with restriction, and
  satisfies the Leibniz rule for the differential of `F_*K^•`.
* `MMP.DeRham.FrobeniusSplittingData.sectionProduct_mul`: in nonnegative degrees the product on
  `𝒦` is the wedge product of logarithmic forms.

## Implementation notes

All degrees are free indices tied by equations (`i + j = m`, `i + 1 = i'`), as in
`MMP.DeRham.SectionProduct`, so that no transport along equalities of degrees is needed. The
product is only biadditive: on `F_*K^•` the module structure is twisted by the Frobenius, and
`SectionProduct` asks for no linearity. In negative degrees `𝒦` is zero and the product is `0`.
The wedge of logarithmic forms is defined by choice of the (unique) logarithmic form restricting
to the wedge on `U`; its properties are read through the injectivity of `e`.

## References

* [P. Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971)][Deligne1971], 3.1.
* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry KaehlerDifferential
open Stacks.Frobenius ComplexShape

universe u v

namespace MMP.DeRham

section Forms

variable {k : Type u} [Field k] {V : Scheme.{u}} (f : V ⟶ Spec (.of k))

/-- The wedge product `Ω^i × Ω^j → Ω^m`, `i + j = m`, of relative differential forms of a
`k`-scheme over an open `B`. -/
def formsWedge (i j m : ℕ) (h : i + j = m) (B : V.Opens) :
    Γ(f.relativeDifferentialForms (i : ℤ), B) →+ Γ(f.relativeDifferentialForms (j : ℤ), B) →+
      Γ(f.relativeDifferentialForms (m : ℤ), B) :=
  (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul (i : ℤ) j).app
    (op B)).compr₂
    ((eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
      (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)))
        (by omega : (i : ℤ) + j = m))).val.app (op B)).hom.toAddMonoidHom

/-- `formsWedge` in degree `i + j` is the product of the exterior algebra of `Ω_{V/k}`. -/
theorem formsWedge_apply (i j : ℕ) (B : V.Opens) (ω : Γ(f.relativeDifferentialForms (i : ℤ), B))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), B)) :
    formsWedge f i j (i + j) rfl B ω η =
      (eqToHom (congrArg (Stacks.AffineExteriorPower.pieceModules
          (Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)))
          (Nat.cast_add i j).symm)).val.app (op B)
          (((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul
            (i : ℤ) j).app (op B) ω η) :=
  rfl

/-- On an affine open, `formsWedge` is the product of the exterior algebra of
`Ω_{Γ(V, W)/k}`. -/
theorem coe_formsAlgEquiv_formsWedge (i j m : ℕ) (h : i + j = m) (W : V.affineOpens)
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), W))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), W)) :
    letI := MMP.Mori.sectionAlgebra f W
    ((formsAlgEquiv f m W (formsWedge f i j m h W ω η) : ⋀[Γ(V, W)]^m (Ω[Γ(V, W)⁄k])) :
        ExteriorAlgebra Γ(V, W) (Ω[Γ(V, W)⁄k])) =
      (formsAlgEquiv f i W ω : ExteriorAlgebra Γ(V, W) (Ω[Γ(V, W)⁄k])) *
        (formsAlgEquiv f j W η : ExteriorAlgebra Γ(V, W) (Ω[Γ(V, W)⁄k])) := by
  subst h
  rw [formsWedge_apply]
  exact congrArg Subtype.val (formsAlgEquiv_mul f i j W ω η)

/-- `formsWedge` commutes with restriction. -/
theorem formsWedge_map (i j m : ℕ) (h : i + j = m) {B B' : V.Opens} (hB : B' ≤ B)
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), B))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), B)) :
    (f.relativeDifferentialForms (m : ℤ)).presheaf.map (homOfLE hB).op
        (formsWedge f i j m h B ω η) =
      formsWedge f i j m h B'
        ((f.relativeDifferentialForms (i : ℤ)).presheaf.map (homOfLE hB).op ω)
        ((f.relativeDifferentialForms (j : ℤ)).presheaf.map (homOfLE hB).op η) := by
  subst h
  exact ((Scheme.Modules.exteriorAlgebra (Scheme.Hom.relativeDifferentials f)).mul
    (i : ℤ) j).naturality
    (homOfLE hB).op ω η

/-- A section of a sheaf of modules vanishing on every affine open inside `B` vanishes. -/
theorem eq_zero_of_forall_affineOpens_le {F : V.Modules} {B : V.Opens} (s : Γ(F, B))
    (hs : ∀ (A : V.affineOpens) (hA : (A : V.Opens) ≤ B), F.presheaf.map (homOfLE hA).op s = 0) :
    s = 0 :=
  Stacks.Algebraization.eq_zero_of_affine_cover s (fun _ : Unit ↦ (⊤ : V.Opens)) (by simp)
    fun A _ hA _ ↦ hs A hA

/-- The Leibniz rule for the wedge product of relative forms over an affine open. -/
theorem deRhamComplex_d_formsWedge_affine (i j : ℕ) (A : V.affineOpens)
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), A))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), A)) :
    @Eq Γ(f.relativeDifferentialForms ((i + j + 1 : ℕ) : ℤ), A)
      (((f.deRhamComplex).d (i + j) (i + j + 1)).val.app (op (A : V.Opens))
        (formsWedge f i j (i + j) rfl A ω η))
      (formsWedge f (i + 1) j (i + j + 1) (by omega) A
          (((f.deRhamComplex).d i (i + 1)).val.app (op (A : V.Opens)) ω) η +
        ((i : ℤ).negOnePow : ℤ) • formsWedge f i (j + 1) (i + j + 1) (by omega) A ω
          (((f.deRhamComplex).d j (j + 1)).val.app (op (A : V.Opens)) η)) := by
  let := MMP.Mori.sectionAlgebra f A
  refine (formsAlgEquiv f (i + j + 1) A).injective (Subtype.ext ?_)
  have hx : formsAlgEquiv f (i + j) A (formsWedge f i j (i + j) rfl A ω η) =
      exteriorPower.wedgeMul i j (formsAlgEquiv f i A ω) (formsAlgEquiv f j A η) := by
    rw [formsWedge_apply]
    exact formsAlgEquiv_mul f i j A ω η
  have h1 := formsAlgEquiv_d f (i + j) A (formsWedge f i j (i + j) rfl A ω η)
  rw [hx] at h1
  refine (congrArg Subtype.val h1).trans ((coe_deRhamDifferential_wedgeMul i j _ _).trans ?_)
  refine Eq.trans ?_ (congrArg Subtype.val (map_add (formsAlgEquiv f (i + j + 1) A) _ _)).symm
  refine Eq.trans ?_ (Submodule.coe_add _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (coe_formsAlgEquiv_formsWedge f _ _ _ _ A _ _).symm
    exact congrArg (fun z ↦ z * _) (congrArg Subtype.val (formsAlgEquiv_d f i A ω).symm)
  · refine Eq.trans ?_ (congrArg Subtype.val
      (map_zsmul (formsAlgEquiv f (i + j + 1) A) _ _)).symm
    refine Eq.trans ?_ (AddSubgroupClass.coe_zsmul _ _).symm
    refine Eq.trans ?_ (congrArg (fun z ↦ ((i : ℤ).negOnePow : ℤ) • z)
      (coe_formsAlgEquiv_formsWedge f _ _ _ _ A _ _)).symm
    rw [← formsAlgEquiv_d, Int.coe_negOnePow_natCast, zsmul_eq_mul]
    push_cast
    rfl

/-- **The Leibniz rule for the wedge product of relative forms**:
`d (ω ∧ η) = dω ∧ η + (-1)^i ω ∧ dη` on any open. -/
theorem deRhamComplex_d_formsWedge (i j m i' j' m' : ℕ) (h : i + j = m) (hi : i + 1 = i')
    (hj : j + 1 = j') (hm : m + 1 = m') (B : V.Opens)
    (ω : Γ(f.relativeDifferentialForms (i : ℤ), B))
    (η : Γ(f.relativeDifferentialForms (j : ℤ), B)) :
    @Eq Γ(f.relativeDifferentialForms (m' : ℤ), B)
      (((f.deRhamComplex).d m m').val.app (op B) (formsWedge f i j m h B ω η))
      (formsWedge f i' j m' (by omega) B (((f.deRhamComplex).d i i').val.app (op B) ω) η +
        ((i : ℤ).negOnePow : ℤ) •
          formsWedge f i j' m' (by omega) B ω (((f.deRhamComplex).d j j').val.app (op B) η)) := by
  subst h hi hj hm
  refine sub_eq_zero.1 (eq_zero_of_forall_affineOpens_le _ fun A hA ↦ ?_)
  have hnat : ∀ (a b : ℕ) (x : Γ(f.relativeDifferentialForms (a : ℤ), B)),
      @Eq Γ(f.relativeDifferentialForms (b : ℤ), A)
        ((f.relativeDifferentialForms (b : ℤ)).presheaf.map (homOfLE hA).op
          (((f.deRhamComplex).d a b).val.app (op B) x))
        (((f.deRhamComplex).d a b).val.app (op (A : V.Opens))
          ((f.relativeDifferentialForms (a : ℤ)).presheaf.map (homOfLE hA).op x)) :=
    fun a b x ↦
      (PresheafOfModules.naturality_apply ((f.deRhamComplex).d a b).val (homOfLE hA).op x).symm
  refine (map_sub _ _ _).trans (sub_eq_zero.2 ?_)
  refine ((hnat _ _ _).trans ((congrArg _ (formsWedge_map f _ _ _ _ hA ω η)).trans
    (deRhamComplex_d_formsWedge_affine f i j A _ _))).trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (formsWedge_map f _ _ _ _ hA _ η).symm
    exact congrArg (fun z ↦ formsWedge f (i + 1) j (i + j + 1) _ A z _) (hnat _ _ ω).symm
  · refine Eq.trans ?_ (map_zsmul _ _ _).symm
    refine congrArg (fun z ↦ ((i : ℤ).negOnePow : ℤ) • z) ?_
    refine Eq.trans ?_ (formsWedge_map f _ _ _ _ hA ω _).symm
    exact congrArg (fun z ↦ formsWedge f i (j + 1) (i + j + 1) _ A _ z) (hnat _ _ η).symm

end Forms

/-! ### The wedge product of logarithmic forms -/

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- **Logarithmic forms are closed under the wedge product**: the wedge of the restrictions to
`A ∩ U` of two logarithmic forms on `A` is the restriction to `A ∩ U` of a logarithmic form on
`A`. -/
theorem formsWedge_e_mem_range (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s : Γ(D.K i, A))
    (t : Γ(D.K j, A)) :
    formsWedge f i j m h (A ⊓ D.U) (D.e i A s) (D.e j A t) ∈ Set.range (D.e m A) := by
  subst h
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  set ω := formsWedge f i j (i + j) rfl (A ⊓ D.U) (D.e i A s) (D.e j A t)
  have hloc : ∀ x : A, ∃ (W : V.Opens) (hW : W ≤ A), (x : V) ∈ W ∧ ∃ z : Γ(D.K (i + j), W),
      D.e (i + j) W z = (f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).presheaf.map
        (homOfLE (inf_le_inf_right D.U hW)).op ω := by
    intro x
    obtain ⟨W, τ, hWA, hxW, hJ, -, hWU, hS⟩ :=
      exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU x.2
    refine ⟨W, hWA, hxW, ?_⟩
    have crit := fun (q : ℕ) (θ : Γ(f.relativeDifferentialForms (q : ℤ), (W : V.Opens) ⊓ D.U)) ↦
      (D.he_range q W θ).trans
        (forall_exists_extension_iff_mem_logForms f W D.J τ hJ D.U hWU hS q θ)
    have hres : (f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).presheaf.map
        (homOfLE (inf_le_inf_right D.U hWA)).op ω =
        formsWedge f i j (i + j) rfl ((W : V.Opens) ⊓ D.U)
          (D.e i W ((D.K i).presheaf.map (homOfLE hWA).op s))
          (D.e j W ((D.K j).presheaf.map (homOfLE hWA).op t)) := by
      rw [formsWedge_map, D.he_res, D.he_res]
    rw [hres]
    refine (crit (i + j) _).2 ?_
    let := MMP.Mori.sectionAlgebra f W
    let := MMP.Mori.sectionAlgebra f ((W : V.Opens) ⊓ D.U)
    let : Algebra Γ(V, W) Γ(V, (W : V.Opens) ⊓ D.U) :=
      (V.presheaf.map (homOfLE (inf_le_left : (W : V.Opens) ⊓ D.U ≤ W)).op).hom.toAlgebra
    have hs := (crit i (D.e i W ((D.K i).presheaf.map (homOfLE hWA).op s))).1 ⟨_, rfl⟩
    have ht := (crit j (D.e j W ((D.K j).presheaf.map (homOfLE hWA).op t))).1 ⟨_, rfl⟩
    rw [coe_formsAlgEquiv_formsWedge f i j (i + j) rfl
      ⟨(W : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _ hWU⟩]
    exact mul_mem_logForms hs ht
  choose W hW hxW z hz using hloc
  have hcov : A ≤ iSup W := fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxW _⟩
  have hcomp : ∀ x y : A, (D.K (i + j)).presheaf.map (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op
      (z x) = (D.K (i + j)).presheaf.map (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op (z y) := by
    intro x y
    refine D.he_inj (i + j) _ ?_
    have h0 : W x ⊓ W y ⊓ D.U ≤ A ⊓ D.U := inf_le_inf_right _ (inf_le_left.trans (hW x))
    rw [D.he_res, D.he_res, hz, hz, presheaf_map_map _ _ (homOfLE h0),
      presheaf_map_map _ _ (homOfLE h0)]
  obtain ⟨w, hw, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(D.K (i + j)).val.presheaf, (D.K (i + j)).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _)
    W A (fun x ↦ homOfLE (hW x)) hcov z hcomp
  let w' : Γ(D.K (i + j), A) := w
  have hw' : ∀ x, (D.K (i + j)).presheaf.map (homOfLE (hW x)).op w' = z x := hw
  refine ⟨w', ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).val.presheaf,
      (f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _)
    (fun x ↦ W x ⊓ D.U) (A ⊓ D.U) (fun x ↦ homOfLE (inf_le_inf_right D.U (hW x)))
    (fun y hy ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨y, hy.1⟩, ⟨hxW ⟨y, hy.1⟩, hy.2⟩⟩) _ _ fun x ↦ ?_
  change (f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_inf_right D.U (hW x))).op (D.e (i + j) A w') =
    (f.relativeDifferentialForms ((i + j : ℕ) : ℤ)).presheaf.map
      (homOfLE (inf_le_inf_right D.U (hW x))).op ω
  rw [← D.he_res (i + j) (W x) A (hW x), ← hz x]
  exact congrArg (D.e (i + j) (W x)) (hw' x)

/-- **The wedge product of logarithmic forms** `K^i × K^j → K^m`, `i + j = m`, over an open `A`:
the logarithmic form whose restriction to `A ∩ U` is the wedge of the restrictions. -/
def wedge (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s : Γ(D.K i, A)) (t : Γ(D.K j, A)) :
    Γ(D.K m, A) :=
  (Set.mem_range.1 (D.formsWedge_e_mem_range i j m h A s t)).choose

/-- The restriction of a wedge of logarithmic forms to `A ∩ U` is the wedge of the restrictions. -/
theorem e_wedge (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s : Γ(D.K i, A)) (t : Γ(D.K j, A)) :
    D.e m A (D.wedge i j m h A s t) = formsWedge f i j m h (A ⊓ D.U) (D.e i A s) (D.e j A t) :=
  (Set.mem_range.1 (D.formsWedge_e_mem_range i j m h A s t)).choose_spec

/-- The wedge product of logarithmic forms is additive in the first variable. -/
theorem wedge_add_left (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s s' : Γ(D.K i, A))
    (t : Γ(D.K j, A)) :
    D.wedge i j m h A (s + s') t = D.wedge i j m h A s t + D.wedge i j m h A s' t :=
  D.he_inj m A (by
    rw [map_add, e_wedge, e_wedge, e_wedge, map_add, map_add, AddMonoidHom.add_apply])

/-- The wedge product of logarithmic forms is additive in the second variable. -/
theorem wedge_add_right (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s : Γ(D.K i, A))
    (t t' : Γ(D.K j, A)) :
    D.wedge i j m h A s (t + t') = D.wedge i j m h A s t + D.wedge i j m h A s t' :=
  D.he_inj m A (by rw [map_add, e_wedge, e_wedge, e_wedge, map_add, map_add])

/-- The wedge product of logarithmic forms, as a biadditive map. -/
def wedgeHom (i j m : ℕ) (h : i + j = m) (A : V.Opens) :
    Γ(D.K i, A) →+ Γ(D.K j, A) →+ Γ(D.K m, A) :=
  AddMonoidHom.mk' (fun s ↦ AddMonoidHom.mk' (D.wedge i j m h A s) (D.wedge_add_right i j m h A s))
    fun s s' ↦ AddMonoidHom.ext fun t ↦ D.wedge_add_left i j m h A s s' t

/-- Evaluating `wedgeHom` at `s` and `t` gives the wedge product of `s` and `t`. -/
@[simp]
theorem wedgeHom_apply (i j m : ℕ) (h : i + j = m) (A : V.Opens) (s : Γ(D.K i, A))
    (t : Γ(D.K j, A)) : D.wedgeHom i j m h A s t = D.wedge i j m h A s t :=
  rfl

/-- **The wedge product commutes with restriction.** -/
theorem wedge_map (i j m : ℕ) (h : i + j = m) {A B : V.Opens} (hB : B ≤ A) (s : Γ(D.K i, A))
    (t : Γ(D.K j, A)) :
    (D.K m).presheaf.map (homOfLE hB).op (D.wedge i j m h A s t) =
      D.wedge i j m h B ((D.K i).presheaf.map (homOfLE hB).op s)
        ((D.K j).presheaf.map (homOfLE hB).op t) :=
  D.he_inj m B (by rw [D.he_res, e_wedge, e_wedge, formsWedge_map, D.he_res, D.he_res])

/-- `e` carries the differential of `F_*K^•` to the de Rham differential, in any degrees
`i + 1 = j`. -/
theorem e_complex_d (i j : ℕ) (hij : i + 1 = j) (A : V.Opens)
    (s : Γ(D.K i, absoluteFrobenius V p D.hV ⁻¹ᵁ A)) :
    D.e j (absoluteFrobenius V p D.hV ⁻¹ᵁ A) ((D.complex.d i j).app A s) =
      ((f.deRhamComplex).d i j).val.app (op (absoluteFrobenius V p D.hV ⁻¹ᵁ A ⊓ D.U))
        (D.e i _ s) := by
  subst hij
  have hd : D.complex.d i (i + 1) = D.d i := CochainComplex.of_d
    (fun q ↦ (Scheme.Modules.pushforward (absoluteFrobenius V p D.hV)).obj (D.K q)) D.d i
  rw [hd]
  exact D.he_d i A s

/-- **The Leibniz rule for the wedge product on `F_*K^•`**:
`d (s ∧ t) = ds ∧ t + (-1)^i s ∧ dt`. -/
theorem complex_d_wedge (i j m i' j' m' : ℕ) (h : i + j = m) (hi : i + 1 = i') (hj : j + 1 = j')
    (hm : m + 1 = m') (A : V.Opens) (s : Γ(D.K i, absoluteFrobenius V p D.hV ⁻¹ᵁ A))
    (t : Γ(D.K j, absoluteFrobenius V p D.hV ⁻¹ᵁ A)) :
    @Eq Γ(D.K m', absoluteFrobenius V p D.hV ⁻¹ᵁ A)
      ((D.complex.d m m').app A (D.wedge i j m h (absoluteFrobenius V p D.hV ⁻¹ᵁ A) s t))
      (D.wedge i' j m' (by omega) (absoluteFrobenius V p D.hV ⁻¹ᵁ A)
          ((D.complex.d i i').app A s) t +
        ((i : ℤ).negOnePow : ℤ) • D.wedge i j' m' (by omega) (absoluteFrobenius V p D.hV ⁻¹ᵁ A) s
          ((D.complex.d j j').app A t)) := by
  refine D.he_inj m' (absoluteFrobenius V p D.hV ⁻¹ᵁ A) ?_
  refine (D.e_complex_d m m' hm A _).trans ?_
  refine (congrArg _ (D.e_wedge i j m h _ s t)).trans ?_
  refine (deRhamComplex_d_formsWedge f i j m i' j' m' h hi hj hm _ _ _).trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Eq.trans ?_ (D.e_wedge _ _ _ _ _ _ _).symm
    exact congrArg (fun z ↦ formsWedge f i' j m' _ _ z _) (D.e_complex_d i i' hi A s).symm
  · refine Eq.trans ?_ (map_zsmul _ _ _).symm
    refine congrArg (fun z ↦ ((i : ℤ).negOnePow : ℤ) • z) ?_
    refine Eq.trans ?_ (D.e_wedge _ _ _ _ _ _ _).symm
    exact congrArg (fun z ↦ formsWedge f i j' m' _ _ _ z) (D.e_complex_d j j' hj A t).symm

/-! ### The product on the extension of `F_*K^•` to `ℤ` -/

/-- **The wedge product on the extension of `F_*K^•` to `ℤ`**, in the degrees `a = i`, `b = j`,
`c = m` with `i + j = m`: the wedge product of logarithmic forms on `F⁻¹ A`, read through the
identifications of the terms of the extension in nonnegative degrees. -/
def extendWedge (i j m : ℕ) (h : i + j = m) {a b c : ℤ} (ha : embeddingUpNat.f i = a)
    (hb : embeddingUpNat.f j = b) (hc : embeddingUpNat.f m = c) (A : V.Opens) :
    Γ((D.complex.extend embeddingUpNat).X a, A) →+
      Γ((D.complex.extend embeddingUpNat).X b, A) →+
        Γ((D.complex.extend embeddingUpNat).X c, A) :=
  (((D.wedgeHom i j m h (absoluteFrobenius V p D.hV ⁻¹ᵁ A)).compr₂
      ((D.complex.extendXIso embeddingUpNat hc).inv.app A).hom).comp
    ((D.complex.extendXIso embeddingUpNat ha).hom.app A).hom).compl₂
    ((D.complex.extendXIso embeddingUpNat hb).hom.app A).hom

/-- `extendWedge` is the wedge of logarithmic forms on `F⁻¹ A`, transported along the
identifications `extendXIso` of the terms of the extension. -/
theorem extendWedge_apply (i j m : ℕ) (h : i + j = m) {a b c : ℤ} (ha : embeddingUpNat.f i = a)
    (hb : embeddingUpNat.f j = b) (hc : embeddingUpNat.f m = c) (A : V.Opens)
    (x : Γ((D.complex.extend embeddingUpNat).X a, A))
    (y : Γ((D.complex.extend embeddingUpNat).X b, A)) :
    D.extendWedge i j m h ha hb hc A x y =
      (D.complex.extendXIso embeddingUpNat hc).inv.app A
        (D.wedge i j m h (absoluteFrobenius V p D.hV ⁻¹ᵁ A)
          ((D.complex.extendXIso embeddingUpNat ha).hom.app A x)
          ((D.complex.extendXIso embeddingUpNat hb).hom.app A y)) :=
  rfl

/-- The wedge product on the extension commutes with restriction. -/
theorem extendWedge_map (i j m : ℕ) (h : i + j = m) {a b c : ℤ} (ha : embeddingUpNat.f i = a)
    (hb : embeddingUpNat.f j = b) (hc : embeddingUpNat.f m = c) {A B : V.Opens} (hB : B ≤ A)
    (x : Γ((D.complex.extend embeddingUpNat).X a, A))
    (y : Γ((D.complex.extend embeddingUpNat).X b, A)) :
    ((D.complex.extend embeddingUpNat).X c).presheaf.map (homOfLE hB).op
        (D.extendWedge i j m h ha hb hc A x y) =
      D.extendWedge i j m h ha hb hc B
        (((D.complex.extend embeddingUpNat).X a).presheaf.map (homOfLE hB).op x)
        (((D.complex.extend embeddingUpNat).X b).presheaf.map (homOfLE hB).op y) := by
  refine (app_presheaf_map _ (homOfLE hB) _).symm.trans (congrArg _ ?_)
  refine (D.wedge_map i j m h (A := absoluteFrobenius V p D.hV ⁻¹ᵁ A)
    (B := absoluteFrobenius V p D.hV ⁻¹ᵁ B) hB _ _).trans ?_
  refine Eq.trans ?_ (D.wedgeHom_apply i j m h _ _ _).symm
  exact congrArg₂ (D.wedge i j m h (absoluteFrobenius V p D.hV ⁻¹ᵁ B))
    (app_presheaf_map (D.complex.extendXIso embeddingUpNat ha).hom (homOfLE hB) x).symm
    (app_presheaf_map (D.complex.extendXIso embeddingUpNat hb).hom (homOfLE hB) y).symm

/-- The identification of a term of the extension, on sections: `hom ∘ inv = id`. -/
@[simp]
theorem extendXIso_hom_app_inv_app {a : ℤ} {i : ℕ} (ha : embeddingUpNat.f i = a) (A : V.Opens)
    (z : Γ(D.complex.X i, A)) :
    (D.complex.extendXIso embeddingUpNat ha).hom.app A
      ((D.complex.extendXIso embeddingUpNat ha).inv.app A z) = z := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
  rfl

/-- The differential of the extension in nonnegative degrees, on sections. -/
theorem extend_d_app {r r' : ℤ} {q q' : ℕ} (hr : embeddingUpNat.f q = r)
    (hr' : embeddingUpNat.f q' = r') (A : V.Opens)
    (z : Γ((D.complex.extend embeddingUpNat).X r, A)) :
    ((D.complex.extend embeddingUpNat).d r r').app A z =
      (D.complex.extendXIso embeddingUpNat hr').inv.app A
        ((D.complex.d q q').app A ((D.complex.extendXIso embeddingUpNat hr).hom.app A z)) := by
  rw [HomologicalComplex.extend_d_eq _ _ hr hr']
  rfl

/-- The identification of the terms of the extension carries its differential to that of
`F_*K^•`. -/
theorem extendXIso_hom_app_extend_d {r r' : ℤ} {q q' : ℕ} (hr : embeddingUpNat.f q = r)
    (hr' : embeddingUpNat.f q' = r') (A : V.Opens)
    (z : Γ((D.complex.extend embeddingUpNat).X r, A)) :
    (D.complex.extendXIso embeddingUpNat hr').hom.app A
        (((D.complex.extend embeddingUpNat).d r r').app A z) =
      (D.complex.d q q').app A ((D.complex.extendXIso embeddingUpNat hr).hom.app A z) :=
  (congrArg _ (D.extend_d_app hr hr' A z)).trans (D.extendXIso_hom_app_inv_app hr' A _)

/-- **The Leibniz rule for the wedge product on the extension of `F_*K^•` to `ℤ`.** -/
theorem extendWedge_d (i j m i' j' m' : ℕ) (h : i + j = m) (hi : i + 1 = i') (hj : j + 1 = j')
    (hm : m + 1 = m') {a b c a' b' c' : ℤ} (ha : embeddingUpNat.f i = a)
    (hb : embeddingUpNat.f j = b) (hc : embeddingUpNat.f m = c) (ha' : embeddingUpNat.f i' = a')
    (hb' : embeddingUpNat.f j' = b') (hc' : embeddingUpNat.f m' = c') (A : V.Opens)
    (x : Γ((D.complex.extend embeddingUpNat).X a, A))
    (y : Γ((D.complex.extend embeddingUpNat).X b, A)) :
    ((D.complex.extend embeddingUpNat).d c c').app A (D.extendWedge i j m h ha hb hc A x y) =
      D.extendWedge i' j m' (by omega) ha' hb hc' A
          (((D.complex.extend embeddingUpNat).d a a').app A x) y +
        (a.negOnePow : ℤ) • D.extendWedge i j' m' (by omega) ha hb' hc' A x
          (((D.complex.extend embeddingUpNat).d b b').app A y) := by
  let ι' := (D.complex.extendXIso embeddingUpNat hc').inv.app A
  refine (D.extend_d_app hc hc' A _).trans ?_
  refine (congrArg (fun z ↦ ι' ((D.complex.d m m').app A z))
    (D.extendXIso_hom_app_inv_app hc A _)).trans ?_
  refine (congrArg ι' (D.complex_d_wedge i j m i' j' m' h hi hj hm A _ _)).trans ?_
  refine (map_add _ _ _).trans (congrArg₂ (· + ·) ?_ ((map_zsmul _ _ _).trans ?_))
  · exact congrArg (fun z ↦ ι' (D.wedge i' j m' (by omega) _ z _))
      (D.extendXIso_hom_app_extend_d ha ha' A x).symm
  · subst ha
    exact congrArg (fun z ↦ (((i : ℤ).negOnePow : ℤˣ) : ℤ) • ι' (D.wedge i j' m' (by omega) _ _ z))
      (D.extendXIso_hom_app_extend_d hb hb' A y).symm

/-- The sections of the extension of `F_*K^•` in a negative degree vanish. -/
theorem extend_X_eq_zero {a : ℤ} (ha : a < 0) {A : V.Opens}
    (x : Γ((D.complex.extend embeddingUpNat).X a, A)) : x = 0 :=
  section_eq_zero_of_isZero (HomologicalComplex.isZero_extend_X _ _ _ fun i hi ↦ by
    rw [embeddingUpNat_f] at hi
    omega) x

/-- **The wedge product on the complex `𝒦 = F_*K^•` extended to `ℤ`**, as a product on its
sections satisfying the Leibniz rule: in degrees `a, b ≥ 0` it is the wedge product of
logarithmic forms, and it vanishes when a degree is negative (where `𝒦` is zero). -/
def sectionProduct : SectionProduct (D.complex.extend embeddingUpNat) where
  mul a b c h A :=
    if hab : 0 ≤ a ∧ 0 ≤ b then
      D.extendWedge a.toNat b.toNat c.toNat (by omega) (by rw [embeddingUpNat_f]; omega)
        (by rw [embeddingUpNat_f]; omega) (by rw [embeddingUpNat_f]; omega) A
    else 0
  map_mul a b c h A B i x y := by
    by_cases hab : 0 ≤ a ∧ 0 ≤ b
    · rw [dite_eq_left hab, dite_eq_left hab]
      exact D.extendWedge_map _ _ _ _ _ _ _ i x y
    · rw [dite_eq_right hab, dite_eq_right hab]
      exact map_zero _
  d_mul a a' b b' c c' h ha hb hc A x y := by
    by_cases hab : 0 ≤ a ∧ 0 ≤ b
    · rw [dite_eq_left hab, dite_eq_left (by omega), dite_eq_left (by omega)]
      exact D.extendWedge_d _ _ _ _ _ _ _ (by omega) (by omega) (by omega) _ _ _ _ _ _ A x y
    · rcases not_and_or.1 hab with ha0 | hb0
      · obtain rfl := D.extend_X_eq_zero (by omega) x
        simp only [map_zero, AddMonoidHom.zero_apply, add_zero, smul_zero]
      · obtain rfl := D.extend_X_eq_zero (by omega) y
        simp only [map_zero, zero_add, smul_zero]

/-- In nonnegative degrees `i, j` the product `sectionProduct` is the wedge product
`extendWedge` of logarithmic forms. -/
theorem sectionProduct_mul (i j m : ℕ) (h : i + j = m) (A : V.Opens)
    (x : Γ((D.complex.extend embeddingUpNat).X (i : ℤ), A))
    (y : Γ((D.complex.extend embeddingUpNat).X (j : ℤ), A)) :
    D.sectionProduct.mul i j m (by omega) A x y = D.extendWedge i j m h rfl rfl rfl A x y := by
  have hab : 0 ≤ (i : ℤ) ∧ 0 ≤ (j : ℤ) := ⟨Int.natCast_nonneg i, Int.natCast_nonneg j⟩
  simp only [sectionProduct, dite_eq_left hab]
  rfl

end FrobeniusSplittingData

end MMP.DeRham
