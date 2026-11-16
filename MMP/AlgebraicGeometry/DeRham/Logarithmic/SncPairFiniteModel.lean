module

public import MMP.AlgebraicGeometry.DeRham.Logarithmic.SncPairSpreadingOut
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeSpreadingOut.WittLift

/-!
# Finite models of a projective SNC pair and their fibre dimensions

Let `X` be a smooth projective complex variety of dimension `n` and `D` a simple normal crossing
divisor on `X`. Then the pair `(X, D)` has a *finite model*: a smooth domain `R` of finite type
over `ℤ`, a subring of `ℂ` through `ι : R ↪ ℂ`, a projective morphism `g : 𝒳 ⟶ Spec R` smooth of
relative dimension `n`, and a relative simple normal crossing divisor `𝒟` on `𝒳` such that
`X ≅ 𝒳 ×_{Spec R} Spec ℂ` over `Spec ℂ`, with `D` the preimage of `𝒟`. After shrinking `Spec R`,
for every point `s ∈ Spec R`, with fibre `(𝒳_s, 𝒟_s)` over the residue field `κ(s)`, the
dimensions of
* the Hodge groups `H^j(X, Ω^p_X(log D))` and `H^j(X, Ω^p_X(log D)(-D))`, and
* the logarithmic de Rham hypercohomology `ℍ^j(X, Ω^•_X(log D))` and
  `ℍ^j(X, Ω^•_X(log D)(-D))`

over `ℂ` equal the dimensions of the corresponding groups of `(𝒳_s, 𝒟_s)` over `κ(s)`.

## Main results

* `MMP.Mori.Divisor.exists_isRelativeSNC_model_finrank_hypercohomology_eq`: the finite model and
  the equality of fibre dimensions.

## Implementation notes

* "After shrinking the base" is built into the conclusion: a basic open `Spec R_a ⊆ Spec R` is
  again the spectrum of a smooth domain of finite type over `ℤ` inside `ℂ`, so the model is
  asserted directly over a base on which the equality holds at every point.
* A reduced effective divisor is determined by its support, so the pair `(X, D)` is identified
  with the base change of `(𝒳, 𝒟)` by asking that `D` and the preimage of `𝒟` have the same
  support, and the fibre divisor `𝒟_s` is the relative snc divisor whose support is the
  preimage of that of `𝒟`.
* Cohomology is hypercohomology over the base: for `h : Y ⟶ T` and a bounded below complex `K`
  of sheaves of `h⁻¹𝒪_T`-modules on `Y`, `ℍ^j(Y, K)` is the `j`-th cohomology of the right
  derived functor `Functor.rightDerivedFunctorPlus` of global sections
  (`SheafOfModules.evaluation` at `⊤`), read over `Γ(T, ⊤)` by restriction of scalars along the
  unit `Γ(T, 𝒪_T) ⟶ Γ(Y, h⁻¹𝒪_T)` of `TopCat.Sheaf.pullbackPushforwardAdjunction`; here
  `Γ(T, ⊤)` is `ℂ`, resp. `κ(s)`. It is written out in the statement as the local function `H`.
  The complex `Ω^•(log D)` (twisted or not) is `MMP.Mori.Divisor.relativeLogDeRhamComplex`,
  extended by zero to `ℤ`; the Hodge group `H^j(Ω^p(log D))` is the hypercohomology of its
  `p`-th term placed in degree `0`. The twist by the reduced boundary is the ideal sheaf
  `D.suppIdeal`; the Boolean `twist` selects it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace MMP.Mori.Divisor.LogSpreadingProof

attribute [local instance] HasDerivedCategory.standard

open G1 TopologicalSpace

/-! ### Logarithmic bases on weak charts -/

section WeakChartBasis

variable {n : ℕ} {Y : Scheme.{0}} {A : CommRingCat.{0}} (f : Y ⟶ Spec A)
  [SmoothOfRelativeDimension n f] (D : MMP.Mori.Divisor Y)

/-- The boundary coordinates of a weak chart are invertible off the support. -/
public theorem isUnit_app_weakChart (c : WeakChart f n (D.supp : Set Y)) (k : Fin c.r) :
    IsUnit (((LU D).ι.app c.W).hom (c.t (Fin.castLE c.hr k))) := by
  refine isUnit_of_le_basicOpen _ fun y hy => ?_
  rw [← Scheme.preimage_basicOpen]
  by_contra hyt
  have hyW : (LU D).ι y ∈ (c.W : Y.Opens) := hy
  have hz : (LU D).ι y ∈ Y.zeroLocus {∏ i : Fin c.r, c.t (Fin.castLE c.hr i)} ∩
      (c.W : Set Y) := by
    refine ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, hyW⟩
    rintro _ rfl hmem
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), Scheme.basicOpen_mul] at hmem
    exact hyt hmem.1
  rw [← c.zero] at hz
  exact (y.2 : (LU D).ι y ∉ D.supp) hz.1

/-- The logarithmic coordinate data of a weak chart. -/
@[expose] public noncomputable def WeakChart.toLogData (c : WeakChart f n (D.supp : Set Y)) :
    LogData n f D :=
  ⟨c.W, c.t, c.r, c.hr, fun k => ↑(isUnit_app_weakChart f D c k).unit⁻¹⟩

public theorem WeakChart.toLogData_hs (c : WeakChart f n (D.supp : Set Y))
    (k : Fin (c.toLogData f D).r) :
    (c.toLogData f D).s k * ((LU D).ι.app (c.toLogData f D).W).hom
      ((c.toLogData f D).t (Fin.castLE (c.toLogData f D).hr k)) = 1 :=
  (isUnit_app_weakChart f D c k).val_inv_mul

variable [IsRegularRing A]

/-- **The logarithmic forms of a weak chart.** On a weak chart of the support of a relative snc
divisor the wedges of the logarithmic coordinate forms are a basis of the logarithmic forms. -/
public theorem WeakChart.hasLogBasis (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : Y, ξ ∈ (D.supp : Set Y) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set Y)) (p : ℕ) {W' : Y.affineOpens}
    (hW' : (W' : Y.Opens) ≤ (c.toLogData f D).W) :
    HasLogBasis hD (c.toLogData f D) p hW' := by
  have hloc : ∀ y : (W' : Y.Opens), ∃ (V : Y.affineOpens) (hV : (V : Y.Opens) ≤ W'),
      (y : Y) ∈ (V : Y.Opens) ∧ ∀ (ε : Bool) (V'' : Y.affineOpens) (h'' : (V'' : Y.Opens) ≤ V),
        (c.toLogData f D).BasisAt hD ε p (h''.trans (hV.trans hW')) := by
    intro y
    obtain ⟨g, σ, r'', hr'', j, hyg, hσS, hunit, hb, hj, hjD, hDW⟩ :=
      exists_snc_chart_explicit f D hcomp c y (hW' y.2)
    let C : SNCChart n f D (y : Y) :=
      ⟨⟨Y.basicOpen g, c.W.2.basicOpen g⟩, ⟨⊤, isAffineOpen_top _⟩, le_top,
        fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op (c.t (σ i)), hyg, hb, r'', hr'',
        j, hj, hjD, hDW⟩
    obtain ⟨V, hyV, hVle⟩ := exists_affineOpens_le (X := Y)
      (show (y : Y) ∈ (W' : Y.Opens) ⊓ Y.basicOpen g from ⟨y.2, hyg⟩)
    refine ⟨V, hVle.trans inf_le_left, hyV, fun ε V'' h'' => ?_⟩
    have h2 : (V'' : Y.Opens) ≤ ((C.toLogChart hD).toLogData).W := h''.trans (hVle.trans inf_le_right)
    have HB : ((C.toLogChart hD).toLogData).BasisAt hD ε p h2 := by
      have := ((C.toLogChart hD).toLogData.hasLogBasis_iff hD p h2).mp ((C.toLogChart hD).basis p h2)
      cases ε
      · exact this.1
      · exact this.2
    exact (c.toLogData f D).basisAt_of_refinement (C.toLogChart hD).toLogData hD
      (Y.basicOpen_le g) σ (fun i => rfl) hσS hunit (c.toLogData_hs f D) C.hs ε p h2 HB
  choose V hV hyV hB using hloc
  have hcov : (W' : Y.Opens) ≤ ⨆ y, (V y : Y.Opens) := fun x hx =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyV ⟨x, hx⟩⟩
  refine ((c.toLogData f D).hasLogBasis_iff hD p hW').mpr ⟨?_, ?_⟩
  · exact (c.toLogData f D).basisAt_of_cover hD false p hW' V hV hcov fun y V'' h'' =>
      hB y false V'' h''
  · exact (c.toLogData f D).basisAt_of_cover hD true p hW' V hV hcov fun y V'' h'' =>
      hB y true V'' h''

/-- The logarithmic chart of a weak chart. -/
private noncomputable def WeakChart.toLogChart (hD : D.IsRelativeSNC n f)
    (hcomp : ∀ ξ : Y, ξ ∈ (D.supp : Set Y) → Order.coheight ξ = 1 →
      ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ)
    (c : WeakChart f n (D.supp : Set Y)) : LogChart n f D hD where
  toLogData := c.toLogData f D
  basis p _ hW' := c.hasLogBasis f D hD hcomp p hW'

end WeakChartBasis

/-! ### Pullback of logarithmic forms -/

section FormsPullback

variable {X Y S T : Scheme.{0}} {g : X ⟶ S} {f : Y ⟶ T} {q : Y ⟶ X} {φ : T ⟶ S}
  (hcomm : q ≫ g = f ≫ φ) (DX : MMP.Mori.Divisor X) (DY : MMP.Mori.Divisor Y)
  (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (DX.supp : Set X))

include hsupp in
/-- The complement of `D_Y` lies over the complement of `D_X`. -/
public theorem LU_le_preimage : LU DY ≤ q ⁻¹ᵁ LU DX := by
  intro y hy hqy
  refine hy ?_
  show y ∈ (DY.supp : Set Y)
  rw [hsupp]
  exact hqy

/-- The restriction `X ∖ D_Y ⟶ X ∖ D_X` of `q`. -/
public noncomputable abbrev qU : (LU DY).toScheme ⟶ (LU DX).toScheme :=
  q.resLE (LU DX) (LU DY) (LU_le_preimage DX DY hsupp)

include hcomm in
/-- The restriction `qU` lies over `φ`. -/
public theorem qU_comm : qU DX DY hsupp ≫ ((LU DX).ι ≫ g) = ((LU DY).ι ≫ f) ≫ φ := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hcomm, Category.assoc]

/-- The preimage under `qU` of `U_X ∩ W` is `U_Y ∩ q⁻¹W`. -/
public theorem qU_preimage (W : X.Opens) :
    qU DX DY hsupp ⁻¹ᵁ ((LU DX).ι ⁻¹ᵁ W) = (LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]

/-- The pullback of relative differential forms along `qU`. -/
public noncomputable abbrev ψ :=
  Scheme.Hom.deRhamFormsPushforwardHom (qU DX DY hsupp) ((LU DX).ι ≫ g) ((LU DY).ι ≫ f) φ
    (qU_comm hcomm DX DY hsupp)

/-- The pullback of forms on the total algebra of forms, read on `U_Y ∩ q⁻¹W`. -/
private noncomputable def ΨW (W : X.Opens) :
    (TB ((LU DX).ι ≫ g)).Total (op ((LU DX).ι ⁻¹ᵁ W)) →+*
      (TB ((LU DY).ι ≫ f)).Total (op ((LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W))) :=
  ((TB ((LU DY).ι ≫ f)).totalRestrictRingHom
      (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op).comp
    (Stacks.GradedAlgebra.totalRingHom
      (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom
        (ψ hcomm DX DY hsupp)) (op ((LU DX).ι ⁻¹ᵁ W)))

/-- The pullback of functions on `U_X ∩ W`, read on `U_Y ∩ q⁻¹W`. -/
private noncomputable def ΨU (W : X.Opens) :
    Γ((LU DX).toScheme, (LU DX).ι ⁻¹ᵁ W) →+* Γ((LU DY).toScheme, (LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W)) :=
  ((LU DY).toScheme.presheaf.map (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op).hom.comp
    ((qU DX DY hsupp).app ((LU DX).ι ⁻¹ᵁ W)).hom

private theorem ΨW_sm (W : X.Opens) (r : Γ((LU DX).toScheme, (LU DX).ι ⁻¹ᵁ W)) :
    ΨW hcomm DX DY hsupp W (smU (f := g) (D := DX) _ r) =
      smU (f := f) (D := DY) _ (ΨU DX DY hsupp W r) := by
  have h := congrArg (fun φ => (φ.app (op ((LU DX).ι ⁻¹ᵁ W))).hom r)
    (Stacks.GradedAlgebra.structureHom_totalPresheafMap
      (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom (ψ hcomm DX DY hsupp)))
  simp only [NatTrans.comp_app, RingCat.hom_comp, RingHom.comp_apply] at h
  exact (congrArg (fun z => (TB ((LU DY).ι ≫ f)).totalRestrictRingHom
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op z) h).trans
    ((TB ((LU DY).ι ≫ f)).structureMap_naturality _ _)

private theorem ΨW_incl (W : X.Opens) (k : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ΨW hcomm DX DY hsupp W ((TB ((LU DX).ι ≫ g)).incl k x) =
      (TB ((LU DY).ι ≫ f)).totalRestrict (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op
        ((TB ((LU DY).ι ≫ f)).incl k
          (((ψ hcomm DX DY hsupp).app k).val.app (op ((LU DX).ι ⁻¹ᵁ W)) x)) := by
  have h1 := Stacks.GradedAlgebra.totalRingHom_incl
    (SheafOfModules.GradedAlgebra.UnitalHom.toPresheafGradedAlgebraHom (ψ hcomm DX DY hsupp))
    (op ((LU DX).ι ⁻¹ᵁ W)) k x
  exact congrArg (fun z => (TB ((LU DY).ι ≫ f)).totalRestrictRingHom
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op z) h1

private theorem ΨW_incl_dOne (W : X.Opens) (a : Γ((LU DX).toScheme, (LU DX).ι ⁻¹ᵁ W)) :
    ΨW hcomm DX DY hsupp W ((TB ((LU DX).ι ≫ g)).incl 1 (dOne g DX _ a)) =
      (TB ((LU DY).ι ≫ f)).incl 1 (dOne f DY _ (ΨU DX DY hsupp W a)) := by
  refine (ΨW_incl hcomm DX DY hsupp W 1 _).trans ?_
  have hψ := Scheme.Hom.deRhamFormsPushforwardHom_exactOne (qU DX DY hsupp) ((LU DX).ι ≫ g)
    ((LU DY).ι ≫ f) φ (qU_comm hcomm DX DY hsupp) (op ((LU DX).ι ⁻¹ᵁ W)) a
  refine (congrArg (fun z => (TB ((LU DY).ι ≫ f)).totalRestrict
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op ((TB ((LU DY).ι ≫ f)).incl 1 z))
      hψ).trans ?_
  exact totalRestrict_incl_dOne f DY _ _

private theorem ΨU_app (W : X.Opens) (b : Γ(X, W)) :
    ΨU DX DY hsupp W (((LU DX).ι.app W).hom b) = ((LU DY).ι.app (q ⁻¹ᵁ W)).hom (q.app W b) := by
  have h := Scheme.Hom.congr_app (Scheme.Hom.resLE_comp_ι q (LU_le_preimage DX DY hsupp)) W
  have h' := congrArg (fun φ => φ.hom b) h
  simp only [Scheme.Hom.comp_app] at h'
  have h'' : ((qU DX DY hsupp).app ((LU DX).ι ⁻¹ᵁ W)).hom (((LU DX).ι.app W).hom b) =
      ((LU DY).toScheme.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]; rfl)).op).hom
        (((LU DY).ι.app (q ⁻¹ᵁ W)).hom ((q.app W).hom b)) := h'
  show ((LU DY).toScheme.presheaf.map _).hom
    (((qU DX DY hsupp).app ((LU DX).ι ⁻¹ᵁ W)).hom (((LU DX).ι.app W).hom b)) = _
  rw [h'', ← CommRingCat.comp_apply, ← Functor.map_comp]
  refine (congrArg (fun φ => ConcreteCategory.hom ((LU DY).toScheme.presheaf.map φ)
    (((LU DY).ι.app (q ⁻¹ᵁ W)).hom ((q.app W).hom b))) (Subsingleton.elim _ (𝟙 _))).trans ?_
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The pullback then restriction to `V' = q⁻¹V` of the structure map of a function. -/
private theorem tRΨW_sm_app {V : X.Opens} {V' : Y.Opens} (hVV : V' ≤ q ⁻¹ᵁ V) (b : Γ(X, V)) :
    (TB ((LU DY).ι ≫ f)).totalRestrict ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
        (ΨW hcomm DX DY hsupp V (smU (f := g) (D := DX) _ (((LU DX).ι.app V).hom b))) =
      smU (f := f) (D := DY) _ (((LU DY).ι.app V').hom ((q.appLE V V' hVV).hom b)) := by
  rw [ΨW_sm, ΨU_app]
  refine (totalRestrict_structureMap f DY _ _).trans (congrArg _ ?_)
  refine (app_restrict hVV _).trans (congrArg _ ?_)
  rw [Scheme.Hom.appLE]
  rfl

private theorem tRΨW_incl_dOne_app {V : X.Opens} {V' : Y.Opens} (hVV : V' ≤ q ⁻¹ᵁ V)
    (b : Γ(X, V)) :
    (TB ((LU DY).ι ≫ f)).totalRestrict ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
        (ΨW hcomm DX DY hsupp V ((TB ((LU DX).ι ≫ g)).incl 1
          (dOne g DX _ (((LU DX).ι.app V).hom b)))) =
      (TB ((LU DY).ι ≫ f)).incl 1 (dOne f DY _ (((LU DY).ι.app V').hom ((q.appLE V V' hVV).hom b))) := by
  rw [ΨW_incl_dOne, ΨU_app]
  refine (totalRestrict_incl_dOne f DY _ _).trans ?_
  refine congrArg (fun z => (TB ((LU DY).ι ≫ f)).incl 1 (dOne f DY _ z)) ?_
  refine (app_restrict hVV _).trans (congrArg _ ?_)
  rw [Scheme.Hom.appLE]
  rfl

/-- Restricted to `V' ≤ q⁻¹V`, `ΨU` sends the restriction to `U_X` of `b : Γ(X, V)` to the
restriction to `U_Y` of `q.appLE V V' hVV b`. -/
private theorem tRΨU_app {V : X.Opens} {V' : Y.Opens} (hVV : V' ≤ q ⁻¹ᵁ V) (b : Γ(X, V)) :
    (LU DY).toScheme.presheaf.map ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
        (ΨU DX DY hsupp V (((LU DX).ι.app V).hom b)) =
      ((LU DY).ι.app V').hom ((q.appLE V V' hVV).hom b) := by
  rw [ΨU_app]
  refine (app_restrict hVV _).trans (congrArg _ ?_)
  rw [Scheme.Hom.appLE]
  rfl

variable {n : ℕ} [SmoothOfRelativeDimension n g] [SmoothOfRelativeDimension n f]

/-- The pullback of the logarithmic coordinate forms of `c` are those of the pulled-back
coordinates. -/
private theorem tRΨW_θr (c : LogData n g DX) (c' : LogData n f DY)
    (hWc : (c'.W : Y.Opens) ≤ q ⁻¹ᵁ c.W)
    (ht : ∀ i, c'.t i = (q.appLE c.W c'.W hWc).hom (c.t i)) (hr : c'.r = c.r)
    (hs : ∀ k, c.s k * ((LU DX).ι.app c.W).hom (c.t (Fin.castLE c.hr k)) = 1)
    (hs' : ∀ k, c'.s k * ((LU DY).ι.app c'.W).hom (c'.t (Fin.castLE c'.hr k)) = 1)
    {V : X.Opens} (hV : V ≤ c.W) {V' : Y.Opens} (hV' : V' ≤ c'.W) (hVV : V' ≤ q ⁻¹ᵁ V)
    (i : Fin n) :
    (TB ((LU DY).ι ≫ f)).totalRestrict ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
        (ΨW hcomm DX DY hsupp V (c.θr hV i)) = c'.θr hV' i := by
  have ht' : (q.appLE V V' hVV).hom (X.presheaf.map (homOfLE hV).op (c.t i)) =
      Y.presheaf.map (homOfLE hV').op (c'.t i) := by
    rw [ht i, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  have hσ : (LU DY).toScheme.presheaf.map ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
      (ΨU DX DY hsupp V (c.σ hV i)) = c'.σ hV' i := by
    by_cases h : (i : ℕ) < c.r
    · have h' : (i : ℕ) < c'.r := hr ▸ h
      have e0 : c'.σ hV' i = (LU DY).toScheme.presheaf.map
          ((Opens.map (LU DY).ι.base).map (homOfLE hV')).op (c'.s ⟨i, h'⟩) := by
        simp only [LogData.σ, dif_pos h']
      have e0' : c.σ hV i = (LU DX).toScheme.presheaf.map
          ((Opens.map (LU DX).ι.base).map (homOfLE hV)).op (c.s ⟨i, h⟩) := by
        simp only [LogData.σ, dif_pos h]
      rw [e0, e0']
      refine eq_of_mul_eq_one (x := ((LU DY).ι.app V').hom
        (Y.presheaf.map (homOfLE hV').op (c'.t i))) ?_ ?_
      · have e1 := hs ⟨i, h⟩
        have hci : Fin.castLE c.hr ⟨i, h⟩ = i := Fin.ext rfl
        rw [hci] at e1
        have e2 := congrArg (fun z => (LU DY).toScheme.presheaf.map
          ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op (ΨU DX DY hsupp V
            ((LU DX).toScheme.presheaf.map ((Opens.map (LU DX).ι.base).map (homOfLE hV)).op z)))
          e1
        simp only [map_mul, map_one] at e2
        rw [app_restrict hV, tRΨU_app, ht'] at e2
        exact e2
      · have e1 := hs' ⟨i, h'⟩
        have hci : Fin.castLE c'.hr ⟨i, h'⟩ = i := Fin.ext rfl
        rw [hci] at e1
        have e2 := congrArg ((LU DY).toScheme.presheaf.map
          ((Opens.map (LU DY).ι.base).map (homOfLE hV')).op) e1
        rw [map_mul, map_one, app_restrict hV'] at e2
        exact e2
    · have h' : ¬ (i : ℕ) < c'.r := hr ▸ h
      simp only [LogData.σ, dif_neg h, dif_neg h', map_one]
  simp only [LogData.θr]
  rw [c.totalRestrict_θ hV i, c'.totalRestrict_θ hV' i, map_mul,
    (TB ((LU DY).ι ≫ f)).totalRestrict_mul]
  congr 1
  · refine (congrArg _ (ΨW_sm hcomm DX DY hsupp V _)).trans ?_
    exact (totalRestrict_structureMap f DY _ _).trans (congrArg _ hσ)
  · rw [tRΨW_incl_dOne_app, ht']

/-- **The pullback of logarithmic forms in coordinates**: the pullback of `∑_K a_K θ_K` is
`∑_K q^*(a_K) θ'_K`. -/
private theorem tRΨW_combo (c : LogData n g DX) (c' : LogData n f DY)
    (hWc : (c'.W : Y.Opens) ≤ q ⁻¹ᵁ c.W)
    (ht : ∀ i, c'.t i = (q.appLE c.W c'.W hWc).hom (c.t i)) (hr : c'.r = c.r)
    (hs : ∀ k, c.s k * ((LU DX).ι.app c.W).hom (c.t (Fin.castLE c.hr k)) = 1)
    (hs' : ∀ k, c'.s k * ((LU DY).ι.app c'.W).hom (c'.t (Fin.castLE c'.hr k)) = 1)
    (p : ℕ) {V : X.affineOpens} (hV : (V : X.Opens) ≤ c.W) {V' : Y.affineOpens}
    (hV' : (V' : Y.Opens) ≤ c'.W) (hVV : (V' : Y.Opens) ≤ q ⁻¹ᵁ V)
    (a : {K : Finset (Fin n) // K.card = p} → Γ(X, V)) :
    (TB ((LU DY).ι ≫ f)).totalRestrict ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op
        (ΨW hcomm DX DY hsupp V (c.combo p hV a)) =
      c'.combo p hV' (fun K => (q.appLE V V' hVV).hom (a K)) := by
  let R := ((TB ((LU DY).ι ≫ f)).totalRestrictRingHom
    ((Opens.map (LU DY).ι.base).map (homOfLE hVV)).op).comp (ΨW hcomm DX DY hsupp V)
  have hR : ∀ z, (TB ((LU DY).ι ≫ f)).totalRestrict ((Opens.map (LU DY).ι.base).map
      (homOfLE hVV)).op (ΨW hcomm DX DY hsupp V z) = R z := fun z => rfl
  rw [hR]
  show R (∑ K, smU (f := g) (D := DX) _ (((LU DX).ι.app V).hom (a K)) *
      ((K.1.sort (· ≤ ·)).map (c.θr hV)).prod) =
    ∑ K, smU (f := f) (D := DY) _ (((LU DY).ι.app V').hom ((q.appLE V V' hVV).hom (a K))) *
      ((K.1.sort (· ≤ ·)).map (c'.θr hV')).prod
  rw [map_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [map_mul, map_list_prod, List.map_map]
  congr 1
  · exact tRΨW_sm_app hcomm DX DY hsupp hVV (a K)
  · congr 1
    exact List.map_congr_left fun i _ =>
      tRΨW_θr hcomm DX DY hsupp c c' hWc ht hr hs hs' hV hV' hVV i

/-- The pullback of forms of degree `k` on `U_X ∩ W`, read on `U_Y ∩ q⁻¹W`. -/
@[expose] public noncomputable def ψW (k : ℤ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.obj
      (op ((LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W))) :=
  ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.map
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op
    (((ψ hcomm DX DY hsupp).app k).val.app (op ((LU DX).ι ⁻¹ᵁ W)) ω)

private theorem ΨW_incl' (W : X.Opens) (k : ℤ)
    (x : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ΨW hcomm DX DY hsupp W ((TB ((LU DX).ι ≫ g)).incl k x) =
      (TB ((LU DY).ι ≫ f)).incl k (ψW hcomm DX DY hsupp k W x) :=
  (ΨW_incl hcomm DX DY hsupp W k x).trans ((TB ((LU DY).ι ≫ f)).totalRestrict_incl _ k _)

private theorem ψW_add (k : ℤ) (W : X.Opens) (x y) :
    ψW hcomm DX DY hsupp k W (x + y) = ψW hcomm DX DY hsupp k W x + ψW hcomm DX DY hsupp k W y :=
  (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.map
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op)
    (map_add (((ψ hcomm DX DY hsupp).app k).val.app (op ((LU DX).ι ⁻¹ᵁ W))).hom x y)).trans
    (map_add _ _ _)

/-- **The pullback of forms commutes with the de Rham differential.** -/
private theorem ψW_d (k : ℕ) (W : X.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ψW hcomm DX DY hsupp ((k + 1 : ℕ) : ℤ) W
        (((Scheme.Hom.deRhamComplex ((LU DX).ι ≫ g)).d k (k + 1)).val.app
          (op ((LU DX).ι ⁻¹ᵁ W)) ω) =
      ((Scheme.Hom.deRhamComplex ((LU DY).ι ≫ f)).d k (k + 1)).val.app
        (op ((LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W))) (ψW hcomm DX DY hsupp k W ω) := by
  have hc := Scheme.Hom.deRhamFormsPushforwardHom_comm (qU DX DY hsupp) ((LU DX).ι ≫ g)
    ((LU DY).ι ≫ f) φ (qU_comm hcomm DX DY hsupp) k (op ((LU DX).ι ⁻¹ᵁ W)) ω
  rw [Scheme.Hom.deRhamComplex_d, Scheme.Hom.deRhamComplex_d]
  unfold ψW
  refine (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece
    ((k + 1 : ℕ) : ℤ)).val.map (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op)
    hc.symm).trans ?_
  exact (PresheafOfModules.naturality_apply
    ((SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras ((LU DY).ι ≫ f))).differential
      k).val (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op
    (((ψ hcomm DX DY hsupp).app k).val.app (op ((LU DX).ι ⁻¹ᵁ W)) ω)).symm

/-- A global function on the base acts on `f⁻¹𝒪_S`-modules over `W` through `f^♯`. -/
private theorem str_res_inverseImageBaseRingHom (r : Γ(S, ⊤)) (W : X.Opens) :
    ((inverseImageStructureMap g).hom.app (op W)).hom
        ((((TopCat.Sheaf.pullback CommRingCat.{0} g.base).obj S.sheaf).obj.map
          (homOfLE le_top : W ⟶ ⊤).op).hom
          (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g r)) =
      (g.appLE ⊤ W le_top).hom r := by
  have hnat := congrArg (fun φ => φ.hom (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g r))
    ((inverseImageStructureMap g).hom.naturality (homOfLE le_top : W ⟶ ⊤).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  refine hnat.trans ?_
  have h2 := congrArg (fun φ => φ r)
    (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingMap_comp_inverseImageBaseRingHom g)
  simp only [RingHom.comp_apply] at h2
  refine (congrArg (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom h2).trans ?_
  rfl

/-- In a presheaf of modules on a thin category, two composites of restrictions with the same
ends agree. -/
private theorem map_map_eq_map_map {C : Type*} [Category C] [Quiver.IsThin C]
    {R : Cᵒᵖ ⥤ RingCat} (M : PresheafOfModules R) {a b b' c : Cᵒᵖ} (i : a ⟶ b) (j : b ⟶ c)
    (k : a ⟶ b') (l : b' ⟶ c) (x : M.obj a) :
    (M.map j).hom ((M.map i).hom x) = (M.map l).hom ((M.map k).hom x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _

/-- The pullback of forms commutes with restriction. -/
private theorem ψW_rs (k : ℤ) {W W' : X.Opens} (h : W' ≤ W)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ψW hcomm DX DY hsupp k W' (rs g DX k h ω) =
      rs f DY k (show q ⁻¹ᵁ W' ≤ q ⁻¹ᵁ W from fun _ hy => h hy) (ψW hcomm DX DY hsupp k W ω) := by
  have hn := PresheafOfModules.naturality_apply ((ψ hcomm DX DY hsupp).app k).val
    ((Opens.map (LU DX).ι.base).map (homOfLE h)).op ω
  refine (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.map
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W').symm)).op).hom hn).trans ?_
  exact map_map_eq_map_map _ _ _ _ _ _

/-- The pullback of forms is semilinear over the pullback of functions. -/
private theorem ψW_smul (k : ℤ) (W : X.Opens) (b : Γ(X, W))
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DX).ι ≫ g)).piece k).val.obj
      (op ((LU DX).ι ⁻¹ᵁ W))) :
    ψW hcomm DX DY hsupp k W
        ((show (Stacks.RingedSpace.structureRingSheaf (LU DX).toScheme.toRingedSpace).obj.obj
          (op ((LU DX).ι ⁻¹ᵁ W)) from ((LU DX).ι.app W).hom b) • ω) =
      (show (Stacks.RingedSpace.structureRingSheaf (LU DY).toScheme.toRingedSpace).obj.obj
          (op ((LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ W))) from ((LU DY).ι.app (q ⁻¹ᵁ W)).hom (q.app W b)) •
        ψW hcomm DX DY hsupp k W ω := by
  refine (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.map
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op).hom
    (Scheme.Hom.deRhamFormsPushforwardHom_smul (qU DX DY hsupp) ((LU DX).ι ≫ g) ((LU DY).ι ≫ f) φ
      (qU_comm hcomm DX DY hsupp) k (op ((LU DX).ι ⁻¹ᵁ W)) (((LU DX).ι.app W).hom b) ω)).trans ?_
  refine (PresheafOfModules.map_smul _ _ _ _).trans ?_
  exact congrArg (· • _) (ΨU_app DX DY hsupp W b)

private theorem prod_castLE_congr {M : Type*} [CommMonoid M] {m r r' : ℕ} (h : r' = r)
    (h1 : r' ≤ m) (h2 : r ≤ m) (F : Fin m → M) :
    ∏ i : Fin r', F (Fin.castLE h1 i) = ∏ i : Fin r, F (Fin.castLE h2 i) := by
  subst h; rfl

variable (q) in
/-- A logarithmic chart of `X` and a logarithmic chart of `Y` whose coordinates are the
pullbacks of the former. -/
public structure ChartPair (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f) where
  c : LogChart n g DX hDX
  c' : LogChart n f DY hDY
  hWc : (c'.W : Y.Opens) ≤ q ⁻¹ᵁ c.W
  ht : ∀ i, c'.t i = (q.appLE c.W c'.W hWc).hom (c.t i)
  hr : c'.r = c.r
  hs : ∀ k, c.s k * ((LU DX).ι.app c.W).hom (c.t (Fin.castLE c.hr k)) = 1
  hs' : ∀ k, c'.s k * ((LU DY).ι.app c'.W).hom (c'.t (Fin.castLE c'.hr k)) = 1

/-- The twisting factor pulls back to the twisting factor. -/
private theorem ChartPair.appLE_hε {hDX : DX.IsRelativeSNC n g} {hDY : DY.IsRelativeSNC n f}
    (pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY) (ε : Bool) {V : X.affineOpens}
    (hV : (V : X.Opens) ≤ pr.c.W) {V' : Y.affineOpens} (hV' : (V' : Y.Opens) ≤ pr.c'.W)
    (hVV : (V' : Y.Opens) ≤ q ⁻¹ᵁ V) :
    (q.appLE V V' hVV).hom (pr.c.hε ε hV) = pr.c'.hε ε hV' := by
  cases ε
  · exact map_one _
  · show (q.appLE V V' hVV).hom (X.presheaf.map (homOfLE hV).op _) =
      Y.presheaf.map (homOfLE hV').op _
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map _ pr.hWc,
      CommRingCat.comp_apply, map_prod]
    congr 1
    refine Eq.trans ?_ (prod_castLE_congr pr.hr pr.c'.hr pr.c.hr pr.c'.t).symm
    exact Finset.prod_congr rfl fun i _ => (pr.ht _).symm

/-- **The pullback of logarithmic forms is logarithmic**, when `Y` is covered by charts pulled
back from charts of `X`. -/
private theorem ψW_mem_relativeLogForms (hDX : DX.IsRelativeSNC n g)
    (hDY : DY.IsRelativeSNC n f)
    (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
      q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (ε : Bool) (k : ℕ) (W : X.Opens) (ω)
    (hω : ω ∈ MMP.Mori.Divisor.relativeLogForms n g DX hDX
      (bif ε then DX.suppIdeal else ⊤) k W) :
    ψW hcomm DX DY hsupp k W ω ∈ MMP.Mori.Divisor.relativeLogForms n f DY hDY
      (bif ε then DY.suppIdeal else ⊤) k (q ⁻¹ᵁ W) := by
  refine relativeLogForms_of_local n f DY hDY _ _ fun y hy => ?_
  obtain ⟨pr, hqy, hy'⟩ := hpairs y
  obtain ⟨V, hqV, hVle⟩ := exists_affineOpens_le (X := X)
    (show q.base y ∈ W ⊓ (pr.c.W : X.Opens) from ⟨hy, hqy⟩)
  obtain ⟨V', hyV', hV'le⟩ := exists_affineOpens_le (X := Y)
    (show y ∈ q ⁻¹ᵁ (V : X.Opens) ⊓ (pr.c'.W : Y.Opens) from ⟨hqV, hy'⟩)
  have hVW : (V : X.Opens) ≤ W := hVle.trans inf_le_left
  have hV : (V : X.Opens) ≤ pr.c.W := hVle.trans inf_le_right
  have hVV : (V' : Y.Opens) ≤ q ⁻¹ᵁ V := hV'le.trans inf_le_left
  have hV' : (V' : Y.Opens) ≤ pr.c'.W := hV'le.trans inf_le_right
  have hle : (V' : Y.Opens) ≤ q ⁻¹ᵁ W := fun z hz => hVW (hVV hz)
  refine ⟨V', hle, hyV', ?_⟩
  obtain ⟨a, ha⟩ := ((pr.c.basisε ε k hV).2 _).1
    (relativeLogForms_restrict n g DX hDX _ _ hVW hω)
  refine ((pr.c'.basisε ε k hV').2 _).2 ⟨fun K => (q.appLE V V' hVV).hom (a K), ?_⟩
  have e1 : rs f DY k hle (ψW hcomm DX DY hsupp k W ω) =
      rs f DY k hVV (ψW hcomm DX DY hsupp k V (rs g DX k hVW ω)) := by
    rw [ψW_rs, rs_rs]
  rw [e1]
  refine ((TB ((LU DY).ι ≫ f)).totalRestrict_incl _ (k : ℤ) _).symm.trans ?_
  rw [← ΨW_incl', ha, tRΨW_combo hcomm DX DY hsupp pr.c.toLogData pr.c'.toLogData pr.hWc pr.ht
    pr.hr pr.hs pr.hs' k hV hV' hVV]
  refine congrArg _ (funext fun K => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, pr.appLE_hε]

private theorem ψW_zero (k : ℤ) (W : X.Opens) : ψW hcomm DX DY hsupp k W 0 = 0 :=
  (congrArg (((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU DY).ι ≫ f)).piece k).val.map
    (homOfLE (le_of_eq (qU_preimage DX DY hsupp W).symm)).op).hom
    (map_zero (((ψ hcomm DX DY hsupp).app k).val.app (op ((LU DX).ι ⁻¹ᵁ W))).hom)).trans
    (map_zero _)

/-- **The pullback of sections of the logarithmic forms.** -/
private noncomputable def Φsec (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f)
    (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
      q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (ε : Bool) (k : ℕ) (W : X.Opens) :
    ((logSubmodule n g DX hDX (bif ε then DX.suppIdeal else ⊤) k).obj (op W)) →+
      ((logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤) k).obj (op (q ⁻¹ᵁ W))) where
  toFun x := ⟨ψW hcomm DX DY hsupp k W x.1,
    ψW_mem_relativeLogForms hcomm DX DY hsupp hDX hDY hpairs ε k W x.1 x.2⟩
  map_zero' := Subtype.ext (ψW_zero hcomm DX DY hsupp k W)
  map_add' x y := Subtype.ext (ψW_add hcomm DX DY hsupp k W x.1 y.1)

private theorem Φsec_val (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f) (hpairs)
    (ε : Bool) (k : ℕ) (W : X.Opens) (x) :
    (Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W x).1 = ψW hcomm DX DY hsupp k W x.1 := rfl

include hcomm in
private theorem app_appLE_of_comm (W : X.Opens) (r : Γ(S, ⊤)) :
    (q.app W).hom ((g.appLE ⊤ W le_top).hom r) =
      (f.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom (φ.appTop.hom r) := by
  have e1 : (q.app W).hom ((g.appLE ⊤ W le_top).hom r) =
      (g.appLE ⊤ W le_top ≫ q.appLE W (q ⁻¹ᵁ W) le_rfl).hom r :=
    congrArg (fun h => h.hom ((g.appLE ⊤ W le_top).hom r)) (Scheme.Hom.app_eq_appLE q)
  have e3 : (f.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom (φ.appTop.hom r) =
      (φ.appLE ⊤ ⊤ le_top ≫ f.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom r := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e2 := congrArg (fun h => h.hom r)
    (Scheme.Hom.appLE_comp_appLE q g ⊤ W (q ⁻¹ᵁ W) (fun _ _ => trivial) le_rfl)
  have e4 := congrArg (fun h => h.hom r)
    (Scheme.Hom.appLE_comp_appLE f φ ⊤ ⊤ (q ⁻¹ᵁ W) (fun _ _ => trivial) (fun _ _ => trivial))
  exact e1.trans (e2.trans ((congrArg (fun h : Y ⟶ S =>
    (h.appLE ⊤ (q ⁻¹ᵁ W) (fun _ _ => trivial)).hom r) hcomm).trans (e4.symm.trans e3.symm)))

/-- The pullback of sections of the logarithmic forms is semilinear over the base. -/
private theorem Φsec_smul (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f) (hpairs)
    (ε : Bool) (k : ℕ) (W : X.Opens) (r : Γ(S, ⊤))
    (x : (logSubmodule n g DX hDX (bif ε then DX.suppIdeal else ⊤) k).toSheafOfModules.val.obj
      (op W)) :
    Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W
        ((((TopCat.Sheaf.pullback CommRingCat.{0} g.base).obj S.sheaf).obj.map
          (homOfLE le_top : W ⟶ ⊤).op).hom
          (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g r) • x) =
      (((TopCat.Sheaf.pullback CommRingCat.{0} f.base).obj T.sheaf).obj.map
          (homOfLE le_top : q ⁻¹ᵁ W ⟶ ⊤).op).hom
          (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f (φ.appTop.hom r)) •
        (show (logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤) k).toSheafOfModules.val.obj
          (op (q ⁻¹ᵁ W)) from Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W x) := by
  apply Subtype.ext
  refine (congrArg (ψW hcomm DX DY hsupp k W) (KX_smul g (LU DX) k _ x.1)).trans ?_
  refine Eq.trans ?_ (KX_smul f (LU DY) k _ (ψW hcomm DX DY hsupp k W x.1)).symm
  rw [str_res_inverseImageBaseRingHom, str_res_inverseImageBaseRingHom, ψW_smul,
    app_appLE_of_comm hcomm]

/-- The pullback of sections of the logarithmic forms commutes with restriction. -/
private theorem Φsec_map (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f) (hpairs)
    (ε : Bool) (k : ℕ) {W W' : X.Opens} (h : W' ≤ W)
    (x : (logSubmodule n g DX hDX (bif ε then DX.suppIdeal else ⊤) k).toSheafOfModules.val.obj
      (op W)) :
    Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W'
        (((logSubmodule n g DX hDX (bif ε then DX.suppIdeal else ⊤) k).toSheafOfModules.val.map
          (homOfLE h).op).hom x) =
      ((logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤) k).toSheafOfModules.val.map
          (homOfLE (show q ⁻¹ᵁ W' ≤ q ⁻¹ᵁ W from fun _ hy => h hy)).op).hom
        (show (logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤) k).toSheafOfModules.val.obj
          (op (q ⁻¹ᵁ W)) from Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W x) := by
  apply Subtype.ext
  have eX : (KX g (LU DX) k).val.map (homOfLE h).op x.1 = rs g DX k h x.1 :=
    PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _
  have eY : (KX f (LU DY) k).val.map (homOfLE (show q ⁻¹ᵁ W' ≤ q ⁻¹ᵁ W from fun _ hy => h hy)).op
      (ψW hcomm DX DY hsupp k W x.1) =
      rs f DY k (show q ⁻¹ᵁ W' ≤ q ⁻¹ᵁ W from fun _ hy => h hy) (ψW hcomm DX DY hsupp k W x.1) :=
    PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _
  refine (congrArg (ψW hcomm DX DY hsupp k W') eX).trans (Eq.trans ?_ eY.symm)
  exact ψW_rs hcomm DX DY hsupp k h x.1

/-- The pullback of sections of the logarithmic forms commutes with the differential. -/
private theorem Φsec_d (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f) (hpairs)
    (ε : Bool) (k : ℕ) (W : X.Opens) (x : ((logCx hDX ε).X k).val.obj (op W)) :
    Φsec hcomm DX DY hsupp hDX hDY hpairs ε (k + 1) W
        ((((logCx hDX ε).d k (k + 1)).val.app (op W)).hom x) =
      (((logCx hDY ε).d k (k + 1)).val.app (op (q ⁻¹ᵁ W))).hom
        (show ((logCx hDY ε).X k).val.obj (op (q ⁻¹ᵁ W)) from
          Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W x) := by
  apply Subtype.ext
  refine (congrArg (ψW hcomm DX DY hsupp ((k + 1 : ℕ) : ℤ) W)
    (subCx_d_val g DX _ _ k (op W) x)).trans ?_
  refine (ψW_d hcomm DX DY hsupp k W x.1).trans ?_
  exact (subCx_d_val f DY (logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤))
    (fun p W ω hω => deRham_mem_relativeLogForms hDY ε p W.unop ω hω) k (op (q ⁻¹ᵁ W))
    (Φsec hcomm DX DY hsupp hDX hDY hpairs ε k W x)).symm

end FormsPullback

/-! ### The total Čech complex as a concrete complex -/

section CechBridge

open Stacks.Cohomology.CechSheaf

variable {Y T : Scheme.{0}} (h : Y ⟶ T)

/-- The global sections of `h⁻¹𝒪_T`, a commutative ring. -/
public noncomputable abbrev secCommRing :
    CommRing (SectionRing (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤) :=
  inferInstanceAs (CommRing ((Stacks.DeRhamDirectImage.inverseImageBase h).presheaf.obj (op ⊤)))

attribute [local instance] secCommRing

/-- Opens of `Y` as objects over `⊤`. -/
public noncomputable abbrev overTop : Y.Opens ⥤ Over (⊤ : Y.Opens) :=
  (Over.equivalenceOfIsTerminal (Limits.isTerminalTop (α := Y.Opens))).inverse

/-- `Opens.map` preserves finite products: preimages commute with finite intersections. -/
public theorem preservesFiniteProducts_opensMap {X Y : TopCat} (f : X ⟶ Y) :
    PreservesFiniteProducts (Opens.map f) := by
  refine ⟨fun n => ⟨fun {K} => preservesLimit_of_preserves_limit_cone (limit.isLimit K) ?_⟩⟩
  refine { lift := fun s => homOfLE fun x hx => ?_, fac := fun _ _ => rfl, uniq := fun _ _ _ => rfl }
  have h1 : (⨅ j, K.obj j : Opens Y) ≤ limit K :=
    (limit.lift K ⟨⨅ j, K.obj j, { app := fun j => homOfLE (iInf_le _ j) }⟩).le
  refine h1 ?_
  show f x ∈ ((⨅ j, K.obj j : Opens Y) : Set Y)
  rw [Opens.coe_iInf, Set.mem_iInter]
  intro j
  exact (s.π.app j).le hx

variable {C : Type} [Category.{0} C] [HasFiniteProducts C] (Φ : C ⥤ Y.Opens)
  [PreservesFiniteProducts Φ]

/-- The objects of a site `C` over the opens of `Y`, as objects over `⊤`. -/
public noncomputable abbrev siteFun : C ⥤ Over (⊤ : Y.Opens) := Φ ⋙ overTop (Y := Y)

variable {ι : Type} (U : ι → C)

/-- **Change of site for the total Čech complex**, from the opens over `⊤` to a site over the
opens. -/
private noncomputable def totalCechSiteIso (R : Type) [CommRing R] :
    Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
        (fun i => (siteFun Φ).obj (U i)) R ≅
      ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj (siteFun Φ).op).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        Stacks.Cech.LinearCupProduct.totalCechComplexFunctor U R := by
  let α₀ := Stacks.CechSiteChange.cechComplexFunctorSiteIso (A := ModuleCat.{0} R)
    (siteFun Φ) U
  let α : Stacks.Cech.LinearCupProduct.cechComplexFunctorInt
      (fun i => (siteFun Φ).obj (U i)) R ≅
      (Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj (siteFun Φ).op ⋙
        Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R :=
    Functor.isoWhiskerRight α₀ (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{0} R)) ≪≫
      Functor.associator _ _ _
  haveI : ((Functor.whiskeringLeft _ _ (ModuleCat.{0} R)).obj
      (siteFun Φ).op ⋙ Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R).PreservesZeroMorphisms :=
    ⟨fun P Q => by
      change (Stacks.Cech.LinearCupProduct.cechComplexFunctorInt U R).map
        (Functor.whiskerLeft _ (0 : P ⟶ Q)) = 0
      rw [show Functor.whiskerLeft (siteFun Φ).op (0 : P ⟶ Q) = 0 from rfl]
      exact Functor.map_zero _ _ _⟩
  exact Functor.isoWhiskerRight (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α
      (ComplexShape.up ℤ) ≪≫ Iso.refl _) _) _

/-- The cohomology of a complex of modules, read over a base ring, is `ker / range` of the
restricted differentials. -/
private noncomputable def homologyRestrictScalarsEquiv {R S : Type} [CommRing R] [CommRing S]
    (ρ : S →+* R) (C : CochainComplex (ModuleCat.{0} R) ℤ) (i : ℤ) :
    (ModuleCat.restrictScalars ρ).obj (C.homology (i + 1)) ≃ₗ[S]
      homologyAt ((ModuleCat.restrictScalars ρ).map (C.d i (i + 1))).hom
        ((ModuleCat.restrictScalars ρ).map (C.d (i + 1) (i + 1 + 1))).hom := by
  let F := ModuleCat.restrictScalars.{0} ρ
  let Sc := C.sc' i (i + 1) (i + 1 + 1)
  let e : F.obj (C.homology (i + 1)) ≅ (Sc.map F).moduleCatLeftHomologyData.H :=
    F.mapIso (C.homologyIsoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp)) ≪≫
      (Sc.mapHomologyIso F).symm ≪≫ (Sc.map F).moduleCatHomologyIso
  refine e.toLinearEquiv.trans (Submodule.quotEquivOfEq
    (LinearMap.range (Sc.map F).moduleCatToCycles)
    ((LinearMap.range (Sc.map F).f.hom).comap (LinearMap.ker (Sc.map F).g.hom).subtype) ?_)
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩

/-- The complex of presheaves on a site over the opens of `Y` underlying a complex of sheaves
of `h⁻¹𝒪_T`-modules. -/
public noncomputable abbrev opensCx
    (K : CochainComplex (SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)) ℤ) :
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0}
      (SectionRing (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) ℤ :=
  (((Functor.whiskeringLeft _ _ _).obj (siteFun Φ).op).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).obj K)

/-- **The total Čech complex is the concrete one**: the total Čech complex of a complex of
sheaves vanishing in negative degrees, for a cover pulled back from a site `C`, is the
elementwise total complex `cechTot` over `C` of any `ℕ`-indexed complex of presheaves
identified with it. -/
private noncomputable def totalCechComplexIsoCechTot (hU : (⊤ : Y.Opens) = ⨆ i, Φ.obj (U i))
    (K : CochainComplex (SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)) ℤ)
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0}
      (SectionRing (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) ℕ)
    (e : ∀ b : ℕ, (opensCx h Φ K).X (b : ℤ) ≅ P.X b)
    (hz : ∀ a : ℤ, a < 0 → IsZero ((opensCx h Φ K).X a))
    (he : ∀ b : ℕ, (opensCx h Φ K).d b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫ P.d b (b + 1)) :
    AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex h (fun i => Φ.obj (U i)) hU K ≅
      Stacks.CategoryTheory.CechComplex.cechTot U P :=
  (totalCechSiteIso Φ U _).app (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).obj K) ≪≫
    Stacks.CategoryTheory.CechComplex.totalCechIso U (opensCx h Φ K) P e hz he

/-- The presheaves on a site over the opens of `Y` underlying sheaves of `h⁻¹𝒪_T`-modules. -/
public noncomputable abbrev siteSections :
    SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{0}
        (SectionRing (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) :=
  sectionsPresheafFunctor ⊤ ⋙ (Functor.whiskeringLeft _ _ _).obj (siteFun Φ).op

/-- Taking presheaves on a site preserves zero morphisms. -/
public theorem siteSections_preservesZeroMorphisms : (siteSections h Φ).PreservesZeroMorphisms :=
  ⟨fun M N => by
    change Functor.whiskerLeft (siteFun Φ).op ((sectionsPresheafFunctor ⊤).map (0 : M ⟶ N)) = 0
    rw [Functor.map_zero]
    rfl⟩

/-- The `ℕ`-indexed complex of presheaves on a site underlying a complex of sheaves. -/
public noncomputable abbrev siteCx
    (L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)) ℕ) :
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0}
      (SectionRing (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) ℕ :=
  (((Functor.whiskeringLeft _ _ _).obj (siteFun Φ).op).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (((sectionsPresheafFunctor ⊤).mapHomologicalComplex _).obj L)

/-- The comparison data of an `ℕ`-indexed complex extended by zero with its presheaves. -/
public theorem exists_extend_cechData
    (L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)) ℕ) :
    ∃ e : ∀ b : ℕ, (opensCx h Φ (L.extend ComplexShape.embeddingUpNat)).X (b : ℤ) ≅
        (siteCx h Φ L).X b,
      (∀ b : ℕ, (opensCx h Φ (L.extend ComplexShape.embeddingUpNat)).d b (b + 1) ≫
        (e (b + 1)).hom = (e b).hom ≫ (siteCx h Φ L).d b (b + 1)) ∧
      ∀ a : ℤ, a < 0 → IsZero ((opensCx h Φ (L.extend ComplexShape.embeddingUpNat)).X a) := by
  haveI := siteSections_preservesZeroMorphisms h Φ
  refine ⟨fun b => (siteSections h Φ).mapIso
    (L.extendXIso ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b)),
    fun b => ?_, fun a ha => ?_⟩
  · change (siteSections h Φ).map ((L.extend ComplexShape.embeddingUpNat).d b (b + 1)) ≫
      (siteSections h Φ).map (L.extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f (b + 1))).hom =
      (siteSections h Φ).map (L.extendXIso ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f b)).hom ≫ (siteSections h Φ).map (L.d b (b + 1))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingUpNat_f b)
      (show ComplexShape.embeddingUpNat.f (b + 1) = (b : ℤ) + 1 by simp)]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id]
    rw [Category.comp_id]
  · exact (siteSections h Φ).map_isZero (L.isZero_extend_X _ a fun i => by
      rw [ComplexShape.embeddingUpNat_f]; omega)

/-- The comparison data of a sheaf placed in degree `0` with its presheaf. -/
public theorem exists_single_cechData
    (M : SheafOfModules.{0} (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)) :
    ∃ e : ∀ b : ℕ, (opensCx h Φ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).X
        (b : ℤ) ≅ ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
          ((siteSections h Φ).obj M)).X b,
      (∀ b : ℕ, (opensCx h Φ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).d
        b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
            ((siteSections h Φ).obj M)).d b (b + 1)) ∧
      ∀ a : ℤ, a < 0 → IsZero ((opensCx h Φ
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M)).X a) := by
  haveI := siteSections_preservesZeroMorphisms h Φ
  refine ⟨fun b => match b with
    | 0 => (siteSections h Φ).mapIso (HomologicalComplex.singleObjXSelf _ 0 M) ≪≫
        (HomologicalComplex.singleObjXSelf _ 0 _).symm
    | b + 1 => IsZero.iso ((siteSections h Φ).map_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)))
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)),
    fun b => (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)).eq_of_tgt _ _,
    fun a ha => (siteSections h Φ).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))⟩

end CechBridge

section CechTotBaseChange

open Stacks.CategoryTheory.CechComplex TensorProduct

variable {C : Type} [Category.{0} C] [HasFiniteProducts C] {ι : Type} (U : ι → C)
  {R₀ L : Type} [CommRing R₀] [CommRing L] [Algebra R₀ L]
  (P₀ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} R₀) ℕ) (P₁ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} L) ℕ)
  (Φ : ∀ (a : ℕ) (V : Cᵒᵖ), (P₀.X a).obj V →+ (P₁.X a).obj V)
  (hnat : ∀ (a : ℕ) {V V' : Cᵒᵖ} (g : V ⟶ V') (x : (P₀.X a).obj V),
    Φ a V' (((P₀.X a).map g).hom x) = ((P₁.X a).map g).hom (Φ a V x))
  (hd : ∀ (a : ℕ) (V : Cᵒᵖ) (x : (P₀.X a).obj V),
    Φ (a + 1) V (((P₀.d a (a + 1)).app V).hom x) = ((P₁.d a (a + 1)).app V).hom (Φ a V x))

/-- The termwise maps on the total Čech complexes induced by maps of the coefficients. -/
public noncomputable def totΦ (n : ℤ) : TotX U P₀ n →+ TotX U P₁ n where
  toFun x i t := Φ i.1.2 _ (x i t)
  map_zero' := by funext i t; exact map_zero _
  map_add' x y := by funext i t; exact map_add _ _ _

include hnat in
/-- The termwise maps commute with the Čech differential. -/
public theorem Φ_cechD (a p : ℕ) (s : Cochain U (P₀.X a) p) (t : Fin (p + 1 + 1) → ι) :
    Φ a _ (cechD U (P₀.X a) p s t) = cechD U (P₁.X a) p (fun t' => Φ a _ (s t')) t := by
  rw [cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact hnat a _ _

include hnat hd in
/-- The termwise maps commute with the total differential. -/
public theorem totΦ_totD (n : ℤ) (x : TotX U P₀ n) :
    totΦ U P₀ P₁ Φ (n + 1) (totD U P₀ n x) = totD U P₁ n (totΦ U P₀ P₁ Φ n x) := by
  funext ⟨⟨p, a⟩, h⟩ t
  rcases p with _ | q <;> rcases a with _ | b
  · simp [totΦ, totD_apply]
  · simp only [totΦ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, totD_apply, totDCech_zero,
      totDCoef_succ, zero_add, Pi.smul_apply, cochainMap_apply, map_zsmul, Pi.zero_apply]
    rw [hd]
  · simp only [totΦ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, totD_apply, totDCech_succ,
      totDCoef_zero, add_zero, Pi.add_apply, Pi.zero_apply]
    exact Φ_cechD U P₀ P₁ Φ hnat _ _ _ _
  · simp only [totΦ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, totD_apply, totDCech_succ,
      totDCoef_succ, Pi.add_apply, Pi.smul_apply, cochainMap_apply, map_add, map_zsmul]
    rw [Φ_cechD U P₀ P₁ Φ hnat, hd]

include hnat hd in
/-- **Base change for the total Čech complex.** Termwise base change maps of complexes of
presheaves, compatible with the restrictions and the differentials, identify the cohomology of
the total Čech complex of `P₁` with that of the base change of the total Čech complex of `P₀`. -/
public theorem nonempty_homologyAt_baseChange_equiv [Finite ι]
    (hsm : ∀ (a : ℕ) (V : Cᵒᵖ) (r : R₀) (x : (P₀.X a).obj V),
      Φ a V (r • x) = algebraMap R₀ L r • Φ a V x)
    (hbc : ∀ (a p : ℕ) (t : Fin (p + 1) → ι),
      ∃ e : L ⊗[R₀] (P₀.X a).obj (op (inter U t)) ≃ₗ[L] (P₁.X a).obj (op (inter U t)),
        ∀ x, e (1 ⊗ₜ x) = Φ a _ x) (i : ℤ) :
    Nonempty (homologyAt ((totD U P₀ i).baseChange L) ((totD U P₀ (i + 1)).baseChange L) ≃ₗ[L]
      homologyAt (totD U P₁ i) (totD U P₁ (i + 1))) := by
  letI inst : ∀ (a : ℕ) (V : Cᵒᵖ), Module R₀ ((P₁.X a).obj V) := fun a V =>
    Module.compHom _ (algebraMap R₀ L)
  haveI : ∀ (a : ℕ) (V : Cᵒᵖ), IsScalarTower R₀ L ((P₁.X a).obj V) := fun a V =>
    ⟨fun r k x => by
      show (r • k) • x = algebraMap R₀ L r • k • x
      rw [Algebra.smul_def, mul_smul]⟩
  let Φc : ∀ (a : ℕ) (V : Cᵒᵖ), (P₀.X a).obj V →ₗ[R₀] (P₁.X a).obj V := fun a V =>
    { toFun := Φ a V
      map_add' := map_add _
      map_smul' := hsm a V }
  have hΦc : ∀ (a p : ℕ) (t : Fin (p + 1) → ι), IsBaseChange L (Φc a (op (inter U t))) := by
    intro a p t
    obtain ⟨e, he⟩ := hbc a p t
    exact IsBaseChange.of_equiv e he
  let Φn : ∀ n, TotX U P₀ n →ₗ[R₀] TotX U P₁ n := fun n =>
    LinearMap.pi fun j => (LinearMap.pi fun t => Φc j.1.2 _ ∘ₗ LinearMap.proj t) ∘ₗ
      LinearMap.proj j
  have hΦn : ∀ n, IsBaseChange L (Φn n) := by
    intro n
    haveI := finite_totIndex n
    exact IsBaseChange.pi _ fun j => IsBaseChange.pi _ fun t => hΦc _ _ t
  exact ⟨homologyAtEquivOfIsBaseChange (totD U P₀) (totD U P₁) Φn hΦn
    (fun n x => totΦ_totD U P₀ P₁ Φ hnat hd n x) i⟩

end CechTotBaseChange

section RestrictCx

open Stacks.CategoryTheory.CechComplex

variable {C : Type} [Category.{0} C] [HasFiniteProducts C] {ι : Type} (U : ι → C)
  {A B : Type} [CommRing A] [CommRing B] (ρ : B →+* A)

/-- A complex of presheaves of `A`-modules, read as presheaves of `B`-modules along `ρ`. -/
public noncomputable abbrev resCx (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} A) ℕ) :
    CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} B) ℕ :=
  (((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{0} ρ)).mapHomologicalComplex
    _).obj P

/-- The restricted total Čech differentials of `P` are those of `P` read over `B`. -/
public noncomputable def homologyAtResCxEquiv (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} A) ℕ)
    (i : ℤ) :
    homologyAt ((ModuleCat.restrictScalars ρ).map ((cechTot U P).d i (i + 1))).hom
        ((ModuleCat.restrictScalars ρ).map ((cechTot U P).d (i + 1) (i + 1 + 1))).hom ≃ₗ[B]
      homologyAt (totD U (resCx ρ P) i) (totD U (resCx ρ P) (i + 1)) :=
  homologyAtCongr _ _ _ _
    { toFun := id, invFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    { toFun := id, invFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    { toFun := id, invFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    (LinearMap.ext fun x => (cechTot_d_apply U P i x).symm)
    (LinearMap.ext fun x => (cechTot_d_apply U P (i + 1) x).symm)

end RestrictCx

section HypercohomologyCech

/-- Homology of the image of an object of the derived category under an exact functor of module
categories which preserves homology. -/
@[expose] public noncomputable def homologyMapDerivedCategoryIso {R₁ R₂ : Type} [Ring R₁] [Ring R₂]
    (F : ModuleCat.{0} R₁ ⥤ ModuleCat.{0} R₂) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] {_ : HasDerivedCategory (ModuleCat.{0} R₁)}
    {_ : HasDerivedCategory (ModuleCat.{0} R₂)} (X : DerivedCategory (ModuleCat.{0} R₁)) (j : ℤ) :
    (DerivedCategory.homologyFunctor _ j).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor _ j).obj X) :=
  (DerivedCategory.homologyFunctor _ j).mapIso
      (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso X).symm) ≪≫
    (DerivedCategory.homologyFunctor _ j).mapIso (F.mapDerivedCategoryFactors.app _) ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫
    ((DerivedCategory.Q.objPreimage X).sc j).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors _ j).app _).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor _ j).mapIso
      (DerivedCategory.Q.objObjPreimageIso X))

section ModelIndependence

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D] (F : C ⥤ D)

/-- **Model independence of derived homology.** For an injective resolution `K ⟶ L` of a bounded
below complex, the homology of the right derived functor of `F` at `K` is the homology of `F`
applied to `L`, in whatever models the derived categories are taken. -/
@[expose] public noncomputable def homologyRightDerivedFunctorPlusIso
    {_ : F.Additive} {_ : EnoughInjectives C} {_ : HasDerivedCategory C}
    {_ : HasDerivedCategory D}
    (K : CochainComplex.Plus C) (L : CochainComplex.Plus (InjectiveObject C))
    (φ : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L) [QuasiIso φ.hom] (j : ℤ) :
    (DerivedCategory.homologyFunctor D j).obj
        (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) ≅
      ((F.mapHomologicalComplex _).obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj L).obj).homology j := by
  let M := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  have hQ : IsIso (DerivedCategory.Q.map φ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C φ.hom).2 inferInstance
  let e1 : DerivedCategory.Plus.Q.obj K ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj M) :=
    DerivedCategory.Plus.ι.preimageIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map φ.hom) hQ ≪≫ ((DerivedCategory.quotientCompQhIso C).app M.obj).symm)
  let e2 : F.rightDerivedFunctorPlus.obj
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj M)) ≅
      DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C).obj M)) :=
    (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj M))).symm
  let e3 : DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C).obj M))) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj M.obj) :=
    (DerivedCategory.quotientCompQhIso D).app ((F.mapHomologicalComplex _).obj M.obj)
  exact (DerivedCategory.homologyFunctor D j).mapIso
      (DerivedCategory.Plus.ι.mapIso (F.rightDerivedFunctorPlus.mapIso e1 ≪≫ e2) ≪≫ e3) ≪≫
    (DerivedCategory.homologyFunctorFactors D j).app _

end ModelIndependence

/-- The hypercohomology of the statement is `AlgebraicGeometry.DeRhamTypeComplex.hypercohomology`. -/
public theorem nonempty_hcIsoHypercohomology {Y T : Scheme.{0}} (h : Y ⟶ T)
    (K : CochainComplex.Plus (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h))) (j : ℤ) :
    Nonempty (Hc h K j ≅ AlgebraicGeometry.DeRhamTypeComplex.hypercohomology h K j) := by
  obtain ⟨n, hn⟩ := K.2
  obtain ⟨L, _, φ, hφ⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
  haveI : QuasiIso φ.hom := hφ
  refine ⟨?_ ≪≫ (homologyMapDerivedCategoryIso (ModuleCat.restrictScalars.{0}
    (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)) _ j).symm⟩
  exact (ModuleCat.restrictScalars.{0}
    (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)).mapIso
    (homologyRightDerivedFunctorPlusIso _ K L φ j ≪≫
      (homologyRightDerivedFunctorPlusIso _ K L φ j).symm)

attribute [local instance] secCommRing in
/-- **Hypercohomology by the concrete total Čech complex.** For a complex vanishing in
negative degrees with quasi-coherent terms and an affine cover pulled back from a site `C`,
`ℍ^{i+1}` is the cohomology of the elementwise total Čech complex `cechTot` over `C`, read over
`Γ(T, ⊤)`. -/
public theorem nonempty_hcEquivHomologyAt {Y T : Scheme.{0}} (h : Y ⟶ T)
    {C : Type} [Category.{0} C] [HasFiniteProducts C] (Φ : C ⥤ Y.Opens)
    [PreservesFiniteProducts Φ] {ι : Type} (U : ι → C) (hU : (⊤ : Y.Opens) = ⨆ i, Φ.obj (U i))
    [IsAffineHom (pullback.diagonal (terminal.from Y))] (hUaff : ∀ i, IsAffineOpen (Φ.obj (U i)))
    (K : CochainComplex.Plus (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h)))
    (hK : ∀ q, ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty (K.1.X q ≅ (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase h)).obj M))
    (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{0} (Stacks.Cohomology.CechSheaf.SectionRing
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing h) ⊤)) ℕ)
    (e : ∀ b : ℕ, (opensCx h Φ K.1).X (b : ℤ) ≅ P.X b)
    (hz : ∀ a : ℤ, a < 0 → IsZero ((opensCx h Φ K.1).X a))
    (he : ∀ b : ℕ, (opensCx h Φ K.1).d b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫ P.d b (b + 1))
    (i : ℤ) :
    Nonempty (Hc h K (i + 1) ≃ₗ[Γ(T, ⊤)] homologyAt
      ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)).map
        ((Stacks.CategoryTheory.CechComplex.cechTot U P).d i (i + 1))).hom
      ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)).map
        ((Stacks.CategoryTheory.CechComplex.cechTot U P).d (i + 1) (i + 1 + 1))).hom) :=
  ⟨((nonempty_hcIsoHypercohomology h K (i + 1)).some ≪≫
    AlgebraicGeometry.DeRhamTypeComplex.homologyDerivedSectionsIso h _ hU hUaff K hK (i + 1) ≪≫
    (ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)).mapIso
      (HomologicalComplex.homologyMapIso
        (totalCechComplexIsoCechTot h Φ U hU K.1 P e hz he) (i + 1))
      ).toLinearEquiv.trans (homologyRestrictScalarsEquiv _ _ i)⟩

end HypercohomologyCech

section LogBaseChange

open Stacks.CategoryTheory.CechComplex TensorProduct

attribute [local instance] secCommRing

variable {X Y S T : Scheme.{0}} {g : X ⟶ S} {f : Y ⟶ T} {q : Y ⟶ X} {φ : T ⟶ S}
  (hcomm : q ≫ g = f ≫ φ) {DX : MMP.Mori.Divisor X} {DY : MMP.Mori.Divisor Y}
  (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (DX.supp : Set X))
  {n : ℕ} [SmoothOfRelativeDimension n g] [SmoothOfRelativeDimension n f]
  (hDX : DX.IsRelativeSNC n g) (hDY : DY.IsRelativeSNC n f)

/-- The logarithmic de Rham complex of `X`, as presheaves of `Γ(S, ⊤)`-modules on the opens. -/
public noncomputable abbrev logPresheafCx (ε : Bool) :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} Γ(S, ⊤)) ℕ :=
  resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)
    (siteCx g (𝟭 X.Opens) (logCx hDX ε))

/-- The logarithmic de Rham complex of `Y`, as presheaves of `Γ(T, ⊤)`-modules on the opens of
`X`, through `q⁻¹`. -/
public noncomputable abbrev logPresheafCxPullback (ε : Bool) :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} Γ(T, ⊤)) ℕ :=
  haveI := preservesFiniteProducts_opensMap q.base
  resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
    (siteCx f (Opens.map q.base) (logCx hDY ε))

/-- The pullback of the logarithmic forms, on the presheaves of the opens of `X`. -/
public noncomputable def logΦ (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q)
      hDX hDY, q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (ε : Bool) (a : ℕ) (V : (X.Opens)ᵒᵖ) :
    ((logPresheafCx hDX ε).X a).obj V →+ ((logPresheafCxPullback (q := q) hDY ε).X a).obj V :=
  Φsec hcomm DX DY hsupp hDX hDY hpairs ε a V.unop

include hcomm hsupp in
/-- The pullback of the logarithmic forms commutes with restriction. -/
public theorem logΦ_nat (hpairs) (ε : Bool) (a : ℕ) {V V' : (X.Opens)ᵒᵖ} (i : V ⟶ V')
    (x : ((logPresheafCx hDX ε).X a).obj V) :
    logΦ hcomm hsupp hDX hDY hpairs ε a V' ((((logPresheafCx hDX ε).X a).map i).hom x) =
      ((((logPresheafCxPullback (q := q) hDY ε).X a).map i).hom
        (logΦ hcomm hsupp hDX hDY hpairs ε a V x)) :=
  Φsec_map hcomm DX DY hsupp hDX hDY hpairs ε a (leOfHom i.unop) x

include hcomm hsupp in
/-- The pullback of the logarithmic forms commutes with the differential. -/
public theorem logΦ_d (hpairs) (ε : Bool) (a : ℕ) (V : (X.Opens)ᵒᵖ)
    (x : ((logPresheafCx hDX ε).X a).obj V) :
    logΦ hcomm hsupp hDX hDY hpairs ε (a + 1) V ((((logPresheafCx hDX ε).d a (a + 1)).app V).hom x) =
      ((((logPresheafCxPullback (q := q) hDY ε).d a (a + 1)).app V).hom
        (logΦ hcomm hsupp hDX hDY hpairs ε a V x)) :=
  Φsec_d hcomm DX DY hsupp hDX hDY hpairs ε a V.unop x

include hcomm hsupp in
/-- The pullback of the logarithmic forms is semilinear over the base. -/
public theorem logΦ_smul (hpairs) (ε : Bool) (a : ℕ) (V : (X.Opens)ᵒᵖ) (r : Γ(S, ⊤))
    (x : ((logPresheafCx hDX ε).X a).obj V) :
    letI := φ.appTop.hom.toAlgebra
    logΦ hcomm hsupp hDX hDY hpairs ε a V (r • x) =
      algebraMap Γ(S, ⊤) Γ(T, ⊤) r • logΦ hcomm hsupp hDX hDY hpairs ε a V x :=
  Φsec_smul hcomm DX DY hsupp hDX hDY hpairs ε a V.unop r x

include hcomm hsupp in
/-- The underlying form of the pullback of a logarithmic form is the pullback of its form. -/
public theorem logΦ_val (hpairs) (ε : Bool) (a : ℕ) (V : (X.Opens)ᵒᵖ)
    (x : ((logPresheafCx hDX ε).X a).obj V) :
    (logΦ hcomm hsupp hDX hDY hpairs ε a V x).1 = ψW hcomm DX DY hsupp a V.unop x.1 :=
  Φsec_val hcomm DX DY hsupp hDX hDY hpairs ε a V.unop x

private theorem totalRestrict_self' {Z B : Scheme.{0}} (h : Z ⟶ B) (O : Z.Opens) (i : op O ⟶ op O)
    (z : (TB h).Total (op O)) : (TB h).totalRestrict i z = z := by
  rw [Subsingleton.elim i (𝟙 _)]
  exact congrArg (fun F => F.hom z) ((TB h).totalPresheaf.map_id _)

include hcomm hsupp in
/-- **The pullback of logarithmic forms in coefficients**: on a chart affine `V`, the pullback
of the form with coefficients `a` is the form with coefficients `q^* a`. -/
private theorem logΦ_coeff (hpairs) (pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY)
    (ε : Bool) (k : ℕ) (V : X.affineOpens) (hV : (V : X.Opens) ≤ pr.c.W)
    (V' : Y.affineOpens) (hV'e : (V' : Y.Opens) = q ⁻¹ᵁ V) (hV' : (V' : Y.Opens) ≤ pr.c'.W)
    (a : {K : Finset (Fin n) // K.card = k} → Γ(X, V)) :
    (Φsec hcomm DX DY hsupp hDX hDY hpairs ε k V (pr.c.coeff ε k hV a)).1 =
      (show ((logSubmodule n f DY hDY (bif ε then DY.suppIdeal else ⊤) k).obj
        (op (q ⁻¹ᵁ (V : X.Opens)))) from
        hV'e ▸ pr.c'.coeff ε k hV' (fun K => (q.appLE V V' hV'e.le).hom (a K))).1 := by
  obtain ⟨V', hV'aff⟩ := V'
  simp only at hV'e
  subst hV'e
  refine incl_injective (f := f) (D := DY) (k : ℤ) _ ?_
  refine ((ΨW_incl' hcomm DX DY hsupp V k _).symm.trans ?_).trans
    (pr.c'.incl_coeff ε k hV' _).symm
  rw [pr.c.incl_coeff ε k hV a]
  refine (totalRestrict_self' ((LU DY).ι ≫ f) ((LU DY).ι ⁻¹ᵁ (q ⁻¹ᵁ (V : X.Opens)))
    (((Opens.map (LU DY).ι.base).map (homOfLE (le_refl (q ⁻¹ᵁ (V : X.Opens))))).op) _).symm.trans ?_
  rw [tRΨW_combo hcomm DX DY hsupp pr.c.toLogData pr.c'.toLogData pr.hWc pr.ht pr.hr pr.hs pr.hs'
    k hV hV' le_rfl]
  refine congrArg _ (funext fun K => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
    ChartPair.appLE_hε DX DY pr ε hV hV' le_rfl]

/-- A global function on the base acts on the logarithmic forms over `W` through `h^♯`. -/
private theorem logSec_smul_val {Z B : Scheme.{0}} {m : ℕ} (h : Z ⟶ B)
    [SmoothOfRelativeDimension m h] {D : MMP.Mori.Divisor Z} (hD : D.IsRelativeSNC m h)
    (I : Z.IdealSheafData) (k : ℕ) (W : Z.Opens) (r : Γ(B, ⊤))
    (x : (logSubmodule m h D hD I k).toSheafOfModules.val.obj (op W)) :
    ((((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj B.sheaf).obj.map
        (homOfLE le_top : W ⟶ ⊤).op).hom
        (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h r) • x).1 =
      (show (Stacks.RingedSpace.structureRingSheaf (LU D).toScheme.toRingedSpace).obj.obj
          (op ((LU D).ι ⁻¹ᵁ W)) from ((LU D).ι.app W).hom ((h.appLE ⊤ W le_top).hom r)) •
        (show ((Scheme.Hom.relativeDifferentialFormsAlgebra ((LU D).ι ≫ h)).piece (k : ℤ)).val.obj
          (op ((LU D).ι ⁻¹ᵁ W)) from x.1) := by
  refine (KX_smul h (LU D) k _ x.1).trans ?_
  rw [str_res_inverseImageBaseRingHom (g := h)]

/-- **The coefficient isomorphism over the base**: on a chart affine, the sections of the
logarithmic forms are free on the `θ_K`, linearly over the global functions of the base. -/
private noncomputable def coeffSiteEquiv {Z B : Scheme.{0}} {m : ℕ} (h : Z ⟶ B)
    [SmoothOfRelativeDimension m h] {D : MMP.Mori.Divisor Z} {hD : D.IsRelativeSNC m h}
    (c : LogChart m h D hD) (ε : Bool) (k : ℕ) {C : Type} [Category.{0} C] [HasFiniteProducts C]
    (Φ : C ⥤ Z.Opens) [PreservesFiniteProducts Φ] (O : C) (hO : IsAffineOpen (Φ.obj O))
    (hV : Φ.obj O ≤ c.W) :
    letI := (h.appLE ⊤ (Φ.obj O) le_top).hom.toAlgebra
    ({K : Finset (Fin m) // K.card = k} → Γ(Z, Φ.obj O)) ≃ₗ[Γ(B, ⊤)]
      ((resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)
        (siteCx h Φ (logCx hD ε))).X k).obj (op O) :=
  letI := (h.appLE ⊤ (Φ.obj O) le_top).hom.toAlgebra
  LinearEquiv.ofBijective
    ({ toFun := fun a => (show ((resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)
          (siteCx h Φ (logCx hD ε))).X k).obj (op O) from
          c.coeff ε k (W' := ⟨Φ.obj O, hO⟩) hV a)
       map_add' := fun a b => map_add (c.coeff ε k (W' := ⟨Φ.obj O, hO⟩) hV) a b
       map_smul' := fun r a => Subtype.ext <|
        (congrArg Subtype.val (map_smul (c.coeff ε k (W' := ⟨Φ.obj O, hO⟩) hV)
          ((h.appLE ⊤ (Φ.obj O) le_top).hom r) a)).trans
          (logSec_smul_val h hD _ k (Φ.obj O) r
            (show ((logCx hD ε).X k).val.obj (op (Φ.obj O)) from
              c.coeff ε k (W' := ⟨Φ.obj O, hO⟩) hV a)).symm } :
      ({K : Finset (Fin m) // K.card = k} → Γ(Z, Φ.obj O)) →ₗ[Γ(B, ⊤)]
        ((resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom h)
          (siteCx h Φ (logCx hD ε))).X k).obj (op O))
    (c.coeff_bijective ε k (W' := ⟨Φ.obj O, hO⟩) hV)

include hcomm hsupp in
/-- **Base change of the logarithmic forms on a chart affine.** For a cartesian square over
affine bases, the pullback of the logarithmic forms over a chart affine `V` is the base change
of the logarithmic forms over `V`. -/
public theorem exists_logΦ_baseChange (H : IsPullback q f g φ) [IsAffine S] [IsAffine T]
    (hpairs) (pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY) (ε : Bool) (k : ℕ)
    (V : X.Opens) (hVa : IsAffineOpen V) (hV : V ≤ pr.c.W) (hVa' : IsAffineOpen (q ⁻¹ᵁ V))
    (hV' : q ⁻¹ᵁ V ≤ pr.c'.W) :
    letI := φ.appTop.hom.toAlgebra
    ∃ e : Γ(T, ⊤) ⊗[Γ(S, ⊤)] ((logPresheafCx hDX ε).X k).obj (op V) ≃ₗ[Γ(T, ⊤)]
        ((logPresheafCxPullback (q := q) hDY ε).X k).obj (op V),
      ∀ x, e (1 ⊗ₜ x) = logΦ hcomm hsupp hDX hDY hpairs ε k (op V) x := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := φ.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, V) := (g.appLE ⊤ V le_top).hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(Y, q ⁻¹ᵁ V) := (f.appLE ⊤ (q ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, q ⁻¹ᵁ V) := (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, q ⁻¹ᵁ V) :=
    ((f.appLE ⊤ (q ⁻¹ᵁ V) le_top).hom.comp φ.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(X, V) Γ(Y, q ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun r =>
    (app_appLE_of_comm hcomm V r).symm.trans
      (congrArg (fun h => h.hom ((g.appLE ⊤ V le_top).hom r)) (Scheme.Hom.app_eq_appLE q))
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, q ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hU' : q ⁻¹ᵁ V = q ⁻¹ᵁ V ⊓ f ⁻¹ᵁ ⊤ :=
    le_antisymm (le_inf le_rfl fun _ _ => trivial) inf_le_left
  have hpo : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(X, V) Γ(Y, q ⁻¹ᵁ V) :=
    algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) hVa (fun _ _ => trivial)
      (isAffineOpen_top T) (fun _ _ => trivial) hU' (fun _ => rfl)
      (fun r => by
        show φ.appTop.hom r = _
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        rfl) (fun _ => rfl) (fun _ => rfl)
  have hbc1 := hpo.out.finitePow {K : Finset (Fin n) // K.card = k}
  -- the coefficient isomorphisms
  let cX : ({K : Finset (Fin n) // K.card = k} → Γ(X, V)) ≃ₗ[Γ(S, ⊤)]
      ((logPresheafCx hDX ε).X k).obj (op V) :=
    coeffSiteEquiv g pr.c ε k (𝟭 X.Opens) V hVa hV
  haveI := preservesFiniteProducts_opensMap q.base
  let cY : ({K : Finset (Fin n) // K.card = k} → Γ(Y, q ⁻¹ᵁ V)) ≃ₗ[Γ(T, ⊤)]
      ((logPresheafCxPullback (q := q) hDY ε).X k).obj (op V) :=
    coeffSiteEquiv f pr.c' ε k (Opens.map q.base) V hVa' hV'
  letI : Module Γ(S, ⊤) (((logPresheafCxPullback (q := q) hDY ε).X k).obj (op V)) :=
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(T, ⊤))
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) (((logPresheafCxPullback (q := q) hDY ε).X k).obj (op V)) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap Γ(S, ⊤) Γ(T, ⊤) r • l • x
      rw [Algebra.smul_def, mul_smul]⟩
  let Φl : ((logPresheafCx hDX ε).X k).obj (op V) →ₗ[Γ(S, ⊤)]
      ((logPresheafCxPullback (q := q) hDY ε).X k).obj (op V) :=
    { toFun := logΦ hcomm hsupp hDX hDY hpairs ε k (op V)
      map_add' := map_add _
      map_smul' := fun r x => logΦ_smul hcomm hsupp hDX hDY hpairs ε k (op V) r x }
  have hΦ : IsBaseChange Γ(T, ⊤) Φl := by
    convert IsBaseChange.comp_equiv cX.symm _ (hbc1.comp (IsBaseChange.ofEquiv cY)) using 1
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := cX.surjective x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.coe_restrictScalars]
    exact Subtype.ext (logΦ_coeff hcomm hsupp hDX hDY hpairs pr ε k ⟨V, hVa⟩ hV ⟨q ⁻¹ᵁ V, hVa'⟩
      rfl hV' a)
  exact ⟨hΦ.equiv, fun x => (hΦ.equiv_tmul 1 x).trans (one_smul _ _)⟩

include hcomm hsupp in
/-- **Base change for the total Čech complex of the logarithmic de Rham complex.** -/
public theorem nonempty_logDeRham_homologyAt_equiv (H : IsPullback q f g φ) [IsAffine S]
    [IsAffine T] (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
      q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens)) {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hcov : ∀ (p : ℕ) (t : Fin (p + 1) → ι), IsAffineOpen (inter U t) ∧
      IsAffineOpen (q ⁻¹ᵁ inter U t) ∧ ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
        inter U t ≤ pr.c.W ∧ q ⁻¹ᵁ inter U t ≤ pr.c'.W) (ε : Bool) (i : ℤ) :
    letI := φ.appTop.hom.toAlgebra
    Nonempty (homologyAt ((totD U (logPresheafCx hDX ε) i).baseChange Γ(T, ⊤))
        ((totD U (logPresheafCx hDX ε) (i + 1)).baseChange Γ(T, ⊤)) ≃ₗ[Γ(T, ⊤)]
      homologyAt (totD U (logPresheafCxPullback (q := q) hDY ε) i)
        (totD U (logPresheafCxPullback (q := q) hDY ε) (i + 1))) := by
  letI := φ.appTop.hom.toAlgebra
  exact nonempty_homologyAt_baseChange_equiv U _ _ (logΦ hcomm hsupp hDX hDY hpairs ε)
    (fun a _ _ i x => logΦ_nat hcomm hsupp hDX hDY hpairs ε a i x)
    (fun a V x => logΦ_d hcomm hsupp hDX hDY hpairs ε a V x)
    (fun a V r x => logΦ_smul hcomm hsupp hDX hDY hpairs ε a V r x)
    (fun a p t => by
      obtain ⟨h1, h2, pr, h3, h4⟩ := hcov p t
      exact exists_logΦ_baseChange hcomm hsupp hDX hDY H hpairs pr ε a _ h1 h3 h2 h4) i

/-- The terms in positive degree of a module placed in degree `0` vanish after restriction. -/
public theorem subsingleton_resCx_single {C : Type} [Category.{0} C] {A B : Type} [CommRing A]
    [CommRing B] (ρ : B →+* A) (M : Cᵒᵖ ⥤ ModuleCat.{0} A) (b : ℕ) (V : Cᵒᵖ) :
    Subsingleton (((resCx ρ ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj M)).X
      (b + 1)).obj V) := by
  have h1 : IsZero (((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj M).X (b + 1)) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have h2 := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{0} ρ)).map_isZero h1
  exact (ModuleCat.isZero_iff_subsingleton).mp (h2.obj V)

/-- The term `Ω^p(log D)` of `X` in degree `0`, as presheaves of `Γ(S, ⊤)`-modules. -/
public noncomputable abbrev hodgePresheafCx (ε : Bool) (p : ℕ) :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} Γ(S, ⊤)) ℕ :=
  resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
      ((siteSections g (𝟭 X.Opens)).obj ((logCx hDX ε).X p)))

/-- The term `Ω^p(log D)` of `Y` in degree `0`, as presheaves of `Γ(T, ⊤)`-modules on the opens
of `X`. -/
public noncomputable abbrev hodgePresheafCxPullback (ε : Bool) (p : ℕ) :
    CochainComplex ((X.Opens)ᵒᵖ ⥤ ModuleCat.{0} Γ(T, ⊤)) ℕ :=
  haveI := preservesFiniteProducts_opensMap q.base
  resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
      ((siteSections f (Opens.map q.base)).obj ((logCx hDY ε).X p)))

/-- The pullback of the logarithmic `p`-forms, on the complexes in degree `0`. -/
public noncomputable def hodgeΦ (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY)
      (q := q) hDX hDY, q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens))
    (ε : Bool) (p : ℕ) :
    ∀ (a : ℕ) (V : (X.Opens)ᵒᵖ), ((hodgePresheafCx hDX ε p).X a).obj V →+
      ((hodgePresheafCxPullback (q := q) hDY ε p).X a).obj V
  | 0, V => logΦ hcomm hsupp hDX hDY hpairs ε p V
  | _ + 1, _ => 0

/-- In degree `0`, `hodgeΦ` is the pullback `logΦ` of the logarithmic `p`-forms. -/
@[simp]
public theorem hodgeΦ_zero (hpairs) (ε : Bool) (p : ℕ) (V : (X.Opens)ᵒᵖ)
    (x : ((hodgePresheafCx hDX ε p).X 0).obj V) :
    hodgeΦ hcomm hsupp hDX hDY hpairs ε p 0 V x = logΦ hcomm hsupp hDX hDY hpairs ε p V x := by
  rfl

/-- In positive degree, `hodgeΦ` is zero. -/
@[simp]
public theorem hodgeΦ_succ (hpairs) (ε : Bool) (p b : ℕ) (V : (X.Opens)ᵒᵖ)
    (x : ((hodgePresheafCx hDX ε p).X (b + 1)).obj V) :
    hodgeΦ hcomm hsupp hDX hDY hpairs ε p (b + 1) V x = 0 := by
  rfl

include hcomm hsupp in
/-- **Base change for the total Čech complex of the logarithmic forms.** -/
public theorem nonempty_logHodge_homologyAt_equiv (H : IsPullback q f g φ) [IsAffine S]
    [IsAffine T] (hpairs : ∀ y : Y, ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
      q.base y ∈ (pr.c.W : X.Opens) ∧ y ∈ (pr.c'.W : Y.Opens)) {ι : Type} [Finite ι] (U : ι → X.Opens)
    (hcov : ∀ (p : ℕ) (t : Fin (p + 1) → ι), IsAffineOpen (inter U t) ∧
      IsAffineOpen (q ⁻¹ᵁ inter U t) ∧ ∃ pr : ChartPair (DX := DX) (DY := DY) (q := q) hDX hDY,
        inter U t ≤ pr.c.W ∧ q ⁻¹ᵁ inter U t ≤ pr.c'.W) (ε : Bool) (p : ℕ) (i : ℤ) :
    letI := φ.appTop.hom.toAlgebra
    Nonempty (homologyAt ((totD U (hodgePresheafCx hDX ε p) i).baseChange Γ(T, ⊤))
        ((totD U (hodgePresheafCx hDX ε p) (i + 1)).baseChange Γ(T, ⊤)) ≃ₗ[Γ(T, ⊤)]
      homologyAt (totD U (hodgePresheafCxPullback (q := q) hDY ε p) i)
        (totD U (hodgePresheafCxPullback (q := q) hDY ε p) (i + 1))) := by
  letI := φ.appTop.hom.toAlgebra
  haveI := preservesFiniteProducts_opensMap q.base
  have hs : ∀ (b : ℕ) (V : (X.Opens)ᵒᵖ),
      Subsingleton (((hodgePresheafCxPullback (q := q) hDY ε p).X (b + 1)).obj V) :=
    fun b V => subsingleton_resCx_single _ _ b V
  have hs₀ : ∀ (b : ℕ) (V : (X.Opens)ᵒᵖ),
      Subsingleton (((hodgePresheafCx hDX ε p).X (b + 1)).obj V) :=
    fun b V => subsingleton_resCx_single _ _ b V
  refine nonempty_homologyAt_baseChange_equiv U _ _ (hodgeΦ hcomm hsupp hDX hDY hpairs ε p)
    (fun a V V' i x => ?_) (fun a V x => ?_) (fun a V r x => ?_) (fun a k t => ?_) i
  · rcases a with _ | b
    · exact logΦ_nat hcomm hsupp hDX hDY hpairs ε p i x
    · exact (hs b V').elim _ _
  · exact (hs a V).elim _ _
  · rcases a with _ | b
    · exact logΦ_smul hcomm hsupp hDX hDY hpairs ε p V r x
    · exact (hs b V).elim _ _
  · rcases a with _ | b
    · obtain ⟨h1, h2, pr, h3, h4⟩ := hcov k t
      exact exists_logΦ_baseChange hcomm hsupp hDX hDY H hpairs pr ε p _ h1 h3 h2 h4
    · haveI := hs b (op (inter U t))
      haveI := hs₀ b (op (inter U t))
      haveI : Subsingleton (Γ(T, ⊤) ⊗[Γ(S, ⊤)] ((hodgePresheafCx hDX ε p).X (b + 1)).obj
          (op (inter U t))) := subsingleton_tensor_right _ _
      exact ⟨LinearEquiv.ofSubsingleton _ _, fun x => Subsingleton.elim _ _⟩

end LogBaseChange

/-- Smoothness of relative dimension `n` is inherited by base change along a pullback square. -/
public theorem smoothOfRelativeDimension_of_isPullback {n : ℕ} {P X Y S : Scheme.{0}}
    {q : P ⟶ X} {p : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback q p f g)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n p :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.of_isPullback h ‹_›

/-! ### Spreading out: a smooth projective model over a smooth `ℤ`-algebra -/

section SpreadingOut

/-- **H-projective models descend along a cofiltered limit.** -/
private theorem exists_isProjectiveMorphism_model_of_isLimit
    {I : Type} [Category.{0} I] [IsCofiltered I] [EssentiallySmall.{0} I]
    (D : I ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {W : Scheme.{0}} (g : W ⟶ c.pt) (hg : IsProjectiveMorphism g)
    {j : I} (Z : Over (D.obj j)) (hfp : FinitePresentation Z.hom)
    (e : Over.mk g ≅ (Over.pullback (c.π.app j)).obj Z) :
    ∃ (k : I) (h : k ⟶ j), IsProjectiveMorphism (pullback.snd Z.hom (D.map h)) := by
  obtain ⟨n, i, hi, hig⟩ := hg
  let P : Over (D.obj j) := Over.mk (projectiveSpaceOver n (D.obj j) ↘ D.obj j)
  have := isProper_projectiveSpaceOver n (D.obj j)
  have hPfp : FinitePresentation P.hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation (projectiveSpaceOver n (D.obj j) ↘ D.obj j)),
      inferInstanceAs (QuasiCompact (projectiveSpaceOver n (D.obj j) ↘ D.obj j)),
      inferInstanceAs (QuasiSeparated (projectiveSpaceOver n (D.obj j) ↘ D.obj j))⟩
  let π : c.pt ⟶ D.obj j := c.π.app j
  let ε : pullback (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π ≅
      projectiveSpaceOver n c.pt :=
    projectiveSpaceOverBaseChangeIso n π
  have hε : ε.inv ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π =
      projectiveSpaceOver n c.pt ↘ c.pt := by
    rw [Iso.inv_comp_eq]
    exact (projectiveSpaceOverBaseChangeIso_hom_over n π).symm
  have hiε : (i ≫ ε.inv) ≫ pullback.snd (projectiveSpaceOver n (D.obj j) ↘ D.obj j) π = g := by
    rw [Category.assoc, hε, hig]
  let φ₀ : Over.mk g ⟶ (Over.pullback π).obj P := Over.homMk (i ≫ ε.inv) hiε
  let φ := e.inv ≫ φ₀
  obtain ⟨k, h, ψ, α, β, -, -, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc j Z P hfp hPfp φ
  have hlim : IsClosedImmersion ((Over.pullback (c.π.app k)).map ψ).left := by
    have hc' : α.hom.left ≫ φ.left =
        ((Over.pullback (c.π.app k)).map ψ).left ≫ β.hom.left :=
      congrArg Over.Hom.left hcomm
    have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso α).hom)
    have hβ : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso β).hom)
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).inv)
    have h1 : IsClosedImmersion (i ≫ ε.inv) := inferInstance
    have h2 : IsClosedImmersion φ.left := (inferInstance : IsClosedImmersion (e.inv.left ≫ i ≫ ε.inv))
    have h3 : IsClosedImmersion (α.hom.left ≫ φ.left) := inferInstance
    rw [hc'] at h3
    exact (@MorphismProperty.cancel_right_of_respectsIso _ _ @IsClosedImmersion _ _ _ _
      ((Over.pullback (c.π.app k)).map ψ).left β.hom.left hβ).mp h3
  let Zk := (Over.pullback (D.map h)).obj Z
  let Pk := (Over.pullback (D.map h)).obj P
  have hZk : FinitePresentation Zk.hom := finitePresentation_overPullback_obj _ Z hfp
  have hPk : FinitePresentation Pk.hom := finitePresentation_overPullback_obj _ P hPfp
  have := hZk.2.1
  have := hZk.2.2
  have := hPk.2.1
  have := hPk.2.2
  have := hZk.1
  have : CompactSpace Zk.left := QuasiCompact.compactSpace_of_compactSpace Zk.hom
  have : QuasiSeparatedSpace Zk.left := quasiSeparatedSpace_of_quasiSeparated Zk.hom
  have : CompactSpace Pk.left := QuasiCompact.compactSpace_of_compactSpace Pk.hom
  have : QuasiSeparatedSpace Pk.left := quasiSeparatedSpace_of_quasiSeparated Pk.hom
  have : LocallyOfFiniteType ψ.left := by
    have : LocallyOfFiniteType (ψ.left ≫ Pk.hom) := by rw [Over.w ψ]; infer_instance
    exact locallyOfFiniteType_of_comp ψ.left Pk.hom
  obtain ⟨l, h', hcl⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc k Zk Pk ψ
  refine ⟨l, h' ≫ h, ?_⟩
  have hPl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Pk).hom :=
    ((isProjectiveMorphism_projectiveSpaceOver n (D.obj j)).baseChange (D.map h)).baseChange
      (D.map h')
  obtain ⟨N, ι, hι, hιf⟩ := hPl
  have hZl : IsProjectiveMorphism ((Over.pullback (D.map h')).obj Zk).hom := by
    refine ⟨N, ((Over.pullback (D.map h')).map ψ).left ≫ ι, inferInstance, ?_⟩
    rw [Category.assoc, hιf]
    exact Over.w ((Over.pullback (D.map h')).map ψ)
  have hmap : D.map (h' ≫ h) = D.map h' ≫ D.map h := D.map_comp _ _
  refine (isProjectiveMorphism_pullback_snd_congr Z.hom hmap).mpr ?_
  exact isProjectiveMorphism_pullback_snd_comp Z.hom (D.map h) (D.map h') hZl

/-- **A projective smooth scheme over `ℂ` has a projective smooth model over a finitely
generated subring.** -/
private theorem exists_projective_smooth_model (n : ℕ) {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π) :
    ∃ (j : (Finset ℂ)ᵒᵖ) (Y : Scheme.{0}) (h : Y ⟶ (specAdjoinFinsetDiagram ℂ).obj j)
      (q : X ⟶ Y), IsProjective h ∧ SmoothOfRelativeDimension n h ∧
        IsPullback q π h ((specAdjoinFinsetCone ℂ).π.app j) := by
  haveI : IsProper π := hπ.isProper
  obtain ⟨j, Y, h, q', hpr, hsm, hpb⟩ :=
    exists_isPullback_specAdjoin_smoothOfRelativeDimension ℂ π n
  haveI := hpr
  haveI := hsm
  haveI : Smooth h := SmoothOfRelativeDimension.smooth n h
  let D := specAdjoinFinsetDiagram ℂ
  let c := specAdjoinFinsetCone ℂ
  have hc : IsLimit c := isLimit_specAdjoinFinsetCone ℂ
  have hfp : FinitePresentation (Over.mk h).hom :=
    ⟨inferInstanceAs (LocallyOfFinitePresentation h), inferInstanceAs (QuasiCompact h),
      inferInstanceAs (QuasiSeparated h)⟩
  let e : Over.mk π ≅ (Over.pullback (c.π.app j)).obj (Over.mk h) :=
    Over.isoMk hpb.isoPullback (hpb.isoPullback_hom_snd)
  have hg : IsProjectiveMorphism π := isProjectiveMorphism_of_isProjective_of_isAffine π hπ
  obtain ⟨k, hk, hproj⟩ := exists_isProjectiveMorphism_model_of_isLimit D c hc π hg
    (Over.mk h) hfp e
  have hw : c.π.app k ≫ D.map hk = c.π.app j := c.w hk
  have hpb' := isPullback_pullbackLift_of_comp hpb hw
  refine ⟨k, pullback h (D.map hk), pullback.snd h (D.map hk), _, hproj.isProjective,
    smoothOfRelativeDimension_of_isPullback (IsPullback.of_hasPullback h (D.map hk)), hpb'⟩

section LimitSections

variable {I : Type} [Category.{0} I] [IsCofiltered I] (E : I ⥤ Scheme.{0}) (cE : Cone E)
  (hE : IsLimit cE) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f)]

include hE in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Sections over the inverse image of an affine open of a stage come from a later stage.** -/
private theorem exists_appLE_eq_of_isLimit {i : I} {U : (E.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(cE.pt, cE.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(E.obj j, E.map f ⁻¹ᵁ U)),
      (cE.π.app j).appLE (E.map f ⁻¹ᵁ U) (cE.π.app i ⁻¹ᵁ U)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, cE.w])) t = s := by
  have (j : _) : IsAffine ((opensDiagram E i U).op.obj j).unop := hU.preimage _
  have (j : _) : IsAffine ((opensDiagram E i U).obj j) := hU.preimage _
  obtain ⟨⟨j⟩, t, ht⟩ := (Types.jointly_surjective_of_isColimit (isColimitOfPreserves
    (Scheme.Γ ⋙ forget _) (isLimitOpensCone E cE hE i U).op) ((cE.π.app i ⁻¹ᵁ U).topIso.inv s))
  obtain ⟨t, rfl⟩ := (E.map j.hom ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.surjective t
  have h : cE.π.app j.left ⁻¹ᵁ E.map j.hom ⁻¹ᵁ U = cE.π.app i ⁻¹ᵁ U := congr($(cE.w j.hom) ⁻¹ᵁ U)
  have key : s = (cE.π.app j.left).appLE (E.map j.hom ⁻¹ᵁ U) (cE.π.app i ⁻¹ᵁ U) h.ge t := by
    convert!
      show s = ((Scheme.Opens.topIso _).inv ≫ ((opensCone E cE i U).π.app j).appTop ≫
        (Scheme.Opens.topIso _).hom) t from
        (cE.π.app i ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp ht.symm using 3
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  exact ⟨j.left, j.hom, t, key.symm⟩

end LimitSections

section KaehlerDescent

open TensorProduct

/-- The differentials of generators span the Kähler differentials. -/
private theorem kaehler_span_eq_top_of_adjoin {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (G : Set A) (hG : Algebra.adjoin R G = ⊤) (N : Submodule A Ω[A⁄R])
    (hN : ∀ g ∈ G, KaehlerDifferential.D R A g ∈ N) : N = ⊤ := by
  let T : Subalgebra R A :=
    { carrier := {a | KaehlerDifferential.D R A a ∈ N}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Derivation.leibniz] at ha hb ⊢
        exact N.add_mem (N.smul_mem _ hb) (N.smul_mem _ ha)
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact N.add_mem ha hb
      algebraMap_mem' := fun r => by
        simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
        exact N.zero_mem }
  have hT : T = ⊤ := top_le_iff.mp (hG ▸ Algebra.adjoin_le fun g hg => hN g hg)
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have : a ∈ T := hT ▸ Algebra.mem_top
  exact this

/-- **Kähler differentials embed under a flat pushout along an injective base map.** -/
private theorem kaehler_map_injective_of_flat {R A R' A' : Type} [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra.IsPushout R R' A A']
    (hR : Function.Injective (algebraMap R R')) [Module.Flat R Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R R' A A') := by
  have h1 : Function.Injective (fun ω : Ω[A⁄R] => (1 : R') ⊗ₜ[R] ω) := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω[A⁄R])
      (Algebra.linearMap R R') hR
    intro x y hxy
    have e : ∀ z : Ω[A⁄R], (Algebra.linearMap R R').rTensor Ω[A⁄R] ((1 : R) ⊗ₜ z) =
        (1 : R') ⊗ₜ z := by
      intro z; simp
    apply (TensorProduct.lid R Ω[A⁄R]).symm.injective
    apply this
    simp only [TensorProduct.lid_symm_apply, e]
    exact hxy
  have h2 : ∀ ω : Ω[A⁄R], KaehlerDifferential.tensorKaehlerEquiv R R' A A' ((1 : A') ⊗ₜ ω) =
      KaehlerDifferential.map R R' A A' ω := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
    · rintro _ ⟨a, rfl⟩
      rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
    · simp
    · intro x y _ _ hx hy
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    · intro a x _ hx
      have e1 : (1 : A') ⊗ₜ[A] (a • x) = algebraMap A A' a • ((1 : A') ⊗ₜ[A] x) := by
        rw [TensorProduct.tmul_smul, algebraMap_smul]
      rw [e1, map_smul, hx, LinearMap.map_smul_of_tower, algebraMap_smul]
  intro x y hxy
  apply h1
  simp only
  rw [← Algebra.IsPushout.cancelBaseChange_tmul R R' A A' Ω[A⁄R] x,
    ← Algebra.IsPushout.cancelBaseChange_tmul R R' A A' Ω[A⁄R] y]
  congr 1
  apply (KaehlerDifferential.tensorKaehlerEquiv R R' A A').injective
  rw [h2, h2, hxy]

/-- **A basis of differentials descends** along an injective map of algebras, once the
differentials span. -/
private theorem exists_basis_of_span_of_basis_map {R A R' A' : Type} [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] {n : ℕ} (t : Fin n → A)
    (hspan : Submodule.span A (Set.range fun i => KaehlerDifferential.D R A (t i)) = ⊤)
    (hinj : Function.Injective (algebraMap A A'))
    (b' : Module.Basis (Fin n) A' Ω[A'⁄R'])
    (hb' : ∀ i, b' i = KaehlerDifferential.D R' A' (algebraMap A A' (t i))) :
    ∃ b : Module.Basis (Fin n) A Ω[A⁄R], ∀ i, b i = KaehlerDifferential.D R A (t i) := by
  have hli : LinearIndependent A fun i => KaehlerDifferential.D R A (t i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hmap := congrArg (KaehlerDifferential.map R R' A A') hg
    simp only [map_sum, map_smul, map_zero, KaehlerDifferential.map_D] at hmap
    have hmap' : ∑ k, algebraMap A A' (g k) • b' k = 0 := by
      simp only [hb']
      convert hmap using 2 with k
      rw [algebraMap_smul]
    have := (Fintype.linearIndependent_iff.mp b'.linearIndependent) _ hmap' i
    exact hinj (this.trans (map_zero _).symm)
  exact ⟨Module.Basis.mk hli hspan.ge, fun i => Module.Basis.mk_apply _ _ _⟩

/-- Generators of an algebra generate its base change. -/
private theorem adjoin_image_eq_top_of_isPushout {R A R' A' : Type} [CommRing R] [CommRing A]
    [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra.IsPushout R R' A A']
    (G : Set A) (hG : Algebra.adjoin R G = ⊤) :
    Algebra.adjoin R' (algebraMap A A' '' G) = ⊤ := by
  have hA : ∀ a : A, algebraMap A A' a ∈ Algebra.adjoin R' (algebraMap A A' '' G) := by
    intro a
    have ha : a ∈ Algebra.adjoin R G := hG ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' A']
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (Algebra.IsPushout.equiv R R' A A').surjective x
  clear ‹_ ∈ ⊤›
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [Algebra.IsPushout.equiv_tmul]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (hA a)
  | add y z hy hz => rw [map_add]; exact Subalgebra.add_mem _ hy hz

end KaehlerDescent

section SquareDescent

open TensorProduct

/-- An algebra embeds into its flat base change along an injective map. -/
private theorem algebraMap_injective_of_isPushout_of_flat {R A R' A' : Type} [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A']
    [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A A'] (hR : Function.Injective (algebraMap R R')) [Module.Flat R A] :
    Function.Injective (algebraMap A A') := by
  have h1 : Function.Injective (fun a : A => (1 : R') ⊗ₜ[R] a) := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R R') hR
    intro x y hxy
    apply (TensorProduct.lid R A).symm.injective
    apply this
    simpa only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
      map_one] using hxy
  intro x y hxy
  apply h1
  simp only
  apply (Algebra.IsPushout.equiv R R' A A').injective
  rwa [Algebra.IsPushout.equiv_tmul, Algebra.IsPushout.equiv_tmul, map_one, one_mul, one_mul]

variable {𝒳 S Y T : Scheme.{0}} [IsAffine S] [IsAffine T] {g : 𝒳 ⟶ S} {q : Y ⟶ 𝒳} {f : Y ⟶ T}
  {φ : T ⟶ S}

include q in
/-- **A basis of differentials descends through a cartesian square** along a flat morphism and
an injective map on global sections of the bases. -/
private theorem exists_basis_of_isPullback {n : ℕ} (H : IsPullback q f g φ) [Smooth g]
    (hφ : Function.Injective (φ.appLE ⊤ ⊤ le_top).hom) (W : 𝒳.affineOpens) (W' : Y.Opens) (hW' : W' = q ⁻¹ᵁ (W : 𝒳.Opens))
    (t : Fin n → Γ(𝒳, W))
    (hspan : letI := (g.appLE ⊤ W le_top).hom.toAlgebra
      Submodule.span Γ(𝒳, W) (Set.range fun i => KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) (t i)) = ⊤)
    (hb : letI := (f.appLE ⊤ W' le_top).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(Y, W') Ω[Γ(Y, W')⁄Γ(T, ⊤)],
        ∀ i, b i = KaehlerDifferential.D Γ(T, ⊤) Γ(Y, W')
          ((q.appLE W W' hW'.le).hom (t i))) :
    letI := (g.appLE ⊤ W le_top).hom.toAlgebra
    ∃ b : Module.Basis (Fin n) Γ(𝒳, W) Ω[Γ(𝒳, W)⁄Γ(S, ⊤)],
      ∀ i, b i = KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) (t i) := by
  have hV' : (⊤ : T.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top
  have e₁ : W' ≤ q ⁻¹ᵁ (W : 𝒳.Opens) := hW'.le
  have e' : W' ≤ f ⁻¹ᵁ ⊤ := le_top
  have hU' : W' = q ⁻¹ᵁ (W : 𝒳.Opens) ⊓ f ⁻¹ᵁ ⊤ :=
    le_antisymm (le_inf hW'.le fun _ _ => trivial) (inf_le_left.trans hW'.ge)
  letI : Algebra Γ(S, ⊤) Γ(𝒳, W) := (g.appLE ⊤ W le_top).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := (φ.appLE ⊤ ⊤ hV').hom.toAlgebra
  letI : Algebra Γ(𝒳, W) Γ(Y, W') := (q.appLE W W' e₁).hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(Y, W') := (f.appLE ⊤ W' e').hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, W') := (g.appLE ⊤ W le_top ≫ q.appLE W W' e₁).hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcomm : φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e' = g.appLE ⊤ W le_top ≫ q.appLE W W' e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE f φ ⊤ ⊤ W' hV' e',
      Scheme.Hom.appLE_comp_appLE q g ⊤ W W' le_top e₁]
    exact appLE_eq_of_eq H.w.symm _ _
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = (φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e').hom x
      rw [hcomm]; rfl)
  haveI : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) W.2 le_top
      (isAffineOpen_top T) hV' hU'
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  haveI : Module.Flat Γ(S, ⊤) Γ(𝒳, W) :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top S⟩ W le_top
  have hinj : Function.Injective (algebraMap Γ(𝒳, W) Γ(Y, W')) :=
    algebraMap_injective_of_isPushout_of_flat (R := Γ(S, ⊤)) (R' := Γ(T, ⊤)) hφ
  obtain ⟨b, hb⟩ := hb
  exact exists_basis_of_span_of_basis_map t hspan hinj b hb

include q in
/-- **The span condition descends through a cartesian square**: if the differentials of
generators are combinations of the `d tᵢ` after base change, with coefficients pulled back from
`W`, they are so on `W`. -/
private theorem span_eq_top_of_isPullback {n : ℕ} (H : IsPullback q f g φ) [Smooth g]
    (hφ : Function.Injective (φ.appLE ⊤ ⊤ le_top).hom) (W : 𝒳.affineOpens) (W' : Y.Opens) (hW' : W' = q ⁻¹ᵁ (W : 𝒳.Opens))
    (t : Fin n → Γ(𝒳, W))
    (G : Set Γ(𝒳, W))
    (hG : letI := (g.appLE ⊤ W le_top).hom.toAlgebra; Algebra.adjoin Γ(S, ⊤) G = ⊤)
    (cf : Γ(𝒳, W) → Fin n → Γ(𝒳, W))
    (hc : ∀ x ∈ G, letI := (f.appLE ⊤ W' le_top).hom.toAlgebra
      KaehlerDifferential.D Γ(T, ⊤) Γ(Y, W')
          ((q.appLE W W' hW'.le).hom x) =
        ∑ i, (q.appLE W W' hW'.le).hom (cf x i) •
          KaehlerDifferential.D Γ(T, ⊤) Γ(Y, W')
            ((q.appLE W W' hW'.le).hom (t i))) :
    letI := (g.appLE ⊤ W le_top).hom.toAlgebra
    Submodule.span Γ(𝒳, W) (Set.range fun i => KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) (t i)) = ⊤ := by
  have hV' : (⊤ : T.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top
  have e₁ : W' ≤ q ⁻¹ᵁ (W : 𝒳.Opens) := hW'.le
  have e' : W' ≤ f ⁻¹ᵁ ⊤ := le_top
  have hU' : W' = q ⁻¹ᵁ (W : 𝒳.Opens) ⊓ f ⁻¹ᵁ ⊤ :=
    le_antisymm (le_inf hW'.le fun _ _ => trivial) (inf_le_left.trans hW'.ge)
  letI : Algebra Γ(S, ⊤) Γ(𝒳, W) := (g.appLE ⊤ W le_top).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := (φ.appLE ⊤ ⊤ hV').hom.toAlgebra
  letI : Algebra Γ(𝒳, W) Γ(Y, W') := (q.appLE W W' e₁).hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(Y, W') := (f.appLE ⊤ W' e').hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, W') := (g.appLE ⊤ W le_top ≫ q.appLE W W' e₁).hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcomm : φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e' = g.appLE ⊤ W le_top ≫ q.appLE W W' e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE f φ ⊤ ⊤ W' hV' e',
      Scheme.Hom.appLE_comp_appLE q g ⊤ W W' le_top e₁]
    exact appLE_eq_of_eq H.w.symm _ _
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = (φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e').hom x
      rw [hcomm]; rfl)
  haveI : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) W.2 le_top
      (isAffineOpen_top T) hV' hU'
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  haveI : Module.Flat Γ(S, ⊤) Γ(𝒳, W) :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top S⟩ W le_top
  haveI : Algebra.Smooth Γ(S, ⊤) Γ(𝒳, W) :=
    HasRingHomProperty.appLE @Smooth g inferInstance ⟨⊤, isAffineOpen_top S⟩ W le_top
  haveI : Module.Projective Γ(𝒳, W) Ω[Γ(𝒳, W)⁄Γ(S, ⊤)] := inferInstance
  haveI : Module.Flat Γ(𝒳, W) Ω[Γ(𝒳, W)⁄Γ(S, ⊤)] := Module.Flat.of_projective
  haveI : Module.Flat Γ(S, ⊤) Ω[Γ(𝒳, W)⁄Γ(S, ⊤)] := Module.Flat.trans _ Γ(𝒳, W) _
  have hinj := kaehler_map_injective_of_flat (R := Γ(S, ⊤)) (A := Γ(𝒳, W)) (R' := Γ(T, ⊤))
    (A' := Γ(Y, W')) hφ
  refine kaehler_span_eq_top_of_adjoin G hG _ fun x hx => ?_
  have hx' : KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) x =
      ∑ i, cf x i • KaehlerDifferential.D Γ(S, ⊤) Γ(𝒳, W) (t i) := by
    apply hinj
    simp only [map_sum, map_smul, KaehlerDifferential.map_D]
    refine (hc x hx).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [← algebraMap_smul Γ(Y, W') (cf x i)]
    rfl
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

include q in
/-- Generators of the sections of an affine open generate those of its base change through a
cartesian square. -/
private theorem adjoin_appLE_image_eq_top_of_isPullback (H : IsPullback q f g φ)
    (W : 𝒳.affineOpens) (W' : Y.Opens) (hW' : W' = q ⁻¹ᵁ (W : 𝒳.Opens)) (G : Set Γ(𝒳, W))
    (hG : letI := (g.appLE ⊤ W le_top).hom.toAlgebra; Algebra.adjoin Γ(S, ⊤) G = ⊤) :
    letI := (f.appLE ⊤ W' le_top).hom.toAlgebra
    Algebra.adjoin Γ(T, ⊤) ((q.appLE W W' hW'.le).hom '' G) = ⊤ := by
  have hV' : (⊤ : T.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top
  have e₁ : W' ≤ q ⁻¹ᵁ (W : 𝒳.Opens) := hW'.le
  have e' : W' ≤ f ⁻¹ᵁ ⊤ := le_top
  have hU' : W' = q ⁻¹ᵁ (W : 𝒳.Opens) ⊓ f ⁻¹ᵁ ⊤ :=
    le_antisymm (le_inf hW'.le fun _ _ => trivial) (inf_le_left.trans hW'.ge)
  letI : Algebra Γ(S, ⊤) Γ(𝒳, W) := (g.appLE ⊤ W le_top).hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := (φ.appLE ⊤ ⊤ hV').hom.toAlgebra
  letI : Algebra Γ(𝒳, W) Γ(Y, W') := (q.appLE W W' e₁).hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(Y, W') := (f.appLE ⊤ W' e').hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(Y, W') := (g.appLE ⊤ W le_top ≫ q.appLE W W' e₁).hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcomm : φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e' = g.appLE ⊤ W le_top ≫ q.appLE W W' e₁ := by
    rw [Scheme.Hom.appLE_comp_appLE f φ ⊤ ⊤ W' hV' e',
      Scheme.Hom.appLE_comp_appLE q g ⊤ W W' le_top e₁]
    exact appLE_eq_of_eq H.w.symm _ _
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(Y, W') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = (φ.appLE ⊤ ⊤ hV' ≫ f.appLE ⊤ W' e').hom x
      rw [hcomm]; rfl)
  haveI : Algebra.IsPushout Γ(S, ⊤) Γ(T, ⊤) Γ(𝒳, W) Γ(Y, W') :=
    algebra_isPushout_appLE_of_isPullback H (isAffineOpen_top S) W.2 le_top
      (isAffineOpen_top T) hV' hU'
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact adjoin_image_eq_top_of_isPushout (R := Γ(S, ⊤)) G hG

end SquareDescent

section SystemDescent

variable {I : Type} [Category.{0} I] [IsCofiltered I] [Quiver.IsThin I] {E : I ⥤ Scheme.{0}}
  {cE : Cone E} (hE : IsLimit cE) [∀ {i j : I} (φ : i ⟶ j), IsAffineHom (E.map φ)]

include hE in
/-- **Finitely many sections over the inverse image of an affine open of a stage come from one
later stage.** -/
private theorem exists_stage_sections {i : I} {U : (E.obj i).Opens} (hU : IsAffineOpen U)
    {V : cE.pt.Opens} (hV : V = cE.π.app i ⁻¹ᵁ U)
    {κ : Type} [Finite κ] (s : κ → Γ(cE.pt, V)) :
    ∃ (j : I) (f : j ⟶ i) (t : κ → Γ(E.obj j, E.map f ⁻¹ᵁ U)), ∀ k,
      (cE.π.app j).appLE (E.map f ⁻¹ᵁ U) V
        (le_of_eq (by rw [hV, ← Scheme.Hom.comp_preimage, cE.w])) (t k) = s k := by
  classical
  subst hV
  choose j f t ht using fun k => exists_appLE_eq_of_isLimit E cE hE hU (s k)
  cases nonempty_fintype κ
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (insert i (Finset.univ.image j))
  have hmi : Nonempty (m ⟶ i) := hm (Finset.mem_insert_self _ _)
  have hmj : ∀ k, Nonempty (m ⟶ j k) := fun k =>
    hm (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  let fm : m ⟶ i := hmi.some
  have hcomp : ∀ k, (hmj k).some ≫ f k = fm := fun k => Subsingleton.elim _ _
  have hle : ∀ k, E.map fm ⁻¹ᵁ U ≤ E.map (hmj k).some ⁻¹ᵁ (E.map (f k) ⁻¹ᵁ U) := fun k => by
    rw [← Scheme.Hom.comp_preimage, ← Functor.map_comp, hcomp]
  refine ⟨m, fm, fun k => ((E.map (hmj k).some).appLE _ _ (hle k)).hom (t k), fun k => ?_⟩
  rw [← ht k, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_eq_of_eq (cE.w (hmj k).some)]

include hE in
/-- **A chart of the limit descends to a stage**: its affine open, its coordinates, and the
basis of differentials given by the coordinates. -/
private theorem exists_stage_chart {D : I ⥤ Scheme.{0}} (g : E ⟶ D) {c : Cone D}
    {gX : cE.pt ⟶ c.pt} (hsq : ∀ i, IsPullback (cE.π.app i) gX (g.app i) (c.π.app i))
    (hst : ∀ {i j : I} (φ : i ⟶ j), IsPullback (E.map φ) (g.app i) (g.app j) (D.map φ))
    [∀ i, IsAffine (D.obj i)] [IsAffine c.pt] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (hinj : ∀ i, Function.Injective ((c.π.app i).appLE ⊤ ⊤ le_top).hom)
    [∀ i, Smooth (g.app i)] {n : ℕ} (W : cE.pt.affineOpens) (t : Fin n → Γ(cE.pt, W))
    (hb : letI := (gX.appLE ⊤ W le_top).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(cE.pt, W) Ω[Γ(cE.pt, W)⁄Γ(c.pt, ⊤)],
        ∀ k, b k = KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W) (t k)) :
    ∃ (i : I) (W' : (E.obj i).affineOpens)
      (hW : (W : cE.pt.Opens) = cE.π.app i ⁻¹ᵁ (W' : (E.obj i).Opens))
      (t' : Fin n → Γ(E.obj i, W')),
      (∀ k, ((cE.π.app i).appLE W' (W : cE.pt.Opens) hW.le).hom (t' k) = t k) ∧
      (letI := ((g.app i).appLE ⊤ W' le_top).hom.toAlgebra
        ∃ b : Module.Basis (Fin n) Γ(E.obj i, W') Ω[Γ(E.obj i, W')⁄Γ(D.obj i, ⊤)],
          ∀ k, b k = KaehlerDifferential.D Γ(D.obj i, ⊤) Γ(E.obj i, W') (t' k)) := by
  classical
  obtain ⟨i₁, W₁, hW₁a, hpre⟩ := exists_isAffineOpen_preimage_eq E cE hE W W.2
  -- the coordinates
  obtain ⟨i₂, f₂, t₂, ht₂⟩ := exists_stage_sections hE hW₁a hpre.symm t
  have hW₂a : IsAffineOpen (E.map f₂ ⁻¹ᵁ W₁) := hW₁a.preimage _
  have hW₂ : (W : cE.pt.Opens) = cE.π.app i₂ ⁻¹ᵁ (E.map f₂ ⁻¹ᵁ W₁) := by
    rw [← hpre, ← Scheme.Hom.comp_preimage, cE.w]
  set W₂ : (E.obj i₂).affineOpens := ⟨E.map f₂ ⁻¹ᵁ W₁, hW₂a⟩
  -- generators of the stage algebra
  obtain ⟨G, hG⟩ : ∃ G : Finset Γ(E.obj i₂, W₂),
      letI := ((g.app i₂).appLE ⊤ W₂ le_top).hom.toAlgebra
      Algebra.adjoin Γ(D.obj i₂, ⊤) (G : Set Γ(E.obj i₂, W₂)) = ⊤ := by
    letI := ((g.app i₂).appLE ⊤ W₂ le_top).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(D.obj i₂, ⊤) Γ(E.obj i₂, W₂) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType (g.app i₂) inferInstance
        ⟨⊤, isAffineOpen_top _⟩ W₂ le_top
    exact Algebra.FiniteType.out
  -- the expansions of their differentials over the limit
  obtain ⟨b, hbk⟩ := hb
  let img : Γ(E.obj i₂, W₂) → Γ(cE.pt, W) := fun x => ((cE.π.app i₂).appLE W₂ (W : cE.pt.Opens) hW₂.le).hom x
  let s : G × Fin n → Γ(cE.pt, W) := fun p =>
    letI := (gX.appLE ⊤ W le_top).hom.toAlgebra
    b.repr (KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W) (img p.1)) p.2
  obtain ⟨i₃, f₃, c₃, hc₃⟩ := exists_stage_sections hE hW₂a hW₂ s
  set W₃ : (E.obj i₃).affineOpens := ⟨E.map f₃ ⁻¹ᵁ (W₂ : (E.obj i₂).Opens), hW₂a.preimage _⟩
  have hW₃ : (W : cE.pt.Opens) = cE.π.app i₃ ⁻¹ᵁ (W₃ : (E.obj i₃).Opens) := by
    rw [← hpre]
    change cE.π.app i₁ ⁻¹ᵁ W₁ = cE.π.app i₃ ⁻¹ᵁ (E.map f₃ ⁻¹ᵁ (E.map f₂ ⁻¹ᵁ W₁))
    simp only [← Scheme.Hom.comp_preimage]
    rw [← Functor.map_comp, cE.w]
  let tr : Γ(E.obj i₂, W₂) → Γ(E.obj i₃, W₃) := fun x =>
    ((E.map f₃).appLE W₂ W₃ le_rfl).hom x
  have hcompat : ∀ x, ((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (tr x) = img x := by
    intro x
    change ((E.map f₃).appLE W₂ W₃ le_rfl ≫ (cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom x
      = _
    rw [Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (cE.w f₃)]
  let t₃ : Fin n → Γ(E.obj i₃, W₃) := fun k => tr (t₂ k)
  have ht₃ : ∀ k, ((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (t₃ k) = t k :=
    fun k => (hcompat _).trans (ht₂ k)
  -- the span condition at the stage `i₃`
  let G₃ : Set Γ(E.obj i₃, W₃) := tr '' (G : Set Γ(E.obj i₂, W₂))
  have hG₃ : letI := ((g.app i₃).appLE ⊤ W₃ le_top).hom.toAlgebra
      Algebra.adjoin Γ(D.obj i₃, ⊤) G₃ = ⊤ :=
    adjoin_appLE_image_eq_top_of_isPullback (hst f₃) W₂ (W₃ : (E.obj i₃).Opens) rfl _ hG
  let cf : Γ(E.obj i₃, W₃) → Fin n → Γ(E.obj i₃, W₃) := fun x k =>
    if h : ∃ p ∈ (G : Set Γ(E.obj i₂, W₂)), tr p = x then c₃ (⟨h.choose, h.choose_spec.1⟩, k)
    else 0
  have hc : ∀ x ∈ G₃, letI := (gX.appLE ⊤ (W : cE.pt.Opens) le_top).hom.toAlgebra
      KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W)
          (((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom x) =
        ∑ k, (show Γ(cE.pt, W) from
            ((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (cf x k)) •
          KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W)
            (((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (t₃ k)) := by
    rintro x ⟨p, hp, rfl⟩
    have h : ∃ p' ∈ (G : Set Γ(E.obj i₂, W₂)), tr p' = tr p := ⟨p, hp, rfl⟩
    have hx : ∀ k, cf (tr p) k = c₃ (⟨h.choose, h.choose_spec.1⟩, k) := fun k => by
      simp only [cf, dif_pos h]
    have e : ((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (tr p) = img h.choose :=
      (congrArg ((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom h.choose_spec.2).symm.trans
        (hcompat _)
    letI := (gX.appLE ⊤ (W : cE.pt.Opens) le_top).hom.toAlgebra
    calc KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W)
          (((cE.π.app i₃).appLE W₃ (W : cE.pt.Opens) hW₃.le).hom (tr p))
        = KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W) (img h.choose) := by rw [e]
      _ = ∑ k, b.repr (KaehlerDifferential.D Γ(c.pt, ⊤) Γ(cE.pt, W) (img h.choose)) k • b k :=
          (b.sum_repr _).symm
      _ = _ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hbk k, ← ht₃ k, hx k]
          congr 1
          exact (hc₃ (⟨h.choose, h.choose_spec.1⟩, k)).symm
  letI := ((g.app i₃).appLE ⊤ W₃ le_top).hom.toAlgebra
  have hspan := span_eq_top_of_isPullback (hsq i₃) (hinj i₃) W₃ (W : cE.pt.Opens) hW₃ t₃ G₃ hG₃
    cf hc
  have hbasis := exists_basis_of_isPullback (hsq i₃) (hinj i₃) W₃ (W : cE.pt.Opens) hW₃ t₃ hspan
    ⟨b, fun k => (hbk k).trans (by rw [ht₃]; rfl)⟩
  exact ⟨i₃, W₃, hW₃, t₃, ht₃, hbasis⟩

/-- **Stage charts transport to later stages.** -/
private theorem exists_stage_chart_transport {D : I ⥤ Scheme.{0}} (g : E ⟶ D)
    (hst : ∀ {i j : I} (φ : i ⟶ j), IsPullback (E.map φ) (g.app i) (g.app j) (D.map φ))
    [∀ i, IsAffine (D.obj i)] {n : ℕ} {i i' : I} (φ : i' ⟶ i) (W' : (E.obj i).affineOpens)
    (t' : Fin n → Γ(E.obj i, W')) (r : ℕ) (hr : r ≤ n)
    (hb : letI := ((g.app i).appLE ⊤ W' le_top).hom.toAlgebra
      ∃ b : Module.Basis (Fin n) Γ(E.obj i, W') Ω[Γ(E.obj i, W')⁄Γ(D.obj i, ⊤)],
        ∀ k, b k = KaehlerDifferential.D Γ(D.obj i, ⊤) Γ(E.obj i, W') (t' k)) :
    ∃ (W'' : (E.obj i').affineOpens) (hW : (W'' : (E.obj i').Opens) = E.map φ ⁻¹ᵁ W')
      (t'' : Fin n → Γ(E.obj i', W'')),
      (∀ k, t'' k = ((E.map φ).appLE W' W'' hW.le).hom (t' k)) ∧
      (letI := ((g.app i').appLE ⊤ W'' le_top).hom.toAlgebra
        ∃ b : Module.Basis (Fin n) Γ(E.obj i', W'') Ω[Γ(E.obj i', W'')⁄Γ(D.obj i', ⊤)],
          ∀ k, b k = KaehlerDifferential.D Γ(D.obj i', ⊤) Γ(E.obj i', W'') (t'' k)) := by
  let c : WeakChart (g.app i) n ((E.obj i).zeroLocus (U := W') {∏ k : Fin r, t' (Fin.castLE hr k)}) :=
    ⟨W', t', r, hr, hb, rfl⟩
  obtain ⟨c', hW, -, hle, ht⟩ := c.exists_baseChange (hst φ)
  have hW' : (c'.W : (E.obj i').Opens) = E.map φ ⁻¹ᵁ W' :=
    hW.trans (le_antisymm inf_le_left (le_inf le_rfl fun _ _ => trivial))
  exact ⟨c'.W, hW', c'.t, ht, c'.basis⟩

end SystemDescent

/-- The preimage of the zero locus of a section is the zero locus of its pullback. -/
private theorem preimage_zeroLocus_singleton {X Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (hV : V = φ ⁻¹ᵁ U) (s : Γ(Y, U)) :
    φ.base ⁻¹' Y.zeroLocus (U := U) {s} = X.zeroLocus (U := V) {(φ.appLE U V hV.le).hom s} := by
  ext x
  simp only [Set.mem_preimage, Scheme.mem_zeroLocus_iff, Set.mem_singleton_iff, forall_eq,
    Scheme.basicOpen_appLE]
  constructor
  · rintro h ⟨_, hx⟩
    exact h hx
  · intro h hx
    apply h
    refine ⟨?_, hx⟩
    rw [hV]
    exact Y.basicOpen_le s hx

/-- **Weak charts of the limit spread out to weak charts of a stage covering it.** -/
private theorem exists_stage_weakCharts {I : Type} [Category.{0} I] [IsCofiltered I]
    [Quiver.IsThin I] {D E : I ⥤ Scheme.{0}} (g : E ⟶ D) {c : Cone D} {cE : Cone E}
    (hE : IsLimit cE) [∀ {i j : I} (φ : i ⟶ j), IsAffineHom (E.map φ)] {gX : cE.pt ⟶ c.pt}
    (hsq : ∀ i, IsPullback (cE.π.app i) gX (g.app i) (c.π.app i))
    (hst : ∀ {i j : I} (φ : i ⟶ j), IsPullback (E.map φ) (g.app i) (g.app j) (D.map φ))
    [∀ i, IsAffine (D.obj i)] [IsAffine c.pt] [∀ i, QuasiSeparatedSpace (E.obj i)]
    [∀ i, CompactSpace (E.obj i)]
    (hinj : ∀ i, Function.Injective ((c.π.app i).appLE ⊤ ⊤ le_top).hom)
    [∀ i, Smooth (g.app i)] {n : ℕ} {ZX : Set cE.pt} {κ : Type} [Finite κ]
    (C : κ → WeakChart gX n ZX) (hC : ⨆ m, ((C m).W : cE.pt.Opens) = ⊤) :
    ∃ (i : I) (Z : Set (E.obj i)), IsClosed Z ∧ (cE.π.app i).base ⁻¹' Z = ZX ∧
      ∃ C' : κ → WeakChart (g.app i) n Z, ⨆ m, ((C' m).W : (E.obj i).Opens) = ⊤ := by
  classical
  cases nonempty_fintype κ
  -- descend every chart
  choose i₀ W₀ hW₀ t₀ ht₀ hb₀ using fun m =>
    exists_stage_chart hE g hsq hst hinj (C m).W (C m).t (C m).basis
  obtain ⟨i₁, hi₁⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i₀)
  let φ₁ : ∀ m, i₁ ⟶ i₀ m := fun m =>
    (hi₁ (Finset.mem_image_of_mem _ (Finset.mem_univ m))).some
  choose W₁ hW₁ t₁ ht₁ hb₁ using fun m =>
    exists_stage_chart_transport g hst (φ₁ m) (W₀ m) (t₀ m) (C m).r (C m).hr (hb₀ m)
  have hlim : ∀ m, ((C m).W : cE.pt.Opens) = cE.π.app i₁ ⁻¹ᵁ (W₁ m : (E.obj i₁).Opens) := by
    intro m
    rw [hW₁ m, ← Scheme.Hom.comp_preimage, cE.w, ← hW₀ m]
  have hlimt : ∀ m k, ((cE.π.app i₁).appLE (W₁ m) ((C m).W : cE.pt.Opens) (hlim m).le).hom (t₁ m k) =
      (C m).t k := by
    intro m k
    rw [ht₁, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (cE.w _)]
    exact ht₀ m k
  -- the products of the boundary coordinates
  let f₁ : ∀ m, Γ(E.obj i₁, W₁ m) := fun m => ∏ k : Fin (C m).r, t₁ m (Fin.castLE (C m).hr k)
  let fX : ∀ m, Γ(cE.pt, (C m).W) := fun m => ∏ k : Fin (C m).r, (C m).t (Fin.castLE (C m).hr k)
  have hfX : ∀ m, ((cE.π.app i₁).appLE (W₁ m) ((C m).W : cE.pt.Opens) (hlim m).le).hom (f₁ m) =
      fX m := fun m => by simp only [f₁, fX, map_prod, hlimt]
  have hpreB : ∀ m, cE.π.app i₁ ⁻¹ᵁ (E.obj i₁).basicOpen (f₁ m) = cE.pt.basicOpen (fX m) := by
    intro m
    rw [← hfX m, Scheme.basicOpen_appLE]
    refine (inf_eq_right.mpr ?_).symm
    rw [hlim m]
    exact Scheme.Hom.preimage_mono _ ((E.obj i₁).basicOpen_le _)
  -- the overlap inclusions hold over the limit, hence at a stage
  have hover : ∀ p : κ × κ, ∃ (j : I) (ψ : j ⟶ i₁),
      E.map ψ ⁻¹ᵁ (((W₁ p.1 : (E.obj i₁).Opens) ⊓ W₁ p.2) ⊓ (E.obj i₁).basicOpen (f₁ p.2)) ≤
        E.map ψ ⁻¹ᵁ (E.obj i₁).basicOpen (f₁ p.1) := by
    rintro ⟨m, m'⟩
    have hcpt : IsCompact (X := E.obj i₁)
        ((((W₁ m : (E.obj i₁).Opens) ⊓ W₁ m') ⊓ (E.obj i₁).basicOpen (f₁ m') : (E.obj i₁).Opens) :
          Set (E.obj i₁)) := by
      have h1 := QuasiSeparatedSpace.inter_isCompact _ _ (W₁ m).1.isOpen (W₁ m).2.isCompact
        (W₁ m').1.isOpen (W₁ m').2.isCompact
      exact QuasiSeparatedSpace.inter_isCompact _ _ ((W₁ m).1 ⊓ (W₁ m').1).isOpen h1
        ((E.obj i₁).basicOpen (f₁ m')).isOpen ((W₁ m').2.basicOpen (f₁ m')).isCompact
    refine exists_map_preimage_le_map_preimage E cE hE hcpt ?_
    simp only [Scheme.Hom.preimage_inf, hpreB, ← hlim]
    intro x ⟨⟨hxm, hxm'⟩, hxb⟩
    by_contra hxn
    have hzero' : x ∉ ZX := by
      intro hxZ
      have : x ∈ ZX ∩ ((C m').W : Set cE.pt) := ⟨hxZ, hxm'⟩
      rw [(C m').zero] at this
      exact (Scheme.mem_zeroLocus_iff _ _ _).mp this.1 _ rfl hxb
    apply hzero'
    have : x ∈ cE.pt.zeroLocus (U := (C m).W) {fX m} ∩ ((C m).W : Set cE.pt) :=
      ⟨(Scheme.mem_zeroLocus_iff _ _ _).mpr (by rintro _ rfl; exact hxn), hxm⟩
    rw [← (C m).zero] at this
    exact this.1
  choose j ψ hψ using hover
  -- a common stage
  obtain ⟨i₂, hi₂⟩ := IsCofiltered.inf_objs_exists (insert i₁ (Finset.univ.image j))
  let φ₂ : i₂ ⟶ i₁ := (hi₂ (Finset.mem_insert_self _ _)).some
  let ψ₂ : ∀ p, i₂ ⟶ j p := fun p =>
    (hi₂ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ p)))).some
  -- the charts cover a later stage
  obtain ⟨i₃, ψ₃, hcov⟩ := exists_map_eq_top E cE hE
    (⨆ m, E.map φ₂ ⁻¹ᵁ (W₁ m : (E.obj i₁).Opens)) (by
      rw [Scheme.Hom.preimage_iSup, ← hC]
      refine iSup_congr fun m => ?_
      rw [hlim m, ← Scheme.Hom.comp_preimage, cE.w])
  let χ : i₃ ⟶ i₁ := ψ₃ ≫ φ₂
  choose W₃ hW₃ t₃ ht₃ hb₃ using fun m =>
    exists_stage_chart_transport g hst χ (W₁ m) (t₁ m) (C m).r (C m).hr (hb₁ m)
  let f₃ : ∀ m, Γ(E.obj i₃, W₃ m) := fun m => ∏ k : Fin (C m).r, t₃ m (Fin.castLE (C m).hr k)
  have hf₃ : ∀ m, ((E.map χ).appLE (W₁ m) (W₃ m) (hW₃ m).le).hom (f₁ m) = f₃ m := fun m => by
    simp only [f₁, f₃, map_prod, ht₃]
  have hB₃ : ∀ m, (E.obj i₃).basicOpen (f₃ m) = E.map χ ⁻¹ᵁ (E.obj i₁).basicOpen (f₁ m) := by
    intro m
    rw [← hf₃ m, Scheme.basicOpen_appLE]
    refine inf_eq_right.mpr ?_
    rw [hW₃ m]
    exact Scheme.Hom.preimage_mono _ ((E.obj i₁).basicOpen_le _)
  have hover₃ : ∀ m m', ((W₃ m : (E.obj i₃).Opens) ⊓ W₃ m') ⊓ (E.obj i₃).basicOpen (f₃ m') ≤
      (E.obj i₃).basicOpen (f₃ m) := by
    intro m m'
    have hχ : χ = (ψ₃ ≫ ψ₂ (m, m')) ≫ ψ (m, m') := Subsingleton.elim _ _
    rw [hB₃, hB₃, hW₃, hW₃, ← Scheme.Hom.preimage_inf, ← Scheme.Hom.preimage_inf, hχ,
      Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ (hψ (m, m'))
  have hlim₃ : ∀ m, ((C m).W : cE.pt.Opens) = cE.π.app i₃ ⁻¹ᵁ (W₃ m : (E.obj i₃).Opens) := by
    intro m
    rw [hW₃ m, ← Scheme.Hom.comp_preimage, cE.w, ← hlim m]
  have hfX₃ : ∀ m, ((cE.π.app i₃).appLE (W₃ m) ((C m).W : cE.pt.Opens) (hlim₃ m).le).hom (f₃ m) =
      fX m := by
    intro m
    rw [← hf₃ m, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (cE.w χ)]
    exact hfX m
  have hpre : ∀ m, (cE.π.app i₃).base ⁻¹' ((E.obj i₃).zeroLocus (U := W₃ m) {f₃ m}) =
      cE.pt.zeroLocus (U := (C m).W) {fX m} := by
    intro m
    rw [preimage_zeroLocus_singleton _ _ _ (hlim₃ m), hfX₃]
  refine ⟨i₃, ⋂ m, (E.obj i₃).zeroLocus (U := W₃ m) {f₃ m},
    isClosed_iInter fun m => (E.obj i₃).zeroLocus_isClosed _, ?_,
    fun m => ⟨W₃ m, t₃ m, (C m).r, (C m).hr, hb₃ m, ?_⟩, ?_⟩
  · rw [Set.preimage_iInter]
    simp only [hpre]
    ext y
    constructor
    · intro hy
      have : y ∈ (⨆ m, ((C m).W : cE.pt.Opens)) := by rw [hC]; trivial
      obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      have h2 : y ∈ cE.pt.zeroLocus (U := (C m).W) {fX m} ∩ ((C m).W : Set cE.pt) :=
        ⟨Set.mem_iInter.mp hy m, hm⟩
      rw [← (C m).zero] at h2
      exact h2.1
    · intro hyZ
      refine Set.mem_iInter.mpr fun m => ?_
      by_cases hm : y ∈ ((C m).W : Set cE.pt)
      · have h2 : y ∈ ZX ∩ ((C m).W : Set cE.pt) := ⟨hyZ, hm⟩
        rw [(C m).zero] at h2
        exact h2.1
      · exact (Scheme.mem_zeroLocus_iff _ _ _).mpr fun _ _ hb => hm (cE.pt.basicOpen_le _ hb)
  · ext y
    constructor
    · rintro ⟨hyZ, hyW⟩
      exact ⟨Set.mem_iInter.mp hyZ m, hyW⟩
    · rintro ⟨hy0, hyW⟩
      refine ⟨Set.mem_iInter.mpr fun m' => (Scheme.mem_zeroLocus_iff _ _ _).mpr ?_, hyW⟩
      rintro _ rfl hb'
      have hb : y ∈ (E.obj i₃).basicOpen (f₃ m) :=
        hover₃ m m' ⟨⟨hyW, (E.obj i₃).basicOpen_le _ hb'⟩, hb'⟩
      exact (Scheme.mem_zeroLocus_iff _ _ _).mp hy0 _ rfl hb
  · change ⨆ m, ((W₃ m : (E.obj i₃).affineOpens) : (E.obj i₃).Opens) = ⊤
    simp only [hW₃]
    rw [← Scheme.Hom.preimage_iSup, show χ = ψ₃ ≫ φ₂ from rfl, Functor.map_comp,
      Scheme.Hom.comp_preimage, Scheme.Hom.preimage_iSup]
    exact hcov

/-- **An snc divisor of a smooth complex scheme has weak charts at every point.** -/
public theorem exists_weakChart_of_isRelativeSNC {n : ℕ} {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] {D : MMP.Mori.Divisor X}
    (hD : D.IsRelativeSNC n π) (x : X) :
    ∃ c : WeakChart π n (D.supp : Set X), x ∈ (c.W : X.Opens) := by
  obtain ⟨W, ⟨V, hVa⟩, e, t, hx, hb, r, hr, -, -, -, hDW⟩ := hD.2 x
  have hV : V = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have : y = π.base x := Subsingleton.elim _ _
    rw [this]
    exact e hx
  subst hV
  refine ⟨⟨W, t, r, hr, hb, ?_⟩, hx⟩
  rw [← MMP.Mori.DivisorWithCoeffs.coe_support_suppIdeal,
    Scheme.IdealSheafData.coe_support_inter, hDW, Scheme.zeroLocus_span]

/-- **Finitely many weak charts cover a compact smooth complex scheme with an snc divisor.** -/
private theorem exists_finite_weakCharts {n : ℕ} {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] [CompactSpace X]
    {D : MMP.Mori.Divisor X} (hD : D.IsRelativeSNC n π) :
    ∃ (κ : Type) (_ : Finite κ) (C : κ → WeakChart π n (D.supp : Set X)),
      ⨆ m, ((C m).W : X.Opens) = ⊤ := by
  classical
  choose c hc using exists_weakChart_of_isRelativeSNC π hD
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => ((c x).W : Set X))
    (fun x => (c x).W.1.isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hc x⟩)
  refine ⟨s, inferInstance, fun m => c m.1, eq_top_iff.mpr fun y _ => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩

section StageSystem

variable {J : Type} [Category.{0} J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j₀ : J) (Y : Over (D.obj j₀))

/-- The transition squares of the base change of a diagram along a morphism into a stage are
cartesian. -/
private theorem stageBaseChangeDiagram_isPullback {k k' : Over j₀} (φ : k ⟶ k') :
    IsPullback ((stageBaseChangeDiagram D j₀ Y).map φ) (pullback.fst (D.map k.hom) Y.hom)
      (pullback.fst (D.map k'.hom) Y.hom) (D.map φ.left) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (D.map k'.hom) Y.hom).flip
  rw [pullback.lift_snd, ← D.map_comp, Over.w φ]
  exact (IsPullback.of_hasPullback (D.map k.hom) Y.hom).flip

end StageSystem

/-- The spectrum of an injective ring map is injective on global sections. -/
private theorem appLE_top_injective_of_injective {R S : CommRingCat.{0}} (f : R ⟶ S)
    (hf : Function.Injective f.hom) :
    Function.Injective ((Spec.map f).appLE ⊤ ⊤ le_top).hom := by
  have h : (Spec.map f).appLE ⊤ ⊤ le_top = (Spec.map f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h]
  have h1 := Scheme.ΓSpecIso_naturality f
  intro x y hxy
  have h2 := congrArg (Scheme.ΓSpecIso S).hom.hom hxy
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, h1, CommRingCat.comp_apply,
    CommRingCat.comp_apply] at h2
  exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective (hf h2)

/-- **A projective smooth snc pair over `ℂ` has a projective smooth model with covering weak
charts over a finitely generated subring.** -/
private theorem exists_stage_model (n : ℕ) {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] (hπ : IsProjective π) (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n π) :
    ∃ (k : (Finset ℂ)ᵒᵖ) (𝒳 : Scheme.{0}) (g : 𝒳 ⟶ (specAdjoinFinsetDiagram ℂ).obj k)
      (q : X ⟶ 𝒳), IsProjective g ∧ SmoothOfRelativeDimension n g ∧
        IsPullback q π g ((specAdjoinFinsetCone ℂ).π.app k) ∧
        ∃ Z : Set 𝒳, IsClosed Z ∧ q.base ⁻¹' Z = (D.supp : Set X) ∧
          ∃ (κ : Type) (_ : Finite κ) (C : κ → WeakChart g n Z), ⨆ m, ((C m).W : 𝒳.Opens) = ⊤ := by
  classical
  obtain ⟨j₀, 𝒴, h, q, hproj, hsm, hpb⟩ := exists_projective_smooth_model n π hπ
  haveI : IsProper π := hπ.isProper
  haveI : IsProper h := hproj.isProper
  haveI : Smooth h := SmoothOfRelativeDimension.smooth n h
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨κ, _, CX, hCX⟩ := exists_finite_weakCharts π hD
  let Dg := specAdjoinFinsetDiagram ℂ
  let c := specAdjoinFinsetCone ℂ
  have hc : IsLimit c := isLimit_specAdjoinFinsetCone ℂ
  let Y : Over (Dg.obj j₀) := Over.mk h
  let E := stageBaseChangeDiagram Dg j₀ Y
  let cE := stageBaseChangeCone Dg c j₀ Y
  have hE : IsLimit cE := stageBaseChangeConeIsLimit Dg c hc j₀ Y
  let ε : X ≅ cE.pt := hpb.flip.isoPullback
  let cX : Cone E := cE.extend ε.hom
  have hX : IsLimit cX := IsLimit.ofIsoLimit hE (Cone.extendIso cE ε.symm)
  let g : E ⟶ Over.forget j₀ ⋙ Dg := stageBaseChangeDiagramι Dg j₀ Y
  haveI : Quiver.IsThin (Over j₀) := fun a b => ⟨fun f₁ f₂ => Over.OverMorphism.ext
    (Subsingleton.elim _ _)⟩
  haveI : ∀ {k k' : Over j₀} (φ : k ⟶ k'), IsAffineHom (E.map φ) :=
    fun φ => stageBaseChangeDiagram_map_isAffineHom Dg j₀ Y φ
  have hpf : ∀ k : Over j₀, IsProper (pullback.fst (Dg.map k.hom) h) := fun k =>
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Dg.map k.hom) h).flip inferInstance
  have hsf : ∀ k : Over j₀, Smooth (pullback.fst (Dg.map k.hom) h) := fun k =>
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (Dg.map k.hom) h).flip inferInstance
  haveI : ∀ k : Over j₀, Smooth (g.app k) := hsf
  haveI : ∀ k : Over j₀, IsAffine ((Over.forget j₀ ⋙ Dg).obj k) := fun k =>
    (inferInstance : IsAffine (Dg.obj k.left))
  have hcs : ∀ k : Over j₀, CompactSpace ↥(pullback (Dg.map k.hom) h : Scheme.{0}) := fun k => by
    haveI := hpf k
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (Dg.map k.hom) h)
  have hqs : ∀ k : Over j₀, QuasiSeparatedSpace ↥(pullback (Dg.map k.hom) h : Scheme.{0}) := fun k => by
    haveI := hpf k
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Dg.map k.hom) h)
  haveI : ∀ k : Over j₀, CompactSpace (E.obj k) := hcs
  haveI : ∀ k : Over j₀, QuasiSeparatedSpace (E.obj k) := hqs
  have hsq : ∀ k, IsPullback (cX.π.app k) π (g.app k) ((c.whisker (Over.forget j₀)).π.app k) := by
    intro k
    have e1 : cX.π.app k ≫ pullback.snd (Dg.map k.hom) h = q := by
      change ε.hom ≫ pullback.lift _ _ _ ≫ pullback.snd (Dg.map k.hom) h = q
      rw [pullback.lift_snd]
      exact hpb.flip.isoPullback_hom_snd
    have e2 : cX.π.app k ≫ pullback.fst (Dg.map k.hom) h = π ≫ c.π.app k.left := by
      change ε.hom ≫ pullback.lift _ _ _ ≫ pullback.fst (Dg.map k.hom) h = _
      rw [pullback.lift_fst, ← Category.assoc]
      congr 1
      exact hpb.flip.isoPullback_hom_fst
    have hw : c.π.app k.left ≫ Dg.map k.hom = c.π.app j₀ := c.w k.hom
    refine IsPullback.of_right (h₁₂ := pullback.snd (Dg.map k.hom) h) (v₁₃ := h)
      (h₂₂ := Dg.map k.hom) ?_ e2 (IsPullback.of_hasPullback (Dg.map k.hom) h).flip
    rw [e1]
    exact (congrArg (IsPullback q π h) hw).mpr hpb
  have hst : ∀ {k k' : Over j₀} (φ : k ⟶ k'),
      IsPullback (E.map φ) (g.app k) (g.app k') ((Over.forget j₀ ⋙ Dg).map φ) :=
    fun φ => stageBaseChangeDiagram_isPullback Dg j₀ Y φ
  have hinj : ∀ k : Over j₀,
      Function.Injective (((c.whisker (Over.forget j₀)).π.app k).appLE ⊤ ⊤ le_top).hom :=
    fun k => appLE_top_injective_of_injective _ Subtype.val_injective
  haveI : IsAffine (c.whisker (Over.forget j₀)).pt := (inferInstance : IsAffine (Spec (CommRingCat.of ℂ)))
  obtain ⟨k, Z, hZc, hZpre, C', hC'⟩ := exists_stage_weakCharts g hX hsq hst hinj CX hCX
  have hpbk := IsPullback.of_hasPullback (Dg.map k.hom) h
  exact ⟨k.left, E.obj k, g.app k, cX.π.app k, IsProjective.of_isPullback hpbk hproj,
    smoothOfRelativeDimension_of_isPullback hpbk.flip, hsq k, Z, hZc, hZpre, κ, inferInstance, C',
    hC'⟩

/-- **Generic smoothness over `ℤ`**: a domain of characteristic zero of finite type over `ℤ`,
embedded in `ℂ`, becomes smooth over `ℤ` after inverting one nonzero element. -/
private theorem exists_smooth_localization (R₀ : Type) [CommRing R₀] [IsDomain R₀] [CharZero R₀]
    [Algebra.FiniteType ℤ R₀] (ι₀ : R₀ →+* ℂ) (hι₀ : Function.Injective ι₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.Smooth ℤ R) (a : R₀ →+* R)
      (ι : R →+* ℂ), Function.Injective ι ∧ ι.comp a = ι₀ := by
  haveI : Algebra.FinitePresentation ℤ R₀ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have h0 := AlgebraicGeometry.HodgeSpreadingOut.mem_smoothLocus_int_bot R₀
  obtain ⟨_, ⟨s, rfl⟩, h0s, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h0
      Algebra.isOpen_smoothLocus
  have hs : s ≠ 0 := by
    intro h
    simp [h, PrimeSpectrum.basicOpen] at h0s
  have hfs : Algebra.FormallySmooth ℤ (Localization.Away s) :=
    Algebra.basicOpen_subset_smoothLocus_iff.mp hsub
  haveI : Algebra.FinitePresentation R₀ (Localization.Away s) :=
    IsLocalization.Away.finitePresentation s
  haveI : Algebra.FinitePresentation ℤ (Localization.Away s) :=
    Algebra.FinitePresentation.trans ℤ R₀ (Localization.Away s)
  have hι₀s : IsUnit (ι₀ s) := ((map_ne_zero_iff _ hι₀).mpr hs).isUnit
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hsm : @Algebra.Smooth ℤ _ (Localization.Away s) _ (Ring.toIntAlgebra _) := by
    convert (⟨hfs, inferInstance⟩ : Algebra.Smooth ℤ (Localization.Away s))
    all_goals exact Subsingleton.elim _ _
  refine ⟨Localization.Away s, inferInstance, inferInstance, hsm, algebraMap R₀ _,
    IsLocalization.Away.lift s hι₀s, ?_, IsLocalization.lift_comp _⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'] at hz
  have hx : ι₀ x = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (Units.ne_zero _)
  rw [(map_eq_zero_iff _ hι₀).mp hx]
  exact IsLocalization.mk'_zero _

/-- **Spreading out.** -/
public theorem exists_model (n : ℕ) {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of ℂ))
    [SmoothOfRelativeDimension n π] (hπ : IsProjective π) (D : MMP.Mori.Divisor X)
    (hD : D.IsRelativeSNC n π) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : Algebra.Smooth ℤ R₀)
      (ι₀ : R₀ →+* ℂ) (_ : Function.Injective ι₀) (𝒳₀ : Scheme.{0})
      (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) (_ : SmoothOfRelativeDimension n g₀)
      (_ : IsProjective g₀) (q₀ : X ⟶ 𝒳₀)
      (_ : IsPullback q₀ π g₀ (Spec.map (CommRingCat.ofHom ι₀))) (Z₀ : Set 𝒳₀),
      IsClosed Z₀ ∧ q₀.base ⁻¹' Z₀ = (D.supp : Set X) ∧
      ∃ (ι : Type) (_ : Finite ι) (C : ι → WeakChart g₀ n Z₀),
        ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤ := by
  obtain ⟨k, 𝒳, g, q, hproj, hsm, hsq, Z, hZc, hZpre, κ, hκ, C, hC⟩ :=
    exists_stage_model n π hπ D hD
  let A := Algebra.adjoin ℤ ((k.unop : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℤ A := finiteType_adjoinFinset_int ℂ k.unop
  let ιA : A →+* ℂ := A.val.toRingHom
  have hιA : Function.Injective ιA := Subtype.val_injective
  haveI : CharZero A := ⟨fun a b hab => by
    have := congrArg ιA hab
    simpa using this⟩
  obtain ⟨R, iR, dR, sR, a, ι, hι, hιcomp⟩ := exists_smooth_localization A ιA hιA
  let gR : Spec (CommRingCat.of R) ⟶ (specAdjoinFinsetDiagram ℂ).obj k :=
    Spec.map (CommRingCat.ofHom a)
  have hw : Spec.map (CommRingCat.ofHom ι) ≫ gR = (specAdjoinFinsetCone ℂ).π.app k := by
    change Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom ιA)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hιcomp]
  have hsqR := IsPullback.of_hasPullback g gR
  haveI := hsm
  refine ⟨R, iR, dR, sR, ι, hι, pullback g gR, pullback.snd g gR,
    smoothOfRelativeDimension_of_isPullback hsqR, IsProjective.of_isPullback hsqR.flip hproj,
    _, isPullback_pullbackLift_of_comp hsq hw, (pullback.fst g gR).base ⁻¹' Z,
    hZc.preimage (pullback.fst g gR).base.hom.continuous, ?_, ?_⟩
  · rw [← Set.preimage_comp, ← hZpre]
    change ((pullback.lift q _ _ ≫ pullback.fst g gR).base) ⁻¹' Z = _
    rw [pullback.lift_fst]
  · choose C' hC'W _ _ _ using fun m => (C m).exists_baseChange hsqR
    refine ⟨κ, hκ, C', ?_⟩
    simp only [hC'W]
    rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, hC]
    exact le_antisymm le_top (le_inf le_top fun _ _ => trivial)

end SpreadingOut

/-- **Base change of the snc structure** to a regular base. -/
public theorem exists_isRelativeSNC_of_isPullback (n : ℕ) {R₀ : Type} [CommRing R₀]
    {A : CommRingCat.{0}} [IsRegularRing A] (φ : CommRingCat.of R₀ ⟶ A) {𝒳₀ Y : Scheme.{0}}
    (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀] [IsProper g₀]
    (Z₀ : Set 𝒳₀) (hZ₀ : IsClosed Z₀) {ι : Type} [Finite ι] (C : ι → WeakChart g₀ n Z₀)
    (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)
    (f : Y ⟶ Spec A) [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀)
    (hsq : IsPullback q f g₀ (Spec.map φ)) :
    ∃ DY : MMP.Mori.Divisor Y, DY.IsRelativeSNC n f ∧ (DY.supp : Set Y) = q.base ⁻¹' Z₀ := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hC' : ∀ i, ∃ c' : WeakChart f n (q.base ⁻¹' Z₀),
      (c'.W : Y.Opens) = q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) ⊓ f ⁻¹ᵁ ⊤ ∧ c'.r = (C i).r :=
    fun i => let ⟨c', h1, h2, _⟩ := (C i).exists_baseChange hsq; ⟨c', h1, h2⟩
  choose C' hC'W hC'r using hC'
  have hZc : IsClosed (q.base ⁻¹' Z₀) := hZ₀.preimage q.base.hom.continuous
  have hcov : ∀ y : Y, ∃ i, y ∈ ((C' i).W : Set Y) := by
    intro y
    have : q.base y ∈ (⨆ i, ((C i).W : 𝒳₀.Opens)) := by rw [hC]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨i, ?_⟩
    change y ∈ ((C' i).W : Y.Opens)
    rw [hC'W]
    exact ⟨hi, trivial⟩
  -- the prime divisors whose generic point lies in `Z`
  set Pset : Set (MMP.Mori.PrimeDivisor Y) :=
    {E | AlgebraicGeometry.PrimeDivisor.genericPoint E ∈ q.base ⁻¹' Z₀}
  have hPsetfin : Pset.Finite := by
    let G : Set Y := ⋃ i, ⋃ k : Fin (C' i).r, (C' i).W.2.fromSpec ''
      {𝔮 : PrimeSpectrum Γ(Y, (C' i).W) |
        𝔮.asIdeal ∈ (Ideal.span {(C' i).t (Fin.castLE (C' i).hr k)}).minimalPrimes}
    have hGfin : G.Finite := by
      refine Set.finite_iUnion fun i => Set.finite_iUnion fun k => Set.Finite.image _ ?_
      haveI := isNoetherianRing_Γ_of_smooth f (C' i).W
      exact (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).preimage
        (fun a _ b _ h => PrimeSpectrum.ext h)
    refine Set.Finite.of_finite_image (hGfin.subset ?_)
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
    rintro _ ⟨E, hE, rfl⟩
    obtain ⟨i, hi⟩ := hcov (AlgebraicGeometry.PrimeDivisor.genericPoint E)
    obtain ⟨𝔮, ⟨k, hk⟩, hsp, hcoh, -⟩ := exists_coheight_one_specializes f (C' i) _ hE hi
    have := eq_of_specializes_of_coheight_eq_one hsp hcoh
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, ⟨𝔮, hk, this⟩⟩⟩
  set F := hPsetfin.toFinset
  set DY : MMP.Mori.Divisor Y := ∑ E ∈ F, Finsupp.single E (1 : ℤ)
  have hDY : ∀ E, DY E = if E ∈ F then 1 else 0 := by
    intro E
    simp only [DY, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hsupport : DY.support = F := by
    ext E
    rw [Finsupp.mem_support_iff, hDY]
    split_ifs with h <;> simp [h]
  have hsupp : (DY.supp : Set Y) = q.base ⁻¹' Z₀ := by
    have h1 : (DY.supp : Set Y) = ⋃ E ∈ F, (AlgebraicGeometry.PrimeDivisor.support E) := by
      rw [MMP.Mori.DivisorWithCoeffs.supp, hsupport, TopologicalSpace.Closeds.coe_finset_sup,
        Finset.sup_set_eq_biUnion]
      rfl
    rw [h1]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨E, hE, hzE⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hzE
      refine closure_minimal ?_ hZc hzE
      rw [Set.singleton_subset_iff]
      exact (Set.Finite.mem_toFinset hPsetfin).mp hE
    · intro hz
      obtain ⟨i, hi⟩ := hcov z
      obtain ⟨𝔮, -, hsp, hcoh, hξZ⟩ := exists_coheight_one_specializes f (C' i) z hz hi
      refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, ?_⟩
      · rw [Set.Finite.mem_toFinset]
        change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ q.base ⁻¹' Z₀
        rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      · rwa [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
          ← specializes_iff_mem_closure]
  have hcomp : ∀ ξ : Y, ξ ∈ (DY.supp : Set Y) → Order.coheight ξ = 1 →
      ∃ E ∈ DY.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ := by
    intro ξ hξ hcoh
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh, ?_,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne ξ hcoh⟩
    rw [hsupport, Set.Finite.mem_toFinset]
    change AlgebraicGeometry.PrimeDivisor.genericPoint _ ∈ q.base ⁻¹' Z₀
    rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, ← hsupp]
  refine ⟨DY, ?_, hsupp⟩
  unfold MMP.Mori.Divisor.IsRelativeSNC
  refine ⟨fun E hE => ?_, fun y => ?_⟩
  · rw [hDY, if_pos (hsupport ▸ hE)]
  · obtain ⟨i, hi⟩ := hcov y
    exact exists_snc_chart f DY hcomp ((C' i).ofEq hsupp.symm) y hi

/-- Every point of coheight one of the support of a divisor is the generic point of one of its
prime components. -/
public theorem exists_mem_support_genericPoint_eq {Y : Scheme.{0}} (D : MMP.Mori.Divisor Y)
    (ξ : Y) (hξ : ξ ∈ (D.supp : Set Y)) (hcoh : Order.coheight ξ = 1) :
    ∃ E ∈ D.support, AlgebraicGeometry.PrimeDivisor.genericPoint E = ξ := by
  have h1 : (D.supp : Set Y) = ⋃ E ∈ D.support, (AlgebraicGeometry.PrimeDivisor.support E) := by
    rw [MMP.Mori.DivisorWithCoeffs.supp, TopologicalSpace.Closeds.coe_finset_sup,
      Finset.sup_set_eq_biUnion]
    rfl
  rw [h1] at hξ
  simp only [Set.mem_iUnion] at hξ
  obtain ⟨E, hE, hξE⟩ := hξ
  refine ⟨E, hE, eq_of_specializes_of_coheight_eq_one ?_
    (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E) hcoh⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hξE
  exact specializes_iff_mem_closure.mpr hξE

section FibreAssembly

/-- Chart pairs for a base change to a field. -/
public theorem exists_chartPairs (n : ℕ) {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
    {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀]
    (𝒟₀ : MMP.Mori.Divisor 𝒳₀) (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type}
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (K : CommRingCat.{0}) [IsRegularRing K]
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀)) :
    ∃ pr : ι → ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
      ∀ i, ((pr i).c.W : 𝒳₀.Opens) = (C i).W ∧
        ((pr i).c'.W : Y.Opens) = q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) := by
  choose c' hW hr hle ht using fun i => (C i).exists_baseChange H
  refine ⟨fun i =>
    { c := (C i).toLogChart g₀ 𝒟₀ h𝒟₀ (exists_mem_support_genericPoint_eq 𝒟₀)
      c' := ((c' i).ofEq hsupp.symm).toLogChart f DY hDY (exists_mem_support_genericPoint_eq DY)
      hWc := hle i
      ht := ht i
      hr := hr i
      hs := WeakChart.toLogData_hs g₀ 𝒟₀ (C i)
      hs' := WeakChart.toLogData_hs f DY ((c' i).ofEq hsupp.symm) }, fun i => ⟨rfl, ?_⟩⟩
  show ((c' i).W : Y.Opens) = _
  rw [hW i]
  exact le_antisymm inf_le_left (le_inf le_rfl fun _ _ => trivial)

/-- The cover data of the charts of `𝒳₀` and their pullbacks to `Y`. -/
public theorem chartPairs_cover {n : ℕ} {R₀ : Type} [CommRing R₀]
    {𝒳₀ : Scheme.{0}} {g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)} [SmoothOfRelativeDimension n g₀]
    [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀} {h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀} {ι : Type}
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)
    {K : CommRingCat.{0}} {φ : CommRingCat.of R₀ ⟶ K} {Y : Scheme.{0}} {f : Y ⟶ Spec K}
    [SmoothOfRelativeDimension n f] {q : Y ⟶ 𝒳₀} (H : IsPullback q f g₀ (Spec.map φ))
    {DY : MMP.Mori.Divisor Y} {hDY : DY.IsRelativeSNC n f}
    (pr : ι → ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY)
    (hpr : ∀ i, ((pr i).c.W : 𝒳₀.Opens) = (C i).W ∧
      ((pr i).c'.W : Y.Opens) = q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens)) :
    (∀ y : Y, ∃ pr' : ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
      q.base y ∈ (pr'.c.W : 𝒳₀.Opens) ∧ y ∈ (pr'.c'.W : Y.Opens)) ∧
    ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      IsAffineOpen (Stacks.CategoryTheory.CechComplex.inter (fun i => ((C i).W : 𝒳₀.Opens)) t) ∧
      IsAffineOpen (q ⁻¹ᵁ Stacks.CategoryTheory.CechComplex.inter
        (fun i => ((C i).W : 𝒳₀.Opens)) t) ∧
      ∃ pr' : ChartPair (DX := 𝒟₀) (DY := DY) (q := q) h𝒟₀ hDY,
        Stacks.CategoryTheory.CechComplex.inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤ pr'.c.W ∧
        q ⁻¹ᵁ Stacks.CategoryTheory.CechComplex.inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤
          pr'.c'.W := by
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper g₀
  refine ⟨fun y => ?_, fun p t => ?_⟩
  · have : q.base y ∈ (⨆ i, ((C i).W : 𝒳₀.Opens)) := by rw [hC]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨pr i, (hpr i).1 ▸ hi, ?_⟩
    rw [(hpr i).2]
    exact hi
  · have he := Stacks.CategoryTheory.CechComplex.inter_eq_iInf (fun i => ((C i).W : 𝒳₀.Opens)) t
    have haff : IsAffineOpen
        (Stacks.CategoryTheory.CechComplex.inter (fun i => ((C i).W : 𝒳₀.Opens)) t) := by
      rw [he]
      exact IsAffineOpen.iInf fun a => (C (t a)).W.2
    have hle : Stacks.CategoryTheory.CechComplex.inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤
        (C (t 0)).W := by
      rw [he]
      exact iInf_le _ 0
    refine ⟨haff, haff.preimage q, pr (t 0), (hpr (t 0)).1 ▸ hle, ?_⟩
    rw [(hpr (t 0)).2]
    exact fun _ h => hle h

section Terms

open scoped ZeroObject

variable {n : ℕ} {Y T : Scheme.{0}} (f : Y ⟶ T) [SmoothOfRelativeDimension n f]
  {D : MMP.Mori.Divisor Y} (hD : D.IsRelativeSNC n f)

/-- The pushforward of the zero module to `h⁻¹𝒪_T`-modules is zero. -/
public theorem isZero_pushforward_zero :
    IsZero ((pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj (0 : Y.Modules)) :=
  (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).map_isZero (isZero_zero _)

/-- The terms of the logarithmic de Rham complex extended by zero are quasi-coherent, and
coherent over a locally Noetherian scheme. -/
public theorem exists_deRhamCx_X (ε : Bool) (k : ℤ) :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧ (IsLocallyNoetherian Y → M.IsCoherent) ∧
      Nonempty ((deRhamCx n f D hD ε).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) := by
  rcases lt_or_ge k 0 with hk | hk
  · have hz : IsZero ((deRhamCx n f D hD ε).1.X k) :=
      HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat k (fun i => by
        change ((i : ℕ) : ℤ) ≠ k; omega)
    have h0 := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Y.Modules))
    exact ⟨0, _root_.isQuasicoherent_of_isCoherent _, fun _ => h0,
      ⟨hz.iso (isZero_pushforward_zero f)⟩⟩
  · obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact ⟨logModule n f D hD (bif ε then D.suppIdeal else ⊤) b, logModule_isQuasicoherent hD ε b,
      fun _ => logModule_isCoherent hD ε b,
      ⟨HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f b) ≪≫ (exists_iso_relativeLogDeRhamComplex_X hD ε b).some⟩⟩

/-- The terms of the logarithmic forms placed in degree `0` are quasi-coherent, and coherent
over a locally Noetherian scheme. -/
public theorem exists_hodgeCx_X (ε : Bool) (p : ℕ) (k : ℤ) :
    ∃ M : Y.Modules, M.IsQuasicoherent ∧ (IsLocallyNoetherian Y → M.IsCoherent) ∧
      Nonempty ((hodgeCx n f D hD ε p).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) := by
  by_cases hk : k = 0
  · subst hk
    exact ⟨logModule n f D hD (bif ε then D.suppIdeal else ⊤) p, logModule_isQuasicoherent hD ε p,
      fun _ => logModule_isCoherent hD ε p,
      ⟨HomologicalComplex.singleObjXSelf _ 0 _ ≪≫ (exists_iso_relativeLogDeRhamComplex_X hD ε p).some⟩⟩
  · have hz : IsZero ((hodgeCx n f D hD ε p).1.X k) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hk
    have h0 := Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (isZero_zero (Y.Modules))
    exact ⟨0, _root_.isQuasicoherent_of_isCoherent _, fun _ => h0,
      ⟨hz.iso (isZero_pushforward_zero f)⟩⟩

end Terms

section HcIdentification

attribute [local instance] secCommRing

variable {n : ℕ} {Y T X : Scheme.{0}} (f : Y ⟶ T) [SmoothOfRelativeDimension n f]
  {D : MMP.Mori.Divisor Y} (hD : D.IsRelativeSNC n f) (q : Y ⟶ X) {ι : Type}
  (U : ι → X.Opens) (hU : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ U i)
  [IsAffineHom (pullback.diagonal (terminal.from Y))] (hUaff : ∀ i, IsAffineOpen (q ⁻¹ᵁ U i))

include hU hUaff in
/-- **The logarithmic de Rham hypercohomology by the concrete total Čech complex**: for an
affine cover of `Y` pulled back along `q` from opens of `X`, `ℍ^{i+1}(Ω^•(log D))` (twisted by
`ε`) is the cohomology of the total Čech complex of `logCx` over the opens of `X`, read over
`Γ(T, ⊤)`. -/
public theorem nonempty_hc_deRhamCx_equiv (ε : Bool) (i : ℤ) :
    haveI := preservesFiniteProducts_opensMap q.base
    Nonempty (Hc f (deRhamCx n f D hD ε) (i + 1) ≃ₗ[Γ(T, ⊤)]
      homologyAt (Stacks.CategoryTheory.CechComplex.totD U
          (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            (siteCx f (Opens.map q.base) (logCx hD ε))) i)
        (Stacks.CategoryTheory.CechComplex.totD U
          (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            (siteCx f (Opens.map q.base) (logCx hD ε))) (i + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  have hcd := exists_extend_cechData f (Opens.map q.base)
    (MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤))
  obtain ⟨e, he, hz⟩ := hcd
  have hK : ∀ k, ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty ((deRhamCx n f D hD ε).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) :=
    fun k => let ⟨M, h1, _, h2⟩ := exists_deRhamCx_X f hD ε k; ⟨M, h1, h2⟩
  have E := nonempty_hcEquivHomologyAt f (Opens.map q.base) U hU hUaff (deRhamCx n f D hD ε)
    hK _ e hz he i
  obtain ⟨E⟩ := E
  have key : ∀ L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)) ℕ, L = logCx hD ε →
      (Hc f (deRhamCx n f D hD ε) (i + 1) ≃ₗ[Γ(T, ⊤)] homologyAt
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)).map
          ((Stacks.CategoryTheory.CechComplex.cechTot U (siteCx f (Opens.map q.base) L)).d i
            (i + 1))).hom
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)).map
          ((Stacks.CategoryTheory.CechComplex.cechTot U (siteCx f (Opens.map q.base) L)).d (i + 1)
            (i + 1 + 1))).hom) →
      Nonempty (Hc f (deRhamCx n f D hD ε) (i + 1) ≃ₗ[Γ(T, ⊤)]
        homologyAt (Stacks.CategoryTheory.CechComplex.totD U
            (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
              (siteCx f (Opens.map q.base) (logCx hD ε))) i)
          (Stacks.CategoryTheory.CechComplex.totD U
            (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
              (siteCx f (Opens.map q.base) (logCx hD ε))) (i + 1))) := by
    rintro L rfl E
    exact ⟨E.trans (homologyAtResCxEquiv U
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      (siteCx f (Opens.map q.base) (logCx hD ε)) i)⟩
  exact key _ (relativeLogDeRhamComplex_eq_logCx hD ε) E

include hU hUaff in
/-- **The logarithmic Hodge cohomology by the concrete total Čech complex**: for an affine cover
of `Y` pulled back along `q` from opens of `X`, `H^{i+1}(Ω^p(log D))` (twisted by `ε`) is the
cohomology of the total Čech complex of `Ω^p(log D)` in degree `0` over the opens of `X`. -/
public theorem nonempty_hc_hodgeCx_equiv (ε : Bool) (p : ℕ) (i : ℤ) :
    haveI := preservesFiniteProducts_opensMap q.base
    Nonempty (Hc f (hodgeCx n f D hD ε p) (i + 1) ≃ₗ[Γ(T, ⊤)]
      homologyAt (Stacks.CategoryTheory.CechComplex.totD U
          (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx hD ε).X p)))) i)
        (Stacks.CategoryTheory.CechComplex.totD U
          (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj ((logCx hD ε).X p)))) (i + 1))) := by
  haveI := preservesFiniteProducts_opensMap q.base
  have hcd := exists_single_cechData f (Opens.map q.base)
    ((MMP.Mori.Divisor.relativeLogDeRhamComplex n f D hD (bif ε then D.suppIdeal else ⊤)).X p)
  obtain ⟨e, he, hz⟩ := hcd
  have hK : ∀ k, ∃ M : Y.Modules, M.IsQuasicoherent ∧
      Nonempty ((hodgeCx n f D hD ε p).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase f)).obj M) :=
    fun k => let ⟨M, h1, _, h2⟩ := exists_hodgeCx_X f hD ε p k; ⟨M, h1, h2⟩
  have E := nonempty_hcEquivHomologyAt f (Opens.map q.base) U hU hUaff (hodgeCx n f D hD ε p)
    hK _ e hz he i
  obtain ⟨E⟩ := E
  have key : ∀ L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing f)) ℕ, L = logCx hD ε →
      (Hc f (hodgeCx n f D hD ε p) (i + 1) ≃ₗ[Γ(T, ⊤)] homologyAt
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)).map
          ((Stacks.CategoryTheory.CechComplex.cechTot U
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj (L.X p)))).d i (i + 1))).hom
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)).map
          ((Stacks.CategoryTheory.CechComplex.cechTot U
            ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
              ((siteSections f (Opens.map q.base)).obj (L.X p)))).d (i + 1) (i + 1 + 1))).hom) →
      Nonempty (Hc f (hodgeCx n f D hD ε p) (i + 1) ≃ₗ[Γ(T, ⊤)]
        homologyAt (Stacks.CategoryTheory.CechComplex.totD U
            (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
              ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
                ((siteSections f (Opens.map q.base)).obj ((logCx hD ε).X p)))) i)
          (Stacks.CategoryTheory.CechComplex.totD U
            (resCx (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
              ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
                ((siteSections f (Opens.map q.base)).obj ((logCx hD ε).X p)))) (i + 1))) := by
    rintro L rfl E
    exact ⟨E.trans (homologyAtResCxEquiv U
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom f)
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        ((siteSections f (Opens.map q.base)).obj ((logCx hD ε).X p))) i)⟩
  exact key _ (relativeLogDeRhamComplex_eq_logCx hD ε) E

end HcIdentification

section TotHomotopy

open Stacks.CategoryTheory.CechComplex Stacks.CategoryTheory.CechComplex.CochainSorting

variable {Z : TopCat.{0}} {ι : Type} [Finite ι] (U : ι → TopologicalSpace.Opens Z)
  {R : Type} [CommRing R] (P : CochainComplex ((TopologicalSpace.Opens Z)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ)

/-- The total Čech complex vanishes in negative degrees. -/
public theorem subsingleton_totX_of_neg (i : ℤ) (hi : i < 0) : Subsingleton (TotX U P i) := by
  haveI : IsEmpty (TotIndex i) := ⟨fun j => by have := j.2; omega⟩
  infer_instance

/-- **The total Čech complex of a bounded complex is contractible in high degrees**: if the
terms of `P` above degree `A` vanish on the Čech intersections, the sorting homotopy contracts
`Tot(Č(U, P))` in degrees `> #ι + A`. -/
public theorem exists_totHomotopy (A : ℕ)
    (hvan : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton ((P.X a).obj (op (inter U t)))) :
    ∃ h : ∀ j, TotX U P (j + 1) →ₗ[R] TotX U P j,
      ∀ j : ℤ, ((Nat.card ι + A : ℕ) : ℤ) ≤ j → ∀ x,
        totD U P j (h j x) + h (j + 1) (totD U P (j + 1) x) = x := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  letI : LinearOrder ι := LinearOrder.lift' e e.injective
  refine ⟨fun j => totHomotopyMap U P (j + 1) j rfl, fun j hj x => ?_⟩
  have key := totHomotopy_identity U P j (j + 1) (j + 1 + 1) rfl rfl x
  have hs : totSort U P (j + 1) x = 0 := by
    funext ⟨⟨p, a⟩, hpa⟩
    rw [totSort_apply]
    by_cases hp : Nat.card ι ≤ p
    · rw [sort_eq_zero U _ p hp]
      rfl
    · have ha : A < a := by
        simp only at hpa
        omega
      haveI : ∀ t : Fin (p + 1) → ι, Subsingleton ((P.X a).obj (op (inter U t))) :=
        hvan a ha p
      exact Subsingleton.elim _ _
  rw [hs, add_zero] at key
  exact (add_comm _ _).trans key

end TotHomotopy

section ZeroSide

open Stacks.CategoryTheory.CechComplex

/-- A finite product of flat modules is flat. -/
public theorem flat_pi' {R : Type} [CommRing R] {κ : Type} [Finite κ] {M : κ → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (h : ∀ i, Module.Flat R (M i)) :
    Module.Flat R (∀ i, M i) := by
  classical
  cases nonempty_fintype κ
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R κ M).symm

variable {n : ℕ} {X S : Scheme.{0}} {g : X ⟶ S} [SmoothOfRelativeDimension n g] [IsAffine S]
  {DX : MMP.Mori.Divisor X} (hDX : DX.IsRelativeSNC n g)

/-- On a chart affine the logarithmic forms are flat over the base. -/
public theorem flat_logComponent (ε : Bool) (a : ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (c : LogChart n g DX hDX) (hle : V ≤ c.W) :
    Module.Flat Γ(S, ⊤) (((logPresheafCx hDX ε).X a).obj (op V)) := by
  letI := (g.appLE ⊤ V le_top).hom.toAlgebra
  haveI : Smooth g := SmoothOfRelativeDimension.smooth n g
  haveI : Module.Flat Γ(S, ⊤) Γ(X, V) :=
    HasRingHomProperty.appLE @Flat g inferInstance ⟨⊤, isAffineOpen_top S⟩ ⟨V, hV⟩
      (fun _ _ => trivial)
  haveI : Module.Flat Γ(S, ⊤) ({K : Finset (Fin n) // K.card = a} → Γ(X, V)) :=
    flat_pi' fun _ => inferInstance
  let e : ({K : Finset (Fin n) // K.card = a} → Γ(X, V)) ≃ₗ[Γ(S, ⊤)]
      ((logPresheafCx hDX ε).X a).obj (op V) := coeffSiteEquiv g c ε a (𝟭 X.Opens) V hV hle
  exact Module.Flat.of_linearEquiv e.symm

/-- The logarithmic forms of degree `> n` vanish on a chart affine. -/
public theorem subsingleton_logComponent (ε : Bool) (a : ℕ) (ha : n < a) (V : X.Opens)
    (hV : IsAffineOpen V) (c : LogChart n g DX hDX) (hle : V ≤ c.W) :
    Subsingleton (((logPresheafCx hDX ε).X a).obj (op V)) := by
  letI := (g.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsEmpty {K : Finset (Fin n) // K.card = a} := ⟨fun K => by
    have := K.1.card_le_univ
    rw [K.2, Fintype.card_fin] at this
    omega⟩
  let e : ({K : Finset (Fin n) // K.card = a} → Γ(X, V)) ≃ₗ[Γ(S, ⊤)]
      ((logPresheafCx hDX ε).X a).obj (op V) := coeffSiteEquiv g c ε a (𝟭 X.Opens) V hV hle
  exact e.symm.toEquiv.subsingleton

end ZeroSide

section Finiteness

attribute [local instance] secCommRing

open Stacks.CategoryTheory.CechComplex

variable {n : ℕ} {X S : Scheme.{0}} (g : X ⟶ S) [SmoothOfRelativeDimension n g]
  {DX : MMP.Mori.Divisor X} (hDX : DX.IsRelativeSNC n g) {ι : Type} (U : ι → X.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

include hU hUaff in
/-- The cohomology of the total Čech complex of the logarithmic de Rham complex is finite over
the base. -/
public theorem moduleFinite_logDeRham [IsAffine S] [IsLocallyNoetherian S] [IsProper g]
    [IsLocallyNoetherian X] (ε : Bool) (i : ℤ) :
    Module.Finite Γ(S, ⊤) (homologyAt (totD U (logPresheafCx hDX ε) i)
      (totD U (logPresheafCx hDX ε) (i + 1))) := by
  have hKcoh : ∀ k, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty ((deRhamCx n g DX hDX ε).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase g)).obj M) :=
    fun k => let ⟨M, _, h1, h2⟩ := exists_deRhamCx_X g hDX ε k; ⟨M, h1 inferInstance, h2⟩
  let K : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing g)) ℤ := (deRhamCx n g DX hDX ε).1
  haveI : K.IsStrictlyGE 0 := CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _
  have hF := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_totalCechComplex g U hU
    hUaff K 0 hKcoh (i + 1)
  have hcd := exists_extend_cechData g (𝟭 X.Opens)
    (MMP.Mori.Divisor.relativeLogDeRhamComplex n g DX hDX (bif ε then DX.suppIdeal else ⊤))
  obtain ⟨e, he, hz⟩ := hcd
  let E := ((ModuleCat.restrictScalars
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).mapIso
    (HomologicalComplex.homologyMapIso (totalCechComplexIsoCechTot g (𝟭 X.Opens) U hU
      (deRhamCx n g DX hDX ε).1 _ e hz he) (i + 1))).toLinearEquiv.trans
    (homologyRestrictScalarsEquiv _ _ i)
  have key : ∀ L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing g)) ℕ, L = logCx hDX ε →
      Module.Finite Γ(S, ⊤) (homologyAt
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).map
          ((cechTot U (siteCx g (𝟭 X.Opens) L)).d i (i + 1))).hom
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).map
          ((cechTot U (siteCx g (𝟭 X.Opens) L)).d (i + 1) (i + 1 + 1))).hom) →
      Module.Finite Γ(S, ⊤) (homologyAt (totD U (logPresheafCx hDX ε) i)
        (totD U (logPresheafCx hDX ε) (i + 1))) := by
    rintro L rfl h
    exact Module.Finite.equiv (homologyAtResCxEquiv U
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)
      (siteCx g (𝟭 X.Opens) (logCx hDX ε)) i)
  have hF' : Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).obj
      ((AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex g (fun i => (𝟭 X.Opens).obj (U i)) hU
        K).homology (i + 1))) := hF
  exact key _ (relativeLogDeRhamComplex_eq_logCx hDX ε) (Module.Finite.equiv E)

include hU hUaff in
/-- The cohomology of the total Čech complex of the logarithmic forms is finite over the
base. -/
public theorem moduleFinite_logHodge [IsAffine S] [IsLocallyNoetherian S] [IsProper g]
    [IsLocallyNoetherian X] (ε : Bool) (p : ℕ) (i : ℤ) :
    Module.Finite Γ(S, ⊤) (homologyAt (totD U (hodgePresheafCx hDX ε p) i)
      (totD U (hodgePresheafCx hDX ε p) (i + 1))) := by
  have hKcoh : ∀ k, ∃ M : X.Modules, M.IsCoherent ∧
      Nonempty ((hodgeCx n g DX hDX ε p).1.X k ≅
        (pushforward (Stacks.DeRhamDirectImage.toInverseImageBase g)).obj M) :=
    fun k => let ⟨M, _, h1, h2⟩ := exists_hodgeCx_X g hDX ε p k; ⟨M, h1 inferInstance, h2⟩
  let K : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing g)) ℤ := (hodgeCx n g DX hDX ε p).1
  haveI : K.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff _ 0).2 fun j hj =>
    HomologicalComplex.isZero_single_obj_X _ 0 _ j (by omega)
  have hF := AlgebraicGeometry.DeRhamTypeComplex.moduleFinite_homology_totalCechComplex g U hU
    hUaff K 0 hKcoh (i + 1)
  have hcd := exists_single_cechData g (𝟭 X.Opens)
    ((MMP.Mori.Divisor.relativeLogDeRhamComplex n g DX hDX (bif ε then DX.suppIdeal else ⊤)).X p)
  obtain ⟨e, he, hz⟩ := hcd
  let E := ((ModuleCat.restrictScalars
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).mapIso
    (HomologicalComplex.homologyMapIso (totalCechComplexIsoCechTot g (𝟭 X.Opens) U hU
      K _ e hz he) (i + 1))).toLinearEquiv.trans
    (homologyRestrictScalarsEquiv _ _ i)
  have key : ∀ L : CochainComplex (SheafOfModules.{0}
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRing g)) ℕ, L = logCx hDX ε →
      Module.Finite Γ(S, ⊤) (homologyAt
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).map
          ((cechTot U ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
            ((siteSections g (𝟭 X.Opens)).obj (L.X p)))).d i (i + 1))).hom
        ((ModuleCat.restrictScalars (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).map
          ((cechTot U ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
            ((siteSections g (𝟭 X.Opens)).obj (L.X p)))).d (i + 1) (i + 1 + 1))).hom) →
      Module.Finite Γ(S, ⊤) (homologyAt (totD U (hodgePresheafCx hDX ε p) i)
        (totD U (hodgePresheafCx hDX ε p) (i + 1))) := by
    rintro L rfl h
    exact Module.Finite.equiv (homologyAtResCxEquiv U
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        ((siteSections g (𝟭 X.Opens)).obj ((logCx hDX ε).X p))) i)
  have hF' : Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars
      (AlgebraicGeometry.DeRhamTypeComplex.inverseImageBaseRingHom g)).obj
      ((AlgebraicGeometry.DeRhamTypeComplex.totalCechComplex g (fun i => (𝟭 X.Opens).obj (U i)) hU
        K).homology (i + 1))) := hF
  exact key _ (relativeLogDeRhamComplex_eq_logCx hDX ε) (Module.Finite.equiv E)

end Finiteness

section GenericFibre

open Stacks.CategoryTheory.CechComplex

/-- **Generic constancy for the total Čech complex of a bounded flat complex.** -/
public theorem exists_s_cechTot {Z : TopCat.{0}} {ι : Type} [Finite ι]
    (U : ι → TopologicalSpace.Opens Z) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (P : CochainComplex ((TopologicalSpace.Opens Z)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ) (A : ℕ)
    (hvan : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton ((P.X a).obj (op (inter U t))))
    (hflat : ∀ i, Module.Flat R (TotX U P i))
    (hfin : ∀ i, Module.Finite R (homologyAt (totD U P i) (totD U P (i + 1)))) :
    ∃ s : R, s ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra R L], algebraMap R L s ≠ 0 → ∀ i,
      Module.finrank L (homologyAt ((totD U P i).baseChange L) ((totD U P (i + 1)).baseChange L)) =
        Module.finrank (FractionRing R) (homologyAt ((totD U P i).baseChange (FractionRing R))
          ((totD U P (i + 1)).baseChange (FractionRing R))) := by
  obtain ⟨h, hh⟩ := exists_totHomotopy U P A hvan
  obtain ⟨s, hs, H⟩ := exists_finrank_homology_baseChange_eq (TotX U P) (totD U P)
    (fun i => LinearMap.ext fun x => totD_totD U P i x) hflat 0 ((Nat.card ι + A : ℕ) : ℤ)
    (fun i hi => subsingleton_totX_of_neg U P i hi) h (fun j hj x => hh j hj x) hfin
  exact ⟨s, hs, fun L _ _ hL i => H L hL i⟩

/-- `exists_s_cechTot` for a cover by opens of a scheme. -/
public theorem exists_s_cechTot_scheme {𝒳 : Scheme.{0}} {ι : Type} [Finite ι]
    (U : ι → 𝒳.Opens) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (P : CochainComplex ((𝒳.Opens)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ) (A : ℕ)
    (hvan : ∀ (a : ℕ), A < a → ∀ (p : ℕ) (t : Fin (p + 1) → ι),
      Subsingleton ((P.X a).obj (op (inter U t))))
    (hflat : ∀ i, Module.Flat R (TotX U P i))
    (hfin : ∀ i, Module.Finite R (homologyAt (totD U P i) (totD U P (i + 1)))) :
    ∃ s : R, s ≠ 0 ∧ ∀ (L : Type) [Field L] [Algebra R L], algebraMap R L s ≠ 0 → ∀ i,
      Module.finrank L (homologyAt ((totD U P i).baseChange L) ((totD U P (i + 1)).baseChange L)) =
        Module.finrank (FractionRing R) (homologyAt ((totD U P i).baseChange (FractionRing R))
          ((totD U P (i + 1)).baseChange (FractionRing R))) :=
  exists_s_cechTot U P A hvan hflat hfin

end GenericFibre

section FibreDims

attribute [local instance] secCommRing

open Stacks.CategoryTheory.CechComplex TensorProduct

/-- The Čech intersections of the charts of `𝒳₀` are chart affines. -/
public theorem inter_charts {n : ℕ} {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
    {𝒳₀ : Scheme.{0}} {g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)} [SmoothOfRelativeDimension n g₀]
    [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀} (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type}
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (p : ℕ) (t : Fin (p + 1) → ι) :
    IsAffineOpen (inter (fun i => ((C i).W : 𝒳₀.Opens)) t) ∧
      ∃ c : LogChart n g₀ 𝒟₀ h𝒟₀, inter (fun i => ((C i).W : 𝒳₀.Opens)) t ≤ c.W := by
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper g₀
  have he := inter_eq_iInf (fun i => ((C i).W : 𝒳₀.Opens)) t
  refine ⟨?_, (C (t 0)).toLogChart g₀ 𝒟₀ h𝒟₀ (exists_mem_support_genericPoint_eq 𝒟₀), ?_⟩
  · rw [he]
    exact IsAffineOpen.iInf fun a => (C (t a)).W.2
  · rw [he]
    exact iInf_le _ 0

/-- A ring map `R₀ ⟶ K` not killing `s` gives a map on global sections of spectra not killing
`s`. -/
public theorem algebraMap_ne_zero_of_hom_ne_zero {R₀ : Type} [CommRing R₀]
    (K : CommRingCat.{0}) (φ : CommRingCat.of R₀ ⟶ K) (s : Γ(Spec (CommRingCat.of R₀), ⊤))
    (hs : φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s) ≠ 0) :
    (Spec.map φ).appTop.hom s ≠ 0 := by
  intro hr
  have h1 := congrArg (fun F => F.hom s) (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  apply hs
  rw [← h1, hr, map_zero]

/-- **The fibre cohomology of the logarithmic de Rham complex is generic** once a base change
constant `s` does not vanish. -/
public theorem finrank_hc_deRhamCx_eq (n : ℕ) {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
    {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀]
    [IsProper g₀] (𝒟₀ : MMP.Mori.Divisor 𝒳₀) (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type}
    [Finite ι] (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀))
    (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤) (K : CommRingCat.{0}) (hK : IsField K)
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀)) (ε : Bool)
    (s : Γ(Spec (CommRingCat.of R₀), ⊤))
    (hs : φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s) ≠ 0)
    (Hs : ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) i).baseChange L)
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
          (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
            ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (i + 1)).baseChange
              (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))))
    (i : ℤ) :
    Module.finrank Γ(Spec K, ⊤) (Hc f (deRhamCx n f DY hDY ε) (i + 1)) =
      Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
        (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) i).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  letI : Field Γ(Spec K, ⊤) :=
    (MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv).toField
  letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  haveI : IsRegularRing K := by
    letI := hK.toField
    exact inferInstance
  have hcp := exists_chartPairs n g₀ 𝒟₀ h𝒟₀ C K φ f q H DY hDY hsupp
  obtain ⟨pr, hpr⟩ := hcp
  have hpc := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀) (h𝒟₀ := h𝒟₀)
    (hDY := hDY) (K := K) (φ := φ) (f := f) (q := q) C hC H pr hpr
  obtain ⟨hpairs, hcov⟩ := hpc
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI : IsProper f := MorphismProperty.of_isPullback H inferInstance
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
  have hUY : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, hC]
    rfl
  have hUaffY : ∀ i, IsAffineOpen (q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens)) := fun i => (C i).W.2.preimage q
  have hE1 := nonempty_hc_deRhamCx_equiv f hDY q (fun i => ((C i).W : 𝒳₀.Opens)) hUY hUaffY ε i
  obtain ⟨E1⟩ := hE1
  have E2 := nonempty_logDeRham_homologyAt_equiv (X := 𝒳₀) (Y := Y) (S := Spec (CommRingCat.of R₀))
    (T := Spec K) (g := g₀) (f := f) (q := q) (φ := Spec.map φ) (DX := 𝒟₀) (DY := DY) (n := n)
    H.w hsupp h𝒟₀ hDY H hpairs (fun i => ((C i).W : 𝒳₀.Opens)) hcov ε i
  obtain ⟨E2⟩ := E2
  have e3 := (E1.trans E2.symm).finrank_eq
  have e4 := Hs Γ(Spec K, ⊤) (algebraMap_ne_zero_of_hom_ne_zero K φ s hs) i
  exact e3.trans e4

/-- **The fibre cohomology of the logarithmic forms is generic** once a base change
constant `s` does not vanish. -/
public theorem finrank_hc_hodgeCx_eq (n : ℕ) {R₀ : Type} [CommRing R₀] [IsRegularRing R₀]
    {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀)) [SmoothOfRelativeDimension n g₀]
    [IsProper g₀] (𝒟₀ : MMP.Mori.Divisor 𝒳₀) (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type}
    [Finite ι] (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀))
    (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤) (K : CommRingCat.{0}) (hK : IsField K)
    (φ : CommRingCat.of R₀ ⟶ K) {Y : Scheme.{0}} (f : Y ⟶ Spec K)
    [SmoothOfRelativeDimension n f] (q : Y ⟶ 𝒳₀) (H : IsPullback q f g₀ (Spec.map φ))
    (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
    (hsupp : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀)) (ε : Bool) (p : ℕ)
    (s : Γ(Spec (CommRingCat.of R₀), ⊤))
    (hs : φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom s) ≠ 0)
    (Hs : ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i).baseChange L)
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
          (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
            ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (i + 1)).baseChange
              (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))))
    (i : ℤ) :
    Module.finrank Γ(Spec K, ⊤) (Hc f (hodgeCx n f DY hDY ε p) (i + 1)) =
      Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
        (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (i + 1)).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  letI : Field Γ(Spec K, ⊤) :=
    (MulEquiv.isField hK (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.toMulEquiv).toField
  letI : Algebra Γ(Spec (CommRingCat.of R₀), ⊤) Γ(Spec K, ⊤) := (Spec.map φ).appTop.hom.toAlgebra
  haveI : IsRegularRing K := by
    letI := hK.toField
    exact inferInstance
  have hcp := exists_chartPairs n g₀ 𝒟₀ h𝒟₀ C K φ f q H DY hDY hsupp
  obtain ⟨pr, hpr⟩ := hcp
  have hpc := chartPairs_cover (n := n) (R₀ := R₀) (g₀ := g₀) (h𝒟₀ := h𝒟₀)
    (hDY := hDY) (K := K) (φ := φ) (f := f) (q := q) C hC H pr hpr
  obtain ⟨hpairs, hcov⟩ := hpc
  haveI : IsAffineHom q :=
    MorphismProperty.of_isPullback H.flip (inferInstance : IsAffineHom (Spec.map φ))
  haveI : IsProper f := MorphismProperty.of_isPullback H inferInstance
  haveI := AlgebraicGeometry.DeRhamTypeComplex.isAffineHom_diagonal_of_isProper f
  have hUY : (⊤ : Y.Opens) = ⨆ i, q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, hC]
    rfl
  have hUaffY : ∀ i, IsAffineOpen (q ⁻¹ᵁ ((C i).W : 𝒳₀.Opens)) := fun i => (C i).W.2.preimage q
  have hE1 := nonempty_hc_hodgeCx_equiv f hDY q (fun i => ((C i).W : 𝒳₀.Opens)) hUY hUaffY ε p i
  obtain ⟨E1⟩ := hE1
  have E2 := nonempty_logHodge_homologyAt_equiv (X := 𝒳₀) (Y := Y) (S := Spec (CommRingCat.of R₀))
    (T := Spec K) (g := g₀) (f := f) (q := q) (φ := Spec.map φ) (DX := 𝒟₀) (DY := DY) (n := n)
    H.w hsupp h𝒟₀ hDY H hpairs (fun i => ((C i).W : 𝒳₀.Opens)) hcov ε p i
  obtain ⟨E2⟩ := E2
  have e3 := (E1.trans E2.symm).finrank_eq
  have e4 := Hs Γ(Spec K, ⊤) (algebraMap_ne_zero_of_hom_ne_zero K φ s hs) i
  exact e3.trans e4

/-- The global sections of `Spec R₀` are a Noetherian domain when `R₀` is. -/
public theorem baseRing_facts {R₀ : Type} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] :
    IsDomain Γ(Spec (CommRingCat.of R₀), ⊤) ∧ IsNoetherianRing Γ(Spec (CommRingCat.of R₀), ⊤) :=
  ⟨MulEquiv.isDomain R₀
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.toMulEquiv,
    isNoetherianRing_of_ringEquiv R₀
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.symm⟩

/-- A generic base change constant for the logarithmic de Rham complex. -/
public theorem exists_s_deRham (n : ℕ) {R₀ : Type} [CommRing R₀] [IsDomain R₀]
    [IsRegularRing R₀] {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀))
    [SmoothOfRelativeDimension n g₀] [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀}
    (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type} [Finite ι]
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)
    (ε : Bool) :
    haveI := (baseRing_facts (R₀ := R₀)).1
    ∃ s : Γ(Spec (CommRingCat.of R₀), ⊤), s ≠ 0 ∧
      ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) i).baseChange L)
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (i + 1)).baseChange L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
          (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
            ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (i + 1)).baseChange
              (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  have hbr := baseRing_facts (R₀ := R₀)
  obtain ⟨h1, h2⟩ := hbr
  haveI : IsLocallyNoetherian 𝒳₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  have hX := inter_charts h𝒟₀ C
  refine exists_s_cechTot_scheme _ (logPresheafCx h𝒟₀ ε) n
    (fun a ha k t => let ⟨haff, c, hle⟩ := hX k t;
      subsingleton_logComponent h𝒟₀ ε a ha _ haff c hle)
    (fun i => ?_) (fun i => moduleFinite_logDeRham g₀ h𝒟₀ _ hC.symm (fun i => (C i).W.2) ε i)
  haveI := finite_totIndex i
  refine flat_pi' fun j => flat_pi' fun t => ?_
  obtain ⟨haff, c, hle⟩ := hX _ t
  exact flat_logComponent h𝒟₀ ε _ _ haff c hle

/-- Both fibre dimensions vanish for a Čech complex with subsingleton terms. -/
public theorem finrank_homologyAt_baseChange_eq_of_subsingleton {𝒳 : Scheme.{0}} {ι : Type}
    (U : ι → 𝒳.Opens) {R : Type} [CommRing R] [IsDomain R]
    (P : CochainComplex ((𝒳.Opens)ᵒᵖ ⥤ ModuleCat.{0} R) ℕ)
    (hsub : ∀ i, Subsingleton (TotX U P i)) (L : Type) [Field L] [Algebra R L] (i : ℤ) :
    Module.finrank L (homologyAt ((totD U P i).baseChange L) ((totD U P (i + 1)).baseChange L)) =
      Module.finrank (FractionRing R) (homologyAt ((totD U P i).baseChange (FractionRing R))
        ((totD U P (i + 1)).baseChange (FractionRing R))) := by
  haveI := hsub (i + 1)
  haveI : Subsingleton (L ⊗[R] TotX U P (i + 1)) := subsingleton_tensor_right _ _
  haveI : Subsingleton (FractionRing R ⊗[R] TotX U P (i + 1)) := subsingleton_tensor_right _ _
  haveI := subsingleton_homologyAt ((totD U P i).baseChange L) ((totD U P (i + 1)).baseChange L)
  haveI := subsingleton_homologyAt ((totD U P i).baseChange (FractionRing R))
    ((totD U P (i + 1)).baseChange (FractionRing R))
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- A generic base change constant for the logarithmic forms. -/
public theorem exists_s_hodge (n : ℕ) {R₀ : Type} [CommRing R₀] [IsDomain R₀]
    [IsRegularRing R₀] {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀))
    [SmoothOfRelativeDimension n g₀] [IsProper g₀] {𝒟₀ : MMP.Mori.Divisor 𝒳₀}
    (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type} [Finite ι]
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤)
    (ε : Bool) (p : ℕ) :
    haveI := (baseRing_facts (R₀ := R₀)).1
    ∃ s : Γ(Spec (CommRingCat.of R₀), ⊤), s ≠ 0 ∧ (n < p → s = 1) ∧
      ∀ (L : Type) [Field L] [Algebra Γ(Spec (CommRingCat.of R₀), ⊤) L],
      algebraMap Γ(Spec (CommRingCat.of R₀), ⊤) L s ≠ 0 → ∀ i,
        Module.finrank L (homologyAt
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i).baseChange L)
          ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (i + 1)).baseChange
            L)) =
        Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
          (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i).baseChange
            (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
            ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (i + 1)).baseChange
              (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))) := by
  have hbr := baseRing_facts (R₀ := R₀)
  obtain ⟨h1, h2⟩ := hbr
  haveI : Nontrivial Γ(Spec (CommRingCat.of R₀), ⊤) := IsDomain.toNontrivial
  haveI : IsLocallyNoetherian 𝒳₀ := LocallyOfFiniteType.isLocallyNoetherian g₀
  have hX := inter_charts h𝒟₀ C
  have hsubHo : ∀ (a : ℕ), 0 < a → ∀ (k : ℕ) (t : Fin (k + 1) → ι),
      Subsingleton (((hodgePresheafCx h𝒟₀ ε p).X a).obj
        (op (inter (fun i => ((C i).W : 𝒳₀.Opens)) t))) := by
    intro a ha k t
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    exact subsingleton_resCx_single _ _ b _
  by_cases hp : n < p
  · refine ⟨1, one_ne_zero, fun _ => rfl, fun L _ _ _ i => ?_⟩
    have hsub : ∀ i, Subsingleton (TotX (fun i => ((C i).W : 𝒳₀.Opens))
        (hodgePresheafCx h𝒟₀ ε p) i) := by
      intro i
      refine @Pi.instSubsingleton _ _ fun j => ?_
      rcases j with ⟨⟨k, a⟩, hka⟩
      refine @Pi.instSubsingleton _ _ fun t => ?_
      rcases a with _ | b
      · obtain ⟨haff, c, hle⟩ := hX _ t
        exact (subsingleton_logComponent h𝒟₀ ε p hp _ haff c hle : _)
      · exact hsubHo (b + 1) (Nat.succ_pos b) _ t
    exact finrank_homologyAt_baseChange_eq_of_subsingleton _ _ hsub L i
  · have hflat : ∀ i, Module.Flat Γ(Spec (CommRingCat.of R₀), ⊤)
        (TotX (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) i) := by
      intro i
      haveI := finite_totIndex i
      refine flat_pi' fun j => ?_
      rcases j with ⟨⟨k, a⟩, hka⟩
      refine flat_pi' fun t => ?_
      rcases a with _ | b
      · obtain ⟨haff, c, hle⟩ := hX _ t
        exact (flat_logComponent h𝒟₀ ε p _ haff c hle : _)
      · haveI := hsubHo (b + 1) (Nat.succ_pos b) _ t
        infer_instance
    refine (exists_s_cechTot_scheme (fun i => ((C i).W : 𝒳₀.Opens))
      (hodgePresheafCx h𝒟₀ ε p) 0 hsubHo hflat
      (fun i => moduleFinite_logHodge g₀ h𝒟₀ _ hC.symm (fun i => (C i).W.2) ε p i)).imp
      fun s hs => ⟨hs.1, fun h => absurd h hp, hs.2⟩

/-- **Generic constancy of the fibre dimensions.** -/
public theorem exists_fibre_dims (n : ℕ) {R₀ : Type} [CommRing R₀] [IsDomain R₀]
    [IsRegularRing R₀] {𝒳₀ : Scheme.{0}} (g₀ : 𝒳₀ ⟶ Spec (CommRingCat.of R₀))
    [SmoothOfRelativeDimension n g₀] [IsProper g₀] (𝒟₀ : MMP.Mori.Divisor 𝒳₀)
    (h𝒟₀ : 𝒟₀.IsRelativeSNC n g₀) {ι : Type} [Finite ι]
    (C : ι → WeakChart g₀ n (𝒟₀.supp : Set 𝒳₀)) (hC : ⨆ i, ((C i).W : 𝒳₀.Opens) = ⊤) :
    ∃ s : R₀, s ≠ 0 ∧ ∃ (N : Bool → ℕ → ℤ → ℕ) (N' : Bool → ℤ → ℕ),
      ∀ (K : CommRingCat.{0}) (_ : IsField K) (φ : CommRingCat.of R₀ ⟶ K), φ.hom s ≠ 0 →
      ∀ {Y : Scheme.{0}} (f : Y ⟶ Spec K) [SmoothOfRelativeDimension n f]
        (q : Y ⟶ 𝒳₀) (_ : IsPullback q f g₀ (Spec.map φ))
        (DY : MMP.Mori.Divisor Y) (hDY : DY.IsRelativeSNC n f)
        (_ : (DY.supp : Set Y) = q.base ⁻¹' (𝒟₀.supp : Set 𝒳₀)),
        ∀ (twist : Bool) (p : ℕ) (j : ℤ),
          Module.finrank Γ(Spec K, ⊤) (Hc f (hodgeCx n f DY hDY twist p) j) =
            N twist p j ∧
          Module.finrank Γ(Spec K, ⊤) (Hc f (deRhamCx n f DY hDY twist) j) =
            N' twist j := by
  classical
  have hbr := baseRing_facts (R₀ := R₀)
  obtain ⟨h1, h2⟩ := hbr
  haveI : Nontrivial Γ(Spec (CommRingCat.of R₀), ⊤) := IsDomain.toNontrivial
  choose sdR hsdR HdR using exists_s_deRham n g₀ h𝒟₀ C hC
  choose sHo hsHo hsHo1 HHo using exists_s_hodge n g₀ h𝒟₀ C hC
  obtain ⟨sTot, hsTot⟩ : ∃ x : Γ(Spec (CommRingCat.of R₀), ⊤),
      x = (∏ ε : Bool, sdR ε) * ∏ ε : Bool, ∏ p : Fin (n + 1), sHo ε p := ⟨_, rfl⟩
  have hsTot0 : sTot ≠ 0 := by
    rw [hsTot]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ε _ => hsdR ε)
      (Finset.prod_ne_zero_iff.mpr fun ε _ => Finset.prod_ne_zero_iff.mpr fun p _ => hsHo ε p)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R₀)).hom sTot,
    fun h => hsTot0 ((Scheme.ΓSpecIso (CommRingCat.of R₀)).commRingCatIsoToRingEquiv.injective
      (h.trans (map_zero _).symm)),
    fun ε p j => Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
      (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p)
        (j - 1)).baseChange (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
        ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (hodgePresheafCx h𝒟₀ ε p) (j - 1 + 1)).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))),
    fun ε j => Module.finrank (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤))
      (homologyAt ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε)
        (j - 1)).baseChange (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))
        ((totD (fun i => ((C i).W : 𝒳₀.Opens)) (logPresheafCx h𝒟₀ ε) (j - 1 + 1)).baseChange
          (FractionRing Γ(Spec (CommRingCat.of R₀), ⊤)))), ?_⟩
  intro K hK φ hφ Y f _ q H DY hDY hsupp twist p j
  have hψ : (φ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom) sTot ≠ 0 := hφ
  have hsdRK : ∀ ε, φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom (sdR ε)) ≠ 0 := by
    intro ε h
    apply hψ
    rw [hsTot, map_mul, map_prod]
    have h' : ∏ ε', (φ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom) (sdR ε') = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ε) h
    rw [h', zero_mul]
  have hsHoK : ∀ ε p, φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R₀)).hom (sHo ε p)) ≠ 0 := by
    intro ε p h
    by_cases hp : n < p
    · haveI := hK.nontrivial
      rw [hsHo1 ε p hp, map_one, map_one] at h
      exact one_ne_zero h
    · apply hψ
      rw [hsTot, map_mul, map_prod, map_prod]
      have h' : ∏ ε' : Bool, (φ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom)
          (∏ p' : Fin (n + 1), sHo ε' p') = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ ε) ?_
        rw [map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ ⟨p, by omega⟩) h
      rw [h', mul_zero]
  have hj : j = (j - 1) + 1 := by ring
  constructor
  · conv_lhs => rw [hj]
    exact finrank_hc_hodgeCx_eq n g₀ 𝒟₀ h𝒟₀ C hC K hK φ f q H DY hDY hsupp twist p
      (sHo twist p) (hsHoK twist p) (HHo twist p) (j - 1)
  · conv_lhs => rw [hj]
    exact finrank_hc_deRhamCx_eq n g₀ 𝒟₀ h𝒟₀ C hC K hK φ f q H DY hDY hsupp twist
      (sdR twist) (hsdRK twist) (HdR twist) (j - 1)

end FibreDims

end FibreAssembly

/-- Smooth algebras over `ℤ` are regular. -/
public theorem isRegularRing_of_smooth_int (R : Type) [CommRing R] [Algebra.Smooth ℤ R] :
    IsRegularRing R :=
  Algebra.isRegularRing_of_smooth ℤ R

/-- The localization of a smooth `ℤ`-algebra at an element is smooth over `ℤ`. -/
public theorem smooth_int_away {R : Type} [CommRing R] [Algebra.Smooth ℤ R] (s : R) :
    Algebra.Smooth ℤ (Localization.Away s) := by
  have : Algebra.Smooth R (Localization.Away s) := Algebra.Smooth.of_isLocalization_Away s
  exact Algebra.Smooth.comp ℤ R (Localization.Away s)

/-- The identity square is a pullback. -/
public theorem isPullback_id_spec {R : Type} [CommRing R] {𝒳 : Scheme.{0}}
    (g : 𝒳 ⟶ Spec (CommRingCat.of R)) :
    IsPullback (𝟙 𝒳) g g (Spec.map (𝟙 (CommRingCat.of R))) := by
  rw [Spec.map_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Inverting a nonzero element of a smooth `ℤ`-domain inside `ℂ`. -/
public theorem exists_away_smooth_int {R₀ : Type} [CommRing R₀] [IsDomain R₀]
    [Algebra.Smooth ℤ R₀] (ι₀ : R₀ →+* ℂ) (hι₀ : Function.Injective ι₀) (s : R₀) (hs : s ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.Smooth ℤ R) (a : R₀ →+* R)
      (ι : R →+* ℂ), IsUnit (a s) ∧ Function.Injective ι ∧ ι.comp a = ι₀ := by
  have hι₀s : IsUnit (ι₀ s) := ((map_ne_zero_iff _ hι₀).mpr hs).isUnit
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
  have hsm : @Algebra.Smooth ℤ _ (Localization.Away s) _ (Ring.toIntAlgebra _) := by
    convert smooth_int_away s
    exact Subsingleton.elim _ _
  refine ⟨Localization.Away s, inferInstance, inferInstance, hsm, algebraMap R₀ _,
    IsLocalization.Away.lift s hι₀s, IsLocalization.Away.algebraMap_isUnit s, ?_,
    IsLocalization.lift_comp _⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'] at hz
  have hx : ι₀ x = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (Units.ne_zero _)
  rw [(map_eq_zero_iff _ hι₀).mp hx]
  exact IsLocalization.mk'_zero _

private theorem main (n : ℕ) {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    (D : MMP.Mori.Divisor X) (hD : D.IsRelativeSNC n π) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.Smooth ℤ R) (ι : R →+* ℂ)
      (_ : Function.Injective ι) (𝒳 : Scheme.{0}) (g : 𝒳 ⟶ Spec (CommRingCat.of R))
      (_ : SmoothOfRelativeDimension n g) (_ : IsProjective g) (𝒟 : MMP.Mori.Divisor 𝒳)
      (_ : 𝒟.IsRelativeSNC n g) (e : X ≅ pullback g (Spec.map (CommRingCat.ofHom ι))),
      e.hom ≫ pullback.snd _ _ = π ∧
      (e.hom ≫ pullback.fst _ _).base ⁻¹' (𝒟.supp : Set 𝒳) = (D.supp : Set X) ∧
      ∀ s : Spec (CommRingCat.of R),
        ∃ (_ : SmoothOfRelativeDimension n
            (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
          (Ds : MMP.Mori.Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
          (hDs : Ds.IsRelativeSNC n (pullback.snd _ _)),
          (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
            (𝒟.supp : Set 𝒳) = (Ds.supp : Set _) ∧
          ∀ (twist : Bool) (p : ℕ) (j : ℤ),
            -- Hodge dimensions `dim H^j(Ω^p(log D))`, resp. with the twist by `-D`
            Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
                (Hc π
                  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
                    ((MMP.Mori.Divisor.relativeLogDeRhamComplex n π D hD (bif twist then D.suppIdeal else ⊤)).X p),
                    0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
                      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ j) =
              Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
                (Hc (pullback.snd _ _)
                  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
                    ((MMP.Mori.Divisor.relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
                      (bif twist then Ds.suppIdeal else ⊤)).X p), 0,
                    (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
                      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ j) ∧
            -- logarithmic de Rham dimensions `dim ℍ^j(Ω^•(log D))`, resp. with the twist
            Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
                (Hc π
                  ⟨(MMP.Mori.Divisor.relativeLogDeRhamComplex n π D hD
                    (bif twist then D.suppIdeal else ⊤)).extend ComplexShape.embeddingUpNat,
                    0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j) =
              Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
                (Hc (pullback.snd _ _)
                  ⟨(MMP.Mori.Divisor.relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
                    (bif twist then Ds.suppIdeal else ⊤)).extend ComplexShape.embeddingUpNat,
                    0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j) := by
  obtain ⟨R₀, iR₀, dR₀, sR₀, ι₀, hι₀, 𝒳₀, g₀, sg₀, hproj₀, q₀, hpb₀, Z₀, hZ₀c, hZ₀, ι, fι, C, hC⟩ :=
    exists_model n π hπ D hD
  haveI := isRegularRing_of_smooth_int R₀
  haveI : IsProper g₀ := hproj₀.isProper
  obtain ⟨𝒟₀, h𝒟₀, h𝒟₀supp⟩ := exists_isRelativeSNC_of_isPullback n (𝟙 _) g₀ Z₀ hZ₀c
    C hC g₀ (𝟙 𝒳₀) (isPullback_id_spec g₀)
  have hZ₀eq : (𝒟₀.supp : Set 𝒳₀) = Z₀ := by rw [h𝒟₀supp]; rfl
  subst hZ₀eq
  obtain ⟨s, hs0, N, N', hN⟩ := exists_fibre_dims n g₀ 𝒟₀ h𝒟₀ C hC
  -- the base `R = R₀[1/s]`
  obtain ⟨R, iR, dR, sR, a, ι, has, hι, hιcomp⟩ := exists_away_smooth_int ι₀ hι₀ s hs0
  haveI := isRegularRing_of_smooth_int R
  -- the model over `R`
  let gR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₀) :=
    Spec.map (CommRingCat.ofHom a)
  let g : pullback g₀ gR ⟶ Spec (CommRingCat.of R) := pullback.snd g₀ gR
  have hsq : IsPullback (pullback.fst g₀ gR) g g₀ gR := IsPullback.of_hasPullback g₀ gR
  haveI : SmoothOfRelativeDimension n g := smoothOfRelativeDimension_of_isPullback hsq
  have hprojg : IsProjective g := IsProjective.of_isPullback hsq.flip hproj₀
  obtain ⟨𝒟, h𝒟, h𝒟supp⟩ := exists_isRelativeSNC_of_isPullback n (CommRingCat.ofHom a) g₀
    (𝒟₀.supp : Set 𝒳₀) hZ₀c C hC g (pullback.fst g₀ gR) hsq
  -- the complex fibre
  have hspec : Spec.map (CommRingCat.ofHom ι₀) =
      Spec.map (CommRingCat.ofHom ι) ≫ gR := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hιcomp]
  have hbig := IsPullback.paste_horiz
    (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom ι))) hsq
  rw [← hspec] at hbig
  let e : X ≅ pullback g (Spec.map (CommRingCat.ofHom ι)) := hpb₀.isoIsPullback _ _ hbig
  have he₁ : e.hom ≫ pullback.snd _ _ = π := hpb₀.isoIsPullback_hom_snd _ _ hbig
  have he₂ : e.hom ≫ pullback.fst _ _ ≫ pullback.fst g₀ gR = q₀ :=
    hpb₀.isoIsPullback_hom_fst _ _ hbig
  refine ⟨R, inferInstance, inferInstance, inferInstance, ι, hι, _, g, inferInstance, hprojg,
    𝒟, h𝒟, e, he₁, ?_, ?_⟩
  · rw [h𝒟supp, ← Set.preimage_comp, ← hZ₀, ← he₂]
    rfl
  · intro s'
    set γ := (Spec (CommRingCat.of R)).fromSpecResidueField s'
    have hfsq : IsPullback (pullback.fst g γ) (pullback.snd g γ) g γ :=
      IsPullback.of_hasPullback g γ
    haveI : SmoothOfRelativeDimension n (pullback.snd g γ) :=
      smoothOfRelativeDimension_of_isPullback hfsq
    have hbig' := IsPullback.paste_horiz hfsq hsq
    let φ' : CommRingCat.of R₀ ⟶ (Spec (CommRingCat.of R)).residueField s' :=
      CommRingCat.ofHom a ≫ Spec.preimage γ
    have hφ' : Spec.map φ' = γ ≫ gR := by
      rw [Spec.map_comp, Spec.map_preimage]
    have hφs : φ'.hom s ≠ 0 := by
      have : φ'.hom s = (Spec.preimage γ).hom (a s) := rfl
      rw [this]
      exact (has.map (Spec.preimage γ).hom).ne_zero
    have hsq' : IsPullback (pullback.fst g γ ≫ pullback.fst g₀ gR) (pullback.snd g γ) g₀
        (Spec.map φ') := by
      rw [hφ']
      exact hbig'
    obtain ⟨Ds, hDs, hDssupp⟩ := exists_isRelativeSNC_of_isPullback n φ' g₀
      (𝒟₀.supp : Set 𝒳₀) hZ₀c C hC (pullback.snd g γ) _ hsq'
    refine ⟨inferInstance, Ds, hDs, ?_, fun twist p j => ?_⟩
    · rw [hDssupp, h𝒟supp, ← Set.preimage_comp]
      rfl
    · obtain ⟨h1, h2⟩ := hN (CommRingCat.of ℂ) (Field.toIsField _) (CommRingCat.ofHom ι₀)
        ((map_ne_zero_iff _ hι₀).mpr hs0) π q₀ hpb₀ D hD hZ₀.symm twist p j
      obtain ⟨h3, h4⟩ := hN _ (Field.toIsField _) φ' hφs (pullback.snd g γ) _ hsq' Ds hDs hDssupp twist p j
      exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

end MMP.Mori.Divisor.LogSpreadingProof

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Mori.Divisor

/-- **Finite models of a smooth projective SNC pair.** For `π : X ⟶ Spec ℂ` smooth of relative
dimension `n` and projective, and `D` a relative snc divisor on `X`, there are a smooth domain
`R` over `ℤ`, an embedding `ι : R →+* ℂ`, a projective `g : 𝒳 ⟶ Spec R` smooth of relative
dimension `n` with a relative snc divisor `𝒟`, and an isomorphism `X ≅ 𝒳 ×_{Spec R} Spec ℂ` over
`Spec ℂ` carrying `D` to the preimage of `𝒟`, such that for every `s ∈ Spec R` the fibre
`𝒳_s ⟶ Spec κ(s)` with the divisor `𝒟_s` of pulled-back support is a relative snc pair whose
Hodge dimensions `dim H^j(Ω^p(log 𝒟_s))`, `dim H^j(Ω^p(log 𝒟_s)(-𝒟_s))` and logarithmic de Rham
dimensions `dim ℍ^j(Ω^•(log 𝒟_s))`, `dim ℍ^j(Ω^•(log 𝒟_s)(-𝒟_s))` over `κ(s)` equal those of
`(X, D)` over `ℂ`. -/
@[mmp "lem_mmp_lc_bpf_log_spreading"]
public theorem exists_isRelativeSNC_model_finrank_hypercohomology_eq (n : ℕ) {X : Scheme.{0}}
    (π : X ⟶ Spec (CommRingCat.of ℂ)) [SmoothOfRelativeDimension n π] (hπ : IsProjective π)
    (D : Divisor X) (hD : D.IsRelativeSNC n π) :
    -- `ℍ^j(Y, K)` over `Γ(T, ⊤)`, for a bounded below complex of `h⁻¹𝒪_T`-modules on `Y`
    let H : ∀ {Y T : Scheme.{0}} (h : Y ⟶ T), CochainComplex.Plus (SheafOfModules.{0}
        (SheafOfModules.underlyingRingSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))) → ℤ →
        ModuleCat.{0} Γ(T, ⊤) := fun {_ T} h K j =>
      let Γd := (SheafOfModules.evaluation.{0} (SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf))
          (op ⊤)).rightDerivedFunctorPlus
      let M := (DerivedCategory.homologyFunctor _ j).obj
        (DerivedCategory.Plus.ι.obj (Γd.obj (DerivedCategory.Plus.Q.obj K)))
      (ModuleCat.restrictScalars.{0} (show Γ(T, ⊤) →+*
          ((TopCat.Sheaf.pullback CommRingCat.{0} h.base).obj T.sheaf).obj.obj (op ⊤) from
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{0} h.base).unit.app
          T.sheaf).hom.app (op ⊤)).hom)).obj M
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.Smooth ℤ R) (ι : R →+* ℂ)
      (_ : Function.Injective ι) (𝒳 : Scheme.{0}) (g : 𝒳 ⟶ Spec (CommRingCat.of R))
      (_ : SmoothOfRelativeDimension n g) (_ : IsProjective g) (𝒟 : Divisor 𝒳)
      (_ : 𝒟.IsRelativeSNC n g) (e : X ≅ pullback g (Spec.map (CommRingCat.ofHom ι))),
      e.hom ≫ pullback.snd _ _ = π ∧
      (e.hom ≫ pullback.fst _ _).base ⁻¹' (𝒟.supp : Set 𝒳) = (D.supp : Set X) ∧
      ∀ s : Spec (CommRingCat.of R),
        ∃ (_ : SmoothOfRelativeDimension n
            (pullback.snd g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
          (Ds : Divisor (pullback g ((Spec (CommRingCat.of R)).fromSpecResidueField s)))
          (hDs : Ds.IsRelativeSNC n (pullback.snd _ _)),
          (pullback.fst g ((Spec (CommRingCat.of R)).fromSpecResidueField s)).base ⁻¹'
            (𝒟.supp : Set 𝒳) = (Ds.supp : Set _) ∧
          ∀ (twist : Bool) (p : ℕ) (j : ℤ),
            -- Hodge dimensions `dim H^j(Ω^p(log D))`, resp. with the twist by `-D`
            Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
                (H π
                  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
                    ((relativeLogDeRhamComplex n π D hD (bif twist then D.suppIdeal else ⊤)).X p),
                    0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
                      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ j) =
              Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
                (H (pullback.snd _ _)
                  ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
                    ((relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
                      (bif twist then Ds.suppIdeal else ⊤)).X p), 0,
                    (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
                      HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩ j) ∧
            -- logarithmic de Rham dimensions `dim ℍ^j(Ω^•(log D))`, resp. with the twist
            Module.finrank Γ(Spec (CommRingCat.of ℂ), ⊤)
                (H π
                  ⟨(relativeLogDeRhamComplex n π D hD
                    (bif twist then D.suppIdeal else ⊤)).extend ComplexShape.embeddingUpNat,
                    0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j) =
              Module.finrank Γ(Spec ((Spec (CommRingCat.of R)).residueField s), ⊤)
                (H (pullback.snd _ _)
                  ⟨(relativeLogDeRhamComplex n (pullback.snd _ _) Ds hDs
                    (bif twist then Ds.suppIdeal else ⊤)).extend ComplexShape.embeddingUpNat,
                    0, CochainComplex.instIsStrictlyGEExtendNatIntEmbeddingUpNatOfNat _⟩ j) := by
  intro H
  exact LogSpreadingProof.main n π hπ D hD

end MMP.Mori.Divisor
