module

public import MMP.AlgebraicGeometry.Divisor.Cartier
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor

/-!
# Local equations of Cartier divisors

Let `D` be a Cartier divisor on a scheme `X`. A local equation of `D` on an open `U` is a unit
`g` of `Γ(U, 𝓜_X)` whose class in `Γ(U, 𝓜_X^*/𝒪_X^*)` is `D|_U`
(`MMP.Intersection.IsLocalEquationOn`). This file proves that local equations restrict to
smaller opens and that two local equations on the same open differ, locally, by a unit of
`𝒪_X`.

## Main definitions

* `MMP.Intersection.resUnit`: the restriction of a unit of `Γ(U, 𝓜_X)` to an open `V ⊆ U`.

## Main results

* `MMP.Intersection.cartierClass_resUnit`: the class of a restricted unit is the restricted class.
* `MMP.Intersection.isLocalEquationOn_resUnit`: local equations restrict.
* `MMP.Intersection.IsLocalEquationOn.exists_unit_mul_eq`: two local equations of `D` on `U`
  differ near every point of `U` by a unit of `𝒪_X`.
* `MMP.Intersection.cartierClass_map_units`: units of `𝒪_X` have trivial class.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry I*][lazarsfeld2004], §1.1.A.
* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.4.4.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace MMP.Intersection

variable {X : Scheme.{u}}

/-- The germ at `x` of the image in `𝓜_X` of a section of `𝒪_X` is the image of its germ. -/
theorem germ_toTotalQuotient {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    X.totalQuotientSheaf.presheaf.germ U x hx (toTotalQuotient U s) =
      stalkToTotalQuotient x (X.presheaf.germ U x hx s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx X.toTotalQuotientSheaf.hom s).symm

/-- The restriction of a unit of `Γ(U, 𝓜_X)` to an open `V ⊆ U`. -/
abbrev resUnit {U V : X.Opens} (i : V ⟶ U) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    (X.totalQuotientSheaf.obj.obj (op V))ˣ :=
  Units.map (X.totalQuotientSheaf.obj.map i.op).hom.toMonoidHom g

/-- The class of a unit `g` of `Γ(U, 𝓜_X)` is the image of `g` under the quotient map to the
cokernel presheaf followed by sheafification. -/
theorem cartierClass_eq_toSheafify (U : X.Opens)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass U g =
      (cokernel.π (unitGroupMap X.toTotalQuotientSheaf) ≫
        toSheafify (Opens.grothendieckTopology X)
          (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op U) (Additive.ofMul g) := by
  rw [toSheafify_naturality _ (cokernel.π (unitGroupMap X.toTotalQuotientSheaf))]
  rfl

/-- The class of the restriction of a unit to `V ⊆ U` is the restriction of its class. -/
theorem cartierClass_resUnit {U V : X.Opens} (i : V ⟶ U)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass V (resUnit i g) = (cartierSheaf X).obj.map i.op (cartierClass U g) := by
  rw [cartierClass_eq_toSheafify, cartierClass_eq_toSheafify]
  exact ConcreteCategory.congr_hom
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf) ≫
        toSheafify (Opens.grothendieckTopology X)
          (cokernel (unitGroupMap X.toTotalQuotientSheaf))).naturality i.op) (Additive.ofMul g)

/-- A local equation of `D` on `U` restricts to a local equation of `D` on any open `V ⊆ U`. -/
theorem isLocalEquationOn_resUnit {D : X.CartierDivisor} {U V : X.Opens} (i : V ⟶ U)
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) :
    IsLocalEquationOn D V (resUnit i g) := by
  unfold IsLocalEquationOn at hg ⊢
  rw [cartierClass_resUnit, hg, restrictDivisor, restrictDivisor, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

/-- The class of a product of units is the sum of their classes. -/
theorem cartierClass_mul (U : X.Opens) (g h : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass U (g * h) = cartierClass U g + cartierClass U h := by
  unfold cartierClass
  exact map_add _ (Additive.ofMul g) (Additive.ofMul h)

/-- The class of the unit `1` is zero. -/
theorem cartierClass_one (U : X.Opens) :
    cartierClass U (1 : (X.totalQuotientSheaf.obj.obj (op U))ˣ) = 0 :=
  map_zero _

/-- The class of the inverse of a unit is the negative of its class. -/
theorem cartierClass_inv (U : X.Opens) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass U g⁻¹ = - cartierClass U g := by
  rw [eq_neg_iff_add_eq_zero, ← cartierClass_mul, inv_mul_cancel, cartierClass_one]

/-- Two local equations `g, g'` of a Cartier divisor on `U` differ, near every point of `U`, by
a unit of `𝒪_X`: the transition function `g' / g` is a unit of `𝒪_X` locally. -/
theorem IsLocalEquationOn.exists_unit_mul_eq {D : X.CartierDivisor} {U : X.Opens}
    {g g' : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g)
    (hg' : IsLocalEquationOn D U g') {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U) (_ : x ∈ W) (u : Γ(X, W)ˣ),
      toTotalQuotient W u * X.totalQuotientSheaf.obj.map (homOfLE h).op (g : _) =
        X.totalQuotientSheaf.obj.map (homOfLE h).op (g' : _) := by
  let w : (unitGroupPresheaf X.totalQuotientSheaf).obj (op U) := Additive.ofMul (g' * g⁻¹)
  have hw0 : (cokernel.π (unitGroupMap X.toTotalQuotientSheaf) ≫
      toSheafify (Opens.grothendieckTopology X)
        (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op U) w = 0 :=
    (cartierClass_eq_toSheafify U (g' * g⁻¹)).symm.trans <| by
      rw [cartierClass_mul, cartierClass_inv]
      exact add_neg_eq_zero.mpr (hg'.trans hg.symm)
  obtain ⟨W, i, hi, hxW⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (cokernel (unitGroupMap X.toTotalQuotientSheaf)))
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op U) w) 0
    (by rwa [map_zero]) x hx
  have hπ : (cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op W)
      ((unitGroupPresheaf X.totalQuotientSheaf).map i.op w) = 0 := by
    have := ConcreteCategory.congr_hom
      ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).naturality i.op) w
    simp only [Presheaf.equalizerSieve_apply, map_zero] at hi
    exact this.trans hi
  obtain ⟨u, hu⟩ := (ShortComplex.ab_exact_iff _).mp
    ((ShortComplex.cokernelSequence_exact (unitGroupMap X.toTotalQuotientSheaf)).map
      ((evaluation _ AddCommGrpCat.{u}).obj (op W))) _ hπ
  refine ⟨W, i.le, hxW, Additive.toMul u, ?_⟩
  have h' : toTotalQuotient W (Additive.toMul u : Γ(X, W)ˣ) =
      X.totalQuotientSheaf.obj.map i.op
        ((g' : X.totalQuotientSheaf.obj.obj (op U)) *
          (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U))) :=
    congrArg (fun a => ((Additive.toMul a : (X.totalQuotientSheaf.obj.obj (op W))ˣ) :
      X.totalQuotientSheaf.obj.obj (op W))) hu
  change toTotalQuotient W (Additive.toMul u : Γ(X, W)ˣ) * X.totalQuotientSheaf.obj.map i.op _ =
    X.totalQuotientSheaf.obj.map i.op _
  rw [h', map_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

/-- The class of (the image of) a unit of `𝒪_X` is trivial: `𝒪_X^* ⟶ 𝓜_X^* ⟶ 𝓜_X^*/𝒪_X^*`
vanishes. -/
theorem cartierClass_map_units (U : X.Opens) (u : Γ(X, U)ˣ) :
    cartierClass U (Units.map (toTotalQuotient U).toMonoidHom u) = 0 := by
  rw [cartierClass_eq_toSheafify]
  have h := cokernel.condition (unitGroupMap X.toTotalQuotientSheaf) =≫
    toSheafify (Opens.grothendieckTopology X) (cokernel (unitGroupMap X.toTotalQuotientSheaf))
  rw [zero_comp, Category.assoc] at h
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => φ.app (op U)) h) (Additive.ofMul u)).trans
    rfl

/-- Every point has an open neighbourhood on which a Cartier divisor has a local equation. -/
theorem exists_isLocalEquationOn (D : X.CartierDivisor) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ),
      IsLocalEquationOn D U g := by
  obtain ⟨V, hVle, ⟨c, hc⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp
      (isLocallySurjective_toSheafify_addCommGrpCat
        (cokernel (unitGroupMap X.toTotalQuotientSheaf))) ⊤ D x (by simp)
  obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V))).mp inferInstance c
  refine ⟨V, hxV, Additive.toMul v, ?_⟩
  unfold IsLocalEquationOn
  rw [cartierClass_eq_toSheafify]
  change (toSheafify (Opens.grothendieckTopology X)
      (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op V)
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V) v) = _
  rw [hv]
  exact hc

/-- **Lazarsfeld (1.1), local data, converse.** Units `fᵢ ∈ Γ(Uᵢ, 𝓜_X^*)` on an open cover with
`fᵢ / fⱼ ∈ Γ(Uᵢ ∩ Uⱼ, 𝒪_X^*)` are the local equations of a unique Cartier divisor. -/
@[mmp "lem_p01a_cartier_divisor_local_data"]
theorem existsUnique_isLocalEquationOn {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (f : ∀ i, (X.totalQuotientSheaf.obj.obj (op (U i)))ˣ)
    (hf : ∀ i j, ∃ u : Γ(X, U i ⊓ U j)ˣ, resUnit (homOfLE inf_le_left) (f i) =
      Units.map (toTotalQuotient (U i ⊓ U j)).toMonoidHom u *
        resUnit (homOfLE inf_le_right) (f j)) :
    ∃! D : X.CartierDivisor, ∀ i, IsLocalEquationOn D (U i) (f i) := by
  have hc : TopCat.Presheaf.IsCompatible (cartierSheaf X).obj U
      (fun i => cartierClass (U i) (f i)) := by
    intro i j
    obtain ⟨u, hu⟩ := hf i j
    change (cartierSheaf X).obj.map (homOfLE inf_le_left).op _ =
      (cartierSheaf X).obj.map (homOfLE inf_le_right).op _
    rw [← cartierClass_resUnit, ← cartierClass_resUnit, hu, cartierClass_mul,
      cartierClass_map_units, zero_add]
  obtain ⟨D, hD, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' (cartierSheaf X) U ⊤
    (fun _ => homOfLE le_top) hU.ge _ hc
  exact ⟨D, fun i => (hD i).symm, fun D' hD' => huniq D' fun i => (hD' i).symm⟩

/-- Restricting `D|_U` to an open `V ⊆ U` gives `D|_V`. -/
theorem restrictDivisor_map (D : X.CartierDivisor) {U V : X.Opens} (i : V ⟶ U) :
    (cartierSheaf X).obj.map i.op (restrictDivisor D U) = restrictDivisor D V := by
  simp only [restrictDivisor, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Multiplying a local equation of `D` on `U` by a unit of `𝒪_X` on `U` gives a local equation
of `D` on `U`. -/
theorem IsLocalEquationOn.units_mul {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) (u : Γ(X, U)ˣ) :
    IsLocalEquationOn D U (Units.map (toTotalQuotient U).toMonoidHom u * g) := by
  unfold IsLocalEquationOn at *
  rw [cartierClass_mul, cartierClass_map_units, zero_add, hg]

/-- Being a local equation is a local property. -/
theorem isLocalEquationOn_of_locally {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (i : W ⟶ U), x ∈ W ∧ IsLocalEquationOn D W (resUnit i g)) :
    IsLocalEquationOn D U g := by
  choose W i hxW hW using h
  refine TopCat.Sheaf.eq_of_locally_eq' (cartierSheaf X) (fun x : U => W x.1 x.2) U
    (fun x => i x.1 x.2) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW x hx⟩) _ _ fun x => ?_
  rw [← cartierClass_resUnit, hW, restrictDivisor_map]

/-! ### Support -/

/-- A point `x ∈ U` lies outside the support of `D` iff `D` vanishes on a neighbourhood `V ⊆ U`
of `x`. -/
theorem notMem_cartierSupport_iff {D : X.CartierDivisor} {x : X} {U : X.Opens} (hx : x ∈ U) :
    x ∉ cartierSupport D ↔ ∃ V : X.Opens, x ∈ V ∧ ∃ _ : V ≤ U, restrictDivisor D V = 0 := by
  simp only [cartierSupport, Set.mem_setOf_eq, not_not]
  constructor
  · intro h0
    rw [← map_zero (ConcreteCategory.hom ((cartierSheaf X).presheaf.germ ⊤ x trivial))] at h0
    obtain ⟨W, hxW, iU, iV, hW⟩ :=
      TopCat.Presheaf.germ_eq _ (U := ⊤) (V := ⊤) x trivial trivial D 0 h0
    refine ⟨W ⊓ U, ⟨hxW, hx⟩, inf_le_right, ?_⟩
    have hW0 : restrictDivisor D W = 0 := by
      rw [restrictDivisor, Subsingleton.elim (homOfLE le_top) iU, hW, map_zero]
    rw [← restrictDivisor_map D (homOfLE inf_le_left : W ⊓ U ⟶ W), hW0, map_zero]
  · rintro ⟨V, hxV, -, hV⟩
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE le_top : V ⟶ ⊤) x hxV]
    change ConcreteCategory.hom ((cartierSheaf X).presheaf.germ V x hxV) (restrictDivisor D V) = 0
    rw [hV, map_zero]

/-- A point `x` lies outside the support of `D` iff the germ of `D` at `x` vanishes. -/
theorem germ_cartierSupport_eq_zero_iff {D : X.CartierDivisor} {x : X} :
    x ∉ cartierSupport D ↔ (cartierSheaf X).presheaf.germ ⊤ x trivial D = 0 := by
  simp [cartierSupport]

/-- The complement of the support of a Cartier divisor is open. -/
theorem isOpen_compl_cartierSupport (D : X.CartierDivisor) : IsOpen (cartierSupport D)ᶜ := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨W, hxW, i, j, hij⟩ := (cartierSheaf X).presheaf.germ_eq x
    (show x ∈ (⊤ : X.Opens) from trivial)
    (show x ∈ (⊤ : X.Opens) from trivial) D 0
    ((germ_cartierSupport_eq_zero_iff.mp hx).trans (map_zero _).symm)
  refine ⟨W, fun y hy => ?_, W.2, hxW⟩
  rw [Set.mem_compl_iff, germ_cartierSupport_eq_zero_iff,
    ← TopCat.Presheaf.germ_res_apply (cartierSheaf X).presheaf i y hy, hij, map_zero, map_zero]

/-- The support of a Cartier divisor is closed. -/
theorem isClosed_cartierSupport (D : X.CartierDivisor) : IsClosed (cartierSupport D) :=
  isOpen_compl_iff.1 (isOpen_compl_cartierSupport D)

end MMP.Intersection
