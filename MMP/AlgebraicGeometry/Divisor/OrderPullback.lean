module

public import MMP.AlgebraicGeometry.Divisor.Cycles
public import MMP.AlgebraicGeometry.Divisor.LocalEquation
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotientFraction
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import StacksFrontier.Order.HeightCoheight

/-!
# Well-definedness of orders, the cycle map and pull-backs of Cartier divisors

Let `X` be a scheme and `D` a Cartier divisor on `X`, a global section of `𝓜_X^*/𝒪_X^*`.
A local equation of `D` at `x` is determined up to a unit of `𝒪_{X,x}`, and two divisors with a
common local equation at every point are equal. From this:

* the order `ord_V(D)` of `D` along an `(n-1)`-dimensional subvariety `V` of a scheme of pure
  dimension `n`, computed from a local equation `a/b` at the generic point `v` of `V` as
  `length(𝒪_{X,v}/a) - length(𝒪_{X,v}/b)`, does not depend on the local equation; it exists when
  `X` is locally Noetherian, since then `𝒪_{X,v}` is a Noetherian local ring of dimension at most
  one; it is additive in `D`, vanishes when `V ⊄ Supp D`, and equals `length(𝒪_{X,v}/f)` when
  `D` has a local equation `f ∈ 𝒪_{X,v}`;
* the Weil divisor `[D] = ∑ ord_V(D) [V]` is unique; on a Noetherian scheme it is a finite sum,
  every `V` with `ord_V(D) ≠ 0` is an irreducible component of `Supp D`, `D ↦ [D]` is a
  homomorphism `Div(X) → WDiv(X)`, and `[D]` is effective when `D` is;
* the pull-back of a divisor along a morphism `f : Y ⟶ X` is unique, its local equation at `y`
  is `f^♯a/f^♯b` for every admissible representation `a/b` of a local equation of `D` at
  `f(y)`, and pull-backs along composites agree: `(f ∘ g)^* D = g^* f^* D`.

## Main definitions

* `MMP.Intersection.orderAlong`: `ord_V : Div(X) →+ ℤ`.
* `MMP.Intersection.cycleMap`: the cycle map `Div(X) →+ WDiv(X)`, `D ↦ [D]`.

## Main results

* `MMP.Intersection.IsLocalEquationAt.exists_eq_mul_units`,
  `MMP.Intersection.eq_of_forall_isLocalEquationAt`: local equations are unique up to units and
  determine the divisor.
* `MMP.Intersection.IsOrderAlong.unique`, `MMP.Intersection.existsUnique_isOrderAlong`,
  `MMP.Intersection.IsOrderAlong.add`, `MMP.Intersection.IsOrderAlong.eq_zero_of_not_subset`,
  `MMP.Intersection.IsOrderAlong.eq_length`: the order along a subvariety is well defined.
* `MMP.Intersection.existsUnique_isWeilDivisorOf`,
  `MMP.Intersection.IsWeilDivisorOf.finite_support`, `MMP.Intersection.IsWeilDivisorOf.add`,
  `MMP.Intersection.IsOrderAlong.maximal_of_ne_zero`,
  `MMP.Intersection.IsWeilDivisorOf.nonneg_of_isEffective`: the cycle map is well defined.
* `MMP.Intersection.IsPullback.unique`, `MMP.Intersection.IsPullback.isLocalEquationAt`: the
  pull-back of a divisor is unique, with the expected local equations.
* `MMP.Intersection.IsPullback.comp_eq`: pull-back along a composite.

## Implementation notes

Lazarsfeld's schemes are of finite type over `ℂ`; the results that need finite lengths assume
only that `X` is locally Noetherian, and the finiteness of `[D]` that the underlying space of `X`
is Noetherian. The bound `dim 𝒪_{X,v} ≤ 1` comes from `height v + coheight v ≤ dim X` in the
specialization order, with `height v = dim V = n - 1` and `dim X ≤ n` for `X` of pure dimension
`n`. An irreducible component of `Supp D` is written as a set maximal among the irreducible
subsets of `Supp D`.

## References

* R. Lazarsfeld, *Positivity in Algebraic Geometry I*, §1.1.A and Remark 1.1.4.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry Order

namespace MMP.Intersection

variable {X Y : Scheme.{u}}

/-! ### Classes of units of `𝓜_X` in `𝓜_X^*/𝒪_X^*` -/

/-- The class of a unit `g` of `Γ(U, 𝓜_X)` in `Γ(U, 𝓜_X^*/𝒪_X^*)` is the image of `g` under the
quotient map `rawUnitGroupQuotientMap`. -/
theorem cartierClass_eq_raw (U : X.Opens) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass U g = (rawUnitGroupQuotientMap X.toTotalQuotientSheaf).app (op U)
      (Additive.ofMul g) := by
  rw [rawUnitGroupQuotientMap_eq]; rfl

/-- Restriction of units of `𝓜_X`. -/
noncomputable abbrev resUnits {U V : X.Opens} (hVU : V ≤ U) :
    (X.totalQuotientSheaf.obj.obj (op U))ˣ →* (X.totalQuotientSheaf.obj.obj (op V))ˣ :=
  Units.map (X.totalQuotientSheaf.obj.map (homOfLE hVU).op).hom.toMonoidHom

/-- The class of the restriction of a unit of `𝓜_X` is the restriction of its class. -/
theorem cartierClass_res {U V : X.Opens} (hVU : V ≤ U)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    cartierClass V (resUnits hVU g) =
      (cartierSheaf X).obj.map (homOfLE hVU).op (cartierClass U g) := by
  unfold cartierClass
  exact ConcreteCategory.congr_hom ((toSheafify (Opens.grothendieckTopology X)
    (unitGroupPresheaf X.totalQuotientSheaf) ≫
    (unitGroupQuotientMap X.toTotalQuotientSheaf).hom).naturality (homOfLE hVU).op)
    (Additive.ofMul g)

/-- The image in `𝓜_X` of a unit of `Γ(U, 𝒪_X)` has trivial class in `Γ(U, 𝓜_X^*/𝒪_X^*)`. -/
theorem cartierClass_units_map (U : X.Opens) (t : (Γ(X, U))ˣ) :
    cartierClass U (Units.map (toTotalQuotient U).toMonoidHom t) = 0 := by
  rw [cartierClass_eq_raw, rawUnitGroupQuotientMap]
  have : (unitGroupMap X.toTotalQuotientSheaf ≫
      cokernel.π (unitGroupMap X.toTotalQuotientSheaf)) = 0 :=
    cokernel.condition _
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U)) this)
    (Additive.ofMul t)
  simp only [NatTrans.comp_app, NatTrans.app_zero] at h2
  have h3 : (cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op U)
      (Additive.ofMul (Units.map (toTotalQuotient U).toMonoidHom t)) = 0 := h2
  change (toSheafify (Opens.grothendieckTopology X)
    (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op U)
      ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op U)
      (Additive.ofMul (Units.map (toTotalQuotient U).toMonoidHom t))) = 0
  rw [h3, map_zero]

/-- The map `𝒪_{X,x} → 𝓜_{X,x}` is injective. -/
theorem stalkToTotalQuotient_injective (x : X) : Function.Injective (stalkToTotalQuotient x) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
  intro V
  exact Stacks.SheafifyMono.injective_toTotalQuotientSheaf_app X.sheaf V

/-- A section of a presheaf of abelian groups on `U` whose image in the sheafification vanishes
restricts to zero on a neighbourhood of every point of `U`. -/
theorem exists_res_eq_zero_of_toSheafify_eq_zero (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    {U : X.Opens} {c : P.obj (op U)}
    (hc : (toSheafify (Opens.grothendieckTopology X) P).app (op U) c = 0) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ P.map (homOfLE hVU).op c = 0 := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  have hinj : Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P)) :=
    (ConcreteCategory.bijective_of_isIso _).1
  have h1 : P.germ U x hx c = P.germ U x hx 0 := by
    apply hinj
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply,
      hc]
    simp
  obtain ⟨V, hxV, i, j, h⟩ := TopCat.Presheaf.germ_eq P x hx hx c 0 h1
  refine ⟨V, i.le, hxV, ?_⟩
  rw [show (homOfLE i.le) = i from rfl, h, map_zero]

/-- A unit of `Γ(U, 𝓜_X)` whose class in `Γ(U, 𝓜^*/𝒪^*)` vanishes is, near every point of `U`,
the image of a unit of `𝒪_X`. -/
theorem exists_units_map_of_cartierClass_eq_zero {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : cartierClass U g = 0) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ t : (Γ(X, V))ˣ,
      resUnits hVU g = Units.map (toTotalQuotient V).toMonoidHom t := by
  rw [cartierClass_eq_raw, rawUnitGroupQuotientMap] at hg
  have hg' : (toSheafify (Opens.grothendieckTopology X)
      (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op U)
      ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op U) (Additive.ofMul g)) = 0 := hg
  obtain ⟨V, hVU, hxV, hV⟩ := exists_res_eq_zero_of_toSheafify_eq_zero _ hg' hx
  have hnat := ConcreteCategory.congr_hom
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).naturality (homOfLE hVU).op)
    (Additive.ofMul g)
  have hz : (cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V)
      ((unitGroupPresheaf X.totalQuotientSheaf).map (homOfLE hVU).op (Additive.ofMul g)) = 0 :=
    hnat.trans hV
  have hex := (ShortComplex.cokernelSequence_exact (unitGroupMap X.toTotalQuotientSheaf)).map
    ((evaluation _ _).obj (op V))
  obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff _).1 hex _ hz
  exact ⟨V, hVU, hxV, Additive.toMul t, (congrArg Additive.toMul ht).symm⟩

/-- Restricting `D|_U` to `V ≤ U` gives `D|_V`. -/
theorem restrictDivisor_res (D : X.CartierDivisor) {U V : X.Opens} (hVU : V ≤ U) :
    (cartierSheaf X).obj.map (homOfLE hVU).op (restrictDivisor D U) = restrictDivisor D V :=
  (ConcreteCategory.congr_hom ((cartierSheaf X).obj.map_comp (homOfLE (le_top : U ≤ ⊤)).op
    (homOfLE hVU).op) D).symm

/-- The restriction to `V ≤ U` of a local equation of `D` on `U` is a local equation of `D` on
`V`. -/
theorem IsLocalEquationOn.res {D : X.CartierDivisor} {U V : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) (hVU : V ≤ U) :
    IsLocalEquationOn D V (resUnits hVU g) := by
  unfold IsLocalEquationOn at hg ⊢
  rw [cartierClass_res, hg, restrictDivisor_res]

/-- The germ map on units of `𝓜_X`. -/
noncomputable abbrev germUnits {U : X.Opens} {x : X} (hx : x ∈ U) :
    (X.totalQuotientSheaf.obj.obj (op U))ˣ →* (X.totalQuotientSheaf.presheaf.stalk x)ˣ :=
  Units.map (X.totalQuotientSheaf.presheaf.germ U x hx).hom.toMonoidHom

/-- The germ at `x` of the restriction of a unit of `𝓜_X` is the germ of the unit. -/
theorem germUnits_res {U V : X.Opens} (hVU : V ≤ U) {x : X} (hx : x ∈ V)
    (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    germUnits hx (resUnits hVU g) = germUnits (hVU hx) g :=
  Units.ext (TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE hVU) x hx
    (g : X.totalQuotientSheaf.presheaf.obj (op U)))

/-- A local equation of `D` at `x` is a unit of `𝓜_{X,x}`. -/
theorem IsLocalEquationAt.isUnit {D : X.CartierDivisor} {x : X}
    {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) : IsUnit f := by
  obtain ⟨U, hx, g, -, rfl⟩ := hf
  exact g.isUnit.map _

/-- Multiplying a local equation at `x` by a unit of `𝒪_{X,x}` gives a local equation at `x`. -/
theorem IsLocalEquationAt.mul_units {D : X.CartierDivisor} {x : X}
    {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f)
    (w : (X.presheaf.stalk x)ˣ) :
    IsLocalEquationAt D x (f * stalkToTotalQuotient x w) := by
  obtain ⟨U, hxU, g, hg, rfl⟩ := hf
  obtain ⟨W, hxW, t, ht⟩ := X.presheaf.exists_germ_eq (w : X.presheaf.stalk x)
  have hxB : x ∈ X.basicOpen t := (X.mem_basicOpen t x hxW).2 (ht ▸ w.isUnit)
  let B := X.basicOpen t ⊓ U
  have hBW : B ≤ W := inf_le_left.trans (X.basicOpen_le t)
  have hBU : B ≤ U := inf_le_right
  have htB : IsUnit (X.presheaf.map (homOfLE hBW).op t) := by
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro y hy
    have : X.presheaf.germ B y hy (X.presheaf.map (homOfLE hBW).op t) =
        X.presheaf.germ W y (hBW hy) t := TopCat.Presheaf.germ_res_apply _ _ _ _ _
    change IsUnit (X.presheaf.germ B y hy (X.presheaf.map (homOfLE hBW).op t))
    rw [this]
    exact (X.mem_basicOpen t y (hBW hy)).1 hy.1
  refine ⟨B, ⟨hxB, hxU⟩, resUnits hBU g * Units.map (toTotalQuotient B).toMonoidHom htB.unit,
    ?_, ?_⟩
  · unfold IsLocalEquationOn
    rw [cartierClass_mul, cartierClass_units_map, add_zero]
    exact hg.res hBU
  · rw [Units.val_mul, map_mul]
    congr 1
    · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    · exact (germ_toTotalQuotient (show x ∈ B from ⟨hxB, hxU⟩) _).trans
        (congrArg (stalkToTotalQuotient x)
          ((TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hBW) x _ t).trans ht))

/-- Two local equations of `D` at `x` differ by a unit of `𝒪_{X,x}`. -/
theorem IsLocalEquationAt.exists_eq_mul_units {D : X.CartierDivisor} {x : X}
    {f f' : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f)
    (hf' : IsLocalEquationAt D x f') :
    ∃ w : (X.presheaf.stalk x)ˣ, f' = f * stalkToTotalQuotient x w := by
  obtain ⟨U, hxU, g, hg, rfl⟩ := hf
  obtain ⟨U', hxU', g', hg', rfl⟩ := hf'
  have hc : cartierClass (U ⊓ U') ((resUnits inf_le_left g)⁻¹ * resUnits inf_le_right g') = 0 := by
    rw [cartierClass_mul, cartierClass_inv, hg.res, hg'.res, neg_add_cancel]
  obtain ⟨V, hVW, hxV, t, ht⟩ := exists_units_map_of_cartierClass_eq_zero hc ⟨hxU, hxU'⟩
  refine ⟨Units.map (X.presheaf.germ V x hxV).hom.toMonoidHom t, ?_⟩
  have h1 := congrArg (germUnits hxV) ht
  simp only [map_mul, map_inv, germUnits_res] at h1
  have h2 : germUnits hxV (Units.map (toTotalQuotient V).toMonoidHom t) =
      Units.map (stalkToTotalQuotient x).toMonoidHom
        (Units.map (X.presheaf.germ V x hxV).hom.toMonoidHom t) :=
    Units.ext (germ_toTotalQuotient hxV _)
  rw [h2, inv_mul_eq_iff_eq_mul] at h1
  exact congrArg Units.val h1

/-- Divisors with a common local equation at every point are equal. -/
theorem eq_of_forall_isLocalEquationAt {D D' : X.CartierDivisor}
    (h : ∀ x, ∃ f, IsLocalEquationAt D x f ∧ IsLocalEquationAt D' x f) : D = D' := by
  apply TopCat.Presheaf.section_ext (cartierSheaf X) ⊤ D D'
  intro x _
  obtain ⟨f, ⟨U, hxU, g, hg, hgf⟩, ⟨U', hxU', g', hg', hgf'⟩⟩ := h x
  obtain ⟨W, hxW, i, j, hij⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hxU hxU' (g : _) (g' : _)
    (hgf.trans hgf'.symm)
  have hW : resUnits i.le g = resUnits j.le g' := Units.ext hij
  have h1 := hg.res i.le
  have h2 := hg'.res j.le
  unfold IsLocalEquationOn at h1 h2
  rw [hW, h2] at h1
  have e1 : (cartierSheaf X).presheaf.germ ⊤ x trivial D =
      (cartierSheaf X).presheaf.germ W x hxW (restrictDivisor D W) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  have e2 : (cartierSheaf X).presheaf.germ ⊤ x trivial D' =
      (cartierSheaf X).presheaf.germ W x hxW (restrictDivisor D' W) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [e1, e2, h1]

/-- Local equations of `D₁, D₂` at `x` multiply to a local equation of `D₁ + D₂`. -/
theorem IsLocalEquationAt.add {D₁ D₂ : X.CartierDivisor} {x : X}
    {f₁ f₂ : X.totalQuotientSheaf.presheaf.stalk x} (h₁ : IsLocalEquationAt D₁ x f₁)
    (h₂ : IsLocalEquationAt D₂ x f₂) : IsLocalEquationAt (D₁ + D₂) x (f₁ * f₂) := by
  obtain ⟨U, hxU, g, hg, rfl⟩ := h₁
  obtain ⟨U', hxU', g', hg', rfl⟩ := h₂
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, resUnits inf_le_left g * resUnits inf_le_right g', ?_, ?_⟩
  · unfold IsLocalEquationOn
    rw [cartierClass_mul, hg.res, hg'.res]
    exact (map_add _ D₁ D₂).symm
  · rw [Units.val_mul, map_mul]
    congr 1 <;> exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Off the support, `1` is a local equation. -/
theorem isLocalEquationAt_one_of_notMem_cartierSupport {D : X.CartierDivisor} {x : X}
    (hx : x ∉ cartierSupport D) : IsLocalEquationAt D x 1 := by
  rw [germ_cartierSupport_eq_zero_iff] at hx
  obtain ⟨W, hxW, i, j, hij⟩ := (cartierSheaf X).presheaf.germ_eq x
    (show x ∈ (⊤ : X.Opens) from trivial)
    (show x ∈ (⊤ : X.Opens) from trivial) D 0
    (hx.trans (map_zero _).symm)
  refine ⟨W, hxW, 1, ?_, map_one _⟩
  unfold IsLocalEquationOn
  rw [cartierClass_one]
  exact (hij.trans (map_zero _)).symm

/-- If `1` is a local equation of `D` at `x`, then `x` is not in `Supp D`. -/
theorem notMem_cartierSupport_of_isLocalEquationAt_one {D : X.CartierDivisor} {x : X}
    (h : IsLocalEquationAt D x 1) : x ∉ cartierSupport D := by
  obtain ⟨U, hxU, g, hg, hg1⟩ := h
  have hg1' : X.totalQuotientSheaf.presheaf.germ U x hxU (g : _) =
      X.totalQuotientSheaf.presheaf.germ U x hxU 1 := by rw [hg1, map_one]
  obtain ⟨W, hxW, i, j, hij⟩ := X.totalQuotientSheaf.presheaf.germ_eq x hxU hxU (g : _) 1 hg1'
  have hW : resUnits i.le g = 1 := Units.ext (hij.trans (by rw [map_one]; rfl))
  have h1 := hg.res i.le
  unfold IsLocalEquationOn at h1
  rw [hW, cartierClass_one] at h1
  rw [germ_cartierSupport_eq_zero_iff, show (cartierSheaf X).presheaf.germ ⊤ x trivial D =
      (cartierSheaf X).presheaf.germ W x hxW (restrictDivisor D W) from
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm, ← h1, map_zero]

/-! ### Fractions -/

/-- An element of `𝒪_{X,x}` whose image in `𝓜_{X,x}` is a unit is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient {x : X} {c : X.presheaf.stalk x}
    (hc : IsUnit (stalkToTotalQuotient x c)) : c ∈ nonZeroDivisors (X.presheaf.stalk x) :=
  mem_nonZeroDivisors_of_injective (stalkToTotalQuotient_injective x) hc.mem_nonZeroDivisors

/-- If `f = a/b` and `f' = a'/b'`, then `f f' = (a a')/(b b')`. -/
theorem IsFraction.mul {x : X} {f f' : X.totalQuotientSheaf.presheaf.stalk x}
    {a b a' b' : X.presheaf.stalk x} (h : IsFraction f a b) (h' : IsFraction f' a' b') :
    IsFraction (f * f') (a * a') (b * b') := by
  refine ⟨by rw [map_mul]; exact h.1.mul h'.1, ?_⟩
  rw [map_mul, map_mul, ← h.2, ← h'.2]; ring

/-- `1 = 1/1` in `𝓜_{X,x}`. -/
theorem isFraction_one_one_one (x : X) :
    IsFraction (1 : X.totalQuotientSheaf.presheaf.stalk x) 1 1 :=
  ⟨by rw [map_one]; exact isUnit_one, by rw [map_one, one_mul]⟩

/-- If `f = a/b` and `f' = a'/b'` with `f' = f · c`, then `a' b = a b' c`. -/
theorem IsFraction.mul_eq_of_eq_mul {x : X} {f f' : X.totalQuotientSheaf.presheaf.stalk x}
    {a b a' b' c : X.presheaf.stalk x} (h : IsFraction f a b) (h' : IsFraction f' a' b')
    (hc : f' = f * stalkToTotalQuotient x c) : a' * b = a * b' * c := by
  apply stalkToTotalQuotient_injective
  rw [map_mul, map_mul, map_mul, ← h'.2, ← h.2, hc]; ring

/-- If `f = a/b` and `f' = a'/b'` with `a' b = a b' c`, then `f' = f · c`. -/
theorem IsFraction.eq_mul_of_mul_eq {x : X} {f f' : X.totalQuotientSheaf.presheaf.stalk x}
    {a b a' b' c : X.presheaf.stalk x} (h : IsFraction f a b) (h' : IsFraction f' a' b')
    (hc : a' * b = a * b' * c) : f' = f * stalkToTotalQuotient x c := by
  have hu : IsUnit (stalkToTotalQuotient x b * stalkToTotalQuotient x b') := h.1.mul h'.1
  apply hu.mul_left_cancel
  have e := congrArg (stalkToTotalQuotient x) hc
  rw [map_mul, map_mul, map_mul, ← h'.2, ← h.2] at e
  linear_combination e

/-! ### The order along a subvariety -/

/-- If `R/aR` has length `n`, then the order of `a` in `R` is `n`. -/
theorem ord_eq_of_length_eq {R : Type*} [CommRing R] {a : R} {n : ℕ}
    (h : Module.length R (R ⧸ Ideal.span {a}) = n) : Ring.ord R a = n := h

/-- The order of `D` along `V` is unique. -/
theorem IsOrderAlong.unique {D : X.CartierDivisor} {V : Scheme.Subvariety X} {N N' : ℤ}
    (h : IsOrderAlong D V N) (h' : IsOrderAlong D V N') : N = N' := by
  obtain ⟨a, b, ha, hb, ⟨g, hg, hab⟩, la, lb, hla, hlb, rfl⟩ := h
  obtain ⟨a', b', ha', hb', ⟨g', hg', hab'⟩, la', lb', hla', hlb', rfl⟩ := h'
  obtain ⟨w, hw⟩ := hg.exists_eq_mul_units hg'
  have key := hab.mul_eq_of_eq_mul hab' hw
  have e := congrArg (Ring.ord _) key
  rw [Ring.ord_mul _ hb, Ring.ord_mul_of_isUnit_right w.isUnit, Ring.ord_mul _ hb',
    ord_eq_of_length_eq hla, ord_eq_of_length_eq hlb, ord_eq_of_length_eq hla',
    ord_eq_of_length_eq hlb'] at e
  have : la' + lb = la + lb' := by exact_mod_cast e
  omega

/-- Orders are additive in the divisor. -/
theorem IsOrderAlong.add {D₁ D₂ : X.CartierDivisor} {V : Scheme.Subvariety X} {N₁ N₂ : ℤ}
    (h₁ : IsOrderAlong D₁ V N₁) (h₂ : IsOrderAlong D₂ V N₂) :
    IsOrderAlong (D₁ + D₂) V (N₁ + N₂) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, ⟨g₁, hg₁, hab₁⟩, la₁, lb₁, hla₁, hlb₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, ha₂, hb₂, ⟨g₂, hg₂, hab₂⟩, la₂, lb₂, hla₂, hlb₂, rfl⟩ := h₂
  refine ⟨a₁ * a₂, b₁ * b₂, mul_mem ha₁ ha₂, mul_mem hb₁ hb₂,
    ⟨g₁ * g₂, hg₁.add hg₂, hab₁.mul hab₂⟩, la₁ + la₂, lb₁ + lb₂, ?_, ?_, ?_⟩
  · change Ring.ord _ (a₁ * a₂) = _
    rw [Ring.ord_mul _ ha₂, ord_eq_of_length_eq hla₁, ord_eq_of_length_eq hla₂]; push_cast; rfl
  · change Ring.ord _ (b₁ * b₂) = _
    rw [Ring.ord_mul _ hb₂, ord_eq_of_length_eq hlb₁, ord_eq_of_length_eq hlb₂]; push_cast; rfl
  · push_cast; ring

/-- If `1` is a local equation of `D` at the generic point of `V`, then `0` is an order of `D`
along `V`. -/
theorem isOrderAlong_zero_of_isLocalEquationAt_one {D : X.CartierDivisor}
    {V : Scheme.Subvariety X} (h : IsLocalEquationAt D V.genericPoint 1) : IsOrderAlong D V 0 :=
  ⟨1, 1, one_mem _, one_mem _, ⟨1, h, isFraction_one_one_one _⟩, 0, 0, Ring.ord_one _,
    Ring.ord_one _, rfl⟩

/-- The generic point of `V` lies in `Supp D` if and only if `V ⊆ Supp D`. -/
theorem genericPoint_mem_cartierSupport_iff {D : X.CartierDivisor} {V : Scheme.Subvariety X} :
    V.genericPoint ∈ cartierSupport D ↔ V.support ⊆ cartierSupport D := by
  refine ⟨fun h => ?_, fun h => h V.isGenericPoint_genericPoint.mem⟩
  rw [← V.isGenericPoint_genericPoint.def]
  exact closure_minimal (Set.singleton_subset_iff.2 h) (isClosed_cartierSupport D)

/-- The order along a subvariety not contained in `Supp D` is zero. -/
theorem IsOrderAlong.eq_zero_of_not_subset {D : X.CartierDivisor} {V : Scheme.Subvariety X}
    {N : ℤ} (h : IsOrderAlong D V N) (hV : ¬ V.support ⊆ cartierSupport D) : N = 0 := by
  rw [← genericPoint_mem_cartierSupport_iff] at hV
  exact h.unique (isOrderAlong_zero_of_isLocalEquationAt_one
    (isLocalEquationAt_one_of_notMem_cartierSupport hV))

/-- If `D` has a local equation `f ∈ 𝒪_{X,v}` at the generic point `v` of `V`, the order of `D`
along `V` is `length(𝒪_{X,v}/f𝒪_{X,v}) ≥ 0`. -/
theorem IsOrderAlong.eq_length {D : X.CartierDivisor} {V : Scheme.Subvariety X} {N : ℤ}
    (h : IsOrderAlong D V N) {f : X.presheaf.stalk V.genericPoint}
    (hf : IsLocalEquationAt D V.genericPoint (stalkToTotalQuotient _ f)) :
    ∃ n : ℕ, Module.length (X.presheaf.stalk V.genericPoint)
        (X.presheaf.stalk V.genericPoint ⧸ Ideal.span {f}) = n ∧ N = n := by
  obtain ⟨a, b, ha, hb, ⟨g, hg, hab⟩, la, lb, hla, hlb, rfl⟩ := h
  have hf1 : IsFraction (stalkToTotalQuotient _ f) f 1 :=
    ⟨by rw [map_one]; exact isUnit_one, by rw [map_one, one_mul]⟩
  obtain ⟨w, hw⟩ := hg.exists_eq_mul_units hf
  have key := hab.mul_eq_of_eq_mul hf1 hw
  have e := congrArg (Ring.ord _) key
  rw [Ring.ord_mul _ hb, mul_one, Ring.ord_mul_of_isUnit_right w.isUnit,
    ord_eq_of_length_eq hla, ord_eq_of_length_eq hlb] at e
  have hne : Ring.ord _ f ≠ ⊤ := by
    intro htop; rw [htop, top_add] at e; exact ENat.natCast_ne_top _ e.symm
  refine ⟨(Ring.ord _ f).toNat, (ENat.natCast_toNat hne).symm, ?_⟩
  rw [← ENat.natCast_toNat hne] at e
  have : (Ring.ord _ f).toNat + lb = la := by exact_mod_cast e
  omega

/-! ### Pull-backs -/

/-- Under a pull-back, the local equations along any two admissible representations differ by the
image of a unit. -/
theorem IsFraction.pullback_eq_mul {f : Y ⟶ X} {D : X.CartierDivisor} {y : Y}
    {a b a₁ b₁ : X.presheaf.stalk (f y)} {g g₁ : X.totalQuotientSheaf.presheaf.stalk (f y)}
    (hg : IsLocalEquationAt D (f y) g) (hab : IsFraction g a b)
    (hg₁ : IsLocalEquationAt D (f y) g₁) (hab₁ : IsFraction g₁ a₁ b₁)
    {g' g₁' : Y.totalQuotientSheaf.presheaf.stalk y}
    (h' : IsFraction g' (f.stalkMap y a) (f.stalkMap y b))
    (h₁' : IsFraction g₁' (f.stalkMap y a₁) (f.stalkMap y b₁)) :
    ∃ w : (Y.presheaf.stalk y)ˣ, g₁' = g' * stalkToTotalQuotient y w := by
  obtain ⟨w, hw⟩ := hg.exists_eq_mul_units hg₁
  have key := hab.mul_eq_of_eq_mul hab₁ hw
  have key' := congrArg (f.stalkMap y).hom key
  simp only [map_mul] at key'
  exact ⟨Units.map (f.stalkMap y).hom.toMonoidHom w, h'.eq_mul_of_mul_eq h₁' key'⟩

/-- **Lazarsfeld §1.1.A.** If `D'` is a pull-back of `D` along `f`, then for *every*
representation `a/b` of a local equation of `D` at `f(y)` with `f^♯a, f^♯b` non-zero-divisors,
`f^♯a/f^♯b` is a local equation of `D'` at `y`. -/
theorem IsPullback.isLocalEquationAt {f : Y ⟶ X} {D : X.CartierDivisor} {D' : Y.CartierDivisor}
    (h : IsPullback f D D') {y : Y} {a b : X.presheaf.stalk (f y)}
    {g : X.totalQuotientSheaf.presheaf.stalk (f y)} (hg : IsLocalEquationAt D (f y) g)
    (hab : IsFraction g a b) {g' : Y.totalQuotientSheaf.presheaf.stalk y}
    (h' : IsFraction g' (f.stalkMap y a) (f.stalkMap y b)) : IsLocalEquationAt D' y g' := by
  obtain ⟨a₀, b₀, ⟨g₀, hg₀, hab₀⟩, -, -, g₀', hg₀', h₀'⟩ := h.2 y
  obtain ⟨w, hw⟩ := IsFraction.pullback_eq_mul hg₀ hab₀ hg hab h₀' h'
  rw [hw]
  exact hg₀'.mul_units w

/-- **Lazarsfeld §1.1.A.** The pull-back of a divisor is unique. -/
theorem IsPullback.unique {f : Y ⟶ X} {D : X.CartierDivisor} {D₁ D₂ : Y.CartierDivisor}
    (h₁ : IsPullback f D D₁) (h₂ : IsPullback f D D₂) : D₁ = D₂ := by
  refine eq_of_forall_isLocalEquationAt fun y => ?_
  obtain ⟨a, b, ⟨g, hg, hab⟩, -, -, g', hg', h'⟩ := h₁.2 y
  exact ⟨g', hg', h₂.isLocalEquationAt hg hab h'⟩

/-- **Lazarsfeld §1.1.A.** Pull-back along a composite: if `D'` is a pull-back of `D` along
`f : Y ⟶ X`, `D''` a pull-back of `D'` along `g : Z ⟶ Y`, and `E` a pull-back of `D` along
`g ≫ f`, then `E = D''`, i.e. `(f ∘ g)^* D = g^* f^* D`. -/
@[mmp "lem_p01a_divisor_pullback_well_defined_composite"]
theorem IsPullback.comp_eq {Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y} {D : X.CartierDivisor}
    {D' : Y.CartierDivisor} {D'' E : Z.CartierDivisor} (hf : IsPullback f D D')
    (hg : IsPullback g D' D'') (hgf : IsPullback (g ≫ f) D E) : E = D'' := by
  refine eq_of_forall_isLocalEquationAt fun z => ?_
  have H : ∃ a b : X.presheaf.stalk (f (g z)),
      (∃ g₀, IsLocalEquationAt D (f (g z)) g₀ ∧ IsFraction g₀ a b) ∧
      ∃ e, IsLocalEquationAt E z e ∧
        IsFraction e (g.stalkMap z (f.stalkMap (g z) a)) (g.stalkMap z (f.stalkMap (g z) b)) := by
    obtain ⟨a, b, h1, -, -, e, he, he'⟩ := hgf.2 z
    rw [Scheme.Hom.stalkMap_comp] at he'
    exact ⟨a, b, h1, e, he, he'⟩
  obtain ⟨a, b, ⟨g₀, hg₀, hab⟩, e, he, he''⟩ := H
  obtain ⟨a₁, b₁, ⟨g₁, hg₁, hab₁⟩, -, hb₁, h', hh', hh''⟩ := hf.2 (g z)
  obtain ⟨a₂, b₂, ⟨k₀, hk₀, hab₂⟩, -, -, k, hk, hk'⟩ := hg.2 z
  refine ⟨e, he, ?_⟩
  set φ := (f.stalkMap (g z)).hom
  set ψ := (g.stalkMap z).hom
  obtain ⟨w, hw⟩ := hg₀.exists_eq_mul_units hg₁
  have k1 := congrArg φ (hab.mul_eq_of_eq_mul hab₁ hw)
  rw [map_mul, map_mul, map_mul] at k1
  obtain ⟨u, hu⟩ := hh'.exists_eq_mul_units hk₀
  have k2 := hh''.mul_eq_of_eq_mul hab₂ hu
  have k3 : a₂ * φ b =
      φ a * b₂ * ((u : Y.presheaf.stalk (g z)) * φ (w : X.presheaf.stalk (f (g z)))) := by
    rw [← sub_eq_zero]
    apply (mem_nonZeroDivisors_iff_right.1 hb₁)
    linear_combination (φ b) * k2 + (b₂ * u) * k1
  have k4 := congrArg ψ k3
  rw [map_mul, map_mul, map_mul, map_mul] at k4
  set c : (Z.presheaf.stalk z)ˣ :=
    Units.map ψ.toMonoidHom (u * Units.map φ.toMonoidHom w) with hc
  have hkc : k = e * stalkToTotalQuotient z (c : Z.presheaf.stalk z) := by
    refine he''.eq_mul_of_mul_eq hk' ?_
    rw [k4, hc, Units.coe_map, Units.val_mul, Units.coe_map, MonoidHom.map_mul]
    rfl
  have := hk.mul_units c⁻¹
  rwa [hkc, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] at this

/-- The dimension of a subvariety is the height of its generic point. -/
theorem subvarietyDim_eq_height (V : Scheme.Subvariety X) :
    subvarietyDim V = height V.genericPoint :=
  V.dim_eq_height_genericPoint

/-- On a scheme of pure dimension `n`, every point has height at most `n`. -/
theorem height_le_of_isPureDimensional {n : ℕ} (hX : IsPureDimensional X n) (x : X) :
    height x ≤ n := by
  set C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hCirr : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  set W : Scheme.Subvariety X := Scheme.Subvariety.ofIrreducibleCloseds ⟨C, hCirr, hCcl⟩
  have hWsupp : W.support = C := Scheme.Subvariety.support_ofIrreducibleCloseds _
  have hxle : x ≤ W.genericPoint := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure,
      Scheme.Subvariety.closure_genericPoint, hWsupp]
    exact mem_irreducibleComponent
  have hdim : W.dim = n := by
    rw [Scheme.Subvariety.dim_eq_topologicalKrullDim_support, hWsupp]
    exact hX C hC
  have h2 : (height W.genericPoint : WithBot ℕ∞) = n := by
    rw [← Scheme.Subvariety.dim_eq_height_genericPoint, hdim]
  have h2' : height W.genericPoint = n := by exact_mod_cast h2
  exact (height_mono hxle).trans h2'.le

/-- On a scheme of pure dimension `n`, the local ring at the generic point of an
`(n-1)`-dimensional subvariety has dimension at most one. -/
theorem coheight_genericPoint_le_one {n : ℕ} (hX : IsPureDimensional X n)
    (V : Codim1Subvariety X n) : coheight V.1.genericPoint ≤ 1 := by
  have h1 := Order.height_add_coheight_le_krullDim V.1.genericPoint
  rw [← WithBot.coe_add] at h1
  have h2 : krullDim X ≤ n := by
    rw [krullDim_eq_iSup_height]
    exact iSup_le fun x => by exact_mod_cast height_le_of_isPureDimensional hX x
  have h3 := V.2
  rw [subvarietyDim_eq_height] at h3
  have h3' : height V.1.genericPoint + 1 = (n : ℕ∞) := by exact_mod_cast h3
  have h4 : height V.1.genericPoint + coheight V.1.genericPoint ≤ (n : ℕ∞) := by
    exact_mod_cast h1.trans h2
  rw [← h3'] at h4
  have hne : height V.1.genericPoint ≠ ⊤ := by
    intro h; rw [h, top_add] at h3'; exact ENat.top_ne_natCast n h3'
  exact (ENat.add_le_add_iff_left hne).1 h4

/-- On a scheme of pure dimension `n`, the local ring `𝒪_{X,v}` at the generic point `v` of an
`(n-1)`-dimensional subvariety has Krull dimension at most one. -/
theorem krullDimLE_one_of_isPureDimensional {n : ℕ} (hX : IsPureDimensional X n)
    (V : Codim1Subvariety X n) : Ring.KrullDimLE 1 (X.presheaf.stalk V.1.genericPoint) :=
  krullDimLE_of_coheight_le (by exact_mod_cast coheight_genericPoint_le_one hX V)

/-! ### Existence of local equations and of orders -/

/-- Every Cartier divisor has a local equation at every point. -/
theorem exists_isLocalEquationAt (D : X.CartierDivisor) (x : X) :
    ∃ f, IsLocalEquationAt D x f := by
  obtain ⟨V, hVle, ⟨c, hc⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    (isLocallySurjective_toSheafify_addCommGrpCat
      (cokernel (unitGroupMap X.toTotalQuotientSheaf))) ⊤ D x trivial
  obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective
    ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V))).mp inferInstance c
  refine ⟨_, V, hxV, Additive.toMul v, ?_, rfl⟩
  unfold IsLocalEquationOn
  rw [cartierClass_eq_raw]
  change (toSheafify (Opens.grothendieckTopology X)
    (cokernel (unitGroupMap X.toTotalQuotientSheaf))).app (op V)
      ((cokernel.π (unitGroupMap X.toTotalQuotientSheaf)).app (op V) v) = _
  rw [hv]
  exact hc

/-- A local equation at `x` is a fraction `a/b` of non-zero-divisors of `𝒪_{X,x}`. -/
theorem IsLocalEquationAt.exists_isFraction {D : X.CartierDivisor} {x : X}
    {f : X.totalQuotientSheaf.presheaf.stalk x} (hf : IsLocalEquationAt D x f) :
    ∃ a b : X.presheaf.stalk x, a ∈ nonZeroDivisors _ ∧ b ∈ nonZeroDivisors _ ∧
      IsFraction f a b := by
  obtain ⟨U, hxU, g, hg, rfl⟩ := hf
  obtain ⟨V, hVU, hxV, a, b, hb, hab⟩ :=
    exists_nhds_mul_toTotalQuotientSheaf_app_eq X.sheaf U (g : _) hxU
  have hfr : IsFraction (X.totalQuotientSheaf.presheaf.germ U x hxU (g : _))
      (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) := by
    have ea := germ_toTotalQuotient (X := X) (U := V) hxV a
    have eb := germ_toTotalQuotient (X := X) (U := V) hxV b
    refine ⟨?_, ?_⟩
    · erw [← eb]; exact hb.map _
    · erw [← ea, ← eb,
        ← TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE hVU) x hxV,
        ← map_mul, mul_comm]
      exact congrArg _ hab
  refine ⟨_, _, ?_, ?_, hfr⟩
  · apply mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient
    rw [← hfr.2]
    exact hfr.1.mul (g.isUnit.map _)
  · exact mem_nonZeroDivisors_of_isUnit_stalkToTotalQuotient hfr.1

/-- If `𝒪_{X,v}` is a Noetherian ring of dimension at most one, `D` has an order along `V`. -/
theorem exists_isOrderAlong (D : X.CartierDivisor) (V : Scheme.Subvariety X)
    [IsNoetherianRing (X.presheaf.stalk V.genericPoint)]
    [Ring.KrullDimLE 1 (X.presheaf.stalk V.genericPoint)] : ∃ N, IsOrderAlong D V N := by
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt D V.genericPoint
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  exact ⟨_, a, b, ha, hb, ⟨f, hf, hab⟩, _, _, (ENat.natCast_toNat (Ring.ord_ne_top ha)).symm,
    (ENat.natCast_toNat (Ring.ord_ne_top hb)).symm, rfl⟩

/-- At a point whose local ring is Artinian, every Cartier divisor is trivial. -/
theorem notMem_cartierSupport_of_isArtinianRing (D : X.CartierDivisor) (x : X)
    [IsArtinianRing (X.presheaf.stalk x)] : x ∉ cartierSupport D := by
  obtain ⟨f, hf⟩ := exists_isLocalEquationAt D x
  obtain ⟨a, b, ha, hb, hab⟩ := hf.exists_isFraction
  have ua := IsArtinianRing.isUnit_of_mem_nonZeroDivisors ha
  have ub := IsArtinianRing.isUnit_of_mem_nonZeroDivisors hb
  set w : (X.presheaf.stalk x)ˣ := ub.unit * ua.unit⁻¹
  have h1 : (1 : X.totalQuotientSheaf.presheaf.stalk x) = f * stalkToTotalQuotient x w := by
    refine hab.eq_mul_of_mul_eq (isFraction_one_one_one x) ?_
    simp only [w, Units.val_mul, IsUnit.unit_spec, one_mul, mul_one]
    rw [mul_comm b, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  exact notMem_cartierSupport_of_isLocalEquationAt_one (h1 ▸ hf.mul_units w)

/-! ### The order along a subvariety is well defined -/

/-- **Lazarsfeld Rem. 1.1.4.** On a locally Noetherian scheme of pure dimension `n`, a Cartier
divisor has exactly one order along each `(n-1)`-dimensional subvariety. -/
@[mmp "lem_p01a_order_along_subvariety_well_defined"]
theorem existsUnique_isOrderAlong [IsLocallyNoetherian X] {n : ℕ} (hX : IsPureDimensional X n)
    (D : X.CartierDivisor) (V : Codim1Subvariety X n) : ∃! N, IsOrderAlong D V.1 N := by
  have := krullDimLE_one_of_isPureDimensional hX V
  obtain ⟨N, hN⟩ := exists_isOrderAlong D V.1
  exact ⟨N, hN, fun N' hN' => hN'.unique hN⟩

/-- The zero divisor has order `0` along every subvariety. -/
theorem isOrderAlong_zero (V : Scheme.Subvariety X) : IsOrderAlong (0 : X.CartierDivisor) V 0 :=
  isOrderAlong_zero_of_isLocalEquationAt_one
    (isLocalEquationAt_one_of_notMem_cartierSupport (by simp [cartierSupport]))

/-- **Lazarsfeld Rem. 1.1.4.** The order `ord_V : Div(X) → ℤ` along an `(n-1)`-dimensional
subvariety `V` of a locally Noetherian scheme of pure dimension `n`, as a group homomorphism:
`ord_V(D)` is the unique order of `D` along `V` (`isOrderAlong_orderAlong`). -/
@[mmp "lem_p01a_order_along_subvariety_well_defined"]
def orderAlong [IsLocallyNoetherian X] {n : ℕ} (hX : IsPureDimensional X n)
    (V : Codim1Subvariety X n) : X.CartierDivisor →+ ℤ where
  toFun D := (existsUnique_isOrderAlong hX D V).exists.choose
  map_zero' := ((existsUnique_isOrderAlong hX 0 V).exists.choose_spec).unique (isOrderAlong_zero _)
  map_add' D₁ D₂ := ((existsUnique_isOrderAlong hX (D₁ + D₂) V).exists.choose_spec).unique
    (((existsUnique_isOrderAlong hX D₁ V).exists.choose_spec).add
      ((existsUnique_isOrderAlong hX D₂ V).exists.choose_spec))

/-- `ord_V(D)` is an order of `D` along `V`. -/
theorem isOrderAlong_orderAlong [IsLocallyNoetherian X] {n : ℕ} (hX : IsPureDimensional X n)
    (V : Codim1Subvariety X n) (D : X.CartierDivisor) : IsOrderAlong D V.1 (orderAlong hX V D) :=
  (existsUnique_isOrderAlong hX D V).exists.choose_spec

/-- `ord_V(D) = N` if and only if `N` is an order of `D` along `V`. -/
theorem orderAlong_eq_iff [IsLocallyNoetherian X] {n : ℕ} (hX : IsPureDimensional X n)
    (V : Codim1Subvariety X n) (D : X.CartierDivisor) (N : ℤ) :
    orderAlong hX V D = N ↔ IsOrderAlong D V.1 N :=
  ⟨fun h => h ▸ isOrderAlong_orderAlong hX V D, fun h => (isOrderAlong_orderAlong hX V D).unique h⟩

attribute [mmp "lem_p01a_order_along_subvariety_well_defined"] IsOrderAlong.unique
  IsOrderAlong.add IsOrderAlong.eq_zero_of_not_subset IsOrderAlong.eq_length

/-- If `D` is effective, every order of `D` is non-negative. -/
theorem IsOrderAlong.nonneg_of_isEffective {D : X.CartierDivisor} {V : Scheme.Subvariety X}
    {N : ℤ} (h : IsOrderAlong D V N) (hD : IsEffective D) : 0 ≤ N := by
  obtain ⟨U, hvU, s, hs, hsD⟩ := hD V.genericPoint
  have hf : IsLocalEquationAt D V.genericPoint
      (stalkToTotalQuotient _ (X.presheaf.germ U V.genericPoint hvU s)) :=
    ⟨U, hvU, hs.unit, hsD, germ_toTotalQuotient hvU s⟩
  obtain ⟨n, -, rfl⟩ := h.eq_length hf
  exact Int.natCast_nonneg n

/-! ### The Weil divisor of a Cartier divisor -/

/-- The irreducible closed subsets of a closed subset `S` of a Noetherian space that are maximal
among the irreducible subsets of `S`, i.e. the irreducible components of `S`, are finitely many. -/
theorem finite_setOf_maximal_isIrreducible_subset {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {S : Set α} (hS : IsClosed S) :
    {Z | Maximal (fun Z : Set α => IsIrreducible Z ∧ Z ⊆ S) Z}.Finite := by
  obtain ⟨T, hTf, hTc, hTi, hTU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine hTf.subset fun Z hZ => ?_
  lift T to Finset (Set α) using hTf
  obtain ⟨t, htT, ht⟩ := isIrreducible_iff_sUnion_isClosed.1 hZ.1.1 T hTc (hTU ▸ hZ.1.2)
  have htS : t ⊆ S := hTU ▸ Set.subset_sUnion_of_mem htT
  rwa [ht.antisymm (hZ.2 ⟨hTi _ htT, htS⟩ ht)]

/-- **Lazarsfeld Rem. 1.1.4.** On a locally Noetherian scheme of pure dimension `n`, every
`(n-1)`-dimensional subvariety along which `D` has non-zero order is an irreducible component
of `Supp D`. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
theorem IsOrderAlong.maximal_of_ne_zero [IsLocallyNoetherian X] {n : ℕ}
    (hX : IsPureDimensional X n) {D : X.CartierDivisor} {V : Codim1Subvariety X n} {N : ℤ}
    (h : IsOrderAlong D V.1 N) (hN : N ≠ 0) :
    Maximal (fun Z : Set X => IsIrreducible Z ∧ Z ⊆ cartierSupport D) V.1.support := by
  have hsub : V.1.support ⊆ cartierSupport D :=
    of_not_not fun hc => hN (h.eq_zero_of_not_subset hc)
  refine ⟨⟨V.1.isIrreducible_support, hsub⟩, fun Z ⟨hZ, hZS⟩ hVZ => ?_⟩
  set ζ := hZ.genericPoint
  have hζ : IsGenericPoint ζ (closure Z) := hZ.isGenericPoint_genericPoint_closure
  have hZS' : closure Z ⊆ cartierSupport D := closure_minimal hZS (isClosed_cartierSupport D)
  have hv : V.1.genericPoint ∈ closure Z := subset_closure (hVZ V.1.isGenericPoint_genericPoint.mem)
  have hle : V.1.genericPoint ≤ ζ := Scheme.le_iff_specializes.2 (hζ.specializes hv)
  by_cases hge : ζ ≤ V.1.genericPoint
  · have heq : ζ = V.1.genericPoint :=
      ((Scheme.le_iff_specializes.1 hle).antisymm (Scheme.le_iff_specializes.1 hge)).eq
    calc Z ⊆ closure Z := subset_closure
      _ = closure {ζ} := hζ.def.symm
      _ = V.1.support := by rw [heq]; exact V.1.isGenericPoint_genericPoint.def
  · exfalso
    have hlt : V.1.genericPoint < ζ := lt_of_le_not_ge hle hge
    have h2 := (coheight_add_one_le hlt).trans (coheight_genericPoint_le_one hX V)
    have h3 : coheight ζ ≤ (0 : ℕ) := by
      have : coheight ζ + 1 ≤ 0 + 1 := by simpa using h2
      exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
    have : IsArtinianRing (X.presheaf.stalk ζ) :=
      isArtinianRing_iff_krullDimLE_zero.2 (krullDimLE_of_coheight_le h3)
    exact notMem_cartierSupport_of_isArtinianRing D ζ (hZS' hζ.mem)

/-- **Lazarsfeld Rem. 1.1.4.** On a locally Noetherian scheme of pure dimension `n` with Noetherian
underlying space (e.g. a Noetherian scheme), a Cartier divisor has non-zero order along only
finitely many `(n-1)`-dimensional subvarieties. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
theorem IsWeilDivisorOf.finite_support [IsLocallyNoetherian X] [NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n)
    {D : X.CartierDivisor} {w : Codim1Subvariety X n → ℤ} (h : IsWeilDivisorOf D w) :
    (Function.support w).Finite := by
  refine Set.Finite.of_finite_image (f := fun V : Codim1Subvariety X n => V.1.support)
    ((finite_setOf_maximal_isIrreducible_subset
    (isClosed_cartierSupport D)).subset ?_) ?_
  · rintro _ ⟨V, hV, rfl⟩
    exact (h V).maximal_of_ne_zero hX hV
  · intro V _ W _ hVW
    exact Subtype.ext (Scheme.Subvariety.support_injective hVW)

/-- **Lazarsfeld Rem. 1.1.4.** On a locally Noetherian scheme of pure dimension `n`, a Cartier
divisor has exactly one Weil divisor `[D] = ∑ ord_V(D) [V]`. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
theorem existsUnique_isWeilDivisorOf [IsLocallyNoetherian X] {n : ℕ}
    (hX : IsPureDimensional X n) (D : X.CartierDivisor) :
    ∃! w : Codim1Subvariety X n → ℤ, IsWeilDivisorOf D w :=
  ⟨fun V => orderAlong hX V D, fun V => isOrderAlong_orderAlong hX V D,
    fun _ hw => funext fun V => (hw V).unique (isOrderAlong_orderAlong hX V D)⟩

/-- The Weil divisor of a sum is the sum of the Weil divisors. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
theorem IsWeilDivisorOf.add {n : ℕ} {D₁ D₂ : X.CartierDivisor}
    {w₁ w₂ : Codim1Subvariety X n → ℤ} (h₁ : IsWeilDivisorOf D₁ w₁) (h₂ : IsWeilDivisorOf D₂ w₂) :
    IsWeilDivisorOf (D₁ + D₂) (w₁ + w₂) :=
  fun V => (h₁ V).add (h₂ V)

/-- The Weil divisor of an effective divisor is effective. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
theorem IsWeilDivisorOf.nonneg_of_isEffective {n : ℕ} {D : X.CartierDivisor}
    {w : Codim1Subvariety X n → ℤ} (h : IsWeilDivisorOf D w) (hD : IsEffective D) :
    ∀ V, 0 ≤ w V :=
  fun V => (h V).nonneg_of_isEffective hD

/-- **Lazarsfeld Rem. 1.1.4.** The cycle map `Div(X) → WDiv(X)`, `D ↦ [D] = ∑ ord_V(D) [V]`, on a
Noetherian scheme of pure dimension `n`, as a group homomorphism. -/
@[mmp "lem_p01a_cartier_cycle_map_well_defined"]
def cycleMap [IsLocallyNoetherian X] [NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n) :
    X.CartierDivisor →+ WeilDivisor X n where
  toFun D := Finsupp.ofSupportFinite (fun V => orderAlong hX V D)
    (IsWeilDivisorOf.finite_support hX (fun V => isOrderAlong_orderAlong hX V D))
  map_zero' := by ext V; simp [Finsupp.ofSupportFinite_coe]
  map_add' D₁ D₂ := by ext V; simp [Finsupp.ofSupportFinite_coe]

/-- The coefficient of `[V]` in `[D]` is `ord_V(D)`. -/
theorem cycleMap_apply [IsLocallyNoetherian X] [NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n)
    (D : X.CartierDivisor) (V : Codim1Subvariety X n) :
    cycleMap hX D V = orderAlong hX V D := by
  simp [cycleMap, Finsupp.ofSupportFinite_coe]

/-- `[D]` is a Weil divisor of `D`. -/
theorem isWeilDivisorOf_cycleMap [IsLocallyNoetherian X] [NoetherianSpace X] {n : ℕ}
    (hX : IsPureDimensional X n)
    (D : X.CartierDivisor) : IsWeilDivisorOf D (cycleMap hX D) := fun V => by
  rw [cycleMap_apply]; exact isOrderAlong_orderAlong hX V D

end MMP.Intersection
