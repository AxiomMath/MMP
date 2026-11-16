module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FunctionFieldSection
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.BasicOpenVanishing

/-!
# The pull-back of a Cartier divisor to an integral scheme (Fulton, §2.3)

Let `f : X' ⟶ X` be a morphism from an integral scheme `X'`, with generic point `ξ`, whose image
is not contained in the support of a Cartier divisor `D` on `X`. Let `η = f(ξ)`. If `g` is a local
equation of `D` on `U ∋ η`, its germ at `η` is a unit `a` of `𝒪_{X,η}`, and `f^*D` is the Cartier
divisor on `X'` whose local equation on `f⁻¹(U)` is `f^*(a) ∈ R(X')^*`.

## Main definitions

* `MMP.CartierDivisorPullback.IsGermUnit g hx a`: the unit `a` of `𝒪_{X,x}` is the germ at `x`
  of the unit `g` of `𝒦_X(U)`.
* `MMP.CartierDivisor.pullback f D hD`: the pull-back `f^*D`.

## Main results

* `MMP.CartierDivisor.isLocalEquationOn_pullback`: the local equations of `f^*D`.
* `MMP.CartierDivisor.eq_pullback_iff`: `f^*D` is the only Cartier divisor with them.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.3.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MMP.Intersection MMP.CartierDivisorSheaf

universe u

namespace MMP

namespace CartierDivisorPullback

variable {X : Scheme.{u}}

/-- The map `𝒪_{X,x} → 𝒦_{X,x}` is injective, since `𝒪_X → 𝒦_X` is injective on sections. -/
theorem stalkToTotalQuotient_injective (X : Scheme.{u}) (x : X) :
    Function.Injective (stalkToTotalQuotient (X := X) x) := by
  intro u v h
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.germ_exist u
  obtain ⟨V', hxV', t, rfl⟩ := X.presheaf.germ_exist v
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV' _ _ h
  have hW' : X.toTotalQuotientSheaf.hom.app (op W) (X.presheaf.map iV.op s) =
      X.toTotalQuotientSheaf.hom.app (op W) (X.presheaf.map iV'.op t) :=
    (NatTrans.naturality_apply X.toTotalQuotientSheaf.hom iV.op s).trans
      (hW.trans (NatTrans.naturality_apply X.toTotalQuotientSheaf.hom iV'.op t).symm)
  have := toTotalQuotientSheaf_app_injective X W hW'
  rw [← X.presheaf.germ_res_apply iV x hxW, ← X.presheaf.germ_res_apply iV' x hxW]
  exact congrArg _ this

/-- The germ at `x` of a section of `𝒪_X`, mapped to `𝒦_{X,x}`, is the germ of its image. -/
theorem stalkToTotalQuotient_germ {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    stalkToTotalQuotient x (X.presheaf.germ U x hx s) =
      X.totalQuotientSheaf.presheaf.germ U x hx (toTotalQuotient U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx X.toTotalQuotientSheaf.hom s

/-- `a ∈ 𝒪_{X,x}^*` is the germ at `x` of the unit `g` of `𝒦_X(U)`, `x ∈ U`. -/
def IsGermUnit {U : X.Opens} (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ) {x : X} (hx : x ∈ U)
    (a : (X.presheaf.stalk x)ˣ) : Prop :=
  stalkToTotalQuotient x a.val = X.totalQuotientSheaf.presheaf.germ U x hx g.val

/-- If `g, g'` are local equations of `D` on `U, U'` whose germs at `x ∈ U ∩ U'` are the units
`a, a'` of `𝒪_{X,x}`, then `a / a'` is the germ at `x` of a unit of `Γ(X, U ∩ U')`. -/
theorem exists_germ_mul_eq {D : X.CartierDivisor} {U U' : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} {g' : (X.totalQuotientSheaf.obj.obj (op U'))ˣ}
    (hg : IsLocalEquationOn D U g) (hg' : IsLocalEquationOn D U' g') {x : X}
    (hx : x ∈ U) (hx' : x ∈ U') {a a' : (X.presheaf.stalk x)ˣ} (ha : IsGermUnit g hx a)
    (ha' : IsGermUnit g' hx' a') :
    ∃ b : Γ(X, U ⊓ U')ˣ, X.presheaf.germ (U ⊓ U') x ⟨hx, hx'⟩ b.val * a'.val = a.val := by
  obtain ⟨b, hb⟩ := exists_units_eq_mul_inv
    (isLocalEquation_restrict (inf_le_left : U ⊓ U' ≤ U) hg)
    (isLocalEquation_restrict (inf_le_right : U ⊓ U' ≤ U') hg')
  refine ⟨b, stalkToTotalQuotient_injective X x ?_⟩
  have hb' := congrArg (fun v ↦ X.totalQuotientSheaf.presheaf.germ (U ⊓ U') x ⟨hx, hx'⟩
    ((v * Units.map (resK (inf_le_right : U ⊓ U' ≤ U')).toMonoidHom g' : _ˣ) :
      X.totalQuotientSheaf.obj.obj (op (U ⊓ U')))) hb
  simp only [inv_mul_cancel_right, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    map_mul] at hb'
  rw [map_mul]
  erw [stalkToTotalQuotient_germ]
  rw [ha, ha']
  have hx2 : x ∈ U ⊓ U' := ⟨hx, hx'⟩
  have e1 := TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf
    (homOfLE (inf_le_right : U ⊓ U' ≤ U')) x hx2 (g' : X.totalQuotientSheaf.obj.obj (op U'))
  have e2 := TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf
    (homOfLE (inf_le_left : U ⊓ U' ≤ U)) x hx2 (g : X.totalQuotientSheaf.obj.obj (op U))
  erw [← e1, ← e2]
  exact hb'

/-- If `x ∉ |D|`, the germ at `x` of a local equation of `D` is a unit of `𝒪_{X,x}`. -/
theorem exists_isGermUnit {D : X.CartierDivisor} {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) {x : X}
    (hx : x ∈ U) (h : x ∉ cartierSupport D) : ∃ a, IsGermUnit g hx a := by
  obtain ⟨V, hxV, hVU, hV⟩ := (notMem_cartierSupport_iff hx).1 h
  have h1 : IsLocalEquationOn D V 1 := by
    rw [IsLocalEquationOn, cartierClass_one, hV]
  obtain ⟨u, hu⟩ := exists_units_eq_mul_inv (isLocalEquation_restrict hVU hg) h1
  refine ⟨Units.map (X.presheaf.germ V x hxV).hom.toMonoidHom u, ?_⟩
  have hu' := congrArg (fun v : (X.totalQuotientSheaf.obj.obj (op V))ˣ ↦
    X.totalQuotientSheaf.presheaf.germ V x hxV (v : X.totalQuotientSheaf.obj.obj (op V))) hu
  simp only [inv_one, mul_one, Units.coe_map, MonoidHom.coe_coe] at hu'
  unfold IsGermUnit
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [stalkToTotalQuotient_germ]
  refine hu'.trans ?_
  erw [TopCat.Presheaf.germ_res_apply]

section Integral

variable {X' : Scheme.{u}} [IsIntegral X']

/-- On an integral scheme, the generic point lies in every open containing some point. -/
theorem genericPoint_mem {V : X'.Opens} {x : X'} (hx : x ∈ V) : genericPoint X' ∈ V :=
  ((genericPoint_spec X').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hx⟩

/-- The ring map `R(X') → 𝒦_{X'}(V)` on an integral scheme `X'`. -/
abbrev functionFieldToK (V : X'.Opens) :
    X'.functionField →+* X'.totalQuotientSheaf.obj.obj (op V) :=
  ((functionFieldToTotalQuotientSheaf X').app (op V)).hom

/-- A nonzero rational function `r ∈ R(X')^*` as a unit of `𝒦_{X'}(V)`. -/
abbrev ofFunctionField (V : X'.Opens) (r : X'.functionFieldˣ) :
    (X'.totalQuotientSheaf.obj.obj (op V))ˣ :=
  Units.map (functionFieldToK V).toMonoidHom r

/-- Restricting `r ∈ R(X')^*`, viewed as a unit of `𝒦_{X'}(V)`, to `W ⊆ V` gives `r` viewed as a
unit of `𝒦_{X'}(W)`. -/
theorem resUnit_ofFunctionField {V W : X'.Opens} (i : W ⟶ V) (r : X'.functionFieldˣ) :
    resUnit i (ofFunctionField V r) = ofFunctionField W r :=
  Units.ext (NatTrans.naturality_apply (functionFieldToTotalQuotientSheaf X') i.op r.val).symm

/-- A section `c` of `𝒪_{X'}` over `V` whose germ at the generic point is `r` maps to `r` in
`𝒦_{X'}(V)`. -/
theorem toTotalQuotient_eq_functionFieldToK {V : X'.Opens} (c : Γ(X', V))
    (hξ : genericPoint X' ∈ V) {r : X'.functionField}
    (h : X'.presheaf.germ V (genericPoint X') hξ c = r) :
    toTotalQuotient V c = functionFieldToK V r := by
  rw [← h]
  exact (functionFieldToTotalQuotientSheaf_germ X' V c hξ).symm

variable (f : X' ⟶ X)

/-- Fulton's `f^* : 𝒪_{η,X} → R(X')` on units, `η` the image of the generic point of `X'`. -/
def pullbackGerm (a : (X.presheaf.stalk (f (genericPoint X')))ˣ) : X'.functionFieldˣ :=
  Units.map (f.stalkMap (genericPoint X')).hom.toMonoidHom a

/-- **Compatibility of the pulled-back local equations.** If `g, g'` are local equations of `D`
on `U, U'` (both containing `η = f(ξ)`) with germs `a, a' ∈ 𝒪_{η,X}^*`, then
`f^*(a) / f^*(a')` is a unit of `𝒪_{X'}` over `f⁻¹U ∩ f⁻¹U'`. -/
theorem exists_unit_mul_eq_pullback {D : X.CartierDivisor} {U U' : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} {g' : (X.totalQuotientSheaf.obj.obj (op U'))ˣ}
    (hg : IsLocalEquationOn D U g) (hg' : IsLocalEquationOn D U' g')
    (hU : f (genericPoint X') ∈ U) (hU' : f (genericPoint X') ∈ U')
    {a a' : (X.presheaf.stalk (f (genericPoint X')))ˣ} (ha : IsGermUnit g hU a)
    (ha' : IsGermUnit g' hU' a') :
    ∃ c : Γ(X', f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U')ˣ,
      resUnit (homOfLE inf_le_left) (ofFunctionField (f ⁻¹ᵁ U) (pullbackGerm f a)) =
        Units.map (toTotalQuotient (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U')).toMonoidHom c *
          resUnit (homOfLE inf_le_right) (ofFunctionField (f ⁻¹ᵁ U') (pullbackGerm f a')) := by
  obtain ⟨b, hb⟩ := exists_germ_mul_eq hg hg' hU hU' ha ha'
  refine ⟨Units.map (f.app (U ⊓ U')).hom.toMonoidHom b, ?_⟩
  rw [resUnit_ofFunctionField, resUnit_ofFunctionField]
  have hξ : genericPoint X' ∈ f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U' :=
    ⟨(hU : genericPoint X' ∈ f ⁻¹ᵁ U), (hU' : genericPoint X' ∈ f ⁻¹ᵁ U')⟩
  have h2 := congrArg (f.stalkMap (genericPoint X')) hb
  rw [map_mul] at h2
  erw [Scheme.Hom.germ_stalkMap_apply] at h2
  refine Units.ext ?_
  change functionFieldToK _ ((f.stalkMap (genericPoint X')).hom a.val) =
    toTotalQuotient (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U')
        (show Γ(X', f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ U') from (f.app (U ⊓ U')).hom b.val) *
      functionFieldToK _ ((f.stalkMap (genericPoint X')).hom a'.val)
  rw [toTotalQuotient_eq_functionFieldToK _ hξ rfl, ← map_mul]
  exact congrArg _ h2.symm

end Integral

end CartierDivisorPullback

namespace CartierDivisor

open CartierDivisorPullback

variable {X X' : Scheme.{u}} [IsIntegral X'] (f : X' ⟶ X)

/-- `f(X') ⊄ |D|` iff the image `η` of the generic point of `X'` lies outside `|D|`, since `|D|`
is closed. -/
theorem genericPoint_notMem_cartierSupport_iff (D : X.CartierDivisor) :
    f (genericPoint X') ∉ cartierSupport D ↔ ¬ Set.range f ⊆ cartierSupport D := by
  refine ⟨fun h hsub ↦ h (hsub ⟨_, rfl⟩), fun h hη ↦ h ?_⟩
  rintro _ ⟨x', rfl⟩
  have hc : IsClosed (f ⁻¹' cartierSupport D) :=
    (isClosed_cartierSupport D).preimage f.continuous
  have hx' : x' ∈ closure {genericPoint X'} := by
    rw [(genericPoint_spec X').def]
    trivial
  exact closure_minimal (Set.singleton_subset_iff.mpr
    (show genericPoint X' ∈ f ⁻¹' cartierSupport D from hη)) hc hx'

/-- `D'` is given by the pulled-back local equations of `D`: whenever `g` is a local equation of
`D` on `U ∋ η` whose germ at `η = f(ξ)` is the unit `a` of `𝒪_{η,X}`, the rational function
`f^*(a) ∈ R(X')^*` is a local equation of `D'` on `f⁻¹(U)`. -/
def HasPullbackEquations (D : X.CartierDivisor) (D' : X'.CartierDivisor) : Prop :=
  ∀ (U : X.Opens) (g : (X.totalQuotientSheaf.obj.obj (op U))ˣ), IsLocalEquationOn D U g →
    ∀ (hU : f (genericPoint X') ∈ U) (a : (X.presheaf.stalk (f (genericPoint X')))ˣ),
      IsGermUnit g hU a →
        IsLocalEquationOn D' (f ⁻¹ᵁ U) (ofFunctionField (f ⁻¹ᵁ U) (pullbackGerm f a))

/-- There is exactly one Cartier divisor on `X'` given by the pulled-back local equations of
`D`, provided the image of the generic point of `X'` lies outside `|D|`. -/
theorem existsUnique_hasPullbackEquations (D : X.CartierDivisor)
    (hD : f (genericPoint X') ∉ cartierSupport D) :
    ∃! D' : X'.CartierDivisor, HasPullbackEquations f D D' := by
  choose U hxU g hg using fun x' : X' ↦ exists_isLocalEquationOn D (f x')
  have hη : ∀ x', f (genericPoint X') ∈ U x' := fun x' ↦
    genericPoint_mem (V := f ⁻¹ᵁ U x') (hxU x')
  choose a ha using fun x' ↦ exists_isGermUnit (hg x') (hη x') hD
  have hcov : iSup (fun x' ↦ f ⁻¹ᵁ U x') = ⊤ :=
    eq_top_iff.mpr fun x' _ ↦ Opens.mem_iSup.mpr ⟨x', hxU x'⟩
  obtain ⟨D', hD', huniq⟩ := existsUnique_isLocalEquationOn (fun x' ↦ f ⁻¹ᵁ U x') hcov
    (fun x' ↦ ofFunctionField (f ⁻¹ᵁ U x') (pullbackGerm f (a x')))
    (fun i j ↦ exists_unit_mul_eq_pullback f (hg i) (hg j) (hη i) (hη j) (ha i) (ha j))
  refine ⟨D', fun V g₀ hg₀ hV a₀ ha₀ ↦ ?_,
    fun D'' hD'' ↦ huniq D'' fun i ↦ hD'' _ _ (hg i) (hη i) _ (ha i)⟩
  refine isLocalEquationOn_of_locally fun y hy ↦
    ⟨f ⁻¹ᵁ V ⊓ f ⁻¹ᵁ U y, homOfLE inf_le_left, ⟨hy, hxU y⟩, ?_⟩
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_pullback f hg₀ (hg y) hV (hη y) ha₀ (ha y)
  rw [hc]
  exact (isLocalEquationOn_resUnit (homOfLE inf_le_right) (hD' y)).units_mul c

/-- The *pull-back* `f^*D` of a Cartier divisor `D` on `X` along a morphism `f : X' ⟶ X` from an
integral scheme `X'` with `f(X') ⊄ |D|` (Fulton, §2.3): if `D` has local equations `g` on opens
`U ∋ η` with germs `a ∈ 𝒪^*_{η,X}` at the image `η` of the generic point of `X'`, then `f^*D` has
the local equations `f^*(a) ∈ R(X')^*` on `f⁻¹U` (`isLocalEquationOn_pullback`). -/
def pullback (D : X.CartierDivisor) (hD : ¬ Set.range f ⊆ cartierSupport D) :
    X'.CartierDivisor :=
  (existsUnique_hasPullbackEquations f D
    ((genericPoint_notMem_cartierSupport_iff f D).mpr hD)).exists.choose

/-- The pull-back `pullback f D hD` has as local equations the pull-backs `f^*(a)` of the germs of
the local equations of `D`. -/
theorem hasPullbackEquations_pullback (D : X.CartierDivisor)
    (hD : ¬ Set.range f ⊆ cartierSupport D) :
    HasPullbackEquations f D (pullback f D hD) :=
  (existsUnique_hasPullbackEquations f D
    ((genericPoint_notMem_cartierSupport_iff f D).mpr hD)).exists.choose_spec

/-- **Local equations of `f^*D`.** If `g` is a local equation of `D` on `U ∋ η` whose germ at
`η` is the unit `a ∈ 𝒪^*_{η,X}`, then `f^*(a) ∈ R(X')^*` is a local equation of `f^*D` on
`f⁻¹(U)`. -/
theorem isLocalEquationOn_pullback (D : X.CartierDivisor) (hD : ¬ Set.range f ⊆ cartierSupport D)
    {U : X.Opens} {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ}
    (hg : IsLocalEquationOn D U g) (hU : f (genericPoint X') ∈ U)
    {a : (X.presheaf.stalk (f (genericPoint X')))ˣ} (ha : IsGermUnit g hU a) :
    IsLocalEquationOn (pullback f D hD) (f ⁻¹ᵁ U)
      (ofFunctionField (f ⁻¹ᵁ U) (pullbackGerm f a)) :=
  hasPullbackEquations_pullback f D hD U g hg hU a ha

/-- The germ at `η` of every local equation of `D` on `U ∋ η` is a unit of `𝒪_{η,X}`. -/
theorem exists_isGermUnit_of_not_range_subset (D : X.CartierDivisor)
    (hD : ¬ Set.range f ⊆ cartierSupport D) {U : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g)
    (hU : f (genericPoint X') ∈ U) : ∃ a, IsGermUnit g hU a :=
  exists_isGermUnit hg hU ((genericPoint_notMem_cartierSupport_iff f D).mpr hD)

/-- `f^*D` is the only Cartier divisor on `X'` with the local equations `f^*(a)`. -/
theorem eq_pullback_iff (D : X.CartierDivisor) (hD : ¬ Set.range f ⊆ cartierSupport D)
    (D' : X'.CartierDivisor) : D' = pullback f D hD ↔ HasPullbackEquations f D D' := by
  refine ⟨fun h ↦ h ▸ hasPullbackEquations_pullback f D hD, fun h ↦ ?_⟩
  exact (existsUnique_hasPullbackEquations f D
    ((genericPoint_notMem_cartierSupport_iff f D).mpr hD)).unique h
      (hasPullbackEquations_pullback f D hD)

end CartierDivisor

end MMP
