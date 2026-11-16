module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic

/-!
# Invertible sheaves on an integral scheme are sheaves of Cartier divisors

Let `X` be an integral scheme. Every invertible `𝒪_X`-module `L` is isomorphic to the sheaf
`𝒪_X(E)` (`MMP.CartierDivisor.sheaf`) of a Cartier divisor `E`.

## Main results

* `MMP.CartierDivisor.exists_nonempty_iso_sheaf`: every invertible module on an integral scheme
  is `𝒪_X(E)` for a Cartier divisor `E`.
* `MMP.CartierDivisor.exists_nonempty_iso_sheaf_of_isFiniteLocallyFreeOfRank`: the same for a
  finite locally free module of rank one.

## Implementation notes

Fix a nonempty open `U₀` on which `L` has a trivializing generator `e₀`. On an integral scheme
restriction `𝒦_X(V) → 𝒦_X(V ∩ U₀)` is bijective, so a section `t ∈ Γ(V, L)` has a ratio
`t / e₀ ∈ 𝒦_X(V)`, the section restricting to the coefficient `c` of `t|_{V ∩ U₀} = c e₀`
(`MMP.Intersection.genericRatio`). For a trivializing generator `e` of `L` on `U`, the ratio
`e / e₀` is a unit of `𝒦_X(U)`; their inverses are the local equations of a Cartier divisor `E`
(`MMP.Intersection.genericDivisor`), and `t ↦ t / e₀` is an isomorphism `L ≅ 𝒪_X(E)`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], II.6.15.
* [W. Fulton, *Intersection Theory*][fulton1998], Appendix B.4.4.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace MMP.Intersection

variable {X : Scheme.{u}}

attribute [local instance] AlgebraicGeometry.hasSheafifyAddCommGrpCat

section Trivializing

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- Every point `x` of `X` has an open neighbourhood on which `L` has a trivializing
generator. -/
theorem exists_isTrivializingGenerator_top (x : X) :
    ∃ (U : X.Opens) (e : Γ(L, U)), x ∈ U ∧ IsTrivializingGenerator L U e := by
  obtain ⟨U, -, e, hxU, he⟩ := exists_isTrivializingGenerator L (Opens.mem_top x)
  exact ⟨U, e, hxU, he⟩

/-- The trivializing open around `x`. -/
def genericOpen (x : X) : X.Opens :=
  (exists_isTrivializingGenerator_top L x).choose

/-- The trivializing generator around `x`. -/
def genericGen (x : X) : Γ(L, genericOpen L x) :=
  (exists_isTrivializingGenerator_top L x).choose_spec.choose

/-- The point `x` lies in `genericOpen L x`. -/
theorem mem_genericOpen (x : X) : x ∈ genericOpen L x :=
  (exists_isTrivializingGenerator_top L x).choose_spec.choose_spec.1

/-- `genericGen L x` is a trivializing generator of `L` on `genericOpen L x`. -/
theorem isTrivializingGenerator_genericGen (x : X) :
    IsTrivializingGenerator L (genericOpen L x) (genericGen L x) :=
  (exists_isTrivializingGenerator_top L x).choose_spec.choose_spec.2

/-- The opens `genericOpen L x` cover `X`. -/
theorem iSup_genericOpen : iSup (genericOpen L) = ⊤ :=
  eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, mem_genericOpen L x⟩

end Trivializing

section GenericRatio

variable [IsIntegral X] {L : X.Modules} {U₀ : X.Opens} {e₀ : Γ(L, U₀)}

/-- On an integral scheme, restriction `𝒦_X(V) → 𝒦_X(V ∩ U₀)` is bijective for a nonempty open
`U₀`. -/
theorem bijective_totalQuotient_map_inf (hU₀ : (U₀ : Set X).Nonempty) (V : X.Opens) :
    Function.Bijective
      (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op).hom := by
  refine ⟨MMP.CartierDivisorSheaf.resK_inf_injective hU₀ V, fun τ => ?_⟩
  by_cases hW : ((V ⊓ U₀ : X.Opens) : Set X).Nonempty
  · obtain ⟨r, rfl⟩ := (MMP.CartierDivisorSheaf.ofFunctionField_bijective _ hW).2 τ
    exact ⟨MMP.CartierDivisorSheaf.ofFunctionField V r,
      MMP.CartierDivisorSheaf.resK_ofFunctionField _ r⟩
  · have : Subsingleton (X.totalQuotientSheaf.obj.obj (op (V ⊓ U₀))) :=
      ⟨fun s t ↦ TopCat.Sheaf.eq_of_locally_eq' X.totalQuotientSheaf
        (fun i : PEmpty.{u + 1} ↦ i.elim) _ (fun i ↦ i.elim)
        (fun x hx ↦ (hW ⟨x, hx⟩).elim) s t (fun i ↦ i.elim)⟩
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Restriction `𝒦_X(V) ≃ 𝒦_X(V ∩ U₀)`, a ring isomorphism on an integral scheme. -/
def totalQuotientInfEquiv (hU₀ : (U₀ : Set X).Nonempty) (V : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op V) ≃+* X.totalQuotientSheaf.obj.obj (op (V ⊓ U₀)) :=
  RingEquiv.ofBijective (X.totalQuotientSheaf.obj.map (homOfLE inf_le_left).op).hom
    (bijective_totalQuotient_map_inf hU₀ V)

variable (he₀ : IsTrivializingGenerator L U₀ e₀) (hU₀ : (U₀ : Set X).Nonempty)

/-- The coefficient `c ∈ Γ(V ∩ U₀, 𝒪_X)` of `t|_{V ∩ U₀} = c e₀`. -/
def genericCoeff {V : X.Opens} (t : Γ(L, V)) : Γ(X, V ⊓ U₀) :=
  (Equiv.ofBijective _ (he₀ (V ⊓ U₀) inf_le_right)).symm
    (L.presheaf.map (homOfLE inf_le_left).op t)

omit [IsIntegral X] in
/-- On `V ⊓ U₀`, the section `t` is `genericCoeff he₀ t • e₀`. -/
theorem genericCoeff_smul_eq {V : X.Opens} (t : Γ(L, V)) :
    genericCoeff he₀ t • L.presheaf.map (homOfLE (inf_le_right : V ⊓ U₀ ≤ U₀)).op e₀ =
      L.presheaf.map (homOfLE inf_le_left).op t :=
  (Equiv.ofBijective _ (he₀ (V ⊓ U₀) inf_le_right)).apply_symm_apply _

omit [IsIntegral X] in
/-- If `c • e₀ = t` on `V ⊓ U₀`, then `c` is the coefficient `genericCoeff he₀ t`. -/
theorem genericCoeff_eq_of_smul_eq {V : X.Opens} {t : Γ(L, V)} {c : Γ(X, V ⊓ U₀)}
    (h : c • L.presheaf.map (homOfLE (inf_le_right : V ⊓ U₀ ≤ U₀)).op e₀ =
      L.presheaf.map (homOfLE inf_le_left).op t) : genericCoeff he₀ t = c :=
  (he₀ (V ⊓ U₀) inf_le_right).1 ((genericCoeff_smul_eq he₀ t).trans h.symm)

omit [IsIntegral X] in
/-- The coefficient of `t + t'` in `e₀` is the sum of the coefficients of `t` and `t'`. -/
theorem genericCoeff_add {V : X.Opens} (t t' : Γ(L, V)) :
    genericCoeff he₀ (t + t') = genericCoeff he₀ t + genericCoeff he₀ t' :=
  genericCoeff_eq_of_smul_eq he₀ (by
    rw [add_smul, genericCoeff_smul_eq, genericCoeff_smul_eq, map_add])

omit [IsIntegral X] in
/-- The coefficient of `a • t` in `e₀` is the restriction of `a` to `V ⊓ U₀` times the
coefficient of `t`. -/
theorem genericCoeff_smul {V : X.Opens} (a : Γ(X, V)) (t : Γ(L, V)) :
    genericCoeff he₀ (a • t) =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op a * genericCoeff he₀ t :=
  genericCoeff_eq_of_smul_eq he₀ (by
    rw [mul_smul, genericCoeff_smul_eq, Scheme.Modules.map_smul])

omit [IsIntegral X] in
/-- The coefficient of the restriction of `t` to `W` is the restriction of the coefficient of
`t` to `W ⊓ U₀`. -/
theorem genericCoeff_res {V W : X.Opens} (h : W ≤ V) (t : Γ(L, V)) :
    genericCoeff he₀ (L.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (inf_le_inf_right U₀ h)).op (genericCoeff he₀ t) :=
  genericCoeff_eq_of_smul_eq he₀ (by
    rw [modules_map_map, ← modules_map_map L (inf_le_right : V ⊓ U₀ ≤ U₀)
      (inf_le_inf_right U₀ h), ← Scheme.Modules.map_smul, genericCoeff_smul_eq, modules_map_map])

/-- The ratio `t / e₀ ∈ 𝒦_X(V)` of a section `t ∈ Γ(V, L)`: the section of `𝒦_X` over `V`
whose restriction to `V ∩ U₀` is the coefficient of `t|_{V ∩ U₀}` in `e₀`. -/
def genericRatio {V : X.Opens} (t : Γ(L, V)) : X.totalQuotientSheaf.obj.obj (op V) :=
  (totalQuotientInfEquiv hU₀ V).symm (toTotalQuotient _ (genericCoeff he₀ t))

/-- The restriction of `t / e₀` to `V ⊓ U₀` is the coefficient of `t` in `e₀`. -/
theorem map_genericRatio {V : X.Opens} (t : Γ(L, V)) :
    X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op
        (genericRatio he₀ hU₀ t) = toTotalQuotient _ (genericCoeff he₀ t) :=
  (totalQuotientInfEquiv hU₀ V).apply_symm_apply _

/-- `t / e₀ = ρ` if and only if the restriction of `ρ` to `V ⊓ U₀` is the coefficient of `t` in
`e₀`. -/
theorem genericRatio_eq_iff {V : X.Opens} (t : Γ(L, V)) (ρ : X.totalQuotientSheaf.obj.obj (op V)) :
    genericRatio he₀ hU₀ t = ρ ↔
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V ⊓ U₀ ≤ V)).op ρ =
        toTotalQuotient _ (genericCoeff he₀ t) := by
  constructor
  · rintro rfl
    exact map_genericRatio he₀ hU₀ t
  · intro h
    exact (totalQuotientInfEquiv hU₀ V).injective ((map_genericRatio he₀ hU₀ t).trans h.symm)

/-- The ratio `(t + t') / e₀` is `t / e₀ + t' / e₀`. -/
theorem genericRatio_add {V : X.Opens} (t t' : Γ(L, V)) :
    genericRatio he₀ hU₀ (t + t') = genericRatio he₀ hU₀ t + genericRatio he₀ hU₀ t' := by
  rw [genericRatio_eq_iff, map_add, map_genericRatio, map_genericRatio, genericCoeff_add, map_add]

/-- The ratio `(a • t) / e₀` is the image of `a` in `𝒦_X(V)` times `t / e₀`. -/
theorem genericRatio_smul {V : X.Opens} (a : Γ(X, V)) (t : Γ(L, V)) :
    genericRatio he₀ hU₀ (a • t) = toTotalQuotient V a * genericRatio he₀ hU₀ t := by
  rw [genericRatio_eq_iff, map_mul, map_genericRatio, genericCoeff_smul, map_mul,
    toTotalQuotient_res]

/-- The ratio of the restriction of `t` to `W` is the restriction of `t / e₀` to `W`. -/
theorem genericRatio_res {V W : X.Opens} (h : W ≤ V) (t : Γ(L, V)) :
    genericRatio he₀ hU₀ (L.presheaf.map (homOfLE h).op t) =
      X.totalQuotientSheaf.obj.map (homOfLE h).op (genericRatio he₀ hU₀ t) := by
  rw [genericRatio_eq_iff, totalQuotient_map_map, genericCoeff_res, toTotalQuotient_res,
    ← map_genericRatio he₀ hU₀ t, totalQuotient_map_map]
  rfl

omit [IsIntegral X] in
/-- The coefficient of a trivializing generator `e` of `L` in `e₀` is a unit. -/
theorem isUnit_genericCoeff {U : X.Opens} {e : Γ(L, U)} (he : IsTrivializingGenerator L U e) :
    IsUnit (genericCoeff he₀ e) := by
  obtain ⟨d, hd⟩ := (he (U ⊓ U₀) inf_le_left).2
    (L.presheaf.map (homOfLE (inf_le_right : U ⊓ U₀ ≤ U₀)).op e₀)
  have h : genericCoeff he₀ e * d = 1 := (he (U ⊓ U₀) inf_le_left).1 (by
    change (genericCoeff he₀ e * d) • _ = (1 : Γ(X, U ⊓ U₀)) • _
    rw [mul_smul]
    simp only at hd
    rw [hd, genericCoeff_smul_eq, one_smul])
  exact ⟨⟨_, d, h, by rw [mul_comm]; exact h⟩, rfl⟩

/-- The ratio `e / e₀` of a trivializing generator `e` of `L` is a unit of `𝒦_X`. -/
theorem isUnit_genericRatio {U : X.Opens} {e : Γ(L, U)} (he : IsTrivializingGenerator L U e) :
    IsUnit (genericRatio he₀ hU₀ e) :=
  (((isUnit_genericCoeff he₀ he).map (toTotalQuotient _)).map
    (totalQuotientInfEquiv hU₀ U).symm)

variable [Stacks.Ample.IsInvertibleModule X L]

/-- The local equation `(e_x / e₀)⁻¹` on the trivializing open around `x`. -/
def genericEquation (x : X) : (X.totalQuotientSheaf.obj.obj (op (genericOpen L x)))ˣ :=
  (isUnit_genericRatio he₀ hU₀ (isTrivializingGenerator_genericGen L x)).unit⁻¹

/-- On `genericOpen L x ⊓ genericOpen L y`, the local equations `genericEquation he₀ hU₀ x` and
`genericEquation he₀ hU₀ y` differ by a unit of `𝒪_X`. -/
theorem exists_genericEquation_eq (x y : X) :
    ∃ u : Γ(X, genericOpen L x ⊓ genericOpen L y)ˣ,
      resUnit (homOfLE inf_le_left) (genericEquation he₀ hU₀ x) =
        Units.map (toTotalQuotient (genericOpen L x ⊓ genericOpen L y)).toMonoidHom u *
          resUnit (homOfLE inf_le_right) (genericEquation he₀ hU₀ y) := by
  set W := genericOpen L x ⊓ genericOpen L y
  have hex := isTrivializingGenerator_genericGen L x
  have hey := isTrivializingGenerator_genericGen L y
  obtain ⟨a, ha⟩ := (hey W inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : W ≤ _)).op (genericGen L x))
  obtain ⟨b, hb⟩ := (hex W inf_le_left).2
    (L.presheaf.map (homOfLE (inf_le_right : W ≤ _)).op (genericGen L y))
  simp only at ha hb
  have hba : b * a = 1 := (hey W inf_le_right).1 (by
    change (b * a) • _ = (1 : Γ(X, W)) • _
    rw [mul_smul, ha, hb, one_smul])
  refine ⟨⟨b, a, hba, by rw [mul_comm]; exact hba⟩, Units.ext ?_⟩
  have hρ := genericRatio_res he₀ hU₀ (inf_le_right : W ≤ _) (genericGen L y)
  rw [← hb, genericRatio_smul, genericRatio_res] at hρ
  set P := isUnit_genericRatio he₀ hU₀ hex
  set Q := isUnit_genericRatio he₀ hU₀ hey
  change X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ≤ _)).op (↑P.unit⁻¹ : _) =
    toTotalQuotient W b *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ≤ _)).op (↑Q.unit⁻¹ : _)
  have h1 : X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ≤ _)).op (↑P.unit⁻¹ : _) *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ≤ _)).op
        (genericRatio he₀ hU₀ (genericGen L x)) = 1 := by
    rw [← map_mul, P.val_inv_mul, map_one]
  have h2 : X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ≤ _)).op (↑Q.unit⁻¹ : _) *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ≤ _)).op
        (genericRatio he₀ hU₀ (genericGen L y)) = 1 := by
    rw [← map_mul, Q.val_inv_mul, map_one]
  linear_combination (toTotalQuotient W b *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ≤ _)).op (↑Q.unit⁻¹ : _)) * h1 -
    X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ≤ _)).op (↑P.unit⁻¹ : _) * h2 -
    (X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : W ≤ _)).op (↑P.unit⁻¹ : _) *
      X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : W ≤ _)).op (↑Q.unit⁻¹ : _)) * hρ

/-- There is a unique Cartier divisor with local equation `genericEquation he₀ hU₀ x` on
`genericOpen L x` for every point `x`. -/
theorem existsUnique_isLocalEquationOn_genericEquation :
    ∃! D : X.CartierDivisor,
      ∀ x, IsLocalEquationOn D (genericOpen L x) (genericEquation he₀ hU₀ x) :=
  existsUnique_isLocalEquationOn _ (iSup_genericOpen L) _ (exists_genericEquation_eq he₀ hU₀)

/-- The Cartier divisor with local equations `(e_x / e₀)⁻¹`. -/
def genericDivisor : X.CartierDivisor :=
  (existsUnique_isLocalEquationOn_genericEquation he₀ hU₀).exists.choose

/-- `genericEquation he₀ hU₀ x` is a local equation of `genericDivisor he₀ hU₀` on
`genericOpen L x`. -/
theorem isLocalEquationOn_genericDivisor (x : X) :
    IsLocalEquationOn (genericDivisor he₀ hU₀) (genericOpen L x) (genericEquation he₀ hU₀ x) :=
  (existsUnique_isLocalEquationOn_genericEquation he₀ hU₀).exists.choose_spec x

/-- For `W ≤ genericOpen L x`, the ratio of `b • genericGen L x|_W` is `b` times the restriction
of `(genericEquation he₀ hU₀ x)⁻¹` to `W`. -/
theorem genericRatio_smul_genericGen (x : X) {W : X.Opens} (h : W ≤ genericOpen L x)
    (b : Γ(X, W)) :
    genericRatio he₀ hU₀ (b • L.presheaf.map (homOfLE h).op (genericGen L x)) =
      b • X.totalQuotientSheaf.obj.map (homOfLE h).op
        (↑(genericEquation he₀ hU₀ x)⁻¹ : X.totalQuotientSheaf.obj.obj (op (genericOpen L x))) := by
  rw [genericRatio_smul, genericRatio_res, smul_totalQuotient_def, genericEquation, inv_inv]
  rfl

/-- The ratio `t / e₀` is a section over `V` of `𝒪_X(E)` for `E = genericDivisor he₀ hU₀`. -/
theorem genericRatio_mem_lineBundleSections {V : X.Opens} (t : Γ(L, V)) :
    genericRatio he₀ hU₀ t ∈ lineBundleSections (genericDivisor he₀ hU₀) V := by
  refine mem_lineBundleSections_of_locally _ fun x hx => ?_
  refine ⟨V ⊓ genericOpen L x, homOfLE inf_le_left, ⟨hx, mem_genericOpen L x⟩, ?_⟩
  obtain ⟨b, hb⟩ := (isTrivializingGenerator_genericGen L x (V ⊓ genericOpen L x) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : V ⊓ genericOpen L x ≤ V)).op t)
  simp only at hb
  rw [← genericRatio_res, ← hb, genericRatio_smul_genericGen]
  exact (mem_lineBundleSections_iff_of_isLocalEquationOn
    (isLocalEquationOn_genericDivisor he₀ hU₀ x) inf_le_right _).2 ⟨b, rfl⟩

/-- Division by `e₀`: the morphism `L ⟶ 𝒪_X(E)`, `t ↦ t / e₀`, where
`E = genericDivisor he₀ hU₀`. -/
def genericRatioHom : L ⟶ MMP.CartierDivisor.sheaf (genericDivisor he₀ hU₀) :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    { app := fun V => ModuleCat.ofHom
        { toFun := fun t => MMP.CartierDivisor.sectionOfMem
            (genericRatio_mem_lineBundleSections he₀ hU₀ (V := V.unop) t)
          map_add' := fun t t' => Subtype.ext (genericRatio_add he₀ hU₀ t t')
          map_smul' := fun a t => Subtype.ext (genericRatio_smul he₀ hU₀ a t) }
      naturality := fun {V W} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun t => Subtype.ext ?_)
        exact genericRatio_res he₀ hU₀ i.unop.le t }

/-- The image of `t` under `genericRatioHom he₀ hU₀` is the ratio `t / e₀`. -/
@[simp]
theorem sectionVal_genericRatioHom_app {V : X.Opens} (t : Γ(L, V)) :
    MMP.CartierDivisorSheaf.sectionVal ((genericRatioHom he₀ hU₀).val.app (op V) t) =
      genericRatio he₀ hU₀ t := rfl

/-- Division by `e₀` is an isomorphism `L ≅ 𝒪_X(E)`, where `E = genericDivisor he₀ hU₀`. -/
instance isIso_genericRatioHom : IsIso (genericRatioHom he₀ hU₀) := by
  have hinj : ∀ V : (X.Opens)ᵒᵖ, Function.Injective ((genericRatioHom he₀ hU₀).val.app V) := by
    intro V t t' htt
    have h0 : genericRatio he₀ hU₀ (V := V.unop) (t - t') = 0 :=
      congrArg MMP.CartierDivisorSheaf.sectionVal (show (genericRatioHom he₀ hU₀).val.app V (t - t')
          = 0 by
        rw [map_sub, htt, sub_self])
    rw [← sub_eq_zero]
    refine TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf X.ringCatSheaf).obj L)
      (fun x : V.unop => V.unop ⊓ genericOpen L x.1) V.unop (fun x => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, mem_genericOpen L y⟩) _ _ fun x => ?_
    obtain ⟨b, hb⟩ := (isTrivializingGenerator_genericGen L x.1 (V.unop ⊓ genericOpen L x.1)
      inf_le_right).2
      (L.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ genericOpen L x.1 ≤ V.unop)).op (t - t'))
    simp only at hb
    have hρ := genericRatio_res he₀ hU₀
      (inf_le_left : V.unop ⊓ genericOpen L x.1 ≤ V.unop) (t - t')
    rw [h0, map_zero, ← hb, genericRatio_smul_genericGen, smul_totalQuotient_def] at hρ
    have hu : IsUnit (X.totalQuotientSheaf.obj.map
        (homOfLE (inf_le_right : V.unop ⊓ genericOpen L x.1 ≤ _)).op
        (↑(genericEquation he₀ hU₀ x.1)⁻¹ : X.totalQuotientSheaf.obj.obj (op _))) :=
      (Units.isUnit _).map _
    have hb0 : b = 0 := injective_toTotalQuotient _ (by
      rw [map_zero]; exact hu.mul_left_eq_zero.1 hρ)
    change L.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ genericOpen L x.1 ≤ V.unop)).op
      (t - t') = L.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ genericOpen L x.1 ≤ V.unop)).op 0
    rw [← hb, hb0, zero_smul, map_zero]
  have hsurj : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (genericRatioHom he₀ hU₀)).hom := by
    refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun V σ x hx => ?_
    obtain ⟨b, hb⟩ := (mem_lineBundleSections_iff_of_isLocalEquationOn
      (isLocalEquationOn_genericDivisor he₀ hU₀ x) (inf_le_right : V ⊓ genericOpen L x ≤ _) _).1
      (MMP.CartierDivisor.sectionVal_mem_lineBundleSections
        ((MMP.CartierDivisor.sheaf (genericDivisor he₀ hU₀)).presheaf.map
          (homOfLE (inf_le_left : V ⊓ genericOpen L x ≤ V)).op σ))
    refine ⟨V ⊓ genericOpen L x, inf_le_left,
      ⟨b • L.presheaf.map (homOfLE inf_le_right).op (genericGen L x), ?_⟩,
      ⟨hx, mem_genericOpen L x⟩⟩
    exact MMP.CartierDivisorSheaf.sectionVal_injective ((genericRatio_smul_genericGen he₀ hU₀ x
        inf_le_right b).trans hb)
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (genericRatioHom he₀ hU₀))).mp
      ⟨Presheaf.isLocallyInjective_of_injective _ _ hinj, hsurj⟩
  have hrefl : (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms := inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (genericRatioHom he₀ hU₀)
    (SheafOfModules.toSheaf X.ringCatSheaf) hiso hrefl

end GenericRatio

end MMP.Intersection

namespace MMP.CartierDivisor

open MMP.Intersection

variable {X : Scheme.{u}}

/-- **Invertible sheaves on an integral scheme are `𝒪_X(E)`** (Hartshorne II.6.15, Fulton
B.4.4): every invertible module `L` on an integral scheme is isomorphic to the sheaf `𝒪_X(E)` of
a Cartier divisor `E`. -/
theorem exists_nonempty_iso_sheaf [IsIntegral X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    ∃ E : X.CartierDivisor, Nonempty (L ≅ sheaf E) := by
  obtain ⟨U₀, e₀, hx, he₀⟩ := exists_isTrivializingGenerator_top L (genericPoint X)
  have hU₀ : (U₀ : Set X).Nonempty := ⟨_, hx⟩
  have := isIso_genericRatioHom he₀ hU₀
  exact ⟨genericDivisor he₀ hU₀, ⟨asIso (genericRatioHom he₀ hU₀)⟩⟩

/-- **Line bundles on an integral scheme are `𝒪_X(E)`**: every finite locally free module of rank
one on an integral scheme is isomorphic to the sheaf `𝒪_X(E)` of a Cartier divisor `E`. -/
theorem exists_nonempty_iso_sheaf_of_isFiniteLocallyFreeOfRank [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) L 1] :
    ∃ E : X.CartierDivisor, Nonempty (L ≅ sheaf E) := by
  have : Stacks.Ample.IsInvertibleModule X L :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one
      X L).2 inferInstance
  exact exists_nonempty_iso_sheaf L

end MMP.CartierDivisor
