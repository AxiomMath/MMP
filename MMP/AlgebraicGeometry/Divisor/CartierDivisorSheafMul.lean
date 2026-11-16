module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators

/-!
# `𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`

For Cartier divisors `D` and `E` on a scheme `X`, multiplication in the sheaf of meromorphic
functions `𝒦_X` induces an isomorphism `𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)` of the subsheaves
`MMP.CartierDivisor.sheaf` (Fulton, §2.1).

## Main definitions

* `MMP.CartierDivisorSheaf.sheafMulHom`, `MMP.CartierDivisorSheaf.sheafMulIso`: multiplication
  `𝒪_X(D) ⊗ 𝒪_X(E) ⟶ 𝒪_X(D + E)`, an isomorphism.
* `MMP.CartierDivisorSheaf.sectionVal`: a section of `𝒪_X(D)` read in `𝒦_X`.
* `MMP.CartierDivisorSheaf.tensorMap`, `tensorIso`: functoriality of `Scheme.Modules.tensorObj`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  MMP.Intersection
open scoped TensorProduct

universe u

namespace MMP.CartierDivisorSheaf

variable {X : Scheme.{u}}

/-! ### Sections of `𝒪_X(D)` as sections of `𝒦_X` -/

/-- A section of `𝒪_X(D)` over `U`, read as a section of `𝒦_X`. -/
def sectionVal {D : X.CartierDivisor} {U : X.Opens}
    (t : (MMP.CartierDivisor.sheaf D).val.obj (op U)) :
    X.totalQuotientSheaf.obj.obj (op U) :=
  (show ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U)) from t).1

/-- `sectionVal` commutes with restriction from `U` to `V`. -/
theorem sectionVal_map {D : X.CartierDivisor} {U V : X.Opens} (h : V ≤ U)
    (t : (MMP.CartierDivisor.sheaf D).val.obj (op U)) :
    sectionVal ((MMP.CartierDivisor.sheaf D).val.map (homOfLE h).op t) =
      resK h (sectionVal t) := rfl

/-- `sectionVal (a • t)` is the product of the image of `a` in `𝒦_X` with `sectionVal t`. -/
theorem sectionVal_smul {D : X.CartierDivisor} {U : X.Opens} (a : Γ(X, U))
    (t : (MMP.CartierDivisor.sheaf D).val.obj (op U)) :
    sectionVal ((show X.ringCatSheaf.obj.obj (op U) from a) • t) = toK U a * sectionVal t := rfl

/-! ### Multiplication -/

/-- If `f` and `g` are local equations of `D` and `E` on `W`, then `f g` is a local equation of
`D + E` on `W`. -/
theorem isLocalEquation_mul {D E : X.CartierDivisor} {W : X.Opens}
    {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn E W g) :
    IsLocalEquationOn (D + E) W (f * g) := by
  unfold IsLocalEquationOn at *
  rw [cartierClass_mul, hf, hg]
  simp only [restrictDivisor, map_add]

private theorem mul_aux {K : Type*} [CommRing K] {S T F G Fi Gi C : K} (hF : F * Fi = 1)
    (hG : G * Gi = 1) : S * F * (T * G) * (C * (Gi * Fi)) = S * T * C := by
  linear_combination (S * T * C * G * Gi) * hF + S * T * C * hG

/-- The product of a section of `𝒪_X(D)` and a section of `𝒪_X(E)` is a section of
`𝒪_X(D + E)`. -/
theorem mem_mul {D E : X.CartierDivisor} {V : X.Opens}
    {s t : X.totalQuotientSheaf.obj.obj (op V)} (hs : Mem D V s) (ht : Mem E V t) :
    Mem (D + E) V (s * t) := by
  intro W h k hk
  refine mem_range_toK_of_locally _ fun x hx ↦ ?_
  obtain ⟨U₁, hx₁, f, hf⟩ := exists_isLocalEquationOn D x
  obtain ⟨U₂, hx₂, g, hg⟩ := exists_isLocalEquationOn E x
  let W' := W ⊓ (U₁ ⊓ U₂)
  have hW : W' ≤ W := inf_le_left
  have h₁ : W' ≤ U₁ := inf_le_right.trans inf_le_left
  have h₂ : W' ≤ U₂ := inf_le_right.trans inf_le_right
  have hf' := isLocalEquation_restrict h₁ hf
  have hg' := isLocalEquation_restrict h₂ hg
  obtain ⟨a, ha⟩ := hs W' (hW.trans h) _ hf'
  obtain ⟨b, hb⟩ := ht W' (hW.trans h) _ hg'
  obtain ⟨c, hc⟩ := exists_units_eq_mul_inv (isLocalEquation_restrict hW hk)
    (isLocalEquation_mul hf' hg')
  refine ⟨W', hW, ⟨hx, hx₁, hx₂⟩, a * b * c.val, ?_⟩
  have hc' := congrArg Units.val hc
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.coe_map_inv,
    mul_inv_rev] at hc'
  have hc'' : toK W' c.val = resK hW (k : X.totalQuotientSheaf.obj.obj (op W)) *
      (resK h₂ ↑g⁻¹ * resK h₁ ↑f⁻¹) := hc'
  rw [map_mul, map_mul, ha, hb, hc'', map_mul (resK hW), resK_resK, map_mul (resK (hW.trans h))]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  have hF : resK h₁ (f : X.totalQuotientSheaf.obj.obj (op U₁)) * resK h₁ ↑f⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hG : resK h₂ (g : X.totalQuotientSheaf.obj.obj (op U₂)) * resK h₂ ↑g⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact mul_aux hF hG

variable {D E : X.CartierDivisor}

/-- The presheaf of modules underlying `𝒪_X(F)`, over the presheaf of rings
`X.sheaf.obj ⋙ forget₂ CommRingCat RingCat` on which the objectwise tensor product is defined. -/
abbrev sheafVal (F : X.CartierDivisor) :
    PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  (MMP.CartierDivisor.sheaf F).val

/-- The product, in `𝒦_X`, of a section of `𝒪_X(D)` and a section of `𝒪_X(E)`, as a section of
`𝒪_X(D + E)`. -/
def mulSection {V : X.Opens} (s : (MMP.CartierDivisor.sheaf D).val.obj (op V))
    (t : (MMP.CartierDivisor.sheaf E).val.obj (op V)) :
    (MMP.CartierDivisor.sheaf (D + E)).val.obj (op V) :=
  (⟨sectionVal s * sectionVal t,
      mem_mul (show ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op V)) from s).2
        (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj (op V)) from t).2⟩ :
    ↥((MMP.CartierDivisor.sheafSubmodule (D + E)).obj (op V)))

/-- `mulSection s t` is the product `s t` in `𝒦_X`. -/
@[simp]
theorem sectionVal_mulSection {V : X.Opens} (s : (MMP.CartierDivisor.sheaf D).val.obj (op V))
    (t : (MMP.CartierDivisor.sheaf E).val.obj (op V)) :
    sectionVal (mulSection s t) = sectionVal s * sectionVal t := rfl

/-- A section of `𝒪_X(F)` is determined by its value in `𝒦_X`. -/
theorem sectionVal_injective {F : X.CartierDivisor} {V : X.Opens} :
    Function.Injective (sectionVal (D := F) (U := V)) :=
  fun _ _ h ↦ Subtype.ext h

/-- Multiplication in `𝒦_X`, as a morphism from the objectwise tensor product of `𝒪_X(D)` and
`𝒪_X(E)` to `𝒪_X(D + E)`. -/
def mulPresheafHom :
    PresheafOfModules.tensorObj (sheafVal D) (sheafVal E) ⟶ sheafVal (D + E) :=
  PresheafOfModules.tensorMk (fun V s t ↦ mulSection (V := V.unop) s t)
    (fun V x x' y ↦ sectionVal_injective (V := V.unop) (by
      change (sectionVal x + sectionVal x') * sectionVal y =
        sectionVal x * sectionVal y + sectionVal x' * sectionVal y
      exact add_mul _ _ _))
    (fun V r x y ↦ sectionVal_injective (V := V.unop) (by
      change toK V.unop r * sectionVal x * sectionVal y =
        toK V.unop r * (sectionVal x * sectionVal y)
      exact mul_assoc _ _ _))
    (fun V x y y' ↦ sectionVal_injective (V := V.unop) (by
      change sectionVal x * (sectionVal y + sectionVal y') =
        sectionVal x * sectionVal y + sectionVal x * sectionVal y'
      exact mul_add _ _ _))
    (fun V r x y ↦ sectionVal_injective (V := V.unop) (by
      change sectionVal x * (toK V.unop r * sectionVal y) =
        toK V.unop r * (sectionVal x * sectionVal y)
      exact mul_left_comm _ _ _))
    (fun V W f x y ↦ sectionVal_injective (V := W.unop) (by
      change resK (leOfHom f.unop) (sectionVal x * sectionVal y) =
        resK (leOfHom f.unop) (sectionVal x) * resK (leOfHom f.unop) (sectionVal y)
      exact map_mul _ _ _))

/-- `mulPresheafHom` sends `s ⊗ t` to the product `s t` in `𝒦_X`. -/
theorem sectionVal_mulPresheafHom_tmul {V : X.Opens}
    (s : (MMP.CartierDivisor.sheaf D).val.obj (op V))
    (t : (MMP.CartierDivisor.sheaf E).val.obj (op V)) :
    sectionVal (PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op V) (s ⊗ₜ t)) =
      sectionVal s * sectionVal t :=
  congrArg sectionVal (PresheafOfModules.tensorMk_tmul (O := X.sheaf.obj) _ _ _ _ _ _ (op V) s t)

/-- The local generator `f⁻¹` of `𝒪_X(F)` over an open `W` on which `f` is a local equation of
`F`. -/
def gen {F : X.CartierDivisor} {W : X.Opens} {f : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn F W f) : (sheafVal F).obj (op W) :=
  (⟨((f⁻¹ : (X.totalQuotientSheaf.obj.obj (op W))ˣ) : X.totalQuotientSheaf.obj.obj (op W)),
    mem_inv hf⟩ : ↥((MMP.CartierDivisor.sheafSubmodule F).obj (op W)))

/-- The value of the local generator `gen hf` in `𝒦_X` is `f⁻¹`. -/
@[simp]
theorem sectionVal_gen {F : X.CartierDivisor} {W : X.Opens}
    {f : (X.totalQuotientSheaf.obj.obj (op W))ˣ} (hf : IsLocalEquationOn F W f) :
    sectionVal (gen hf) = ↑f⁻¹ := rfl

/-- Every section of `𝒪_X(F)` over `W` is a multiple of the local generator `f⁻¹`. -/
theorem exists_eq_smul_gen {F : X.CartierDivisor} {W : X.Opens}
    {f : (X.totalQuotientSheaf.obj.obj (op W))ˣ} (hf : IsLocalEquationOn F W f)
    (s : (sheafVal F).obj (op W)) :
    ∃ a : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W), a • gen hf = s := by
  obtain ⟨a, ha⟩ := (mem_iff hf le_rfl (sectionVal s)).mp
    (show ↥((MMP.CartierDivisor.sheafSubmodule F).obj (op W)) from s).2
  refine ⟨show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W) from a,
    sectionVal_injective ?_⟩
  change toK W a * ↑f⁻¹ = sectionVal s
  rw [← ha, resK_id]

/-- Over an open `W` on which `D` and `E` have local equations `f` and `g`, every section of the
objectwise tensor product of `𝒪_X(D)` and `𝒪_X(E)` is a multiple of `f⁻¹ ⊗ g⁻¹`. -/
theorem exists_eq_smul_tmul_gen {W : X.Opens} {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn E W g)
    (z : (PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)).obj (op W)) :
    ∃ c : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W), c •
      (gen hf ⊗ₜ gen hg : (PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)).obj (op W)) =
        z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_smul _ _⟩
  | tmul x y =>
    obtain ⟨a, rfl⟩ := exists_eq_smul_gen hf x
    obtain ⟨b, rfl⟩ := exists_eq_smul_gen hg y
    exact ⟨a * b, (TensorProduct.smul_tmul_smul _ _ _ _).symm⟩
  | add z z' hz hz' =>
    obtain ⟨c, rfl⟩ := hz
    obtain ⟨c', rfl⟩ := hz'
    exact ⟨c + c', add_smul _ _ _⟩

/-- Multiplication sends `c • (f⁻¹ ⊗ g⁻¹)` to `c f⁻¹ g⁻¹`. -/
theorem sectionVal_mulPresheafHom_smul_tmul_gen {W : X.Opens}
    {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn E W g)
    (c : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)) :
    sectionVal (PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op W)
      (c • (gen hf ⊗ₜ gen hg :
        (PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)).obj (op W)))) =
      toK W c * (↑f⁻¹ * ↑g⁻¹) := by
  erw [map_smul]
  change toK W c * sectionVal (PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op W)
    (gen hf ⊗ₜ gen hg)) = _
  rw [sectionVal_mulPresheafHom_tmul]
  rfl

/-- Over an open on which `D` and `E` have local equations, multiplication is injective on the
objectwise tensor product. -/
theorem eq_zero_of_mulPresheafHom_eq_zero {W : X.Opens}
    {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn E W g)
    (z : (PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)).obj (op W))
    (hz : PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op W) z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := exists_eq_smul_tmul_gen hf hg z
  have h := sectionVal_mulPresheafHom_smul_tmul_gen hf hg c
  rw [hz] at h
  have h0 : toK W c = 0 := by
    calc toK W c = toK W c * (↑f⁻¹ * ↑g⁻¹) * ((f : X.totalQuotientSheaf.obj.obj (op W)) * g) := by
          rw [mul_assoc, mul_mul_mul_comm, Units.inv_mul, Units.inv_mul, mul_one, mul_one]
      _ = 0 := by
          rw [← h]
          exact zero_mul _
  have hc : c = 0 := toK_injective W (h0.trans (map_zero _).symm)
  rw [hc]
  exact zero_smul _ _

/-- Over an open on which `D` and `E` have local equations, every section of `𝒪_X(D + E)` is a
product. -/
theorem exists_mulPresheafHom_eq {W : X.Opens}
    {f g : (X.totalQuotientSheaf.obj.obj (op W))ˣ}
    (hf : IsLocalEquationOn D W f) (hg : IsLocalEquationOn E W g)
    (s : (sheafVal (D + E)).obj (op W)) :
    ∃ z, PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op W) z = s := by
  obtain ⟨a, ha⟩ := (mem_iff (isLocalEquation_mul hf hg) le_rfl (sectionVal s)).mp
    (show ↥((MMP.CartierDivisor.sheafSubmodule (D + E)).obj (op W)) from s).2
  refine ⟨(show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W) from a) •
    (gen hf ⊗ₜ gen hg : (PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)).obj (op W)),
    sectionVal_injective ?_⟩
  rw [sectionVal_mulPresheafHom_smul_tmul_gen, ← ha, resK_id, mul_inv_rev, Units.val_mul,
    mul_comm (↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op W))]

/-- Every point has an open neighbourhood on which both `D` and `E` have local equations. -/
theorem exists_isLocalEquation_pair (D E : X.CartierDivisor) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f g : (X.totalQuotientSheaf.obj.obj (op U))ˣ,
      IsLocalEquationOn D U f ∧ IsLocalEquationOn E U g := by
  obtain ⟨U₁, hx₁, f, hf⟩ := exists_isLocalEquationOn D x
  obtain ⟨U₂, hx₂, g, hg⟩ := exists_isLocalEquationOn E x
  exact ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, _, _, isLocalEquation_restrict inf_le_left hf,
    isLocalEquation_restrict inf_le_right hg⟩

/-- Multiplication on the objectwise tensor product is locally injective. -/
instance isLocallyInjective_mulPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (mulPresheafHom (D := D) (E := E))) where
  equalizerSieve_mem {V} x y hxy := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨U, hpU, f, g, hf, hg⟩ := exists_isLocalEquation_pair D E p
    refine ⟨V.unop ⊓ U, homOfLE inf_le_left, ?_, hp, hpU⟩
    have hxy' : PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) V x =
        PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) V y := hxy
    let T := PresheafOfModules.tensorObj (sheafVal D) (sheafVal E)
    let r : V ⟶ op (V.unop ⊓ U) := (homOfLE (inf_le_left : V.unop ⊓ U ≤ V.unop)).op
    change T.map r x = T.map r y
    have key : PresheafOfModules.Hom.app (mulPresheafHom (D := D) (E := E)) (op (V.unop ⊓ U))
        (T.map r x - T.map r y) = 0 := by
      erw [map_sub, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hxy',
        sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mulPresheafHom_eq_zero
      (isLocalEquation_restrict inf_le_right hf) (isLocalEquation_restrict inf_le_right hg) _ key)

/-- Multiplication on the objectwise tensor product is locally surjective. -/
instance isLocallySurjective_mulPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (mulPresheafHom (D := D) (E := E))) where
  imageSieve_mem {V} s := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨U, hpU, f, g, hf, hg⟩ := exists_isLocalEquation_pair D E p
    exact ⟨V ⊓ U, homOfLE inf_le_left, exists_mulPresheafHom_eq
      (isLocalEquation_restrict (inf_le_right : V ⊓ U ≤ U) hf)
      (isLocalEquation_restrict (inf_le_right : V ⊓ U ≤ U) hg)
      ((sheafVal (D + E)).map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s), hp, hpU⟩

/-- The sheafification adjunction through which `Scheme.Modules.tensorObj` is defined. -/
abbrev tensorAdj (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)

/-- The canonical morphism from the objectwise tensor product of `L` and `N` to `L ⊗ N`. -/
abbrev tensorUnit (L N : X.Modules) :=
  (tensorAdj X).unit.app (PresheafOfModules.tensorObj L.val N.val)

/-- **Multiplication in `𝒦_X`**, as a morphism `𝒪_X(D) ⊗ 𝒪_X(E) ⟶ 𝒪_X(D + E)` of
`𝒪_X`-modules: the morphism out of the sheafified tensor product induced by `s ⊗ t ↦ s t`. -/
def sheafMulHom (D E : X.CartierDivisor) :
    Scheme.Modules.tensorObj (MMP.CartierDivisor.sheaf D) (MMP.CartierDivisor.sheaf E) ⟶
      MMP.CartierDivisor.sheaf (D + E) :=
  ((PresheafOfModules.sheafificationAdjunction _).homEquiv _ _).symm mulPresheafHom

/-- `sheafMulHom D E` restricted to the objectwise tensor product is `mulPresheafHom`. -/
theorem unit_comp_sheafMulHom (D E : X.CartierDivisor) :
    (PresheafOfModules.sheafificationAdjunction _).unit.app _ ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars _).map (sheafMulHom D E) =
    mulPresheafHom :=
  PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm _ _

/-- If `f₁ ≫ f₂` is locally bijective and `f₁` is locally surjective, then `f₂` is locally
bijective. -/
theorem isLocallyBijective_of_comp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) (g : F₁ ⟶ F₃)
    (h : f₁ ≫ f₂ = g) (h₁ : Presheaf.IsLocallySurjective J f₁)
    (hg : Presheaf.IsLocallyInjective J g) (hg' : Presheaf.IsLocallySurjective J g) :
    Presheaf.IsLocallyInjective J f₂ ∧ Presheaf.IsLocallySurjective J f₂ := by
  subst h
  exact ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂,
    Presheaf.isLocallySurjective_of_isLocallySurjective J f₁ f₂⟩

/-- **Multiplication `𝒪_X(D) ⊗ 𝒪_X(E) ⟶ 𝒪_X(D + E)` is an isomorphism.** -/
instance isIso_sheafMulHom (D E : X.CartierDivisor) : IsIso (sheafMulHom D E) := by
  have hfac := congrArg (PresheafOfModules.toPresheaf _).map (unit_comp_sheafMulHom D E)
  rw [Functor.map_comp] at hfac
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map (sheafMulHom D E))).mp
    (isLocallyBijective_of_comp _ _ _ hfac
      (PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app _ _)
      isLocallyInjective_mulPresheafHom isLocallySurjective_mulPresheafHom)
  have hrefl : (_root_.SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (sheafMulHom D E)
    (_root_.SheafOfModules.toSheaf X.ringCatSheaf) hiso hrefl

/-- **The isomorphism `𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`** given by multiplication in `𝒦_X`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_homomorphism"]
def sheafMulIso (D E : X.CartierDivisor) :
    Scheme.Modules.tensorObj (MMP.CartierDivisor.sheaf D) (MMP.CartierDivisor.sheaf E) ≅
      MMP.CartierDivisor.sheaf (D + E) :=
  asIso (sheafMulHom D E)

/-- The forward morphism of `sheafMulIso D E` is `sheafMulHom D E`. -/
@[simp]
theorem sheafMulIso_hom (D E : X.CartierDivisor) : (sheafMulIso D E).hom = sheafMulHom D E :=
  rfl

/-- **`sheafMulHom D E` is multiplication in `𝒦_X`**: it sends the image of `s ⊗ t` in
`𝒪_X(D) ⊗ 𝒪_X(E)` to the product `s t`. -/
@[mmp "lem_p01a_line_bundle_of_divisor_homomorphism"]
theorem sectionVal_sheafMulHom_tmul {V : X.Opens} (s : (MMP.CartierDivisor.sheaf D).val.obj (op V))
    (t : (MMP.CartierDivisor.sheaf E).val.obj (op V)) :
    sectionVal (D := D + E) (PresheafOfModules.Hom.app
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars _).map (sheafMulHom D E)) (op V)
        (PresheafOfModules.Hom.app
          (tensorUnit (MMP.CartierDivisor.sheaf D) (MMP.CartierDivisor.sheaf E)) (op V) (s ⊗ₜ t))) =
      sectionVal s * sectionVal t :=
  (congrArg sectionVal (PresheafOfModules.hom_congr_apply' (unit_comp_sheafMulHom D E) (op V)
    (s ⊗ₜ t))).trans (sectionVal_mulPresheafHom_tmul s t)

section Bundle

/-! ### The isomorphism of line bundles `𝒪(D) ⊗ 𝒪(E) ≅ 𝒪(D + E)` -/

variable {L L' N N' : X.Modules}

/-- The tensor product `f ⊗ g : L ⊗ N ⟶ L' ⊗ N'` of morphisms of `𝒪_X`-modules. -/
def tensorMap (f : L ⟶ L') (g : N ⟶ N') :
    Scheme.Modules.tensorObj L N ⟶ Scheme.Modules.tensorObj L' N' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor _).map f).app N ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj L').map g

/-- The tensor product `α ⊗ β : L ⊗ N ≅ L' ⊗ N'` of isomorphisms of `𝒪_X`-modules. -/
def tensorIso (α : L ≅ L') (β : N ≅ N') :
    Scheme.Modules.tensorObj L N ≅ Scheme.Modules.tensorObj L' N' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso α).app N ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj L').mapIso β

/-- The forward morphism of `tensorIso α β` is `tensorMap α.hom β.hom`. -/
@[simp]
theorem tensorIso_hom (α : L ≅ L') (β : N ≅ N') : (tensorIso α β).hom = tensorMap α.hom β.hom :=
  rfl

/-- `f ⊗ g` sends the image of `s ⊗ t` to the image of `f s ⊗ g t`. -/
theorem tensorMap_tensorUnit_tmul (f : L ⟶ L') (g : N ⟶ N') (W : X.Opens) (s : Γ(L, W))
    (t : Γ(N, W)) :
    PresheafOfModules.Hom.app ((SheafOfModules.forget _).map (tensorMap f g)) (op W)
      (PresheafOfModules.Hom.app (tensorUnit L N) (op W) (s ⊗ₜ[X.sheaf.obj.obj (op W)] t)) =
    PresheafOfModules.Hom.app (tensorUnit L' N') (op W)
      ((f.val.app (op W)).hom s ⊗ₜ[X.sheaf.obj.obj (op W)] (g.val.app (op W)).hom t) := by
  have n1 := (tensorAdj X).unit.naturality
    (((PresheafOfModules.tensorBifunctor _).map ((SheafOfModules.forget _).map f)).app N.val)
  have n2 := (tensorAdj X).unit.naturality
    (((PresheafOfModules.tensorBifunctor _).obj L'.val).map ((SheafOfModules.forget _).map g))
  have e1 := congr(PresheafOfModules.Hom.app $n1 (op W) (s ⊗ₜ[X.sheaf.obj.obj (op W)] t))
  have e2 := congr(PresheafOfModules.Hom.app $n2 (op W)
    ((f.val.app (op W)).hom s ⊗ₜ[X.sheaf.obj.obj (op W)] t))
  exact (congrArg (fun z ↦ PresheafOfModules.Hom.app ((SheafOfModules.forget _).map
    (((Stacks.SheafOfModules.Tensor.sheafTensor _).obj L').map g)) (op W) z) e1.symm).trans e2.symm

end Bundle

end MMP.CartierDivisorSheaf
