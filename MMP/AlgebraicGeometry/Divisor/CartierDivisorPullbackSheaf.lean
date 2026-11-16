module

public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullback
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation

/-!
# The invertible sheaf of the pull-back of a Cartier divisor

Let `f : X' ⟶ X` be a morphism from an integral scheme `X'`, with generic point `ξ`, whose image
is not contained in the support of a Cartier divisor `D` on `X`, and let `η = f(ξ)`, a point
outside `|D|`. The pull-back `f^*D` is the Cartier divisor whose local equation on `f⁻¹U` is
`f^*(a) ∈ R(X')^*`, where `a ∈ 𝒪_{X,η}^*` is the germ of a local equation of `D` on `U ∋ η`. This
file identifies its invertible sheaf with the pull-back of the invertible sheaf of `D`:
`𝒪_{X'}(f^*D) ≅ f^*𝒪_X(D)`.

Since `η ∉ |D|`, the germ at `η` of a section `s` of `𝒪_X(D) ⊆ 𝒦_X` over `V ∋ η` lies in `𝒪_{X,η}`;
its image under `f^♯ : 𝒪_{X,η} → R(X')` is a section `f^*s` of `𝒪_{X'}(f^*D) ⊆ 𝒦_{X'}` over
`f⁻¹V`. This defines a morphism `𝒪_X(D) ⟶ f_*𝒪_{X'}(f^*D)`, and its adjoint
`f^*𝒪_X(D) ⟶ 𝒪_{X'}(f^*D)` is an isomorphism: on `f⁻¹U` it sends the pull-back of the local
generator `g⁻¹` of `𝒪_X(D)` to the local generator `f^*(a)⁻¹` of `𝒪_{X'}(f^*D)`, and both are
generators of invertible sheaves.

## Main definitions

* `MMP.CartierDivisor.pullbackSection`: the pull-back `f^*s ∈ R(X')` of a section of `𝒪_X(D)`.
* `MMP.CartierDivisor.toPushforwardSheaf`: the morphism `𝒪_X(D) ⟶ f_*𝒪_{X'}(f^*D)`.
* `MMP.CartierDivisor.pullbackToSheaf`: its adjoint `f^*𝒪_X(D) ⟶ 𝒪_{X'}(f^*D)`.
* `MMP.CartierDivisor.pullbackSheafIso`: the isomorphism `𝒪_{X'}(f^*D) ≅ f^*𝒪_X(D)`.

## Main results

* `MMP.CartierDivisor.exists_stalkToTotalQuotient_eq_germ`: outside `|D|`, germs of sections of
  `𝒪_X(D)` are regular.
* `MMP.CartierDivisor.mem_pullbackSection`: `f^*s` is a section of `𝒪_{X'}(f^*D)`.
* `MMP.CartierDivisor.isIso_pullbackToSheaf`: the adjoint morphism is an isomorphism.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §2.3 and Appendix B.4.4.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MMP.Intersection MMP.CartierDivisorSheaf MMP.CartierDivisorPullback

universe u

namespace MMP.CartierDivisor

variable {X X' : Scheme.{u}}

/-- If `b = s · g` on `V ∩ U`, `g` a local equation with germ the unit `a` at `x`, then the germ of
`b` at `x` is the germ of `s` times `a` in `𝒦_{X,x}`. -/
theorem stalkToTotalQuotient_germ_eq {U V : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    {a : (X.presheaf.stalk x)ˣ} (ha : IsGermUnit g hxU a)
    (s : X.totalQuotientSheaf.obj.obj (op V)) (b : Γ(X, V ⊓ U))
    (hb : toK (V ⊓ U) b = resK inf_le_left s *
      ((Units.map (resK (inf_le_right : V ⊓ U ≤ U)).toMonoidHom g :
        (X.totalQuotientSheaf.obj.obj (op (V ⊓ U)))ˣ) : X.totalQuotientSheaf.obj.obj _)) :
    stalkToTotalQuotient x (X.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩ b) =
      X.totalQuotientSheaf.presheaf.germ V x hxV s * stalkToTotalQuotient x a := by
  erw [stalkToTotalQuotient_germ]
  rw [ha]
  change X.totalQuotientSheaf.presheaf.germ (V ⊓ U) x ⟨hxV, hxU⟩ (toK (V ⊓ U) b) = _
  rw [hb, map_mul]
  simp only [Units.coe_map]
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- Outside `|D|`, the germ of a section of `𝒪_X(D)` lies in `𝒪_{X,x}`. -/
theorem exists_stalkToTotalQuotient_eq_germ {D : X.CartierDivisor} {V : X.Opens} {x : X}
    (hx : x ∈ V) (hxD : x ∉ cartierSupport D) {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem D V s) :
    ∃ t, stalkToTotalQuotient x t = X.totalQuotientSheaf.presheaf.germ V x hx s := by
  obtain ⟨U, hxU, g, hg⟩ := exists_isLocalEquationOn D x
  obtain ⟨a, ha⟩ := exists_isGermUnit hg hxU hxD
  obtain ⟨b, hb⟩ := hs (V ⊓ U) inf_le_left _ (isLocalEquation_restrict inf_le_right hg)
  refine ⟨X.presheaf.germ (V ⊓ U) x ⟨hx, hxU⟩ b * ↑a⁻¹, ?_⟩
  rw [map_mul, stalkToTotalQuotient_germ_eq hxU hx ha s b hb, mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]

/-- Over an open `W ⊆ U`, where `g` is a local equation of `D` on `U`, the section `g⁻¹` of
`𝒪_X(D)` generates: `c ↦ c • g⁻¹` is a bijection `Γ(X, W) → Γ(𝒪_X(D), W)`. -/
theorem bijective_smul_of_isLocalEquationOn {D : X.CartierDivisor} {U W : X.Opens}
    {g : (X.totalQuotientSheaf.obj.obj (op U))ˣ} (hg : IsLocalEquationOn D U g) (h : W ≤ U)
    (s : Γ(sheaf D, W)) (hs : (s.1 : X.totalQuotientSheaf.obj.obj (op W)) = resK h ↑g⁻¹) :
    Function.Bijective fun c : Γ(X, W) ↦ c • s := by
  have hu : resK h ↑g⁻¹ * resK h (g : X.totalQuotientSheaf.obj.obj (op U)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨fun c c' hcc ↦ toK_injective W ?_, fun t ↦ ?_⟩
  · have e := congrArg (fun t : Γ(sheaf D, W) ↦
      (show X.totalQuotientSheaf.obj.obj (op W) from t.1) * resK h (g : _)) hcc
    change (toK W c * (show X.totalQuotientSheaf.obj.obj (op W) from s.1)) * _ =
      (toK W c' * (show X.totalQuotientSheaf.obj.obj (op W) from s.1)) * _ at e
    rwa [hs, mul_assoc, mul_assoc, hu, mul_one, mul_one] at e
  · obtain ⟨c, hc⟩ := (mem_iff hg h t.1).mp t.2
    exact ⟨c, Subtype.ext ((congrArg (toK W c * ·) hs).trans hc)⟩

section Pullback

variable [IsIntegral X'] (f : X' ⟶ X) (D : X.CartierDivisor)
  (hD : ¬ Set.range f ⊆ cartierSupport D)

/-- On an integral scheme, `𝒦` has a single section over an open missing the generic point. -/
theorem subsingleton_totalQuotient {W : X'.Opens} (hW : genericPoint X' ∉ W) :
    Subsingleton (X'.totalQuotientSheaf.obj.obj (op W)) :=
  ⟨fun s t ↦ TopCat.Sheaf.eq_of_locally_eq' X'.totalQuotientSheaf (fun i : PEmpty.{u + 1} ↦ i.elim)
    W (fun i ↦ i.elim) (fun _ hx ↦ (hW (genericPoint_mem hx)).elim) s t (fun i ↦ i.elim)⟩

/-- The image of a rational function `r ∈ R(X')` in `𝒦_{X'}(V)`, restricted to `W ⊆ V`, is its
image in `𝒦_{X'}(W)`. -/
theorem resK_functionFieldToK {V W : X'.Opens} (h : W ≤ V) (r : X'.functionField) :
    resK h (functionFieldToK V r) = functionFieldToK W r :=
  (NatTrans.naturality_apply (functionFieldToTotalQuotientSheaf X') (homOfLE h).op r).symm

/-- The pull-back `f^*s ∈ R(X')` of a section `s` of `𝒪_X(D)` over `V`: the image under
`f^♯ : 𝒪_{X,η} → R(X')` of its germ at `η = f(ξ)`, which lies in `𝒪_{X,η}` as `η ∉ |D|`. -/
def pullbackSection (V : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op V)) :
    X'.functionField :=
  open Classical in
  if h : f (genericPoint X') ∈ V ∧ Mem D V s then
    (f.stalkMap (genericPoint X')).hom (exists_stalkToTotalQuotient_eq_germ h.1
      ((genericPoint_notMem_cartierSupport_iff f D).mpr hD) h.2).choose
  else 0

variable {f D hD}

/-- If `η = f(ξ) ∈ V` and `t ∈ 𝒪_{X,η}` has the same image in `𝒦_{X,η}` as the germ of a section
`s` of `𝒪_X(D)`, then `f^*s = f^♯(t)`. -/
theorem pullbackSection_eq {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hV : f (genericPoint X') ∈ V) (hs : Mem D V s) {t : X.presheaf.stalk (f (genericPoint X'))}
    (ht : stalkToTotalQuotient _ t = X.totalQuotientSheaf.presheaf.germ V _ hV s) :
    pullbackSection f D hD V s = (f.stalkMap (genericPoint X')).hom t := by
  rw [pullbackSection, dite_eq_left_of_eq_true (eq_true ⟨hV, hs⟩)]
  exact congrArg _ (stalkToTotalQuotient_injective X _
    ((exists_stalkToTotalQuotient_eq_germ hV
      ((genericPoint_notMem_cartierSupport_iff f D).mpr hD) hs).choose_spec.trans ht.symm))

/-- If `f(ξ) ∉ V`, then `pullbackSection f D hD V s = 0`. -/
theorem pullbackSection_of_notMem {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hV : f (genericPoint X') ∉ V) : pullbackSection f D hD V s = 0 := by
  rw [pullbackSection, dite_eq_right_of_eq_false (eq_false fun h ↦ hV h.1)]

/-- If `η = f(ξ) ∈ V` and `s` is a section of `𝒪_X(D)` over `V`, there is `t ∈ 𝒪_{X,η}` whose
image in `𝒦_{X,η}` is the germ of `s`, and `f^*s = f^♯(t)`. -/
theorem exists_pullbackSection_eq {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hV : f (genericPoint X') ∈ V) (hs : Mem D V s) :
    ∃ t, stalkToTotalQuotient _ t = X.totalQuotientSheaf.presheaf.germ V _ hV s ∧
      pullbackSection f D hD V s = (f.stalkMap (genericPoint X')).hom t := by
  obtain ⟨t, ht⟩ := exists_stalkToTotalQuotient_eq_germ hV
    ((genericPoint_notMem_cartierSupport_iff f D).mpr hD) hs
  exact ⟨t, ht, pullbackSection_eq hV hs ht⟩

/-- `f^*s` is a section of `𝒪_{X'}(f^*D)` over `f⁻¹V`. -/
theorem mem_pullbackSection {V : X.Opens} {s : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem D V s) :
    Mem (pullback f D hD) (f ⁻¹ᵁ V) (functionFieldToK _ (pullbackSection f D hD V s)) := by
  refine Mem.of_locally fun x' hx' ↦ ?_
  obtain ⟨U, hxU, g, hg⟩ := exists_isLocalEquationOn D (f x')
  have hηU : f (genericPoint X') ∈ U := genericPoint_mem (V := f ⁻¹ᵁ U) hxU
  have hηV : f (genericPoint X') ∈ V := genericPoint_mem (V := f ⁻¹ᵁ V) hx'
  have hξ : genericPoint X' ∈ f ⁻¹ᵁ (V ⊓ U) := genericPoint_mem (V := f ⁻¹ᵁ (V ⊓ U)) ⟨hx', hxU⟩
  obtain ⟨a, ha⟩ := exists_isGermUnit_of_not_range_subset f D hD hg hηU
  obtain ⟨b, hb⟩ := hs (V ⊓ U) inf_le_left _ (isLocalEquation_restrict inf_le_right hg)
  obtain ⟨t, ht, hst⟩ := exists_pullbackSection_eq (hD := hD) hηV hs
  have hta : t * a = X.presheaf.germ (V ⊓ U) _ ⟨hηV, hηU⟩ b :=
    stalkToTotalQuotient_injective X _ (by
      rw [map_mul, ht, stalkToTotalQuotient_germ_eq hηU hηV ha s b hb])
  refine ⟨f ⁻¹ᵁ (V ⊓ U), (Opens.map f.base).monotone inf_le_left, ⟨hx', hxU⟩, ?_⟩
  rw [mem_iff (isLocalEquationOn_pullback f D hD hg hηU ha)
    ((Opens.map f.base).monotone inf_le_right)]
  refine ⟨f.app (V ⊓ U) b, ?_⟩
  rw [toTotalQuotient_eq_functionFieldToK _ hξ rfl, resK_functionFieldToK]
  simp only [ofFunctionField, Units.coe_map_inv]
  erw [resK_functionFieldToK]
  rw [← map_mul, hst]
  erw [← Scheme.Hom.germ_stalkMap_apply f (V ⊓ U) (genericPoint X') hξ b]
  rw [← hta]
  congr 1
  rw [map_mul, mul_assoc]
  exact (congrArg (_ * ·) (Units.mul_inv (pullbackGerm f a))).trans (mul_one _)

/-- Pull-back is additive on sections of `𝒪_X(D)`: `f^*(s + t) = f^*s + f^*t`. -/
theorem pullbackSection_add {V : X.Opens} {s t : X.totalQuotientSheaf.obj.obj (op V)}
    (hs : Mem D V s) (ht : Mem D V t) :
    pullbackSection f D hD V (s + t) =
      pullbackSection f D hD V s + pullbackSection f D hD V t := by
  by_cases hV : f (genericPoint X') ∈ V
  · obtain ⟨a, ha, has⟩ := exists_pullbackSection_eq (hD := hD) hV hs
    obtain ⟨b, hb, hbt⟩ := exists_pullbackSection_eq (hD := hD) hV ht
    rw [has, hbt, ← map_add]
    exact pullbackSection_eq hV (hs.add ht) (by rw [map_add, ha, hb, map_add])
  · simp [pullbackSection_of_notMem hV]

/-- Pull-back is semilinear along `f^♯`: for `c ∈ Γ(X, V)` and a section `s` of `𝒪_X(D)` over
`V`, `f^*(c · s) = f^♯(c) · f^*s` in `𝒦_{X'}(f⁻¹V)`. -/
theorem functionFieldToK_pullbackSection_toK_mul {V : X.Opens}
    {s : X.totalQuotientSheaf.obj.obj (op V)} (hs : Mem D V s) (c : Γ(X, V)) :
    functionFieldToK (f ⁻¹ᵁ V) (pullbackSection f D hD V (toK V c * s)) =
      toK (f ⁻¹ᵁ V) (f.app V c) * functionFieldToK (f ⁻¹ᵁ V) (pullbackSection f D hD V s) := by
  by_cases hV : f (genericPoint X') ∈ V
  · obtain ⟨a, ha, has⟩ := exists_pullbackSection_eq (hD := hD) hV hs
    rw [has, pullbackSection_eq hV (hs.mul_toK c) (t := X.presheaf.germ V _ hV c * a),
      toTotalQuotient_eq_functionFieldToK _ (show genericPoint X' ∈ f ⁻¹ᵁ V from hV) rfl,
      ← map_mul]
    · congr 1
      rw [map_mul]
      erw [Scheme.Hom.germ_stalkMap_apply]
    · rw [map_mul, ha, map_mul]
      erw [stalkToTotalQuotient_germ]
  · simp [pullbackSection_of_notMem hV]

/-- Pull-back commutes with restriction: for `V' ⊆ V` and a section `s` of `𝒪_X(D)` over `V`,
`f^*(s|_{V'})` is the restriction of `f^*s` from `f⁻¹V` to `f⁻¹V'`. -/
theorem functionFieldToK_pullbackSection_resK {V V' : X.Opens} (h : V' ≤ V)
    {s : X.totalQuotientSheaf.obj.obj (op V)} (hs : Mem D V s) :
    functionFieldToK (f ⁻¹ᵁ V') (pullbackSection f D hD V' (resK h s)) =
      resK ((Opens.map f.base).monotone h)
        (functionFieldToK (f ⁻¹ᵁ V) (pullbackSection f D hD V s)) := by
  rw [resK_functionFieldToK]
  by_cases hV : f (genericPoint X') ∈ V'
  · obtain ⟨a, ha, has⟩ := exists_pullbackSection_eq (hD := hD) (h hV) hs
    rw [has, pullbackSection_eq hV (hs.res h) (t := a)]
    rw [ha]
    erw [TopCat.Presheaf.germ_res_apply]
  · have := subsingleton_totalQuotient (W := f ⁻¹ᵁ V') hV
    exact Subsingleton.elim _ _

variable (f D hD)

/-- The pull-back of sections `𝒪_X(D) ⟶ f_*𝒪_{X'}(f^*D)`, `s ↦ f^*s`. -/
def toPushforwardSheaf :
    sheaf D ⟶ (Scheme.Modules.pushforward f).obj (sheaf (pullback f D hD)) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun s ↦ ⟨functionFieldToK _ (pullbackSection f D hD V.unop s.1), mem_pullbackSection s.2⟩)
        fun s t ↦ Subtype.ext ((congrArg (functionFieldToK _)
          (pullbackSection_add (hD := hD) s.2 t.2)).trans (map_add _ _ _)))
      naturality _ _ i := AddCommGrpCat.ext fun s ↦
        Subtype.ext (functionFieldToK_pullbackSection_resK (leOfHom i.unop) s.2) }
    (fun _ c s ↦ Subtype.ext (functionFieldToK_pullbackSection_toK_mul s.2 c))⟩

/-- The morphism `f^*𝒪_X(D) ⟶ 𝒪_{X'}(f^*D)` adjoint to `toPushforwardSheaf`. -/
def pullbackToSheaf : (Scheme.Modules.pullback f).obj (sheaf D) ⟶ sheaf (pullback f D hD) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (toPushforwardSheaf f D hD)

/-- On `f⁻¹U`, `pullbackToSheaf` sends the image under the adjunction unit of a section `s` of
`𝒪_X(D)` over `U` to `f^*s`. -/
theorem pullbackToSheaf_app_unit (U : X.Opens) (s : Γ(sheaf D, U)) :
    (pullbackToSheaf f D hD).app (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (sheaf D)).app U s) =
      (toPushforwardSheaf f D hD).app U s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _
    (pullbackToSheaf f D hD)).symm.trans (Equiv.apply_symm_apply _ (toPushforwardSheaf f D hD))
  exact congrArg (fun φ ↦ φ.app U s) h

/-- The morphism `f^*𝒪_X(D) ⟶ 𝒪_{X'}(f^*D)` is an isomorphism. -/
instance isIso_pullbackToSheaf : IsIso (pullbackToSheaf f D hD) := by
  have hinv : Stacks.Ample.IsInvertibleModule X (sheaf D) :=
    Stacks.ProjectiveFromSections.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one _
  have hpb : Stacks.SheafOfModules.IsInvertible X'.toRingedSpace.presheaf
      (structureSheafRing X'.toRingedSpace).property
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj (sheaf D)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (Stacks.InvertiblePullback.isInvertibleModule_pullback f _)
  refine Scheme.Modules.isIso_of_bijective_smul _ fun x' ↦ ?_
  obtain ⟨U, hxU, g, hg⟩ := exists_isLocalEquationOn D (f x')
  have hηU : f (genericPoint X') ∈ U := genericPoint_mem (V := f ⁻¹ᵁ U) hxU
  obtain ⟨a, ha⟩ := exists_isGermUnit_of_not_range_subset f D hD hg hηU
  let e : Γ(sheaf D, U) := ⟨(↑g⁻¹ : X.totalQuotientSheaf.obj.obj (op U)), mem_inv hg⟩
  refine ⟨f ⁻¹ᵁ U, hxU, ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
    (sheaf D)).app U e, fun W hW ↦ ⟨?_, ?_⟩⟩
  · refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
      (X := X'.toRingedSpace) _ _ _ hW fun x hx ↦ ?_
    have h1 := Scheme.Modules.germ_notMem_maximalSmul_of_bijective_smul (sheaf D) e
      (fun W' hW' ↦ bijective_smul_of_isLocalEquationOn hg hW' _ rfl) (f x) (hW hx)
    rw [← Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff f (sheaf D) e x
      (hW hx)] at h1
    rwa [Stacks.NonvanishingPullback.mem_maximalSmul_iff] at h1
  · rw [pullbackToSheaf_app_unit]
    refine bijective_smul_of_isLocalEquationOn (isLocalEquationOn_pullback f D hD hg hηU ha) hW
      _ ?_
    change resK hW (functionFieldToK _ (pullbackSection f D hD U ↑g⁻¹)) = _
    have hu : Units.map (stalkToTotalQuotient _).toMonoidHom a =
        Units.map (X.totalQuotientSheaf.presheaf.germ U _ hηU).hom.toMonoidHom g :=
      Units.ext ha
    rw [pullbackSection_eq hηU (mem_inv hg) (t := ↑a⁻¹)]
    · simp only [ofFunctionField, pullbackGerm, Units.coe_map_inv]
      rfl
    · have h2 := congrArg (fun u : (X.totalQuotientSheaf.presheaf.stalk (f (genericPoint X')))ˣ ↦
        (u⁻¹ : (X.totalQuotientSheaf.presheaf.stalk (f (genericPoint X')))ˣ).val) hu
      simp only [Units.coe_map_inv] at h2
      exact h2

/-- **`𝒪_{X'}(f^*D) ≅ f^*𝒪_X(D)`** for a morphism `f : X' ⟶ X` from an integral scheme whose
image is not contained in `|D|`: the pull-back of sections `s ↦ f^*s`, adjoint to
`f^*𝒪_X(D) ⟶ 𝒪_{X'}(f^*D)`, is an isomorphism. -/
def pullbackSheafIso :
    sheaf (pullback f D hD) ≅ (Scheme.Modules.pullback f).obj (sheaf D) :=
  (asIso (pullbackToSheaf f D hD)).symm

end Pullback

end MMP.CartierDivisor
