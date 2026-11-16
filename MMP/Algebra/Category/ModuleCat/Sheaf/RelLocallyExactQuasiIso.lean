module

public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import MMP.Algebra.Category.ModuleCat.Sheaf.RelLocallyExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Relatively locally exact monomorphisms are quasi-isomorphisms

Let `φ : K' ⟶ K` be a morphism of `ℕ`-indexed cochain complexes of sheaves of modules on a
topological space, injective in every degree. If `φ` is relatively locally exact
(`MMP.LcBpf.RelLocallyExact`), then the quotient complex `K / K'` is exact, and `φ` is a
quasi-isomorphism.

## Main results

* `MMP.LcBpf.quasiIso_f_of_shortExact_of_acyclic`: for a short exact sequence of homological
  complexes, the first map is a quasi-isomorphism when the third complex is acyclic.
* `MMP.LcBpf.quasiIso_of_relLocallyExact`: a degreewise monomorphism that is relatively locally
  exact is a quasi-isomorphism.

## Implementation notes

The quotient `K / K'` is the cokernel of `φ` in the category of complexes. Its exactness is
checked on the stalks of the underlying sheaves of abelian groups: the functor to sheaves of
abelian groups is exact and faithful, and exactness of sheaves of abelian groups on a topological
space is checked on stalks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace MMP.LcBpf

/-- **A short exact sequence with acyclic quotient.** If `0 → X₁ → X₂ → X₃ → 0` is a short
exact sequence of homological complexes in an abelian category and `X₃` is acyclic, then
`X₁ → X₂` is a quasi-isomorphism. -/
theorem quasiIso_f_of_shortExact_of_acyclic {C ι : Type*} [Category C] [Abelian C]
    {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (h : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f ((h i).isZero_homology.eq_of_tgt _ _)
  have : Mono (HomologicalComplex.homologyMap S.f i) := by
    by_cases hi : c.Rel (c.prev i) i
    · exact (hS.homology_exact₁ (c.prev i) i hi).mono_g ((h _).isZero_homology.eq_of_src _ _)
    · have := hS.mono_f
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f i
        (fun j hj => hi (by rwa [c.prev_eq' hj]))
  exact isIso_of_mono_of_epi _

section Stalks

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- The underlying sheaf of abelian groups of a sheaf of modules, as a sheaf on `X`. -/
noncomputable abbrev sheafAb : SheafOfModules.{0} R ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  SheafOfModules.toSheaf R

/-- The underlying presheaf of abelian groups of a sheaf of modules. -/
noncomputable abbrev presheafAb : SheafOfModules.{0} R ⥤ TopCat.Presheaf AddCommGrpCat.{0} X :=
  sheafAb ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X

/-- The stalk at `x` of the underlying sheaf of abelian groups of a sheaf of modules. -/
noncomputable abbrev stalkAb (x : X) : SheafOfModules.{0} R ⥤ AddCommGrpCat.{0} :=
  sheafAb ⋙ TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x

/-- The functor `sheafAb` preserves finite limits. -/
instance : PreservesFiniteLimits (sheafAb (R := R)) :=
  (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{0} R))

/-- The functor `sheafAb` preserves finite colimits. -/
instance : PreservesFiniteColimits (sheafAb (R := R)) :=
  ⟨fun J _ _ => Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesColimitsOfShape_toSheaf
    R J⟩

/-- The functor `sheafAb` is faithful. -/
instance : (sheafAb (R := R)).Faithful :=
  (inferInstance : (SheafOfModules.toSheaf.{0} R).Faithful)

/-- The functor `sheafAb` is additive. -/
instance : (sheafAb (R := R)).Additive :=
  (inferInstance : (SheafOfModules.toSheaf.{0} R).Additive)

/-- The stalk functor `stalkAb x` is additive. -/
instance (x : X) : (stalkAb (R := R) x).Additive := by
  unfold stalkAb
  infer_instance

/-- The stalk functor `stalkAb x` preserves finite limits. -/
instance (x : X) : PreservesFiniteLimits (stalkAb (R := R) x) :=
  comp_preservesFiniteLimits sheafAb
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)

/-- The stalk functor `stalkAb x` preserves finite colimits. -/
instance (x : X) : PreservesFiniteColimits (stalkAb (R := R) x) :=
  comp_preservesFiniteColimits sheafAb
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)

/-- Exactness of a short complex of sheaves of modules is checked on stalks. -/
theorem exact_of_forall_stalkAb {S : ShortComplex (SheafOfModules.{0} R)}
    (h : ∀ x : X, (S.map (stalkAb x)).Exact) : S.Exact := by
  rw [← S.exact_map_iff_of_faithful sheafAb, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  exact h

/-- The germ at `x` of a section of a sheaf of modules, in the stalk of its underlying sheaf of
abelian groups. -/
noncomputable def germAb (x : X) (A : SheafOfModules.{0} R) (U : Opens X) (hx : x ∈ U)
    (s : A.val.obj (op U)) : (stalkAb x).obj A :=
  (presheafAb.obj A).germ U x hx s

/-- The map induced on stalks by a morphism `f` sends the germ of `s` to the germ of `f s`. -/
@[simp]
theorem stalkAb_map_germAb (x : X) {A B : SheafOfModules.{0} R} (f : A ⟶ B) (U : Opens X)
    (hx : x ∈ U) (s : A.val.obj (op U)) :
    (stalkAb x).map f (germAb x A U hx s) = germAb x B U hx (f.val.app (op U) s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (presheafAb.map f) s

/-- The germ of the restriction of a section `s` to a smaller open set is the germ of `s`. -/
@[simp]
theorem germAb_res (x : X) (A : SheafOfModules.{0} R) {U V : Opens X} (i : V ⟶ U) (hx : x ∈ V)
    (s : A.val.obj (op U)) :
    germAb x A V hx (A.val.map i.op s) = germAb x A U (i.le hx) s :=
  TopCat.Presheaf.germ_res_apply (presheafAb.obj A) i x hx s

/-- The germ of a sum of sections is the sum of their germs. -/
@[simp]
theorem germAb_add (x : X) (A : SheafOfModules.{0} R) (U : Opens X) (hx : x ∈ U)
    (s t : A.val.obj (op U)) :
    germAb x A U hx (s + t) = germAb x A U hx s + germAb x A U hx t :=
  map_add ((presheafAb.obj A).germ U x hx).hom s t

/-- Every element of the stalk at `x` is the germ of a section over an open set containing `x`. -/
theorem exists_germAb_eq (x : X) (A : SheafOfModules.{0} R) (k : (stalkAb x).obj A) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : A.val.obj (op U)), germAb x A U hx s = k :=
  TopCat.Presheaf.exists_germ_eq (presheafAb.obj A) k

/-- Two sections with the same germ at `x` agree on some open neighbourhood of `x` contained in
both of their domains. -/
theorem exists_res_eq_of_germAb_eq (x : X) (A : SheafOfModules.{0} R) {U V : Opens X}
    (hU : x ∈ U) (hV : x ∈ V) (s : A.val.obj (op U)) (t : A.val.obj (op V))
    (h : germAb x A U hU s = germAb x A V hV t) :
    ∃ (W : Opens X) (_ : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V),
      A.val.map iU.op s = A.val.map iV.op t :=
  TopCat.Presheaf.germ_eq (presheafAb.obj A) x hU hV s t h

/-- The cokernel of a degreewise monomorphism of complexes that is relatively locally exact is
exact in every degree. -/
theorem exactAt_cokernel_of_relLocallyExact {K' K : CochainComplex (SheafOfModules.{0} R) ℕ}
    (φ : K' ⟶ K) [∀ p, Mono (φ.f p)] (h : RelLocallyExact φ) (i : ℕ) :
    (cokernel φ).ExactAt i := by
  have : Mono φ := HomologicalComplex.mono_of_mono_f φ inferInstance
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel φ) }
  have hSx : ∀ (n : ℕ) (x : X),
      ((S.map (HomologicalComplex.eval _ _ n)).map (stalkAb x)).ShortExact :=
    fun n x => (hS.map_of_exact (HomologicalComplex.eval _ _ n)).map_of_exact (stalkAb x)
  let π := cokernel.π φ
  have hprev : (ComplexShape.up ℕ).prev i = i - 1 := by
    cases i <;> simp
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) hprev (by simp)]
  refine exact_of_forall_stalkAb fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro q hq
  obtain ⟨k, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 (hSx i x).epi_g q
  have hdk : (stalkAb x).map (π.f (i + 1)) ((stalkAb x).map (K.d i (i + 1)) k) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← π.comm, Functor.map_comp,
      ConcreteCategory.comp_apply]
    exact hq
  obtain ⟨k'', hk : (stalkAb x).map (φ.f (i + 1)) k'' = (stalkAb x).map (K.d i (i + 1)) k⟩ :=
    (ShortComplex.ab_exact_iff _).1 (hSx (i + 1) x).exact _ hdk
  obtain ⟨W, hxW, s, rfl⟩ := exists_germAb_eq x (K.X i) k
  obtain ⟨W'', hxW'', s'', rfl⟩ := exists_germAb_eq x (K'.X (i + 1)) k''
  rw [stalkAb_map_germAb, stalkAb_map_germAb] at hk
  obtain ⟨W₀, hxW₀, iW, iW'', he⟩ := exists_res_eq_of_germAb_eq x _ hxW'' hxW _ _ hk
  let s₀ : (K.X i).val.obj (op W₀) := (K.X i).val.map iW''.op s
  have hz : ∃ z : (K'.X (i + 1)).val.obj (op W₀),
      (φ.f (i + 1)).val.app (op W₀) z = (K.d i (i + 1)).val.app (op W₀) s₀ := by
    refine ⟨(K'.X (i + 1)).val.map iW.op s'', ?_⟩
    have n1 := congrArg (fun f => f s'') ((φ.f (i + 1)).val.naturality iW.op)
    have n2 := congrArg (fun f => f s) ((K.d i (i + 1)).val.naturality iW''.op)
    exact n1.trans (he.trans n2.symm)
  obtain ⟨V, hV, hxV, y, x', hyx⟩ := h i W₀ s₀ hz x hxW₀
  have hs : germAb x (K.X i) W hxW s =
      germAb x (K.X i) V hxV ((K.d (i - 1) i).val.app (op V) y + (φ.f i).val.app (op V) x') := by
    rw [← hyx, germAb_res, germAb_res]
  have h0 : (stalkAb x).map (π.f i) (germAb x (K.X i) V hxV ((φ.f i).val.app (op V) x')) = 0 := by
    rw [← stalkAb_map_germAb, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f,
      Functor.map_zero]
    rfl
  have key : (stalkAb x).map ((cokernel φ).d (i - 1) i)
      ((stalkAb x).map (π.f (i - 1)) (germAb x (K.X (i - 1)) V hxV y)) =
      (stalkAb x).map (π.f i) (germAb x (K.X i) W hxW s) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, π.comm, Functor.map_comp,
      ConcreteCategory.comp_apply, stalkAb_map_germAb, hs, germAb_add, map_add, h0, add_zero]
  exact ⟨_, key⟩

/-- **Relative local exactness gives a quasi-isomorphism.** A morphism `φ : K' ⟶ K` of
`ℕ`-indexed cochain complexes of sheaves of modules on a topological space which is a
monomorphism in every degree and relatively locally exact is a quasi-isomorphism. -/
theorem quasiIso_of_relLocallyExact {K' K : CochainComplex (SheafOfModules.{0} R) ℕ}
    (φ : K' ⟶ K) [∀ p, Mono (φ.f p)] (h : RelLocallyExact φ) : QuasiIso φ := by
  have : Mono φ := HomologicalComplex.mono_of_mono_f φ inferInstance
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel φ) }
  exact quasiIso_f_of_shortExact_of_acyclic hS (exactAt_cokernel_of_relLocallyExact φ h)

end Stalks

end MMP.LcBpf
